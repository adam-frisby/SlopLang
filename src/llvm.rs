use std::fmt::Write;

use crate::ir::{
    BinOp, ConstValue, FuncId, Function, Operand, Place, Program, Projection, Rvalue, Statement,
    Terminator, Type, TypeId, UnOp,
};

pub struct LlvmLowering<'a> {
    program: &'a Program,
    globals: String,
    out: String,
    metadata: Vec<String>,
    temp_counter: u32,
    str_counter: u32,
}

impl<'a> LlvmLowering<'a> {
    pub fn lower(program: &'a Program) -> Result<String, String> {
        let mut lowering = Self {
            program,
            globals: String::new(),
            out: String::new(),
            metadata: Vec::new(),
            temp_counter: 0,
            str_counter: 0,
        };
        lowering.emit_program()?;
        let mut res = if lowering.globals.is_empty() {
            lowering.out
        } else {
            format!("{}\n{}", lowering.globals, lowering.out)
        };
        if !lowering.metadata.is_empty() {
            res.push('\n');
            for (i, md) in lowering.metadata.iter().enumerate() {
                writeln!(res, "!{i} = {md}").unwrap();
            }
        }
        Ok(res)
    }

    fn next_temp(&mut self) -> String {
        let id = self.temp_counter;
        self.temp_counter += 1;
        format!("%t{id}")
    }

    fn intern_c_string(&mut self, s: &str) -> String {
        let id = self.str_counter;
        self.str_counter += 1;
        let name = format!("@.str.{id}");
        let byte_len = s.len() + 1; // +1 for null terminator
        let mut escaped = String::new();
        for b in s.bytes() {
            if b.is_ascii_graphic() && b != b'"' && b != b'\\' {
                escaped.push(b as char);
            } else {
                write!(escaped, "\\{b:02X}").unwrap();
            }
        }
        escaped.push_str("\\00");
        writeln!(
            self.globals,
            "{name} = private unnamed_addr constant [{byte_len} x i8] c\"{escaped}\""
        )
        .unwrap();
        name
    }

    fn func_symbol(&self, id: FuncId) -> String {
        if let Some(ext) = self.program.externs.iter().find(|e| e.id == id) {
            format!("@{}", ext.symbol)
        } else if let Some(func) = self.program.functions.iter().find(|f| f.id == id)
            && let Some(sym) = &func.export
        {
            format!("@{sym}")
        } else {
            format!("@{id}")
        }
    }

    fn get_type(&self, id: TypeId) -> Result<&'a Type, String> {
        self.program
            .types
            .get(id.0 as usize)
            .ok_or_else(|| format!("Undefined {id}"))
    }

    fn type_size_align(&self, id: TypeId) -> Result<(u64, u64), String> {
        match self.get_type(id)? {
            Type::Void => Ok((0, 1)),
            Type::Bool => Ok((1, 1)),
            Type::Int { bits, .. } => {
                let size = u64::from(*bits).div_ceil(8).next_power_of_two();
                let align = size.min(16);
                Ok((size, align))
            }
            Type::Rune | Type::F32 => Ok((4, 4)),
            Type::F64 | Type::Ptr { .. } | Type::FnPtr { .. } => Ok((8, 8)),
            Type::MetaType => {
                Err("Cannot compute runtime size of comptime 'type' (MetaType)".to_string())
            }
            Type::Pattern { base, .. } => self.type_size_align(*base),
            Type::Array { elem, len } => {
                let (es, ea) = self.type_size_align(*elem)?;
                Ok((es * len, ea))
            }
            Type::Simd { elem, len } => {
                let (es, ea) = self.type_size_align(*elem)?;
                let size = es * len;
                Ok((size, size.next_power_of_two().min(64).max(ea)))
            }
            Type::Struct(fields) => {
                let mut offset = 0u64;
                let mut max_align = 1u64;
                for &f in fields {
                    let (fs, fa) = self.type_size_align(f)?;
                    max_align = max_align.max(fa);
                    offset = (offset + fa - 1) & !(fa - 1);
                    offset += fs;
                }
                let size = (offset + max_align - 1) & !(max_align - 1);
                Ok((size, max_align))
            }
            Type::Overlay(variants) => {
                let mut max_size = 0u64;
                let mut max_align = 1u64;
                for &v in variants {
                    let (vs, va) = self.type_size_align(v)?;
                    max_size = max_size.max(vs);
                    max_align = max_align.max(va);
                }
                let size = (max_size + max_align - 1) & !(max_align - 1);
                Ok((size, max_align))
            }
            Type::Union { tag, variants } => {
                let (ts, ta) = self.type_size_align(*tag)?;
                let mut max_vsize = 0u64;
                let mut max_valign = 1u64;
                for &v in variants {
                    let (vs, va) = self.type_size_align(v)?;
                    max_vsize = max_vsize.max(vs);
                    max_valign = max_valign.max(va);
                }
                let union_size = (max_vsize + max_valign - 1) & !(max_valign - 1);
                let max_align = ta.max(max_valign);
                let mut offset = ts;
                offset = (offset + max_valign - 1) & !(max_valign - 1);
                offset += union_size;
                let size = (offset + max_align - 1) & !(max_align - 1);
                Ok((size, max_align))
            }
        }
    }

    fn union_llvm_type(&self, variants: &[TypeId]) -> Result<String, String> {
        let mut max_size = 0u64;
        let mut max_align = 1u64;
        for &v in variants {
            let (vs, va) = self.type_size_align(v)?;
            max_size = max_size.max(vs);
            max_align = max_align.max(va);
        }
        let size = (max_size + max_align - 1) & !(max_align - 1);
        if size == 0 {
            return Ok("{}".to_string());
        }
        let align_bits = max_align * 8;
        let words = size / max_align;
        Ok(format!("[{words} x i{align_bits}]"))
    }

    fn llvm_type(&self, id: TypeId) -> Result<String, String> {
        match self.get_type(id)? {
            Type::Void => Ok("{}".to_string()),
            Type::Bool => Ok("i1".to_string()),
            Type::Int { bits, .. } => Ok(format!("i{bits}")),
            Type::Rune => Ok("i32".to_string()),
            Type::F32 => Ok("float".to_string()),
            Type::F64 => Ok("double".to_string()),
            Type::MetaType => {
                Err("Cannot lower comptime 'type' (MetaType) to runtime LLVM IR".to_string())
            }
            Type::Pattern { base, .. } => self.llvm_type(*base),
            Type::Ptr { .. } | Type::FnPtr { .. } => Ok("ptr".to_string()),
            Type::Array { elem, len } => {
                let elem_ty = self.llvm_type(*elem)?;
                Ok(format!("[{len} x {elem_ty}]"))
            }
            Type::Simd { elem, len } => {
                let elem_ty = self.llvm_type(*elem)?;
                Ok(format!("<{len} x {elem_ty}>"))
            }
            Type::Struct(fields) => {
                let mut s = String::from("{ ");
                for (i, &field_ty) in fields.iter().enumerate() {
                    if i > 0 {
                        s.push_str(", ");
                    }
                    s.push_str(&self.llvm_type(field_ty)?);
                }
                s.push_str(" }");
                Ok(s)
            }
            Type::Overlay(variants) => self.union_llvm_type(variants),
            Type::Union { tag, variants } => {
                let tag_ty = self.llvm_type(*tag)?;
                let payload_ty = self.union_llvm_type(variants)?;
                Ok(format!("{{ {tag_ty}, {payload_ty} }}"))
            }
        }
    }

    fn llvm_intrinsic_suffix(&self, id: TypeId) -> Result<String, String> {
        match self.get_type(id)? {
            Type::F32 => Ok("f32".to_string()),
            Type::F64 => Ok("f64".to_string()),
            Type::Pattern { base, .. } => self.llvm_intrinsic_suffix(*base),
            Type::Simd { elem, len } => {
                let elem_suf = self.llvm_intrinsic_suffix(*elem)?;
                Ok(format!("v{len}{elem_suf}"))
            }
            _ => self.llvm_type(id),
        }
    }

    fn llvm_splat_const(&self, ty_id: TypeId, scalar_val: &str) -> Result<String, String> {
        if let Type::Simd { elem, len } = *self.get_type(ty_id)? {
            let elem_ty = self.llvm_type(elem)?;
            let lane = format!("{elem_ty} {scalar_val}");
            let lanes = std::iter::repeat_n(lane, len as usize)
                .collect::<Vec<_>>()
                .join(", ");
            Ok(format!("<{lanes}>"))
        } else {
            Ok(scalar_val.to_string())
        }
    }

    fn type_bit_width(&self, id: TypeId) -> Result<u64, String> {
        match self.get_type(id)? {
            Type::Bool => Ok(1),
            Type::Int { bits, .. } => Ok(u64::from(*bits)),
            Type::Rune | Type::F32 => Ok(32),
            Type::F64 => Ok(64),
            Type::Pattern { base, .. } => self.type_bit_width(*base),
            Type::Simd { elem, len } => Ok(self.type_bit_width(*elem)? * len),
            _ => Ok(self.type_size_align(id)?.0 * 8),
        }
    }

    fn emit_const_value(&mut self, cv: &ConstValue, ty_id: TypeId) -> Result<String, String> {
        if let Type::Simd { elem, len } = *self.get_type(ty_id)? {
            let elem_ty = self.llvm_type(elem)?;
            let elem_val = self.emit_const_value(cv, elem)?;
            let lane = format!("{elem_ty} {elem_val}");
            let lanes = std::iter::repeat_n(lane, len as usize)
                .collect::<Vec<_>>()
                .join(", ");
            return Ok(format!("<{lanes}>"));
        }
        match cv {
            ConstValue::Void => Ok("zeroinitializer".to_string()),
            ConstValue::Bool(b) => Ok(if *b { "1" } else { "0" }.to_string()),
            ConstValue::I64(n) => Ok(n.to_string()),
            ConstValue::F64(bits) => {
                if matches!(self.get_type(ty_id)?, Type::F32) {
                    let f32_bits = (f64::from_bits(*bits) as f32 as f64).to_bits();
                    Ok(format!("0x{f32_bits:016X}"))
                } else {
                    Ok(format!("0x{bits:016X}"))
                }
            }
            ConstValue::Type(t) => Err(format!(
                "Cannot lower comptime type value '{t}' to runtime LLVM IR"
            )),
            ConstValue::Func(fn_id) => Ok(self.func_symbol(*fn_id)),
            ConstValue::Global(gl_id) => Ok(format!("@{gl_id}")),
            ConstValue::Str(s) => Ok(self.intern_c_string(s)),
        }
    }

    fn emit_program(&mut self) -> Result<(), String> {
        for gl in &self.program.globals {
            let gl_ty = self.llvm_type(gl.ty)?;
            let init_val = self.emit_const_value(&gl.init, gl.ty)?;
            let kind = if gl.mutable { "global" } else { "constant" };
            writeln!(self.globals, "@{} = {kind} {gl_ty} {init_val}", gl.id).unwrap();
        }
        for ext in &self.program.externs {
            let ret_ty = self.llvm_type(ext.ret)?;
            write!(self.out, "declare {ret_ty} @{}(", ext.symbol).unwrap();
            for (i, &arg_ty) in ext.args.iter().enumerate() {
                if i > 0 {
                    write!(self.out, ", ").unwrap();
                }
                write!(self.out, "{}", self.llvm_type(arg_ty)?).unwrap();
            }
            writeln!(self.out, ")").unwrap();
        }
        if !self.program.externs.is_empty() && !self.program.functions.is_empty() {
            writeln!(self.out).unwrap();
        }
        let mut emitted_any = false;
        for func in &self.program.functions {
            // Skip comptime-only functions (functions that take/return/store `type`)
            let is_comptime_only = func.locals.iter().any(|&ty_id| {
                matches!(self.program.types.get(ty_id.0 as usize), Some(Type::MetaType))
            });
            if is_comptime_only {
                continue;
            }
            if emitted_any {
                writeln!(self.out).unwrap();
            }
            self.emit_function(func)?;
            emitted_any = true;
        }
        Ok(())
    }

    fn emit_function(&mut self, func: &Function) -> Result<(), String> {
        self.temp_counter = 0;

        if func.locals.is_empty() {
            return Err(format!("Function {} is missing return local _0", func.id));
        }
        let ret_ty = self.llvm_type(func.locals[0])?;

        if let Some(sym) = &func.export {
            write!(self.out, "define {ret_ty} @{sym}(").unwrap();
        } else {
            write!(self.out, "define internal {ret_ty} @{}(", func.id).unwrap();
        }
        for i in 1..=func.arg_count {
            if i > 1 {
                write!(self.out, ", ").unwrap();
            }
            let arg_ty = self.llvm_type(func.locals[i])?;
            write!(self.out, "{arg_ty} %arg{i}").unwrap();
        }
        writeln!(self.out, ") {{").unwrap();

        // Entry block: stack allocations (`alloca`) for all locals and storing incoming args
        writeln!(self.out, "entry:").unwrap();
        for (i, &local_ty) in func.locals.iter().enumerate() {
            let llvm_ty = self.llvm_type(local_ty)?;
            writeln!(self.out, "  %_{i} = alloca {llvm_ty}").unwrap();
        }
        for i in 1..=func.arg_count {
            let arg_ty = self.llvm_type(func.locals[i])?;
            writeln!(self.out, "  store {arg_ty} %arg{i}, ptr %_{i}").unwrap();
        }
        writeln!(self.out, "  br label %bb0").unwrap();

        // Emit each basic block
        for (bb_idx, block) in func.blocks.iter().enumerate() {
            writeln!(self.out, "bb{bb_idx}:").unwrap();
            for stmt in &block.statements {
                self.emit_statement(func, stmt)?;
            }
            self.emit_terminator(func, &block.terminator)?;
        }

        writeln!(self.out, "}}").unwrap();
        Ok(())
    }

    fn place_type(&self, func: &Function, place: &Place) -> Result<TypeId, String> {
        let mut cur_ty = *func
            .locals
            .get(place.local.0 as usize)
            .ok_or_else(|| format!("Undefined local {} in {}", place.local, func.id))?;
        for proj in &place.projections {
            match proj {
                Projection::Deref => {
                    let Type::Ptr { pointee, .. } = *self.get_type(cur_ty)? else {
                        return Err(format!("Cannot deref non-pointer type {cur_ty}"));
                    };
                    cur_ty = pointee;
                }
                Projection::Field(idx) => match self.get_type(cur_ty)? {
                    Type::Struct(fields) | Type::Overlay(fields) => {
                        cur_ty = *fields
                            .get(*idx as usize)
                            .ok_or_else(|| format!("Field .{idx} out of bounds on {cur_ty}"))?;
                    }
                    _ => return Err(format!("Cannot access field on non-struct/overlay type {cur_ty}")),
                },
                Projection::Variant(v_idx) => {
                    let Type::Union { variants, .. } = self.get_type(cur_ty)? else {
                        return Err(format!("Cannot access variant .v{v_idx} on non-union type {cur_ty}"));
                    };
                    cur_ty = *variants
                        .get(*v_idx as usize)
                        .ok_or_else(|| format!("Variant .v{v_idx} out of bounds on {cur_ty}"))?;
                }
                Projection::Index(_) => match *self.get_type(cur_ty)? {
                    Type::Array { elem, .. } | Type::Simd { elem, .. } => {
                        cur_ty = elem;
                    }
                    _ => return Err(format!("Cannot index non-array/simd type {cur_ty}")),
                },
            }
        }
        Ok(cur_ty)
    }

    /// Computes the memory address (`ptr`) and pointee `TypeId` of a `Place`.
    fn emit_place_addr(
        &mut self,
        func: &Function,
        place: &Place,
    ) -> Result<(String, TypeId), String> {
        let mut cur_ptr = format!("%_{}", place.local.0);
        let mut cur_ty = *func
            .locals
            .get(place.local.0 as usize)
            .ok_or_else(|| format!("Undefined local {} in {}", place.local, func.id))?;

        for proj in &place.projections {
            match proj {
                Projection::Deref => {
                    let Type::Ptr { pointee, .. } = *self.get_type(cur_ty)? else {
                        return Err(format!("Cannot deref non-pointer type {cur_ty}"));
                    };
                    let next_ptr = self.next_temp();
                    writeln!(self.out, "  {next_ptr} = load ptr, ptr {cur_ptr}").unwrap();
                    cur_ptr = next_ptr;
                    cur_ty = pointee;
                }
                Projection::Field(field_idx) => match self.get_type(cur_ty)? {
                    Type::Struct(fields) => {
                        let &field_ty = fields.get(*field_idx as usize).ok_or_else(|| {
                            format!("Field .{field_idx} out of bounds on {cur_ty}")
                        })?;
                        let struct_llvm_ty = self.llvm_type(cur_ty)?;
                        let next_ptr = self.next_temp();
                        writeln!(
                            self.out,
                            "  {next_ptr} = getelementptr inbounds {struct_llvm_ty}, ptr {cur_ptr}, i32 0, i32 {field_idx}"
                        )
                        .unwrap();
                        cur_ptr = next_ptr;
                        cur_ty = field_ty;
                    }
                    Type::Overlay(fields) => {
                        let &field_ty = fields.get(*field_idx as usize).ok_or_else(|| {
                            format!("Overlay field .{field_idx} out of bounds on {cur_ty}")
                        })?;
                        // With LLVM opaque pointers (`ptr`), all overlay fields sit at byte offset 0!
                        cur_ty = field_ty;
                    }
                    _ => {
                        return Err(format!(
                            "Cannot access field .{field_idx} on non-struct/overlay type {cur_ty}"
                        ));
                    }
                },
                Projection::Variant(v_idx) => {
                    let Type::Union { variants, .. } = self.get_type(cur_ty)? else {
                        return Err(format!(
                            "Cannot access variant .v{v_idx} on non-union type {cur_ty}"
                        ));
                    };
                    let &var_ty = variants.get(*v_idx as usize).ok_or_else(|| {
                        format!("Variant .v{v_idx} out of bounds on {cur_ty}")
                    })?;
                    let tagged_llvm_ty = self.llvm_type(cur_ty)?;
                    let next_ptr = self.next_temp();
                    writeln!(
                        self.out,
                        "  {next_ptr} = getelementptr inbounds {tagged_llvm_ty}, ptr {cur_ptr}, i32 0, i32 1"
                    )
                    .unwrap();
                    cur_ptr = next_ptr;
                    cur_ty = var_ty;
                }
                Projection::Index(idx_local) => {
                    let elem = match *self.get_type(cur_ty)? {
                        Type::Array { elem, .. } | Type::Simd { elem, .. } => elem,
                        _ => return Err(format!("Cannot index non-array/simd type {cur_ty}")),
                    };
                    let idx_ty_id = *func
                        .locals
                        .get(idx_local.0 as usize)
                        .ok_or_else(|| format!("Undefined index local {idx_local}"))?;
                    let idx_llvm_ty = self.llvm_type(idx_ty_id)?;
                    let idx_reg = self.next_temp();
                    writeln!(
                        self.out,
                        "  {idx_reg} = load {idx_llvm_ty}, ptr %_{}",
                        idx_local.0
                    )
                    .unwrap();
                    let arr_llvm_ty = self.llvm_type(cur_ty)?;
                    let next_ptr = self.next_temp();
                    writeln!(
                        self.out,
                        "  {next_ptr} = getelementptr inbounds {arr_llvm_ty}, ptr {cur_ptr}, i64 0, {idx_llvm_ty} {idx_reg}"
                    )
                    .unwrap();
                    cur_ptr = next_ptr;
                    cur_ty = elem;
                }
            }
        }

        Ok((cur_ptr, cur_ty))
    }

    fn intern_range_metadata(&mut self, llvm_ty: &str, ranges: &[(i128, i128)]) -> usize {
        let mut md = String::from("!{");
        for (i, (lo, hi)) in ranges.iter().enumerate() {
            if i > 0 {
                md.push_str(", ");
            }
            let hi_exclusive = hi.wrapping_add(1);
            write!(md, "{llvm_ty} {lo}, {llvm_ty} {hi_exclusive}").unwrap();
        }
        md.push('}');
        if let Some(idx) = self.metadata.iter().position(|m| m == &md) {
            idx
        } else {
            let idx = self.metadata.len();
            self.metadata.push(md);
            idx
        }
    }

    /// Evaluates an `Operand` into an `(llvm_value_str, llvm_type_str)`.
    fn emit_operand(&mut self, func: &Function, op: &Operand) -> Result<(String, String), String> {
        match op {
            Operand::Copy(place) | Operand::Move(place) => {
                let (addr, ty_id) = self.emit_place_addr(func, place)?;
                let llvm_ty = self.llvm_type(ty_id)?;
                let val_reg = self.next_temp();
                let range_md = match self.get_type(ty_id)? {
                    Type::Pattern { ranges, .. } => {
                        let r = ranges.clone();
                        Some(self.intern_range_metadata(&llvm_ty, &r))
                    }
                    Type::Rune => Some(
                        self.intern_range_metadata(&llvm_ty, &[(0, 0xD7FF), (0xE000, 0x10FFFF)]),
                    ),
                    _ => None,
                };
                if let Some(md_idx) = range_md {
                    writeln!(
                        self.out,
                        "  {val_reg} = load {llvm_ty}, ptr {addr}, !range !{md_idx}"
                    )
                    .unwrap();
                } else {
                    writeln!(self.out, "  {val_reg} = load {llvm_ty}, ptr {addr}").unwrap();
                }
                Ok((val_reg, llvm_ty))
            }
            Operand::Const(cv) => match cv {
                ConstValue::Void => Ok(("zeroinitializer".to_string(), "{}".to_string())),
                ConstValue::Bool(b) => {
                    Ok((if *b { "1" } else { "0" }.to_string(), "i1".to_string()))
                }
                ConstValue::I64(n) => Ok((n.to_string(), "i64".to_string())),
                ConstValue::F64(bits) => Ok((format!("0x{bits:016X}"), "double".to_string())),
                ConstValue::Type(ty_id) => Err(format!(
                    "Cannot lower comptime type value '{ty_id}' to runtime LLVM IR"
                )),
                ConstValue::Func(fn_id) => Ok((self.func_symbol(*fn_id), "ptr".to_string())),
                ConstValue::Global(gl_id) => Ok((format!("@{gl_id}"), "ptr".to_string())),
                ConstValue::Str(s) => {
                    let sym = self.intern_c_string(s);
                    Ok((sym, "ptr".to_string()))
                }
            },
        }
    }

    fn emit_operand_as(
        &mut self,
        func: &Function,
        op: &Operand,
        target_ty: TypeId,
    ) -> Result<(String, String), String> {
        if let Operand::Const(cv) = op {
            let val = self.emit_const_value(cv, target_ty)?;
            let llvm_ty = self.llvm_type(target_ty)?;
            Ok((val, llvm_ty))
        } else {
            self.emit_operand(func, op)
        }
    }

    fn operand_type(&self, func: &Function, op: &Operand) -> Result<Option<TypeId>, String> {
        match op {
            Operand::Copy(place) | Operand::Move(place) => Ok(Some(self.place_type(func, place)?)),
            Operand::Const(_) => Ok(None),
        }
    }

    fn type_is_unsigned(&self, ty_id: TypeId) -> Result<bool, String> {
        match self.get_type(ty_id)? {
            Type::Pattern { base, .. } => self.type_is_unsigned(*base),
            Type::Simd { elem, .. } => self.type_is_unsigned(*elem),
            ty => Ok(ty.is_unsigned()),
        }
    }

    fn operand_is_unsigned(&self, func: &Function, op: &Operand) -> Result<bool, String> {
        if let Some(ty_id) = self.operand_type(func, op)? {
            self.type_is_unsigned(ty_id)
        } else {
            Ok(false)
        }
    }

    fn type_is_float(&self, ty_id: TypeId) -> Result<bool, String> {
        match self.get_type(ty_id)? {
            Type::Pattern { base, .. } => self.type_is_float(*base),
            Type::Simd { elem, .. } => self.type_is_float(*elem),
            ty => Ok(ty.is_float()),
        }
    }

    fn operand_is_float(&self, func: &Function, op: &Operand) -> Result<bool, String> {
        match op {
            Operand::Copy(place) | Operand::Move(place) => {
                let ty_id = self.place_type(func, place)?;
                self.type_is_float(ty_id)
            }
            Operand::Const(ConstValue::F64(_)) => Ok(true),
            Operand::Const(_) => Ok(false),
        }
    }

    fn emit_statement(&mut self, func: &Function, stmt: &Statement) -> Result<(), String> {
        match stmt {
            Statement::StorageLive(local) => {
                writeln!(self.out, "  ; StorageLive({local})").unwrap();
                Ok(())
            }
            Statement::StorageDead(local) => {
                writeln!(self.out, "  ; StorageDead({local})").unwrap();
                Ok(())
            }
            Statement::SetDiscriminant(place, variant) => {
                let (addr, ty_id) = self.emit_place_addr(func, place)?;
                let Type::Union { tag, .. } = *self.get_type(ty_id)? else {
                    return Err(format!(
                        "Cannot set discriminant on non-union type {ty_id}"
                    ));
                };
                let tagged_llvm_ty = self.llvm_type(ty_id)?;
                let tag_llvm_ty = self.llvm_type(tag)?;
                let tag_ptr = self.next_temp();
                writeln!(
                    self.out,
                    "  {tag_ptr} = getelementptr inbounds {tagged_llvm_ty}, ptr {addr}, i32 0, i32 0"
                )
                .unwrap();
                writeln!(self.out, "  store {tag_llvm_ty} {variant}, ptr {tag_ptr}").unwrap();
                Ok(())
            }
            Statement::Assign(dest_place, rvalue) => {
                let (dest_addr, dest_ty_id) = self.emit_place_addr(func, dest_place)?;
                let dest_llvm_ty = self.llvm_type(dest_ty_id)?;

                match rvalue {
                    Rvalue::Use(op) => {
                        let (val, _) = self.emit_operand_as(func, op, dest_ty_id)?;
                        writeln!(self.out, "  store {dest_llvm_ty} {val}, ptr {dest_addr}").unwrap();
                    }
                    Rvalue::UnaryOp(unop, op) => {
                        let is_float = self.operand_is_float(func, op)?;
                        let (val, val_ty) = self.emit_operand_as(func, op, dest_ty_id)?;
                        let res_reg = self.next_temp();
                        match (unop, is_float) {
                            (UnOp::Neg, true) => {
                                writeln!(self.out, "  {res_reg} = fneg {val_ty} {val}").unwrap();
                            }
                            (UnOp::Neg, false) => {
                                let zero = self.llvm_splat_const(dest_ty_id, "0")?;
                                writeln!(self.out, "  {res_reg} = sub {val_ty} {zero}, {val}")
                                    .unwrap();
                            }
                            (UnOp::Not, false) => {
                                let all_ones = self.llvm_splat_const(dest_ty_id, "-1")?;
                                writeln!(self.out, "  {res_reg} = xor {val_ty} {val}, {all_ones}")
                                    .unwrap();
                            }
                            (UnOp::Not, true) => {
                                return Err("Cannot apply bitwise 'not' to float".to_string());
                            }
                        }
                        writeln!(self.out, "  store {dest_llvm_ty} {res_reg}, ptr {dest_addr}")
                            .unwrap();
                    }
                    Rvalue::BinaryOp(binop, lhs, rhs) => {
                        let is_float = self.operand_is_float(func, lhs)?
                            || self.operand_is_float(func, rhs)?;
                        let unsigned = self.operand_is_unsigned(func, lhs)?
                            || self.operand_is_unsigned(func, rhs)?;
                        let inferred_ty = self
                            .operand_type(func, lhs)?
                            .or(self.operand_type(func, rhs)?)
                            .unwrap_or(dest_ty_id);
                        let (l_val, l_ty) = self.emit_operand_as(func, lhs, inferred_ty)?;
                        let (r_val, r_ty) = self.emit_operand_as(func, rhs, inferred_ty)?;
                        let op_ty = if matches!(lhs, Operand::Const(_)) {
                            r_ty
                        } else {
                            l_ty
                        };
                        let intr_suffix = self.llvm_intrinsic_suffix(inferred_ty)?;
                        let ovf_ty = if let Type::Simd { len, .. } = *self.get_type(inferred_ty)? {
                            format!("<{len} x i1>")
                        } else {
                            "i1".to_string()
                        };
                        let res_reg = self.next_temp();
                        if is_float {
                            let op_str = match binop {
                                BinOp::Add => "fadd",
                                BinOp::Sub => "fsub",
                                BinOp::Mul => "fmul",
                                BinOp::Div => "fdiv",
                                BinOp::Rem => "frem",
                                BinOp::Eq => "fcmp oeq",
                                BinOp::Ne => "fcmp une",
                                BinOp::Lt => "fcmp olt",
                                BinOp::Le => "fcmp ole",
                                BinOp::Gt => "fcmp ogt",
                                BinOp::Ge => "fcmp oge",
                                _ => {
                                    return Err(format!(
                                        "Unsupported float binary op {binop}"
                                    ))
                                }
                            };
                            writeln!(self.out, "  {res_reg} = {op_str} {op_ty} {l_val}, {r_val}")
                                .unwrap();
                        } else {
                            match (binop, unsigned) {
                                (BinOp::Add | BinOp::Sub | BinOp::Mul, _) => {
                                    let intr = match (binop, unsigned) {
                                        (BinOp::Add, false) => "sadd.with.overflow",
                                        (BinOp::Add, true) => "uadd.with.overflow",
                                        (BinOp::Sub, false) => "ssub.with.overflow",
                                        (BinOp::Sub, true) => "usub.with.overflow",
                                        (BinOp::Mul, false) => "smul.with.overflow",
                                        (BinOp::Mul, true) => "umul.with.overflow",
                                        _ => unreachable!(),
                                    };
                                    let pair_reg = self.next_temp();
                                    let ovf_reg = self.next_temp();
                                    let trap_lbl = format!("ovf_trap_{}", self.temp_counter);
                                    let ok_lbl = format!("ovf_ok_{}", self.temp_counter);
                                    self.temp_counter += 1;
                                    writeln!(
                                        self.out,
                                        "  {pair_reg} = call {{ {op_ty}, {ovf_ty} }} @llvm.{intr}.{intr_suffix}({op_ty} {l_val}, {op_ty} {r_val})"
                                    )
                                    .unwrap();
                                    writeln!(
                                        self.out,
                                        "  {res_reg} = extractvalue {{ {op_ty}, {ovf_ty} }} {pair_reg}, 0"
                                    )
                                    .unwrap();
                                    writeln!(
                                        self.out,
                                        "  {ovf_reg} = extractvalue {{ {op_ty}, {ovf_ty} }} {pair_reg}, 1"
                                    )
                                    .unwrap();
                                    let branch_cond =
                                        if let Type::Simd { len, .. } = *self.get_type(inferred_ty)? {
                                            let mask_reg = self.next_temp();
                                            let any_reg = self.next_temp();
                                            writeln!(
                                                self.out,
                                                "  {mask_reg} = bitcast <{len} x i1> {ovf_reg} to i{len}"
                                            )
                                            .unwrap();
                                            writeln!(
                                                self.out,
                                                "  {any_reg} = icmp ne i{len} {mask_reg}, 0"
                                            )
                                            .unwrap();
                                            any_reg
                                        } else {
                                            ovf_reg
                                        };
                                    writeln!(
                                        self.out,
                                        "  br i1 {branch_cond}, label %{trap_lbl}, label %{ok_lbl}"
                                    )
                                    .unwrap();
                                    writeln!(self.out, "{trap_lbl}:").unwrap();
                                    writeln!(self.out, "  call void @llvm.trap()").unwrap();
                                    writeln!(self.out, "  unreachable").unwrap();
                                    writeln!(self.out, "{ok_lbl}:").unwrap();
                                }
                                (BinOp::AddSat | BinOp::SubSat, _) => {
                                    let intr = match (binop, unsigned) {
                                        (BinOp::AddSat, false) => "sadd.sat",
                                        (BinOp::AddSat, true) => "uadd.sat",
                                        (BinOp::SubSat, false) => "ssub.sat",
                                        (BinOp::SubSat, true) => "usub.sat",
                                        _ => unreachable!(),
                                    };
                                    writeln!(
                                        self.out,
                                        "  {res_reg} = call {op_ty} @llvm.{intr}.{intr_suffix}({op_ty} {l_val}, {op_ty} {r_val})"
                                    )
                                    .unwrap();
                                }
                                (BinOp::MulSat, true) => {
                                    let all_ones = self.llvm_splat_const(inferred_ty, "-1")?;
                                    let pair_reg = self.next_temp();
                                    let raw_reg = self.next_temp();
                                    let ovf_reg = self.next_temp();
                                    writeln!(
                                        self.out,
                                        "  {pair_reg} = call {{ {op_ty}, {ovf_ty} }} @llvm.umul.with.overflow.{intr_suffix}({op_ty} {l_val}, {op_ty} {r_val})"
                                    )
                                    .unwrap();
                                    writeln!(
                                        self.out,
                                        "  {raw_reg} = extractvalue {{ {op_ty}, {ovf_ty} }} {pair_reg}, 0"
                                    )
                                    .unwrap();
                                    writeln!(
                                        self.out,
                                        "  {ovf_reg} = extractvalue {{ {op_ty}, {ovf_ty} }} {pair_reg}, 1"
                                    )
                                    .unwrap();
                                    writeln!(
                                        self.out,
                                        "  {res_reg} = select {ovf_ty} {ovf_reg}, {op_ty} {all_ones}, {op_ty} {raw_reg}"
                                    )
                                    .unwrap();
                                }
                                (BinOp::MulSat, false) => {
                                    let zero = self.llvm_splat_const(inferred_ty, "0")?;
                                    let one = self.llvm_splat_const(inferred_ty, "1")?;
                                    let all_ones = self.llvm_splat_const(inferred_ty, "-1")?;
                                    let pair_reg = self.next_temp();
                                    let raw_reg = self.next_temp();
                                    let ovf_reg = self.next_temp();
                                    let xor_reg = self.next_temp();
                                    let neg_reg = self.next_temp();
                                    let max_reg = self.next_temp();
                                    let min_reg = self.next_temp();
                                    let sat_reg = self.next_temp();
                                    writeln!(
                                        self.out,
                                        "  {pair_reg} = call {{ {op_ty}, {ovf_ty} }} @llvm.smul.with.overflow.{intr_suffix}({op_ty} {l_val}, {op_ty} {r_val})"
                                    )
                                    .unwrap();
                                    writeln!(
                                        self.out,
                                        "  {raw_reg} = extractvalue {{ {op_ty}, {ovf_ty} }} {pair_reg}, 0"
                                    )
                                    .unwrap();
                                    writeln!(
                                        self.out,
                                        "  {ovf_reg} = extractvalue {{ {op_ty}, {ovf_ty} }} {pair_reg}, 1"
                                    )
                                    .unwrap();
                                    writeln!(
                                        self.out,
                                        "  {xor_reg} = xor {op_ty} {l_val}, {r_val}"
                                    )
                                    .unwrap();
                                    writeln!(
                                        self.out,
                                        "  {neg_reg} = icmp slt {op_ty} {xor_reg}, {zero}"
                                    )
                                    .unwrap();
                                    writeln!(
                                        self.out,
                                        "  {max_reg} = lshr {op_ty} {all_ones}, {one}"
                                    )
                                    .unwrap();
                                    writeln!(
                                        self.out,
                                        "  {min_reg} = xor {op_ty} {max_reg}, {all_ones}"
                                    )
                                    .unwrap();
                                    writeln!(
                                        self.out,
                                        "  {sat_reg} = select {ovf_ty} {neg_reg}, {op_ty} {min_reg}, {op_ty} {max_reg}"
                                    )
                                    .unwrap();
                                    writeln!(
                                        self.out,
                                        "  {res_reg} = select {ovf_ty} {ovf_reg}, {op_ty} {sat_reg}, {op_ty} {raw_reg}"
                                    )
                                    .unwrap();
                                }
                                _ => {
                                    let op_str = match (binop, unsigned) {
                                        (BinOp::AddWrap, _) => "add",
                                        (BinOp::SubWrap, _) => "sub",
                                        (BinOp::MulWrap, _) => "mul",
                                        (BinOp::AddUnchecked, false) => "add nsw",
                                        (BinOp::AddUnchecked, true) => "add nuw",
                                        (BinOp::SubUnchecked, false) => "sub nsw",
                                        (BinOp::SubUnchecked, true) => "sub nuw",
                                        (BinOp::MulUnchecked, false) => "mul nsw",
                                        (BinOp::MulUnchecked, true) => "mul nuw",
                                        (BinOp::Div, false) => "sdiv",
                                        (BinOp::Div, true) => "udiv",
                                        (BinOp::Rem, false) => "srem",
                                        (BinOp::Rem, true) => "urem",
                                        (BinOp::BitAnd, _) => "and",
                                        (BinOp::BitOr, _) => "or",
                                        (BinOp::BitXor, _) => "xor",
                                        (BinOp::Shl, _) => "shl",
                                        (BinOp::Shr, false) => "ashr",
                                        (BinOp::Shr, true) => "lshr",
                                        (BinOp::Eq, _) => "icmp eq",
                                        (BinOp::Ne, _) => "icmp ne",
                                        (BinOp::Lt, false) => "icmp slt",
                                        (BinOp::Lt, true) => "icmp ult",
                                        (BinOp::Le, false) => "icmp sle",
                                        (BinOp::Le, true) => "icmp ule",
                                        (BinOp::Gt, false) => "icmp sgt",
                                        (BinOp::Gt, true) => "icmp ugt",
                                        (BinOp::Ge, false) => "icmp sge",
                                        (BinOp::Ge, true) => "icmp uge",
                                        _ => unreachable!(),
                                    };
                                    writeln!(
                                        self.out,
                                        "  {res_reg} = {op_str} {op_ty} {l_val}, {r_val}"
                                    )
                                    .unwrap();
                                }
                            }
                        }
                        writeln!(self.out, "  store {dest_llvm_ty} {res_reg}, ptr {dest_addr}")
                            .unwrap();
                    }
                    Rvalue::Cast(op, target_ty_id) => {
                        let src_ty_id = self
                            .operand_type(func, op)?
                            .ok_or_else(|| "cast requires a typed place operand".to_string())?;
                        let src_ty = self.get_type(src_ty_id)?;
                        let dst_ty = self.get_type(*target_ty_id)?;
                        let (src_val, src_llvm_ty) = self.emit_operand(func, op)?;
                        let dst_llvm_ty = self.llvm_type(*target_ty_id)?;
                        let src_bits = self.type_bit_width(src_ty_id)?;
                        let dst_bits = self.type_bit_width(*target_ty_id)?;

                        if src_llvm_ty == dst_llvm_ty {
                            writeln!(self.out, "  store {dst_llvm_ty} {src_val}, ptr {dest_addr}")
                                .unwrap();
                        } else {
                            let cast_op = match (
                                self.type_is_float(src_ty_id)?,
                                self.type_is_float(*target_ty_id)?,
                            ) {
                                (true, true) => {
                                    if dst_bits > src_bits {
                                        "fpext"
                                    } else {
                                        "fptrunc"
                                    }
                                }
                                (false, true) => {
                                    if self.type_is_unsigned(src_ty_id)? {
                                        "uitofp"
                                    } else {
                                        "sitofp"
                                    }
                                }
                                (true, false) => {
                                    if self.type_is_unsigned(*target_ty_id)? {
                                        "fptoui"
                                    } else {
                                        "fptosi"
                                    }
                                }
                                (false, false) => match (src_ty, dst_ty) {
                                    (Type::Ptr { .. } | Type::FnPtr { .. }, _) => "ptrtoint",
                                    (_, Type::Ptr { .. } | Type::FnPtr { .. }) => "inttoptr",
                                    _ if dst_bits > src_bits => {
                                        if self.type_is_unsigned(src_ty_id)?
                                            || matches!(src_ty, Type::Bool)
                                        {
                                            "zext"
                                        } else {
                                            "sext"
                                        }
                                    }
                                    _ => "trunc",
                                },
                            };
                            let res_reg = self.next_temp();
                            writeln!(
                                self.out,
                                "  {res_reg} = {cast_op} {src_llvm_ty} {src_val} to {dst_llvm_ty}"
                            )
                            .unwrap();
                            writeln!(self.out, "  store {dst_llvm_ty} {res_reg}, ptr {dest_addr}")
                                .unwrap();
                        }
                    }
                    Rvalue::Ref { place, .. } => {
                        let (ref_addr, _) = self.emit_place_addr(func, place)?;
                        writeln!(self.out, "  store ptr {ref_addr}, ptr {dest_addr}").unwrap();
                    }
                    Rvalue::Aggregate(agg_ty_id, fields) => {
                        let agg_llvm_ty = self.llvm_type(*agg_ty_id)?;
                        if let Type::Simd { elem, len } = *self.get_type(*agg_ty_id)?
                            && fields.len() == 1
                            && len > 1
                        {
                            let (f_val, f_ty) = self.emit_operand_as(func, &fields[0], elem)?;
                            for idx in 0..len {
                                let field_ptr = self.next_temp();
                                writeln!(
                                    self.out,
                                    "  {field_ptr} = getelementptr inbounds {agg_llvm_ty}, ptr {dest_addr}, i32 0, i32 {idx}"
                                )
                                .unwrap();
                                writeln!(self.out, "  store {f_ty} {f_val}, ptr {field_ptr}")
                                    .unwrap();
                            }
                        } else {
                            for (idx, field_op) in fields.iter().enumerate() {
                                let elem_ty_id = match self.get_type(*agg_ty_id)? {
                                    Type::Struct(ftys) => ftys[idx],
                                    Type::Array { elem, .. } | Type::Simd { elem, .. } => *elem,
                                    _ => {
                                        return Err(format!(
                                            "Cannot aggregate into non-struct/array/simd type {agg_ty_id}"
                                        ))
                                    }
                                };
                                let (f_val, f_ty) =
                                    self.emit_operand_as(func, field_op, elem_ty_id)?;
                                let field_ptr = self.next_temp();
                                writeln!(
                                    self.out,
                                    "  {field_ptr} = getelementptr inbounds {agg_llvm_ty}, ptr {dest_addr}, i32 0, i32 {idx}"
                                )
                                .unwrap();
                                writeln!(self.out, "  store {f_ty} {f_val}, ptr {field_ptr}")
                                    .unwrap();
                            }
                        }
                    }
                    Rvalue::Union {
                        ty,
                        variant,
                        payload,
                    } => {
                        let Type::Union { tag, variants } = self.get_type(*ty)? else {
                            return Err(format!(
                                "Cannot construct union value of non-union type {ty}"
                            ));
                        };
                        let &var_ty = variants.get(*variant as usize).ok_or_else(|| {
                            format!("Variant v{variant} out of bounds on {ty}")
                        })?;
                        let tagged_llvm_ty = self.llvm_type(*ty)?;
                        let tag_llvm_ty = self.llvm_type(*tag)?;
                        let tag_ptr = self.next_temp();
                        writeln!(
                            self.out,
                            "  {tag_ptr} = getelementptr inbounds {tagged_llvm_ty}, ptr {dest_addr}, i32 0, i32 0"
                        )
                        .unwrap();
                        writeln!(self.out, "  store {tag_llvm_ty} {variant}, ptr {tag_ptr}")
                            .unwrap();

                        if !matches!(self.get_type(var_ty)?, Type::Void) {
                            let (p_val, p_ty) = self.emit_operand_as(func, payload, var_ty)?;
                            let payload_ptr = self.next_temp();
                            writeln!(
                                self.out,
                                "  {payload_ptr} = getelementptr inbounds {tagged_llvm_ty}, ptr {dest_addr}, i32 0, i32 1"
                            )
                            .unwrap();
                            writeln!(self.out, "  store {p_ty} {p_val}, ptr {payload_ptr}")
                                .unwrap();
                        }
                    }
                    Rvalue::Discriminant(place) => {
                        let (addr, ty_id) = self.emit_place_addr(func, place)?;
                        let Type::Union { tag, .. } = *self.get_type(ty_id)? else {
                            return Err(format!(
                                "Cannot read discriminant of non-union type {ty_id}"
                            ));
                        };
                        let tagged_llvm_ty = self.llvm_type(ty_id)?;
                        let tag_llvm_ty = self.llvm_type(tag)?;
                        let tag_ptr = self.next_temp();
                        let tag_val = self.next_temp();
                        writeln!(
                            self.out,
                            "  {tag_ptr} = getelementptr inbounds {tagged_llvm_ty}, ptr {addr}, i32 0, i32 0"
                        )
                        .unwrap();
                        writeln!(self.out, "  {tag_val} = load {tag_llvm_ty}, ptr {tag_ptr}")
                            .unwrap();
                        writeln!(self.out, "  store {dest_llvm_ty} {tag_val}, ptr {dest_addr}")
                            .unwrap();
                    }
                    Rvalue::ArrayType { .. }
                    | Rvalue::SimdType { .. }
                    | Rvalue::OverlayType(_)
                    | Rvalue::UnionType { .. }
                    | Rvalue::PatternType { .. } => {
                        return Err(
                            "Cannot lower comptime type constructor to runtime LLVM IR".to_string(),
                        );
                    }
                }
                Ok(())
            }
        }
    }

    fn emit_terminator(&mut self, func: &Function, term: &Terminator) -> Result<(), String> {
        match term {
            Terminator::Goto { target } => {
                writeln!(self.out, "  br label %{target}").unwrap();
                Ok(())
            }
            Terminator::SwitchInt {
                discr,
                targets,
                otherwise,
            } => {
                let (discr_val, discr_ty) = self.emit_operand(func, discr)?;
                write!(
                    self.out,
                    "  switch {discr_ty} {discr_val}, label %{otherwise} ["
                )
                .unwrap();
                for (val, target_bb) in targets {
                    write!(self.out, "\n    {discr_ty} {val}, label %{target_bb}").unwrap();
                }
                writeln!(self.out, "\n  ]").unwrap();
                Ok(())
            }
            Terminator::Call {
                func: callee,
                args,
                destination,
                target,
            } => {
                let (callee_val, _) = self.emit_operand(func, callee)?;
                let mut evaluated_args = Vec::with_capacity(args.len());
                for arg in args {
                    evaluated_args.push(self.emit_operand(func, arg)?);
                }
                let (dest_addr, dest_ty_id) = self.emit_place_addr(func, destination)?;
                let ret_llvm_ty = self.llvm_type(dest_ty_id)?;
                let call_reg = self.next_temp();

                write!(self.out, "  {call_reg} = call {ret_llvm_ty} {callee_val}(").unwrap();
                for (i, (a_val, a_ty)) in evaluated_args.iter().enumerate() {
                    if i > 0 {
                        write!(self.out, ", ").unwrap();
                    }
                    write!(self.out, "{a_ty} {a_val}").unwrap();
                }
                writeln!(self.out, ")").unwrap();
                writeln!(self.out, "  store {ret_llvm_ty} {call_reg}, ptr {dest_addr}").unwrap();
                writeln!(self.out, "  br label %{target}").unwrap();
                Ok(())
            }
            Terminator::Drop { place, .. } => Err(format!(
                "Unelaborated 'drop({place})' terminator in {}; run drop::elaborate_drops(&mut program) before LLVM lowering",
                func.id
            )),
            Terminator::Return => {
                let ret_llvm_ty = self.llvm_type(func.locals[0])?;
                let ret_reg = self.next_temp();
                writeln!(self.out, "  {ret_reg} = load {ret_llvm_ty}, ptr %_0").unwrap();
                writeln!(self.out, "  ret {ret_llvm_ty} {ret_reg}").unwrap();
                Ok(())
            }
            Terminator::Unreachable => {
                writeln!(self.out, "  unreachable").unwrap();
                Ok(())
            }
        }
    }
}
