use std::fmt::Write;

use crate::ir::{
    BinOp, ConstValue, FuncId, Function, Operand, Place, Program, Projection, Rvalue, Statement,
    Terminator, Type, TypeId, UnOp,
};

pub struct LlvmLowering<'a> {
    program: &'a Program,
    globals: String,
    out: String,
    temp_counter: u32,
    str_counter: u32,
}

impl<'a> LlvmLowering<'a> {
    pub fn lower(program: &'a Program) -> Result<String, String> {
        let mut lowering = Self {
            program,
            globals: String::new(),
            out: String::new(),
            temp_counter: 0,
            str_counter: 0,
        };
        lowering.emit_program()?;
        if lowering.globals.is_empty() {
            Ok(lowering.out)
        } else {
            Ok(format!("{}\n{}", lowering.globals, lowering.out))
        }
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
            Type::Bool | Type::I8 | Type::U8 => Ok((1, 1)),
            Type::I16 | Type::U16 => Ok((2, 2)),
            Type::I32 | Type::U32 | Type::F32 => Ok((4, 4)),
            Type::I64 | Type::U64 | Type::F64 | Type::Ptr { .. } | Type::FnPtr { .. } => Ok((8, 8)),
            Type::MetaType => {
                Err("Cannot compute runtime size of comptime 'type' (MetaType)".to_string())
            }
            Type::Array { elem, len } => {
                let (es, ea) = self.type_size_align(*elem)?;
                Ok((es * len, ea))
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
            Type::Union(variants) => {
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
            Type::Tagged { tag, variants } => {
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
            Type::I8 | Type::U8 => Ok("i8".to_string()),
            Type::I16 | Type::U16 => Ok("i16".to_string()),
            Type::I32 | Type::U32 => Ok("i32".to_string()),
            Type::I64 | Type::U64 => Ok("i64".to_string()),
            Type::F32 => Ok("float".to_string()),
            Type::F64 => Ok("double".to_string()),
            Type::MetaType => {
                Err("Cannot lower comptime 'type' (MetaType) to runtime LLVM IR".to_string())
            }
            Type::Ptr { .. } | Type::FnPtr { .. } => Ok("ptr".to_string()),
            Type::Array { elem, len } => {
                let elem_ty = self.llvm_type(*elem)?;
                Ok(format!("[{len} x {elem_ty}]"))
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
            Type::Union(variants) => self.union_llvm_type(variants),
            Type::Tagged { tag, variants } => {
                let tag_ty = self.llvm_type(*tag)?;
                let payload_ty = self.union_llvm_type(variants)?;
                Ok(format!("{{ {tag_ty}, {payload_ty} }}"))
            }
        }
    }

    fn emit_const_value(&mut self, cv: &ConstValue, ty_id: TypeId) -> Result<String, String> {
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
                    Type::Struct(fields) | Type::Union(fields) => {
                        cur_ty = *fields
                            .get(*idx as usize)
                            .ok_or_else(|| format!("Field .{idx} out of bounds on {cur_ty}"))?;
                    }
                    _ => return Err(format!("Cannot access field on non-struct/union type {cur_ty}")),
                },
                Projection::Variant(v_idx) => {
                    let Type::Tagged { variants, .. } = self.get_type(cur_ty)? else {
                        return Err(format!("Cannot access variant .v{v_idx} on non-tagged type {cur_ty}"));
                    };
                    cur_ty = *variants
                        .get(*v_idx as usize)
                        .ok_or_else(|| format!("Variant .v{v_idx} out of bounds on {cur_ty}"))?;
                }
                Projection::Index(_) => {
                    let Type::Array { elem, .. } = *self.get_type(cur_ty)? else {
                        return Err(format!("Cannot index non-array type {cur_ty}"));
                    };
                    cur_ty = elem;
                }
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
                    Type::Union(fields) => {
                        let &field_ty = fields.get(*field_idx as usize).ok_or_else(|| {
                            format!("Union field .{field_idx} out of bounds on {cur_ty}")
                        })?;
                        // With LLVM opaque pointers (`ptr`), all union fields sit at byte offset 0!
                        cur_ty = field_ty;
                    }
                    _ => {
                        return Err(format!(
                            "Cannot access field .{field_idx} on non-struct/union type {cur_ty}"
                        ));
                    }
                },
                Projection::Variant(v_idx) => {
                    let Type::Tagged { variants, .. } = self.get_type(cur_ty)? else {
                        return Err(format!(
                            "Cannot access variant .v{v_idx} on non-tagged type {cur_ty}"
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
                    let Type::Array { elem, .. } = *self.get_type(cur_ty)? else {
                        return Err(format!("Cannot index non-array type {cur_ty}"));
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

    /// Evaluates an `Operand` into an `(llvm_value_str, llvm_type_str)`.
    fn emit_operand(&mut self, func: &Function, op: &Operand) -> Result<(String, String), String> {
        match op {
            Operand::Copy(place) | Operand::Move(place) => {
                let (addr, ty_id) = self.emit_place_addr(func, place)?;
                let llvm_ty = self.llvm_type(ty_id)?;
                let val_reg = self.next_temp();
                writeln!(self.out, "  {val_reg} = load {llvm_ty}, ptr {addr}").unwrap();
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

    fn operand_is_unsigned(&self, func: &Function, op: &Operand) -> Result<bool, String> {
        if let Some(ty_id) = self.operand_type(func, op)? {
            Ok(self.get_type(ty_id)?.is_unsigned())
        } else {
            Ok(false)
        }
    }

    fn operand_is_float(&self, func: &Function, op: &Operand) -> Result<bool, String> {
        match op {
            Operand::Copy(place) | Operand::Move(place) => {
                let ty_id = self.place_type(func, place)?;
                Ok(self.get_type(ty_id)?.is_float())
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
                let Type::Tagged { tag, .. } = *self.get_type(ty_id)? else {
                    return Err(format!(
                        "Cannot set discriminant on non-tagged type {ty_id}"
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
                                writeln!(self.out, "  {res_reg} = sub {val_ty} 0, {val}").unwrap();
                            }
                            (UnOp::Not, false) => {
                                writeln!(self.out, "  {res_reg} = xor {val_ty} {val}, -1").unwrap();
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
                            let op_str = match (binop, unsigned) {
                                (BinOp::Add, _) => "add",
                                (BinOp::Sub, _) => "sub",
                                (BinOp::Mul, _) => "mul",
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
                            };
                            writeln!(self.out, "  {res_reg} = {op_str} {op_ty} {l_val}, {r_val}")
                                .unwrap();
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
                        let (src_size, _) = self.type_size_align(src_ty_id)?;
                        let (dst_size, _) = self.type_size_align(*target_ty_id)?;

                        if src_llvm_ty == dst_llvm_ty {
                            writeln!(self.out, "  store {dst_llvm_ty} {src_val}, ptr {dest_addr}")
                                .unwrap();
                        } else {
                            let cast_op = match (src_ty.is_float(), dst_ty.is_float()) {
                                (true, true) => {
                                    if dst_size > src_size {
                                        "fpext"
                                    } else {
                                        "fptrunc"
                                    }
                                }
                                (false, true) => {
                                    if src_ty.is_unsigned() {
                                        "uitofp"
                                    } else {
                                        "sitofp"
                                    }
                                }
                                (true, false) => {
                                    if dst_ty.is_unsigned() {
                                        "fptoui"
                                    } else {
                                        "fptosi"
                                    }
                                }
                                (false, false) => match (src_ty, dst_ty) {
                                    (Type::Ptr { .. } | Type::FnPtr { .. }, _) => "ptrtoint",
                                    (_, Type::Ptr { .. } | Type::FnPtr { .. }) => "inttoptr",
                                    _ if dst_size > src_size => {
                                        if src_ty.is_unsigned() || matches!(src_ty, Type::Bool) {
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
                        for (idx, field_op) in fields.iter().enumerate() {
                            let elem_ty_id = match self.get_type(*agg_ty_id)? {
                                Type::Struct(ftys) => ftys[idx],
                                Type::Array { elem, .. } => *elem,
                                _ => {
                                    return Err(format!(
                                        "Cannot aggregate into non-struct/array type {agg_ty_id}"
                                    ))
                                }
                            };
                            let (f_val, f_ty) = self.emit_operand_as(func, field_op, elem_ty_id)?;
                            let field_ptr = self.next_temp();
                            writeln!(
                                self.out,
                                "  {field_ptr} = getelementptr inbounds {agg_llvm_ty}, ptr {dest_addr}, i32 0, i32 {idx}"
                            )
                            .unwrap();
                            writeln!(self.out, "  store {f_ty} {f_val}, ptr {field_ptr}").unwrap();
                        }
                    }
                    Rvalue::Tagged {
                        ty,
                        variant,
                        payload,
                    } => {
                        let Type::Tagged { tag, variants } = self.get_type(*ty)? else {
                            return Err(format!(
                                "Cannot construct tagged value of non-tagged type {ty}"
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
                        let Type::Tagged { tag, .. } = *self.get_type(ty_id)? else {
                            return Err(format!(
                                "Cannot read discriminant of non-tagged type {ty_id}"
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
                    | Rvalue::UnionType(_)
                    | Rvalue::TaggedType { .. } => {
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
