use super::*;

impl Compiler {
    pub fn c_type_name(&self, ty_id: TypeId) -> String {
        let ptr = |mutable: bool, pointee: TypeId| {
            let pt = self.c_type_name(pointee);
            if mutable {
                format!("{pt}*")
            } else {
                format!("const {pt}*")
            }
        };
        match self.type_kind(ty_id) {
            Some(TypeKind::CInt) => return self.c_ints[&ty_id].c_header_name().to_string(),
            Some(TypeKind::OpaqueNewtype) => return self.opaque_newtypes[&ty_id].name.clone(),
            Some(TypeKind::Composite) => return self.composites[&ty_id].name.clone(),
            Some(TypeKind::Overlay) => return self.overlays[&ty_id].name.clone(),
            Some(TypeKind::Union) => return self.unions[&ty_id].name.clone(),
            Some(TypeKind::Enum) => return self.enums[&ty_id].0.clone(),
            Some(TypeKind::Error) => return self.errors[&ty_id].name.clone(),
            Some(TypeKind::UniversalOpaque) => return "void".to_string(),
            Some(TypeKind::RawPtr) => {
                let (mutable, pointee) = self.raw_ptrs[&ty_id];
                return ptr(mutable, pointee);
            }
            _ => {}
        }
        if let Some((mutable, pointee, _)) = self.as_nullable_raw_ptr(ty_id) {
            return ptr(mutable, pointee);
        }
        match &self.program.types[ty_id.0 as usize] {
            Type::Void | Type::Never => "void".to_string(),
            Type::Bool => "bool".to_string(),
            Type::F32 => "float".to_string(),
            Type::F64 => "double".to_string(),
            Type::Rune => "uint32_t".to_string(),
            Type::Int {
                signed: true,
                bits: 8,
            } => "int8_t".to_string(),
            Type::Int {
                signed: false,
                bits: 8,
            } => "uint8_t".to_string(),
            Type::Int {
                signed: true,
                bits: 16,
            } => "int16_t".to_string(),
            Type::Int {
                signed: false,
                bits: 16,
            } => "uint16_t".to_string(),
            Type::Int {
                signed: true,
                bits: 32,
            } => "int32_t".to_string(),
            Type::Int {
                signed: false,
                bits: 32,
            } => "uint32_t".to_string(),
            Type::Int {
                signed: true,
                bits: 64,
            } => "int64_t".to_string(),
            Type::Int {
                signed: false,
                bits: 64,
            } => "uint64_t".to_string(),
            other => format!("/* {} */ void", other),
        }
    }

    pub fn c_decl(&self, ty_id: TypeId, ident: &str) -> String {
        if self.program.c_fn_ptr_types.contains(&ty_id)
            && let Type::FnPtr { args, ret } = &self.program.types[ty_id.0 as usize]
        {
            let params: Vec<String> = args.iter().map(|a| self.c_type_name(*a)).collect();
            let params = if params.is_empty() { "void".to_string() } else { params.join(", ") };
            return format!("{} (*{ident})({params})", self.c_type_name(*ret));
        }
        let mut cur = ty_id;
        let mut dims = String::new();
        while let Type::Array { elem, len } = self.program.types[cur.0 as usize] {
            dims.push_str(&format!("[{len}]"));
            cur = elem;
        }
        format!("{} {}{}", self.c_type_name(cur), ident, dims)
    }

    pub fn generate_c_header(&self) -> String {
        use std::fmt::Write as _;
        let mut out = String::new();
        writeln!(out, "#ifndef LRRR_EXPORT_H").unwrap();
        writeln!(out, "#define LRRR_EXPORT_H").unwrap();
        writeln!(out).unwrap();
        writeln!(out, "#include <stdint.h>").unwrap();
        writeln!(out, "#include <stddef.h>").unwrap();
        writeln!(out, "#include <stdbool.h>").unwrap();
        writeln!(out).unwrap();
        writeln!(out, "#ifdef __cplusplus").unwrap();
        writeln!(out, "extern \"C\" {{").unwrap();
        writeln!(out, "#endif").unwrap();
        writeln!(out).unwrap();

        // 1. Forward declarations for exported opaque types, opaque structs, and records
        let mut emitted_forwards = false;
        for meta in &self.exported_types {
            if self.named_opaques.contains(&meta.ty_id) || self.composites.contains_key(&meta.ty_id)
            {
                writeln!(out, "typedef struct {0} {0};", meta.name).unwrap();
                emitted_forwards = true;
            } else if self.overlays.contains_key(&meta.ty_id) {
                writeln!(out, "typedef union {0} {0};", meta.name).unwrap();
                emitted_forwards = true;
            } else if self.unions.contains_key(&meta.ty_id) {
                writeln!(out, "typedef struct {0} {0};", meta.name).unwrap();
                emitted_forwards = true;
            }
        }
        if emitted_forwards {
            writeln!(out).unwrap();
        }

        // 2. Concrete type definitions for exported enums, errors, newtypes/aliases, and records
        for meta in &self.exported_types {
            let tid = meta.ty_id;
            if let Some((_, variants)) = self.enums.get(&tid) {
                writeln!(out, "typedef enum {} {{", meta.name).unwrap();
                for (vname, val) in variants {
                    writeln!(out, "    {}_{} = {},", meta.name, vname, val).unwrap();
                }
                writeln!(out, "}} {};\n", meta.name).unwrap();
            } else if let Some(err_info) = self.errors.get(&tid) {
                let mut enumerators = vec![format!(
                    "    {}_{} = {},",
                    meta.name, err_info.ok_flag.0, err_info.ok_flag.1
                )];
                let c_values = self.export_error_values.get(&tid);
                let value = |idx: usize| c_values.map_or((idx + 1) as i128, |v| v[idx]);
                let mut order: Vec<usize> = (0..err_info.leaves.len()).collect();
                order.sort_by_key(|&idx| value(idx));
                for idx in order {
                    let leaf = &err_info.leaves[idx];
                    enumerators.push(if leaf.key.error_name == meta.name {
                        format!("    {}_{} = {},", meta.name, leaf.key.variant_name, value(idx))
                    } else {
                        format!(
                            "    {}_{}_{} = {},",
                            meta.name,
                            leaf.key.error_name,
                            leaf.key.variant_name,
                            value(idx)
                        )
                    });
                }
                let enumerators = enumerators.join("\n");
                if let Some(b_ty) = err_info.c_backing
                    && self.c_ints.get(&b_ty) != Some(&CIntKind::CInt)
                {
                    // A fixed underlying type needs C23 or C++11; earlier C gets the same layout
                    // from a typedef of the backing integer plus anonymous enum constants.
                    let b_name = self.c_type_name(b_ty);
                    writeln!(
                        out,
                        "#if defined(__cplusplus) || (defined(__STDC_VERSION__) && __STDC_VERSION__ >= 202311L)"
                    )
                    .unwrap();
                    writeln!(out, "typedef enum {} : {b_name} {{", meta.name).unwrap();
                    writeln!(out, "{enumerators}").unwrap();
                    writeln!(out, "}} {};", meta.name).unwrap();
                    writeln!(out, "#else").unwrap();
                    writeln!(out, "typedef {b_name} {};", meta.name).unwrap();
                    writeln!(out, "enum {{").unwrap();
                    writeln!(out, "{enumerators}").unwrap();
                    writeln!(out, "}};").unwrap();
                    writeln!(out, "#endif\n").unwrap();
                } else {
                    writeln!(out, "typedef enum {} {{", meta.name).unwrap();
                    writeln!(out, "{enumerators}").unwrap();
                    writeln!(out, "}} {};\n", meta.name).unwrap();
                }
            } else if let Some(nt) = self.opaque_newtypes.get(&tid) {
                writeln!(
                    out,
                    "typedef {} {};\n",
                    self.c_type_name(nt.underlying),
                    meta.name
                )
                .unwrap();
            } else if let Some(comp) = self.composites.get(&tid) {
                if !comp.is_opaque {
                    writeln!(out, "struct {} {{", meta.name).unwrap();
                    for (fname, fty, _, _) in &comp.fields {
                        writeln!(out, "    {};", self.c_decl(*fty, fname)).unwrap();
                    }
                    writeln!(out, "}};\n").unwrap();
                }
            } else if let Some(u_info) = self.unions.get(&tid) {
                self.emit_c_union(&mut out, &meta.name, tid, &u_info.variants);
            } else if let Some(ov_info) = self.overlays.get(&tid) {
                writeln!(out, "union {} {{", meta.name).unwrap();
                for (fname, fty) in &ov_info.fields {
                    writeln!(out, "    {};", self.c_decl(*fty, fname)).unwrap();
                }
                writeln!(out, "}};\n").unwrap();
            } else if !self.named_opaques.contains(&tid) {
                writeln!(out, "typedef {} {};\n", self.c_type_name(tid), meta.name).unwrap();
            }
        }

        // 3. Function prototypes for exported functions
        for fmeta in &self.exported_funcs {
            let mut c_params: Vec<String> = fmeta
                .params
                .iter()
                .map(|(pname, pty)| self.c_decl(*pty, pname))
                .collect();
            let ret_c = match &fmeta.ret_kind {
                ExportRetKind::Direct(ret_ty) => self.c_type_name(*ret_ty),
                ExportRetKind::OptionalPtr { raw_ptr_ty, .. } => self.c_type_name(*raw_ptr_ty),
                ExportRetKind::OptionalVal { val_ty, .. } => {
                    c_params.push(format!("/* out */ {}* out_val", self.c_type_name(*val_ty)));
                    "bool".to_string()
                }
                ExportRetKind::ResultVal { err_ty, ok_ty, .. } => {
                    if !matches!(self.program.types[ok_ty.0 as usize], Type::Void) {
                        c_params.push(format!("/* out */ {}* out_val", self.c_type_name(*ok_ty)));
                    }
                    self.c_type_name(*err_ty)
                }
            };
            let params_str = if c_params.is_empty() {
                "void".to_string()
            } else {
                c_params.join(", ")
            };
            writeln!(out, "{} {}({});", ret_c, fmeta.symbol, params_str).unwrap();
        }

        writeln!(out).unwrap();
        writeln!(out, "#ifdef __cplusplus").unwrap();
        writeln!(out, "}}").unwrap();
        writeln!(out, "#endif").unwrap();
        writeln!(out).unwrap();
        writeln!(out, "#endif /* LRRR_EXPORT_H */").unwrap();
        out
    }

    /// An exported union as C's tagged representation: a tag enum (`<Name>_Tag`, unless linked
    /// to an exported enum with `union(Enum)`) and `struct { tag; union { ... } payload; }`.
    fn emit_c_union(
        &self,
        out: &mut String,
        name: &str,
        ty: TypeId,
        variants: &[(String, TypeId)],
    ) {
        use std::fmt::Write as _;
        let Type::Union { tag, .. } = self.program.types[ty.0 as usize] else {
            return;
        };
        let linked = self.union_tag_enums.get(&ty).copied().filter(|e| {
            self.program.union_tag_values(ty).is_some() && self.exported_type_set.contains(e)
        });
        let tag_c = match linked {
            Some(e) => self.c_type_name(e),
            None => {
                writeln!(out, "typedef enum {name}_Tag {{").unwrap();
                for (i, (vname, _)) in variants.iter().enumerate() {
                    writeln!(out, "    {name}_{vname} = {i},").unwrap();
                }
                writeln!(out, "}} {name}_Tag;\n").unwrap();
                if matches!(self.program.types[tag.0 as usize], Type::Int { bits: 32, .. }) {
                    format!("{name}_Tag")
                } else {
                    self.c_type_name(tag)
                }
            }
        };
        writeln!(out, "struct {name} {{").unwrap();
        writeln!(out, "    {tag_c} tag;").unwrap();
        let members: Vec<String> = variants
            .iter()
            .filter(|(_, p)| !matches!(self.program.types[p.0 as usize], Type::Void))
            .map(|(vname, p)| format!("        {};", self.c_member_decl(*p, vname, "        ")))
            .collect();
        if !members.is_empty() {
            writeln!(out, "    union {{").unwrap();
            for m in members {
                writeln!(out, "{m}").unwrap();
            }
            writeln!(out, "    }} payload;").unwrap();
        }
        writeln!(out, "}};\n").unwrap();
    }

    pub(super) fn register_and_validate_exported_type(
        &mut self,
        _def_mod: &str,
        orig_name: &str,
        ty_id: TypeId,
        ty_expr: &TypeExpr,
    ) -> Result<(), String> {
        if !self.exported_type_set.insert(ty_id)
            && self.exported_types.iter().any(|m| m.ty_id == ty_id)
        {
            return Ok(());
        }
        match ty_expr {
            TypeExpr::Union { .. } => {
                // C sees `struct { Tag tag; union { ... } payload; }`, Lrrr's own layout.
                let info = self.unions[&ty_id].clone();
                for (vname, p_ty) in &info.variants {
                    self.validate_export_payload(
                        *p_ty,
                        &format!("payload of variant '{orig_name}::{vname}'"),
                    )?;
                }
                if !self.is_copy_type(ty_id) {
                    return Err(format!(
                        "Exported union '{orig_name}' must be 'copy' (C copies it freely); its payloads cannot own resources"
                    ));
                }
                if let Some(&tag_enum) = self.union_tag_enums.get(&ty_id)
                    && self.program.union_tag_values(ty_id).is_some()
                    && !self.exported_type_set.contains(&tag_enum)
                {
                    return Err(format!(
                        "Tag enum '{}' of exported union '{orig_name}' is not declared 'export'",
                        self.type_display_name(tag_enum)
                    ));
                }
            }
            TypeExpr::Trait(_) => {
                return Err(format!(
                    "Traits cannot be declared 'export' ('{orig_name}')"
                ));
            }
            TypeExpr::Error { .. } => {
                return Err(format!(
                    "Tagged 'error' types cannot be declared 'export' ('{orig_name}'); use 'export errorcode' instead"
                ));
            }
            TypeExpr::ErrorCode { .. } => {}
            TypeExpr::Struct { .. } => {
                if let Some(comp) = self.composites.get(&ty_id).cloned() {
                    for (fname, fty, _, _) in &comp.fields {
                        self.validate_export_field_type(
                            *fty,
                            &format!("field '{}' of export struct '{}'", fname, orig_name),
                        )?;
                    }
                }
            }
            TypeExpr::Overlay(_) => {
                if let Some(ov_info) = self.overlays.get(&ty_id).cloned() {
                    for (fname, fty) in &ov_info.fields {
                        self.validate_export_field_type(
                            *fty,
                            &format!("field '{}' of export overlay '{}'", fname, orig_name),
                        )?;
                    }
                }
            }
            TypeExpr::Opaque { .. }
            | TypeExpr::BareOpaque
            | TypeExpr::OpaqueDef { .. }
            | TypeExpr::Enum { .. } => {}
            TypeExpr::OpaqueNewtype { .. } => {
                if let Some(nt) = self.opaque_newtypes.get(&ty_id).cloned() {
                    self.validate_export_value_type(
                        nt.underlying,
                        &format!("export opaque newtype '{}'", orig_name),
                    )?;
                }
            }
            _ => {
                if let Some(err_info) = self.errors.get(&ty_id).cloned() {
                    if !err_info.is_errorcode {
                        return Err(format!(
                            "Tagged 'error' types cannot be declared 'export' ('{orig_name}'); use 'export errorcode' instead"
                        ));
                    }
                } else {
                    self.validate_export_value_type(ty_id, &format!("export type '{orig_name}'"))?;
                }
            }
        }
        if !self.exported_types.iter().any(|m| m.ty_id == ty_id) {
            self.exported_types.push(ExportedTypeMeta {
                name: orig_name.to_string(),
                ty_id,
            });
        }
        Ok(())
    }

    pub(super) fn validate_export_pointee_type(
        &self,
        pointee: TypeId,
        ctx: &str,
    ) -> Result<(), String> {
        if self.is_universal_opaque_type(pointee) {
            return Ok(());
        }
        if self.named_opaques.contains(&pointee) {
            if !self.exported_type_set.contains(&pointee) {
                return Err(format!(
                    "Cannot use pointer to non-exported opaque type '{}' in {}; declare it with 'export opaque {}'",
                    self.type_display_name(pointee),
                    ctx,
                    self.type_display_name(pointee)
                ));
            }
            return Ok(());
        }
        if let Some(comp) = self.composites.get(&pointee)
            && comp.is_opaque
        {
            if !self.exported_type_set.contains(&pointee) {
                return Err(format!(
                    "Cannot use pointer to non-exported opaque '{}' in {}; declare it with 'export opaque {}'",
                    comp.name, ctx, comp.name
                ));
            }
            return Ok(());
        }
        self.validate_export_field_type(pointee, ctx)
    }

    /// Validates the payload of an exported union variant: `void`, an anonymous struct or tuple
    /// of FFI-safe fields (emitted inline), or any FFI-safe field type.
    fn validate_export_payload(&self, ty: TypeId, ctx: &str) -> Result<(), String> {
        if let Some(fields) = self.inline_c_struct_fields(ty) {
            for (fname, fty) in fields {
                self.validate_export_payload(fty, &format!("field '{fname}' of {ctx}"))?;
            }
            return Ok(());
        }
        if matches!(self.program.types[ty.0 as usize], Type::Void) {
            return Ok(());
        }
        self.validate_export_field_type(ty, ctx)
    }

    /// The fields of an anonymous struct or a tuple, which C headers declare inline
    /// (`struct { ... } name;`); `None` for named and non-struct types.
    fn inline_c_struct_fields(&self, ty: TypeId) -> Option<Vec<(String, TypeId)>> {
        if let Some(comp) = self.composites.get(&ty) {
            // Anonymous structs (`<anon_struct>`) and inline variant payloads (`Msg::Move`).
            let inline = comp.name.starts_with('<') || comp.name.contains("::");
            return (inline && !comp.is_opaque)
                .then(|| comp.fields.iter().map(|(n, t, _, _)| (n.clone(), *t)).collect());
        }
        match &self.program.types[ty.0 as usize] {
            Type::Struct(elems) if self.type_kind(ty).is_none() => Some(
                elems.iter().enumerate().map(|(i, t)| (format!("_{i}"), *t)).collect(),
            ),
            _ => None,
        }
    }

    /// A C member declaration of `ty` named `ident`, with anonymous structs and tuples inline.
    fn c_member_decl(&self, ty: TypeId, ident: &str, indent: &str) -> String {
        match self.inline_c_struct_fields(ty) {
            Some(fields) => {
                let inner = format!("{indent}    ");
                let members: Vec<String> = fields
                    .iter()
                    .map(|(n, t)| format!("{inner}{};\n", self.c_member_decl(*t, n, &inner)))
                    .collect();
                format!("struct {{\n{}{indent}}} {ident}", members.concat())
            }
            None => self.c_decl(ty, ident),
        }
    }

    /// The stored tag values a C caller may pass for an exported `errorcode` or union, used to
    /// trap on anything else: `(tag type, values)`.
    pub(super) fn c_valid_tags(&self, ty: TypeId) -> Option<(TypeId, Vec<i128>)> {
        if !self.exported_type_set.contains(&ty) {
            return None;
        }
        let Type::Union { tag, variants } = &self.program.types[ty.0 as usize] else {
            return None;
        };
        if let Some(values) = self.export_error_values.get(&ty) {
            return Some((*tag, values.clone()));
        }
        if !self.unions.contains_key(&ty) {
            return None;
        }
        let values = match self.program.union_tag_values(ty) {
            Some(v) => v.to_vec(),
            None => (0..variants.len() as i128).collect(),
        };
        Some((*tag, values))
    }

    /// For a scalar whose valid values Lrrr restricts but C does not (`bool`, an enum, `rune`,
    /// a pattern type, a non-null raw pointer): the integer type of its storage and the valid
    /// ranges of that integer.
    fn c_scalar_valid_ranges(&mut self, ty: TypeId) -> Option<(TypeId, Vec<(Wide, Wide)>)> {
        let int = |c: &mut Self, signed, bits| c.intern_type(Type::Int { signed, bits });
        if self.raw_ptrs.contains_key(&ty) {
            let usize_ty = int(self, false, 64);
            return Some((usize_ty, vec![(Wide::from_i128(1), Wide::max_value(64, false))]));
        }
        if let Some((_, values)) = self.enums.get(&ty) {
            let ranges = values
                .iter()
                .map(|&(_, v)| (Wide::from_i128(v), Wide::from_i128(v)))
                .collect();
            let Type::Int { signed, bits } = self.program.types[ty.0 as usize] else {
                return None;
            };
            return Some((int(self, signed, bits), ranges));
        }
        match self.program.types[ty.0 as usize].clone() {
            Type::Bool => Some((int(self, false, 8), vec![(Wide::ZERO, Wide::from_i128(1))])),
            Type::Rune => Some((
                int(self, false, 32),
                vec![
                    (Wide::ZERO, Wide::from_i128(0xD7FF)),
                    (Wide::from_i128(0xE000), Wide::from_i128(0x10FFFF)),
                ],
            )),
            Type::Pattern { base, ranges } => Some((base, ranges)),
            _ => None,
        }
    }

    /// Whether a value of `ty` received from C needs checking (see `emit_c_value_checks`).
    fn c_value_needs_checks(&mut self, ty: TypeId) -> bool {
        if let Some(nt) = self.opaque_newtypes.get(&ty) {
            return self.c_value_needs_checks(nt.underlying);
        }
        if self.c_scalar_valid_ranges(ty).is_some() || self.c_valid_tags(ty).is_some() {
            return true;
        }
        match self.program.types[ty.0 as usize].clone() {
            Type::Struct(fields) => fields.iter().any(|&f| self.c_value_needs_checks(f)),
            Type::Array { elem, len } => len > 0 && self.c_value_needs_checks(elem),
            _ => false,
        }
    }

    /// Emits checks that the value C handed over at `place` (of type `ty`) is a valid Lrrr
    /// value, branching to `trap_bb` otherwise: restricted scalars hold an allowed value (read
    /// as their raw storage integer), union and `errorcode` tags name a variant, and the fields,
    /// elements, and active payload of an aggregate are valid in turn. Overlays are not checked:
    /// any bits are a valid overlay.
    fn emit_c_value_checks(
        &mut self,
        b: &mut BodyBuilder,
        place: Place,
        ty: TypeId,
        trap_bb: BlockId,
    ) {
        if !self.c_value_needs_checks(ty) {
            return;
        }
        if let Some(nt) = self.opaque_newtypes.get(&ty) {
            let underlying = nt.underlying;
            return self.emit_c_value_checks(b, place, underlying, trap_bb);
        }
        let with = |proj: Projection| {
            let mut p = place.clone();
            p.projections.push(proj);
            p
        };
        if let Some((raw_ty, ranges)) = self.c_scalar_valid_ranges(ty) {
            let raw = if self.raw_ptrs.contains_key(&ty) {
                // A pointer's address, by conversion (as the compile-time VM can also do).
                let addr = b.alloc_temp(raw_ty);
                b.emit(Statement::Assign(
                    Place::new(addr),
                    Rvalue::Cast(Operand::Copy(place), raw_ty),
                ));
                addr
            } else {
                self.emit_c_raw_read(b, place, ty, raw_ty)
            };
            self.emit_c_range_check(b, raw, &ranges, trap_bb);
            return;
        }
        if let Some((tag_ty, values)) = self.c_valid_tags(ty) {
            let tag_bits = match self.program.types[tag_ty.0 as usize] {
                Type::Int { bits, .. } => bits,
                _ => 32,
            };
            let raw_ty = self.intern_type(Type::Int {
                signed: false,
                bits: tag_bits,
            });
            // The tag is the first field: read it through a pointer to the whole value.
            let raw = self.emit_c_raw_read(b, place.clone(), ty, raw_ty);
            let stored = |v: i128| {
                if tag_bits >= 128 {
                    v
                } else {
                    v.rem_euclid(1i128 << tag_bits)
                }
            };
            let Type::Union { variants, .. } = self.program.types[ty.0 as usize].clone() else {
                return;
            };
            // Each variant's tag leads to the check of its payload, then to `join`.
            let join = b.new_block();
            let mut targets = Vec::new();
            for (i, &v) in values.iter().enumerate() {
                let payload = variants.get(i).copied();
                match payload {
                    Some(p) if self.c_value_needs_checks(p) => {
                        let bb = b.new_block();
                        targets.push((stored(v), bb));
                        let resume = b.cur_block;
                        b.cur_block = bb;
                        let payload_place = with(Projection::Variant(i as u32));
                        self.emit_c_value_checks(b, payload_place, p, trap_bb);
                        b.terminate(Terminator::Goto { target: join });
                        b.cur_block = resume;
                    }
                    _ => targets.push((stored(v), join)),
                }
            }
            b.terminate(Terminator::SwitchInt {
                discr: Operand::Copy(Place::new(raw)),
                targets,
                otherwise: trap_bb,
            });
            b.cur_block = join;
            return;
        }
        match self.program.types[ty.0 as usize].clone() {
            Type::Struct(fields) => {
                for (i, f) in fields.into_iter().enumerate() {
                    self.emit_c_value_checks(b, with(Projection::Field(i as u32)), f, trap_bb);
                }
            }
            Type::Array { elem, len } => {
                // `for i in 0..len { check(place[i]) }`
                let usize_ty = self.intern_type(Type::Int {
                    signed: false,
                    bits: 64,
                });
                let bool_ty = self.intern_type(Type::Bool);
                let idx = b.alloc_temp(usize_ty);
                let more = b.alloc_temp(bool_ty);
                b.emit(Statement::Assign(
                    Place::new(idx),
                    Rvalue::Use(Operand::Const(ConstValue::I64(0))),
                ));
                let (head, body, exit) = (b.new_block(), b.new_block(), b.new_block());
                b.terminate(Terminator::Goto { target: head });
                b.cur_block = head;
                b.emit(Statement::Assign(
                    Place::new(more),
                    Rvalue::BinaryOp(
                        BinOp::Lt,
                        Operand::Copy(Place::new(idx)),
                        Operand::Const(ConstValue::I64(len as i128)),
                    ),
                ));
                b.terminate(Terminator::SwitchInt {
                    discr: Operand::Copy(Place::new(more)),
                    targets: vec![(1, body)],
                    otherwise: exit,
                });
                b.cur_block = body;
                self.emit_c_value_checks(b, with(Projection::Index(idx)), elem, trap_bb);
                b.emit(Statement::Assign(
                    Place::new(idx),
                    Rvalue::BinaryOp(
                        BinOp::AddWrap,
                        Operand::Copy(Place::new(idx)),
                        Operand::Const(ConstValue::I64(1)),
                    ),
                ));
                b.terminate(Terminator::Goto { target: head });
                b.cur_block = exit;
            }
            _ => {}
        }
    }

    /// Checks every value C hands back to the Lrrr function `b`: the results of calls to
    /// `extern fn`s and through `extern fn(...)` pointers (see `emit_c_value_checks`).
    pub(super) fn check_c_call_results(&mut self, b: &mut BodyBuilder) {
        for bb in 0..b.blocks.len() {
            let Terminator::Call {
                func,
                destination,
                target,
                ..
            } = &b.blocks[bb].terminator
            else {
                continue;
            };
            let ret_ty = match func {
                Operand::Const(ConstValue::Func(id)) => {
                    let ext = self.program.externs.iter().find(|e| e.id == *id);
                    match ext {
                        Some(e)
                            if !e.symbol.starts_with("llvm.")
                                && !e.symbol.starts_with(crate::vm::HOST_PREFIX) =>
                        {
                            e.ret
                        }
                        _ => continue,
                    }
                }
                Operand::Copy(p) | Operand::Move(p) if p.projections.is_empty() => {
                    let ty = b.locals[p.local.0 as usize];
                    match &self.program.types[ty.0 as usize] {
                        Type::FnPtr { ret, .. } if self.program.c_fn_ptr_types.contains(&ty) => {
                            *ret
                        }
                        _ => continue,
                    }
                }
                _ => continue,
            };
            if !self.c_value_needs_checks(ret_ty) {
                continue;
            }
            let (destination, target) = (destination.clone(), *target);
            let check_bb = b.new_block();
            if let Terminator::Call { target, .. } = &mut b.blocks[bb].terminator {
                *target = check_bb;
            }
            b.cur_block = check_bb;
            let trap_bb = b.new_block();
            self.emit_c_value_checks(b, destination, ret_ty, trap_bb);
            b.terminate(Terminator::Goto { target });
        }
    }

    /// Reads the storage of the value at `place` (of type `ty`) as the integer type `raw_ty`,
    /// through a pointer, so that no invalid value of `ty` is ever loaded.
    fn emit_c_raw_read(
        &mut self,
        b: &mut BodyBuilder,
        place: Place,
        ty: TypeId,
        raw_ty: TypeId,
    ) -> LocalId {
        let ref_ty = self.intern_type(Type::Ptr {
            mutable: false,
            pointee: ty,
        });
        let raw_ptr_ty = self.intern_raw_ptr_type(false, raw_ty);
        let r = b.alloc_temp(ref_ty);
        let raw_ptr = b.alloc_temp(raw_ptr_ty);
        let raw = b.alloc_temp(raw_ty);
        b.emit(Statement::Assign(
            Place::new(r),
            Rvalue::Ref {
                mutable: false,
                place,
            },
        ));
        b.emit(Statement::Assign(
            Place::new(raw_ptr),
            Rvalue::Cast(Operand::Copy(Place::new(r)), raw_ptr_ty),
        ));
        b.emit(Statement::Assign(
            Place::new(raw),
            Rvalue::Use(Operand::Copy(Place {
                local: raw_ptr,
                projections: vec![Projection::Deref],
            })),
        ));
        raw
    }

    /// Branches to `trap_bb` unless the integer local `raw` lies in one of `ranges`.
    fn emit_c_range_check(
        &mut self,
        b: &mut BodyBuilder,
        raw: LocalId,
        ranges: &[(Wide, Wide)],
        trap_bb: BlockId,
    ) {
        let bool_ty = self.intern_type(Type::Bool);
        let ok = b.new_block();
        for &(lo, hi) in ranges {
            let next = b.new_block();
            for (op, bound) in [(BinOp::Ge, lo), (BinOp::Le, hi)] {
                let cond = b.alloc_temp(bool_ty);
                b.emit(Statement::Assign(
                    Place::new(cond),
                    Rvalue::BinaryOp(
                        op,
                        Operand::Copy(Place::new(raw)),
                        Operand::Const(int_const(bound)),
                    ),
                ));
                let pass = b.new_block();
                b.terminate(Terminator::SwitchInt {
                    discr: Operand::Copy(Place::new(cond)),
                    targets: vec![(1, pass)],
                    otherwise: next,
                });
                b.cur_block = pass;
            }
            b.terminate(Terminator::Goto { target: ok });
            b.cur_block = next;
        }
        b.terminate(Terminator::Goto { target: trap_bb });
        b.cur_block = ok;
    }

    pub(super) fn validate_export_field_type(
        &self,
        ty_id: TypeId,
        ctx: &str,
    ) -> Result<(), String> {
        if let Type::Array { elem, .. } = self.program.types[ty_id.0 as usize] {
            return self.validate_export_field_type(elem, ctx);
        }
        self.validate_export_value_type(ty_id, ctx)
    }

    pub(super) fn validate_export_value_type(
        &self,
        ty_id: TypeId,
        ctx: &str,
    ) -> Result<(), String> {
        if self.slices.contains_key(&ty_id) {
            return Err(format!(
                "Safe slice or string reference '{}' is forbidden across FFI in {}; pass a raw pointer and length instead",
                self.type_display_name(ty_id),
                ctx
            ));
        }
        if self.trait_objs.contains_key(&ty_id) {
            return Err(format!(
                "Dynamic trait reference '{}' is forbidden across FFI in {}",
                self.type_display_name(ty_id),
                ctx
            ));
        }
        if let Some((_, pointee, _)) = self.as_nullable_raw_ptr(ty_id) {
            return self.validate_export_pointee_type(pointee, ctx);
        }
        if let Some(&(_, pointee)) = self.raw_ptrs.get(&ty_id) {
            return self.validate_export_pointee_type(pointee, ctx);
        }
        if matches!(self.program.types[ty_id.0 as usize], Type::Ptr { .. }) {
            return Err(format!(
                "Safe reference '{}' is forbidden across FFI in {}; use raw pointers ('*const T', '*mut T', '?*const T', '?*mut T') instead",
                self.type_display_name(ty_id),
                ctx
            ));
        }
        if let Some(comp) = self.composites.get(&ty_id) {
            if comp.is_opaque {
                return Err(format!(
                    "Opaque type '{}' cannot be passed, returned, or embedded by value in {}; an 'export opaque' is a handle type and must be passed behind a raw pointer ('*const {}' or '*mut {}')",
                    comp.name, ctx, comp.name, comp.name
                ));
            }
            if !self.exported_type_set.contains(&ty_id) {
                return Err(format!(
                    "Struct '{}' used in {} is not declared 'export'; declare it with 'export struct {}'",
                    comp.name, ctx, comp.name
                ));
            }
            return Ok(());
        }
        if let Some((ename, _)) = self.enums.get(&ty_id) {
            if !self.exported_type_set.contains(&ty_id) {
                return Err(format!(
                    "Enum '{}' used in {} is not declared 'export'; declare it with 'export enum {}'",
                    ename, ctx, ename
                ));
            }
            return Ok(());
        }
        if let Some(err_info) = self.errors.get(&ty_id) {
            if !err_info.is_errorcode {
                return Err(format!(
                    "Tagged error '{}' is forbidden across FFI in {}; use an 'export errorcode' instead",
                    err_info.name, ctx
                ));
            }
            if !self.exported_type_set.contains(&ty_id) {
                return Err(format!(
                    "Errorcode '{}' used in {} is not declared 'export'; declare it with 'export errorcode {}'",
                    err_info.name, ctx, err_info.name
                ));
            }
            return Ok(());
        }
        if let Some(u_info) = self.unions.get(&ty_id) {
            if !self.exported_type_set.contains(&ty_id) {
                return Err(format!(
                    "Union '{}' used in {} is not declared 'export'; declare it with 'export union {}'",
                    u_info.name, ctx, u_info.name
                ));
            }
            return Ok(());
        }
        if let Some(ov_info) = self.overlays.get(&ty_id) {
            if !self.exported_type_set.contains(&ty_id) {
                return Err(format!(
                    "Overlay '{}' used in {} is not declared 'export'; declare it with 'export overlay {}'",
                    ov_info.name, ctx, ov_info.name
                ));
            }
            return Ok(());
        }
        if let Some(nt) = self.opaque_newtypes.get(&ty_id) {
            if !self.exported_type_set.contains(&ty_id) {
                return Err(format!(
                    "Opaque newtype '{}' used in {} is not declared 'export'; declare it with 'export type {} = opaque ...'",
                    nt.name, ctx, nt.name
                ));
            }
            return self.validate_export_value_type(nt.underlying, ctx);
        }
        if self.is_opaque_type(ty_id) {
            return Err(format!(
                "Unsized opaque type '{}' cannot be used by value in {}",
                self.type_display_name(ty_id),
                ctx
            ));
        }
        if self.c_ints.contains_key(&ty_id) {
            return Ok(());
        }
        if self.program.c_fn_ptr_types.contains(&ty_id)
            && let Type::FnPtr { args, ret } = self.program.types[ty_id.0 as usize].clone()
        {
            for a in args {
                self.validate_export_value_type(a, &format!("a parameter of {ctx}"))?;
            }
            return self.validate_export_value_type(ret, &format!("the result of {ctx}"));
        }
        match &self.program.types[ty_id.0 as usize] {
            Type::Void | Type::Bool | Type::F32 | Type::F64 | Type::Rune => Ok(()),
            Type::Int { bits, .. } if matches!(*bits, 8 | 16 | 32 | 64) => Ok(()),
            Type::Array { .. } => Err(format!(
                "Bare fixed-size array '{}' cannot be passed or returned by value in {}; wrap it in an 'export struct' or pass a pointer",
                self.type_display_name(ty_id),
                ctx
            )),
            _ => Err(format!(
                "Type '{}' is not valid across C FFI in {}",
                self.type_display_name(ty_id),
                ctx
            )),
        }
    }

    pub(super) fn setup_export_function(
        &mut self,
        fn_id: FuncId,
        export_symbol: String,
        decl: &FuncDecl,
        param_tys: &[TypeId],
        ret_ty: TypeId,
    ) -> Result<(), String> {
        let mut user_params = Vec::with_capacity(param_tys.len());
        let mut c_abi_params = Vec::with_capacity(param_tys.len());
        let mut c_abi_param_tys = Vec::with_capacity(param_tys.len() + 2);

        for (p, &pty) in decl
            .params
            .iter()
            .filter(|p| !p.is_comptime)
            .zip(param_tys.iter())
        {
            self.validate_export_value_type(
                pty,
                &format!(
                    "parameter '{}' of export function '{}'",
                    p.name, export_symbol
                ),
            )?;
            user_params.push((p.name.clone(), pty));
            if let Some((_, _, raw_ptr_ty)) = self.as_nullable_raw_ptr(pty) {
                c_abi_params.push(CAbiParamInfo {
                    name: p.name.clone(),
                    inner_ty: pty,
                    c_abi_ty: raw_ptr_ty,
                    is_nullable_raw_ptr: Some((pty, raw_ptr_ty)),
                });
                c_abi_param_tys.push(raw_ptr_ty);
            } else {
                c_abi_params.push(CAbiParamInfo {
                    name: p.name.clone(),
                    inner_ty: pty,
                    c_abi_ty: pty,
                    is_nullable_raw_ptr: None,
                });
                c_abi_param_tys.push(pty);
            }
        }

        let (ret_kind, c_abi_ret_ty) = if let Some(&res_info) = self.results.get(&ret_ty) {
            self.validate_export_value_type(
                res_info.err_ty,
                &format!("error return of export function '{}'", export_symbol),
            )?;
            self.validate_export_value_type(
                res_info.ok_ty,
                &format!("return value of export function '{}'", export_symbol),
            )?;
            let out_val_ptr_ty =
                if matches!(self.program.types[res_info.ok_ty.0 as usize], Type::Void) {
                    None
                } else {
                    let p = self.intern_raw_ptr_type(true, res_info.ok_ty);
                    c_abi_param_tys.push(p);
                    Some(p)
                };
            let err_c_ty = if let Some(b_ty) = self.errors[&res_info.err_ty].c_backing {
                b_ty
            } else {
                self.intern_c_int_type(CIntKind::CInt)
            };
            (
                ExportRetKind::ResultVal {
                    res_ty: ret_ty,
                    err_ty: res_info.err_ty,
                    ok_ty: res_info.ok_ty,
                    out_val_ptr_ty,
                },
                err_c_ty,
            )
        } else if let Some(inner_opt_ty) = self.as_optional_type(ret_ty) {
            self.validate_export_value_type(
                inner_opt_ty,
                &format!("optional return of export function '{}'", export_symbol),
            )?;
            if self.raw_ptrs.contains_key(&inner_opt_ty) {
                (
                    ExportRetKind::OptionalPtr {
                        opt_ty: ret_ty,
                        raw_ptr_ty: inner_opt_ty,
                    },
                    inner_opt_ty,
                )
            } else {
                let out_ptr_ty = self.intern_raw_ptr_type(true, inner_opt_ty);
                c_abi_param_tys.push(out_ptr_ty);
                let bool_ty = self.intern_type(Type::Bool);
                (
                    ExportRetKind::OptionalVal {
                        opt_ty: ret_ty,
                        val_ty: inner_opt_ty,
                        out_ptr_ty,
                    },
                    bool_ty,
                )
            }
        } else {
            self.validate_export_value_type(
                ret_ty,
                &format!("return type of export function '{}'", export_symbol),
            )?;
            (ExportRetKind::Direct(ret_ty), ret_ty)
        };

        if !self
            .exported_funcs
            .iter()
            .any(|f| f.symbol == export_symbol)
        {
            self.exported_funcs.push(ExportedFuncMeta {
                symbol: export_symbol.clone(),
                params: user_params,
                ret_kind: ret_kind.clone(),
            });
        }

        // Two-symbol model: the internal body keeps the Lrrr ABI (no entry null checks, native
        // `?T` / `E!T` returns) and is what every Lrrr call site binds to; a separate C-ABI wrapper
        // carries the exported symbol and performs null checks and out-pointer lowering.
        {
            if let Some(func) = self.program.functions.iter_mut().find(|f| f.id == fn_id) {
                func.export = None;
            }
            let c_abi_fn_id = self.reserve_function(
                Visibility::Export,
                Some(export_symbol.clone()),
                &c_abi_param_tys,
                c_abi_ret_ty,
            );
            self.build_c_abi_export_wrapper(
                c_abi_fn_id,
                fn_id,
                &c_abi_params,
                &c_abi_param_tys,
                c_abi_ret_ty,
                &ret_kind,
            );
            self.c_abi_func_wrappers.insert(
                fn_id,
                CAbiExportWrapperInfo {
                    c_abi_fn_id,
                    export_symbol,
                    user_params: c_abi_params,
                    c_abi_param_tys,
                    c_abi_ret_ty,
                    ret_kind,
                },
            );
        }
        Ok(())
    }

    pub(super) fn build_c_abi_export_wrapper(
        &mut self,
        c_abi_fn_id: FuncId,
        inner_fn_id: FuncId,
        c_abi_params: &[CAbiParamInfo],
        c_abi_param_tys: &[TypeId],
        c_abi_ret_ty: TypeId,
        ret_kind: &ExportRetKind,
    ) {
        let usize_ty = self.intern_type(Type::Int {
            signed: false,
            bits: 64,
        });
        let u8_ty = self.intern_type(Type::Int {
            signed: false,
            bits: 8,
        });
        let (_, inner_ret_ty) = self.func_sigs[&inner_fn_id].clone();
        let assign = |b: &mut BodyBuilder, place: Place, rv: Rvalue| {
            b.emit(Statement::Assign(place, rv));
        };
        let projected = |local: LocalId, proj: Projection| Place {
            local,
            projections: vec![proj],
        };

        let mut locals = vec![c_abi_ret_ty];
        locals.extend_from_slice(c_abi_param_tys);
        let mut b = BodyBuilder::new(locals);
        let mut call_args = Vec::with_capacity(c_abi_params.len());

        for (idx, pinfo) in c_abi_params.iter().enumerate() {
            let param_local = LocalId((idx + 1) as u32);
            if let Some((opt_ty, _)) = pinfo.is_nullable_raw_ptr {
                // `?*T` parameters: C `NULL` becomes `null`.
                let addr_local = b.alloc_temp(usize_ty);
                let opt_local = b.alloc_temp(opt_ty);
                assign(
                    &mut b,
                    Place::new(addr_local),
                    Rvalue::Cast(Operand::Copy(Place::new(param_local)), usize_ty),
                );
                let null_bb = b.new_block();
                let some_bb = b.new_block();
                let join_bb = b.new_block();
                b.terminate(Terminator::SwitchInt {
                    discr: Operand::Copy(Place::new(addr_local)),
                    targets: vec![(0, null_bb)],
                    otherwise: some_bb,
                });
                for (bb, variant, payload) in [
                    (null_bb, 0, Operand::Const(ConstValue::Void)),
                    (some_bb, 1, Operand::Copy(Place::new(param_local))),
                ] {
                    b.cur_block = bb;
                    assign(
                        &mut b,
                        Place::new(opt_local),
                        Rvalue::Union {
                            ty: opt_ty,
                            variant,
                            payload,
                        },
                    );
                    b.terminate(Terminator::Goto { target: join_bb });
                }
                b.cur_block = join_bb;
                call_args.push(Operand::Copy(Place::new(opt_local)));
                continue;
            }
            // C may pass any bits: trap on a `NULL` non-optional raw pointer, an out-of-range
            // `bool`, enum, `rune`, or pattern value, or a union tag that names no variant,
            // wherever it sits in the parameter.
            if self.c_value_needs_checks(c_abi_param_tys[idx]) {
                let trap_bb = b.new_block();
                let ty = c_abi_param_tys[idx];
                self.emit_c_value_checks(&mut b, Place::new(param_local), ty, trap_bb);
            }
            call_args.push(Operand::Copy(Place::new(param_local)));
        }

        let inner_ret_local = b.alloc_temp(inner_ret_ty);
        let after_call_bb = b.new_block();
        b.terminate(Terminator::Call {
            func: Operand::Const(ConstValue::Func(inner_fn_id)),
            args: call_args,
            destination: Place::new(inner_ret_local),
            target: after_call_bb,
        });
        b.cur_block = after_call_bb;
        // `ret_slot = value; return` in block `bb`.
        let return_with = |b: &mut BodyBuilder, bb: BlockId, rv: Rvalue| {
            b.cur_block = bb;
            b.emit(Statement::Assign(Place::new(LocalId(0)), rv));
            b.terminate(Terminator::Return);
        };

        match ret_kind {
            ExportRetKind::Direct(_) => {
                let bb = b.cur_block;
                return_with(&mut b, bb, Rvalue::Use(Operand::Copy(Place::new(inner_ret_local))));
            }
            ExportRetKind::OptionalPtr { raw_ptr_ty, .. } => {
                let discr_local = b.alloc_temp(u8_ty);
                assign(
                    &mut b,
                    Place::new(discr_local),
                    Rvalue::Discriminant(Place::new(inner_ret_local)),
                );
                let some_bb = b.new_block();
                let none_bb = b.new_block();
                b.terminate(Terminator::SwitchInt {
                    discr: Operand::Copy(Place::new(discr_local)),
                    targets: vec![(1, some_bb)],
                    otherwise: none_bb,
                });
                return_with(
                    &mut b,
                    some_bb,
                    Rvalue::Use(Operand::Copy(projected(inner_ret_local, Projection::Variant(1)))),
                );
                let zero_local = b.alloc_temp(usize_ty);
                b.cur_block = none_bb;
                assign(
                    &mut b,
                    Place::new(zero_local),
                    Rvalue::Use(Operand::Const(ConstValue::I64(0))),
                );
                return_with(
                    &mut b,
                    none_bb,
                    Rvalue::Cast(Operand::Copy(Place::new(zero_local)), *raw_ptr_ty),
                );
            }
            ExportRetKind::OptionalVal { .. } => {
                let out_val_local = LocalId(c_abi_param_tys.len() as u32);
                let discr_local = b.alloc_temp(u8_ty);
                assign(
                    &mut b,
                    Place::new(discr_local),
                    Rvalue::Discriminant(Place::new(inner_ret_local)),
                );
                let some_bb = b.new_block();
                let none_bb = b.new_block();
                let write_bb = b.new_block();
                let ret_true_bb = b.new_block();
                b.terminate(Terminator::SwitchInt {
                    discr: Operand::Copy(Place::new(discr_local)),
                    targets: vec![(1, some_bb)],
                    otherwise: none_bb,
                });
                // Write `*out_val` unless C passed `NULL`.
                let addr_local = b.alloc_temp(usize_ty);
                b.cur_block = some_bb;
                assign(
                    &mut b,
                    Place::new(addr_local),
                    Rvalue::Cast(Operand::Copy(Place::new(out_val_local)), usize_ty),
                );
                b.terminate(Terminator::SwitchInt {
                    discr: Operand::Copy(Place::new(addr_local)),
                    targets: vec![(0, ret_true_bb)],
                    otherwise: write_bb,
                });
                b.cur_block = write_bb;
                assign(
                    &mut b,
                    projected(out_val_local, Projection::Deref),
                    Rvalue::Use(Operand::Copy(projected(inner_ret_local, Projection::Variant(1)))),
                );
                b.terminate(Terminator::Goto {
                    target: ret_true_bb,
                });
                return_with(
                    &mut b,
                    ret_true_bb,
                    Rvalue::Use(Operand::Const(ConstValue::Bool(true))),
                );
                return_with(
                    &mut b,
                    none_bb,
                    Rvalue::Use(Operand::Const(ConstValue::Bool(false))),
                );
            }
            ExportRetKind::ResultVal {
                err_ty,
                out_val_ptr_ty,
                ..
            } => {
                let ok_val = self.errors[err_ty].ok_flag.1;
                let out_val_local = out_val_ptr_ty.map(|_| LocalId(c_abi_param_tys.len() as u32));
                let discr_local = b.alloc_temp(u8_ty);
                assign(
                    &mut b,
                    Place::new(discr_local),
                    Rvalue::Discriminant(Place::new(inner_ret_local)),
                );
                let ok_bb = b.new_block();
                let err_bb = b.new_block();
                b.terminate(Terminator::SwitchInt {
                    discr: Operand::Copy(Place::new(discr_local)),
                    targets: vec![(0, ok_bb)],
                    otherwise: err_bb,
                });

                // Success: write `*out_val` unless C passed `NULL`, then return the sentinel.
                let ret_ok_bb = match out_val_local {
                    Some(ov_local) => {
                        let write_ok_bb = b.new_block();
                        let ret_ok_bb = b.new_block();
                        let ok_addr = b.alloc_temp(usize_ty);
                        b.cur_block = ok_bb;
                        assign(
                            &mut b,
                            Place::new(ok_addr),
                            Rvalue::Cast(Operand::Copy(Place::new(ov_local)), usize_ty),
                        );
                        b.terminate(Terminator::SwitchInt {
                            discr: Operand::Copy(Place::new(ok_addr)),
                            targets: vec![(0, ret_ok_bb)],
                            otherwise: write_ok_bb,
                        });
                        b.cur_block = write_ok_bb;
                        assign(
                            &mut b,
                            projected(ov_local, Projection::Deref),
                            Rvalue::Use(Operand::Copy(projected(
                                inner_ret_local,
                                Projection::Variant(0),
                            ))),
                        );
                        b.terminate(Terminator::Goto { target: ret_ok_bb });
                        ret_ok_bb
                    }
                    None => ok_bb,
                };
                return_with(
                    &mut b,
                    ret_ok_bb,
                    Rvalue::Use(Operand::Const(ConstValue::I64(ok_val))),
                );

                // Failure: return the error code itself (its tag is the C value).
                let err_tmp = b.alloc_temp(*err_ty);
                b.cur_block = err_bb;
                assign(
                    &mut b,
                    Place::new(err_tmp),
                    Rvalue::Use(Operand::Copy(projected(inner_ret_local, Projection::Variant(1)))),
                );
                return_with(
                    &mut b,
                    err_bb,
                    Rvalue::Transmute(Operand::Copy(Place::new(err_tmp)), c_abi_ret_ty),
                );
            }
        }
        if let Some(func) = self.program.functions.iter_mut().find(|f| f.id == c_abi_fn_id) {
            func.locals = b.locals;
            func.blocks = b.blocks;
        }
    }
}
