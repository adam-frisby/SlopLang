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
            // Non-optional raw pointers are contractually non-null: trap on C `NULL`.
            if self.raw_ptrs.contains_key(&c_abi_param_tys[idx]) {
                let addr_local = b.alloc_temp(usize_ty);
                assign(
                    &mut b,
                    Place::new(addr_local),
                    Rvalue::Cast(Operand::Copy(Place::new(param_local)), usize_ty),
                );
                let trap_bb = b.new_block();
                let ok_bb = b.new_block();
                b.terminate(Terminator::SwitchInt {
                    discr: Operand::Copy(Place::new(addr_local)),
                    targets: vec![(0, trap_bb)],
                    otherwise: ok_bb,
                });
                b.cur_block = ok_bb;
            }
            // C may store any integer in the tag of an `export errorcode` or `export union`:
            // trap unless it names a variant.
            if let Some((tag_ty, values)) = self.c_valid_tags(c_abi_param_tys[idx]) {
                let tag_bits = match self.program.types[tag_ty.0 as usize] {
                    Type::Int { bits, .. } => bits,
                    _ => 32,
                };
                let raw_ty = self.intern_type(Type::Int {
                    signed: false,
                    bits: tag_bits,
                });
                // The tag is the first field: read it through a pointer to the parameter.
                let param_ref_ty = self.intern_type(Type::Ptr {
                    mutable: false,
                    pointee: c_abi_param_tys[idx],
                });
                let tag_ptr_ty = self.intern_raw_ptr_type(false, raw_ty);
                let param_ref = b.alloc_temp(param_ref_ty);
                let tag_ptr = b.alloc_temp(tag_ptr_ty);
                let raw_local = b.alloc_temp(raw_ty);
                assign(
                    &mut b,
                    Place::new(param_ref),
                    Rvalue::Ref {
                        mutable: false,
                        place: Place::new(param_local),
                    },
                );
                assign(
                    &mut b,
                    Place::new(tag_ptr),
                    Rvalue::Cast(Operand::Copy(Place::new(param_ref)), tag_ptr_ty),
                );
                assign(
                    &mut b,
                    Place::new(raw_local),
                    Rvalue::Use(Operand::Copy(projected(tag_ptr, Projection::Deref))),
                );
                let trap_bb = b.new_block();
                let ok_bb = b.new_block();
                let stored = |v: i128| {
                    if tag_bits >= 128 {
                        v
                    } else {
                        v.rem_euclid(1i128 << tag_bits)
                    }
                };
                b.terminate(Terminator::SwitchInt {
                    discr: Operand::Copy(Place::new(raw_local)),
                    targets: values.iter().map(|&v| (stored(v), ok_bb)).collect(),
                    otherwise: trap_bb,
                });
                b.cur_block = ok_bb;
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
