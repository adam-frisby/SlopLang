use super::*;

impl Compiler {
    pub fn c_type_name(&self, ty_id: TypeId) -> String {
        if let Some(ck) = self.c_ints.get(&ty_id) {
            return ck.c_header_name().to_string();
        }
        if let Some(nt) = self.opaque_newtypes.get(&ty_id) {
            return nt.name.clone();
        }
        if self.named_opaques.contains(&ty_id) {
            return self.composites[&ty_id].name.clone();
        }
        if let Some(comp) = self.composites.get(&ty_id) {
            return comp.name.clone();
        }
        if let Some(ov_info) = self.overlays.get(&ty_id) {
            return ov_info.name.clone();
        }
        if let Some((ename, _)) = self.enums.get(&ty_id) {
            return ename.clone();
        }
        if let Some(err_info) = self.errors.get(&ty_id) {
            return err_info.name.clone();
        }
        if self.is_universal_opaque_type(ty_id) {
            return "void".to_string();
        }
        if let Some((mutable, pointee, _)) = self.as_nullable_raw_ptr(ty_id) {
            let pt = self.c_type_name(pointee);
            return if mutable {
                format!("{pt}*")
            } else {
                format!("const {pt}*")
            };
        }
        if let Some(&(mutable, pointee)) = self.raw_ptrs.get(&ty_id) {
            let pt = self.c_type_name(pointee);
            return if mutable {
                format!("{pt}*")
            } else {
                format!("const {pt}*")
            };
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
                writeln!(out, "typedef enum {} {{", meta.name).unwrap();
                for (idx, leaf) in err_info.leaves.iter().enumerate() {
                    if leaf.key.error_name == meta.name {
                        writeln!(
                            out,
                            "    {}_{} = {},",
                            meta.name, leaf.key.variant_name, idx
                        )
                        .unwrap();
                    } else {
                        writeln!(
                            out,
                            "    {}_{}_{} = {},",
                            meta.name, leaf.key.error_name, leaf.key.variant_name, idx
                        )
                        .unwrap();
                    }
                }
                writeln!(out, "}} {};\n", meta.name).unwrap();
            } else if let Some(nt) = self.opaque_newtypes.get(&tid) {
                writeln!(
                    out,
                    "typedef {} {};\n",
                    self.c_type_name(nt.underlying),
                    meta.name
                )
                .unwrap();
            } else if let Some(comp) = self.composites.get(&tid) {
                if !comp.is_struct {
                    writeln!(out, "struct {} {{", meta.name).unwrap();
                    for (fname, fty, _, _) in &comp.fields {
                        writeln!(out, "    {};", self.c_decl(*fty, fname)).unwrap();
                    }
                    writeln!(out, "}};\n").unwrap();
                }
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
                    c_params.push(format!("/* out */ {}* out_err", self.c_type_name(*err_ty)));
                    if !matches!(self.program.types[ok_ty.0 as usize], Type::Void) {
                        c_params.push(format!("/* out */ {}* out_val", self.c_type_name(*ok_ty)));
                    }
                    "bool".to_string()
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
                return Err(format!(
                    "Tagged 'union' types cannot be declared 'export' ('{orig_name}'); use an 'export record' with an explicit tag or an 'export struct' opaque handle"
                ));
            }
            TypeExpr::Trait(_) => {
                return Err(format!(
                    "Traits cannot be declared 'export' ('{orig_name}')"
                ));
            }
            TypeExpr::Error(_) => {
                let void_ty = self.intern_type(Type::Void);
                if let Some(err_info) = self.errors.get(&ty_id) {
                    for leaf in &err_info.leaves {
                        if leaf.payload_ty != void_ty {
                            return Err(format!(
                                "Exported error type '{}' cannot have payload-carrying variant '{}::{}'; 'export error' is restricted to unit variants",
                                orig_name, leaf.key.error_name, leaf.key.variant_name
                            ));
                        }
                    }
                }
            }
            TypeExpr::Record { .. } => {
                if let Some(comp) = self.composites.get(&ty_id).cloned() {
                    for (fname, fty, _, _) in &comp.fields {
                        self.validate_export_field_type(
                            *fty,
                            &format!("field '{}' of export record '{}'", fname, orig_name),
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
            TypeExpr::Struct { .. }
            | TypeExpr::Opaque
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
                    let void_ty = self.intern_type(Type::Void);
                    for leaf in &err_info.leaves {
                        if leaf.payload_ty != void_ty {
                            return Err(format!(
                                "Exported error type '{}' cannot have payload-carrying variant '{}::{}'; 'export error' is restricted to unit variants",
                                orig_name, leaf.key.error_name, leaf.key.variant_name
                            ));
                        }
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
            && comp.is_struct
        {
            if !self.exported_type_set.contains(&pointee) {
                return Err(format!(
                    "Cannot use pointer to non-exported struct '{}' in {}; declare it with 'export struct {}'",
                    comp.name, ctx, comp.name
                ));
            }
            return Ok(());
        }
        self.validate_export_field_type(pointee, ctx)
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
            if comp.is_struct {
                return Err(format!(
                    "Opaque type '{}' cannot be passed, returned, or embedded by value in {}; an 'export opaque' is a handle type and must be passed behind a raw pointer ('*const {}' or '*mut {}')",
                    comp.name, ctx, comp.name, comp.name
                ));
            }
            if !self.exported_type_set.contains(&ty_id) {
                return Err(format!(
                    "Record '{}' used in {} is not declared 'export'; declare it with 'export record {}'",
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
            if !self.exported_type_set.contains(&ty_id) {
                return Err(format!(
                    "Error type '{}' used in {} is not declared 'export'; declare it with 'export error {}'",
                    err_info.name, ctx, err_info.name
                ));
            }
            let void_ty = TypeId(0);
            for leaf in &err_info.leaves {
                if !matches!(self.program.types[leaf.payload_ty.0 as usize], Type::Void)
                    && leaf.payload_ty != void_ty
                {
                    return Err(format!(
                        "Error type '{}' used in {} has payload-carrying variant '{}::{}'; exported errors are restricted to unit variants",
                        err_info.name, ctx, leaf.key.error_name, leaf.key.variant_name
                    ));
                }
            }
            return Ok(());
        }
        if let Some(u_info) = self.unions.get(&ty_id) {
            return Err(format!(
                "Tagged union '{}' is forbidden across FFI in {}",
                u_info.name, ctx
            ));
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
                "Bare fixed-size array '{}' cannot be passed or returned by value in {}; wrap it in an 'export record' or pass a pointer",
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
            let out_err_ptr_ty = self.intern_raw_ptr_type(true, res_info.err_ty);
            c_abi_param_tys.push(out_err_ptr_ty);
            let out_val_ptr_ty =
                if matches!(self.program.types[res_info.ok_ty.0 as usize], Type::Void) {
                    None
                } else {
                    let p = self.intern_raw_ptr_type(true, res_info.ok_ty);
                    c_abi_param_tys.push(p);
                    Some(p)
                };
            let bool_ty = self.intern_type(Type::Bool);
            (
                ExportRetKind::ResultVal {
                    res_ty: ret_ty,
                    err_ty: res_info.err_ty,
                    out_err_ptr_ty,
                    ok_ty: res_info.ok_ty,
                    out_val_ptr_ty,
                },
                bool_ty,
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

        let mut locals = vec![c_abi_ret_ty];
        locals.extend_from_slice(c_abi_param_tys);
        let mut alloc_local = |ty: TypeId| -> LocalId {
            let id = LocalId(locals.len() as u32);
            locals.push(ty);
            id
        };

        let mut blocks = vec![BasicBlock {
            statements: Vec::new(),
            terminator: Terminator::Unreachable,
        }];
        let new_block = |blocks: &mut Vec<BasicBlock>| -> BlockId {
            let id = BlockId(blocks.len() as u32);
            blocks.push(BasicBlock {
                statements: Vec::new(),
                terminator: Terminator::Unreachable,
            });
            id
        };

        let mut cur_bb = BlockId(0);
        let mut call_args = Vec::with_capacity(c_abi_params.len());

        for (idx, pinfo) in c_abi_params.iter().enumerate() {
            let param_local = LocalId((idx + 1) as u32);
            if let Some((opt_ty, _)) = pinfo.is_nullable_raw_ptr {
                let addr_local = alloc_local(usize_ty);
                let opt_local = alloc_local(opt_ty);
                blocks[cur_bb.0 as usize].statements.push(Statement::Assign(
                    Place::new(addr_local),
                    Rvalue::Cast(Operand::Copy(Place::new(param_local)), usize_ty),
                ));
                let null_bb = new_block(&mut blocks);
                let some_bb = new_block(&mut blocks);
                let join_bb = new_block(&mut blocks);
                blocks[cur_bb.0 as usize].terminator = Terminator::SwitchInt {
                    discr: Operand::Copy(Place::new(addr_local)),
                    targets: vec![(0, null_bb)],
                    otherwise: some_bb,
                };
                blocks[null_bb.0 as usize]
                    .statements
                    .push(Statement::Assign(
                        Place::new(opt_local),
                        Rvalue::Union {
                            ty: opt_ty,
                            variant: 0,
                            payload: Operand::Const(ConstValue::Void),
                        },
                    ));
                blocks[null_bb.0 as usize].terminator = Terminator::Goto { target: join_bb };
                blocks[some_bb.0 as usize]
                    .statements
                    .push(Statement::Assign(
                        Place::new(opt_local),
                        Rvalue::Union {
                            ty: opt_ty,
                            variant: 1,
                            payload: Operand::Copy(Place::new(param_local)),
                        },
                    ));
                blocks[some_bb.0 as usize].terminator = Terminator::Goto { target: join_bb };
                cur_bb = join_bb;
                call_args.push(Operand::Copy(Place::new(opt_local)));
            } else {
                // Non-optional raw pointers are contractually non-null: trap on C `NULL`.
                if self.raw_ptrs.contains_key(&c_abi_param_tys[idx]) {
                    let addr_local = alloc_local(usize_ty);
                    blocks[cur_bb.0 as usize].statements.push(Statement::Assign(
                        Place::new(addr_local),
                        Rvalue::Cast(Operand::Copy(Place::new(param_local)), usize_ty),
                    ));
                    let trap_bb = new_block(&mut blocks);
                    let ok_bb = new_block(&mut blocks);
                    blocks[cur_bb.0 as usize].terminator = Terminator::SwitchInt {
                        discr: Operand::Copy(Place::new(addr_local)),
                        targets: vec![(0, trap_bb)],
                        otherwise: ok_bb,
                    };
                    cur_bb = ok_bb;
                }
                call_args.push(Operand::Copy(Place::new(param_local)));
            }
        }

        let inner_ret_local = alloc_local(inner_ret_ty);
        let after_call_bb = new_block(&mut blocks);
        blocks[cur_bb.0 as usize].terminator = Terminator::Call {
            func: Operand::Const(ConstValue::Func(inner_fn_id)),
            args: call_args,
            destination: Place::new(inner_ret_local),
            target: after_call_bb,
        };
        cur_bb = after_call_bb;

        match ret_kind {
            ExportRetKind::Direct(_) => {
                blocks[cur_bb.0 as usize].statements.push(Statement::Assign(
                    Place::new(LocalId(0)),
                    Rvalue::Use(Operand::Copy(Place::new(inner_ret_local))),
                ));
                blocks[cur_bb.0 as usize].terminator = Terminator::Return;
            }
            ExportRetKind::OptionalPtr { raw_ptr_ty, .. } => {
                let discr_local = alloc_local(u8_ty);
                blocks[cur_bb.0 as usize].statements.push(Statement::Assign(
                    Place::new(discr_local),
                    Rvalue::Discriminant(Place::new(inner_ret_local)),
                ));
                let some_bb = new_block(&mut blocks);
                let none_bb = new_block(&mut blocks);
                blocks[cur_bb.0 as usize].terminator = Terminator::SwitchInt {
                    discr: Operand::Copy(Place::new(discr_local)),
                    targets: vec![(1, some_bb)],
                    otherwise: none_bb,
                };
                blocks[some_bb.0 as usize]
                    .statements
                    .push(Statement::Assign(
                        Place::new(LocalId(0)),
                        Rvalue::Use(Operand::Copy(Place {
                            local: inner_ret_local,
                            projections: vec![Projection::Variant(1)],
                        })),
                    ));
                blocks[some_bb.0 as usize].terminator = Terminator::Return;

                let zero_local = alloc_local(usize_ty);
                blocks[none_bb.0 as usize]
                    .statements
                    .push(Statement::Assign(
                        Place::new(zero_local),
                        Rvalue::Use(Operand::Const(ConstValue::I64(0))),
                    ));
                blocks[none_bb.0 as usize]
                    .statements
                    .push(Statement::Assign(
                        Place::new(LocalId(0)),
                        Rvalue::Cast(Operand::Copy(Place::new(zero_local)), *raw_ptr_ty),
                    ));
                blocks[none_bb.0 as usize].terminator = Terminator::Return;
            }
            ExportRetKind::OptionalVal { .. } => {
                let out_val_local = LocalId(c_abi_param_tys.len() as u32);
                let discr_local = alloc_local(u8_ty);
                blocks[cur_bb.0 as usize].statements.push(Statement::Assign(
                    Place::new(discr_local),
                    Rvalue::Discriminant(Place::new(inner_ret_local)),
                ));
                let some_bb = new_block(&mut blocks);
                let none_bb = new_block(&mut blocks);
                let write_bb = new_block(&mut blocks);
                let ret_true_bb = new_block(&mut blocks);
                blocks[cur_bb.0 as usize].terminator = Terminator::SwitchInt {
                    discr: Operand::Copy(Place::new(discr_local)),
                    targets: vec![(1, some_bb)],
                    otherwise: none_bb,
                };
                let addr_local = alloc_local(usize_ty);
                blocks[some_bb.0 as usize]
                    .statements
                    .push(Statement::Assign(
                        Place::new(addr_local),
                        Rvalue::Cast(Operand::Copy(Place::new(out_val_local)), usize_ty),
                    ));
                blocks[some_bb.0 as usize].terminator = Terminator::SwitchInt {
                    discr: Operand::Copy(Place::new(addr_local)),
                    targets: vec![(0, ret_true_bb)],
                    otherwise: write_bb,
                };
                blocks[write_bb.0 as usize]
                    .statements
                    .push(Statement::Assign(
                        Place {
                            local: out_val_local,
                            projections: vec![Projection::Deref],
                        },
                        Rvalue::Use(Operand::Copy(Place {
                            local: inner_ret_local,
                            projections: vec![Projection::Variant(1)],
                        })),
                    ));
                blocks[write_bb.0 as usize].terminator = Terminator::Goto {
                    target: ret_true_bb,
                };
                blocks[ret_true_bb.0 as usize]
                    .statements
                    .push(Statement::Assign(
                        Place::new(LocalId(0)),
                        Rvalue::Use(Operand::Const(ConstValue::Bool(true))),
                    ));
                blocks[ret_true_bb.0 as usize].terminator = Terminator::Return;

                blocks[none_bb.0 as usize]
                    .statements
                    .push(Statement::Assign(
                        Place::new(LocalId(0)),
                        Rvalue::Use(Operand::Const(ConstValue::Bool(false))),
                    ));
                blocks[none_bb.0 as usize].terminator = Terminator::Return;
            }
            ExportRetKind::ResultVal { out_val_ptr_ty, .. } => {
                let (out_err_local, out_val_local) = if out_val_ptr_ty.is_some() {
                    (
                        LocalId((c_abi_param_tys.len() - 1) as u32),
                        Some(LocalId(c_abi_param_tys.len() as u32)),
                    )
                } else {
                    (LocalId(c_abi_param_tys.len() as u32), None)
                };
                let discr_local = alloc_local(u8_ty);
                blocks[cur_bb.0 as usize].statements.push(Statement::Assign(
                    Place::new(discr_local),
                    Rvalue::Discriminant(Place::new(inner_ret_local)),
                ));
                let ok_bb = new_block(&mut blocks);
                let err_bb = new_block(&mut blocks);
                blocks[cur_bb.0 as usize].terminator = Terminator::SwitchInt {
                    discr: Operand::Copy(Place::new(discr_local)),
                    targets: vec![(0, ok_bb)],
                    otherwise: err_bb,
                };

                if let Some(ov_local) = out_val_local {
                    let write_ok_bb = new_block(&mut blocks);
                    let ret_true_bb = new_block(&mut blocks);
                    let ok_addr = alloc_local(usize_ty);
                    blocks[ok_bb.0 as usize].statements.push(Statement::Assign(
                        Place::new(ok_addr),
                        Rvalue::Cast(Operand::Copy(Place::new(ov_local)), usize_ty),
                    ));
                    blocks[ok_bb.0 as usize].terminator = Terminator::SwitchInt {
                        discr: Operand::Copy(Place::new(ok_addr)),
                        targets: vec![(0, ret_true_bb)],
                        otherwise: write_ok_bb,
                    };
                    blocks[write_ok_bb.0 as usize]
                        .statements
                        .push(Statement::Assign(
                            Place {
                                local: ov_local,
                                projections: vec![Projection::Deref],
                            },
                            Rvalue::Use(Operand::Copy(Place {
                                local: inner_ret_local,
                                projections: vec![Projection::Variant(0)],
                            })),
                        ));
                    blocks[write_ok_bb.0 as usize].terminator = Terminator::Goto {
                        target: ret_true_bb,
                    };
                    blocks[ret_true_bb.0 as usize]
                        .statements
                        .push(Statement::Assign(
                            Place::new(LocalId(0)),
                            Rvalue::Use(Operand::Const(ConstValue::Bool(true))),
                        ));
                    blocks[ret_true_bb.0 as usize].terminator = Terminator::Return;
                } else {
                    blocks[ok_bb.0 as usize].statements.push(Statement::Assign(
                        Place::new(LocalId(0)),
                        Rvalue::Use(Operand::Const(ConstValue::Bool(true))),
                    ));
                    blocks[ok_bb.0 as usize].terminator = Terminator::Return;
                }

                let write_err_bb = new_block(&mut blocks);
                let ret_false_bb = new_block(&mut blocks);
                let err_addr = alloc_local(usize_ty);
                blocks[err_bb.0 as usize].statements.push(Statement::Assign(
                    Place::new(err_addr),
                    Rvalue::Cast(Operand::Copy(Place::new(out_err_local)), usize_ty),
                ));
                blocks[err_bb.0 as usize].terminator = Terminator::SwitchInt {
                    discr: Operand::Copy(Place::new(err_addr)),
                    targets: vec![(0, ret_false_bb)],
                    otherwise: write_err_bb,
                };
                blocks[write_err_bb.0 as usize]
                    .statements
                    .push(Statement::Assign(
                        Place {
                            local: out_err_local,
                            projections: vec![Projection::Deref],
                        },
                        Rvalue::Use(Operand::Copy(Place {
                            local: inner_ret_local,
                            projections: vec![Projection::Variant(1)],
                        })),
                    ));
                blocks[write_err_bb.0 as usize].terminator = Terminator::Goto {
                    target: ret_false_bb,
                };
                blocks[ret_false_bb.0 as usize]
                    .statements
                    .push(Statement::Assign(
                        Place::new(LocalId(0)),
                        Rvalue::Use(Operand::Const(ConstValue::Bool(false))),
                    ));
                blocks[ret_false_bb.0 as usize].terminator = Terminator::Return;
            }
        }

        if let Some(func) = self
            .program
            .functions
            .iter_mut()
            .find(|f| f.id == c_abi_fn_id)
        {
            func.locals = locals;
            func.blocks = blocks;
        }
    }
}
