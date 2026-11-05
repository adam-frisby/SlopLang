use super::*;

impl<'a> FuncLowerer<'a> {
    /// Whether `args` suit a variant without a payload: none, or one `void` (as `.A(x)` gives
    /// when `A(T)` is instantiated with `T = void`), which is evaluated and discarded.
    fn void_payload_args(&mut self, args: &[Expr]) -> Result<bool, String> {
        let void_ty = self.compiler.intern_type(Type::Void);
        match args {
            [] => Ok(true),
            [arg] => {
                let (_, ty) = self.lower_expr(arg, Some(void_ty))?;
                Ok(ty == void_ty)
            }
            _ => Ok(false),
        }
    }

    /// A method is callable inside its type's block when private, anywhere in the defining
    /// module when `pub(mod)`, and everywhere when `pub`.
    fn check_method_visibility(
        &self,
        vis: Visibility,
        owner: TypeId,
        def_mod: &str,
        method_name: &str,
        type_name: &str,
    ) -> Result<(), String> {
        match vis {
            Visibility::Private if !self.has_private_access(owner) => Err(format!(
                "Cannot call private method '{method_name}' of '{type_name}' outside its block; declare it 'pub(mod) fn' to use it elsewhere in module '{def_mod}'"
            )),
            Visibility::PubMod if self.mod_path != def_mod => Err(format!(
                "Cannot call method '{method_name}' of '{type_name}' outside module '{def_mod}': it is 'pub(mod)'"
            )),
            _ => Ok(()),
        }
    }

    pub(super) fn lower_format_str(
        &mut self,
        segments: &[FmtSegment],
    ) -> Result<(Operand, TypeId), String> {
        let mut ref_field_tys = Vec::new();
        let mut ref_field_ops = Vec::new();
        let mut interp_meta: Vec<(u32, TypeId, String)> = Vec::new();

        for seg in segments {
            if let FmtSegment::Interp { expr, spec } = seg {
                let (mut place, val_ty) = if matches!(expr, Expr::Str(_)) {
                    let str_ty = self.compiler.intern_str_type();
                    let (op, src_ty) = self.lower_expr(expr, Some(str_ty))?;
                    let coerced = self.coerce_operand(op, src_ty, str_ty)?;
                    let tmp = self.alloc_temp(str_ty);
                    self.emit(Statement::Assign(Place::new(tmp), Rvalue::Use(coerced)));
                    (Place::new(tmp), str_ty)
                } else {
                    self.lower_place(expr, false)?
                };
                if let Some((stat_name, true)) = self.static_locals.get(&place.local) {
                    if !self.is_copy_type(val_ty) {
                        return Err(format!(
                            "Taking a safe reference to mutable static '{}' in format string is forbidden",
                            stat_name
                        ));
                    }
                    let copy_tmp = self.alloc_temp(val_ty);
                    self.emit(Statement::Assign(
                        Place::new(copy_tmp),
                        Rvalue::Use(Operand::Copy(place)),
                    ));
                    place = Place::new(copy_tmp);
                }

                if !self.compiler.is_format_type(val_ty) {
                    let mut inner_ty = val_ty;
                    while let Type::Ptr { pointee, .. } =
                        self.compiler.program.types[inner_ty.0 as usize]
                    {
                        if self.compiler.raw_ptrs.contains_key(&inner_ty)
                            || self.compiler.slices.contains_key(&inner_ty)
                        {
                            break;
                        }
                        inner_ty = pointee;
                    }
                    if let Some(comp) = self.compiler.composites.get(&inner_ty)
                        && comp.is_opaque
                    {
                        return Err(format!(
                            "Opaque type '{}' does not define a 'format' hook; only transparent types or opaque types with a 'format' hook can be formatted",
                            comp.name
                        ));
                    }
                    return Err(format!(
                        "Type '{}' cannot be formatted",
                        self.compiler.type_display_name(val_ty)
                    ));
                }

                let ref_ty = self.compiler.intern_type(Type::Ptr {
                    mutable: false,
                    pointee: val_ty,
                });
                let ref_tmp = self.alloc_temp(ref_ty);
                self.emit(Statement::Assign(
                    Place::new(ref_tmp),
                    Rvalue::Ref {
                        mutable: false,
                        place,
                    },
                ));
                let field_idx = ref_field_tys.len() as u32;
                ref_field_tys.push(ref_ty);
                ref_field_ops.push(Operand::Copy(Place::new(ref_tmp)));
                interp_meta.push((field_idx, val_ty, spec.clone()));
            }
        }

        let fmt_struct_ty = self
            .compiler
            .alloc_distinct_type(Type::Struct(ref_field_tys.clone()));
        let self_ref_ty = self.compiler.intern_type(Type::Ptr {
            mutable: false,
            pointee: fmt_struct_ty,
        });
        let formatter_ty = self.compiler.resolve_named_type("core::fmt", "Formatter")?;
        let formatter_mut_ref_ty = self.compiler.intern_type(Type::Ptr {
            mutable: true,
            pointee: formatter_ty,
        });
        let void_ty = self.compiler.intern_type(Type::Void);

        let fmt_fn_id = self.compiler.reserve_function(
            Visibility::Private,
            None,
            &[self_ref_ty, formatter_mut_ref_ty],
            void_ty,
        );

        let mut field_infos = Vec::with_capacity(ref_field_tys.len());
        for (i, &fty) in ref_field_tys.iter().enumerate() {
            field_infos.push((format!("arg{i}"), fty, Visibility::Private, None));
        }

        self.compiler.composites.insert(
            fmt_struct_ty,
            std::sync::Arc::new(CompositeInfo {
                name: format!("<fmt_str_{}>", fmt_fn_id.0),
                is_opaque: true,
                is_packed: false,
                total_bits: 0,
                packed_offsets: Vec::new(),
                ownership: OpaqueOwnership::Copy,
                threads: ThreadDecl::default(),
                cell_fields: Vec::new(),
                has_format_hook: true,
                def_module: self.mod_path.clone(),
                comptime_env: HashMap::default(),
                fields: field_infos,
                rel_fields: HashMap::default(),
                methods: Default::default(),
                method_fn_ids: HashMap::default(),
                consts: HashMap::default(),
                statics: HashMap::default(),
                default_fn: None,
                clone_fn: None,
                drop_fn: None,
                format_fn: Some((fmt_fn_id, false)),
                declared: DeclaredContents::default(),
                may_dangle: Vec::new(),
            }),
        );

        // Synthesize body of `fmt_fn_id(self: &FmtStruct, f: &mut Formatter)`
        let dummy_decl = FuncDecl {
            vis: Visibility::Private,
            name: format!("<fmt_str_{}::format>", fmt_fn_id.0),
            params: Vec::new(),
            ret_ty: TypeExpr::Void,
            borrows: None,
            where_clauses: Vec::new(),
            body: Block { stmts: Vec::new(), lines: Vec::new() },
            is_unsafe: false,
            impl_of: None,
            is_unsafe_impl: false,
            discardable: false,
        };
        let mut sub = FuncLowerer::new(
            self.compiler,
            PendingFunc {
                func_id: fmt_fn_id,
                module_path: self.mod_path.clone(),
                owner_ty: Some(fmt_struct_ty),
                decl: dummy_decl,
                comptime_env: HashMap::default(),
                closure_captures: Vec::new(),
            },
        );
        let fmt_ref_op = Operand::Copy(Place::new(LocalId(2)));
        let mut interp_cursor = 0usize;
        for seg in segments {
            match seg {
                FmtSegment::Lit(s) => {
                    sub.call_formatter_write_str(fmt_ref_op.clone(), s)?;
                }
                FmtSegment::Interp { .. } => {
                    let (f_idx, val_ty, ref spec) = interp_meta[interp_cursor];
                    interp_cursor += 1;
                    let mut arg_place = Place::new(LocalId(1));
                    arg_place.projections.push(Projection::Deref);
                    arg_place.projections.push(Projection::Field(f_idx));
                    arg_place.projections.push(Projection::Deref);
                    sub.emit_format_place(fmt_ref_op.clone(), arg_place, val_ty, spec)?;
                }
            }
        }
        sub.emit(Statement::Assign(
            Place::new(LocalId(0)),
            Rvalue::Use(Operand::Const(ConstValue::Void)),
        ));
        sub.terminate(Terminator::Return);
        let func = sub
            .compiler
            .program
            .functions
            .iter_mut()
            .find(|f| f.id == fmt_fn_id)
            .unwrap();
        func.locals = sub.body.locals;
        func.blocks = sub.body.blocks;

        let dst = self.alloc_temp(fmt_struct_ty);
        self.emit(Statement::Assign(
            Place::new(dst),
            Rvalue::Aggregate(fmt_struct_ty, ref_field_ops),
        ));
        Ok((Operand::Copy(Place::new(dst)), fmt_struct_ty))
    }

    pub(super) fn call_formatter_method(
        &mut self,
        method_name: &str,
        fmt_ref_op: Operand,
        extra_args: Vec<Operand>,
    ) -> Result<(), String> {
        let formatter_ty = self.compiler.resolve_named_type("core::fmt", "Formatter")?;
        let fn_id = self.compiler.composites[&formatter_ty].method_fn_ids[method_name];
        let void_ty = self.compiler.intern_type(Type::Void);
        let dst = self.alloc_temp(void_ty);
        let mut args = Vec::with_capacity(extra_args.len() + 1);
        args.push(fmt_ref_op);
        args.extend(extra_args);
        let next_bb = self.new_block();
        self.terminate(Terminator::Call {
            func: Operand::Const(ConstValue::Func(fn_id)),
            args,
            destination: Place::new(dst),
            target: next_bb,
        });
        self.body.cur_block = next_bb;
        Ok(())
    }

    pub(super) fn call_formatter_write_str(
        &mut self,
        fmt_ref_op: Operand,
        s: &str,
    ) -> Result<(), String> {
        if s.is_empty() {
            return Ok(());
        }
        let u8_ty = self.compiler.intern_type(Type::Int {
            signed: false,
            bits: 8,
        });
        let ptr_u8_ty = self.compiler.intern_type(Type::Ptr {
            mutable: false,
            pointee: u8_ty,
        });
        let str_ty = self.compiler.intern_str_type();
        let str_op = Operand::Const(ConstValue::Str(s.to_string()));
        let slice_op = self.coerce_operand(str_op, ptr_u8_ty, str_ty)?;
        self.call_formatter_method("write_str", fmt_ref_op, vec![slice_op])
    }

    pub(super) fn parse_int_format_spec(spec: &str) -> Result<(u64, bool, usize, bool), String> {
        if spec.is_empty() || spec == "?" || spec == "d" {
            return Ok((10, false, 0, false));
        }
        let bytes = spec.as_bytes();
        let mut pos = 0usize;
        let pad_zero = if bytes.get(pos) == Some(&b'0')
            && bytes.get(pos + 1).is_some_and(|b| b.is_ascii_digit())
        {
            pos += 1;
            true
        } else {
            false
        };
        let width_start = pos;
        while pos < bytes.len() && bytes[pos].is_ascii_digit() {
            pos += 1;
        }
        let min_width = if pos > width_start {
            spec[width_start..pos]
                .parse::<usize>()
                .map_err(|_| format!("Invalid width in format specifier '{spec}'"))?
        } else {
            0
        };
        let rest = &spec[pos..];
        match rest {
            "" | "d" | "?" => Ok((10, false, min_width, pad_zero)),
            "x" => Ok((16, false, min_width, pad_zero)),
            "X" => Ok((16, true, min_width, pad_zero)),
            "b" => Ok((2, false, min_width, pad_zero)),
            "o" => Ok((8, false, min_width, pad_zero)),
            _ => Err(format!("Unsupported integer format specifier '{spec}'")),
        }
    }

    pub(super) fn parse_float_format_spec(spec: &str) -> Result<usize, String> {
        if spec.is_empty() || spec == "?" {
            return Ok(2);
        }
        if let Some(rest) = spec.strip_prefix('.')
            && let Ok(prec) = rest.parse::<usize>()
        {
            return Ok(prec);
        }
        Err(format!("Unsupported float format specifier '{spec}'"))
    }

    pub(super) fn emit_format_place(
        &mut self,
        fmt_ref_op: Operand,
        mut place: Place,
        mut ty_id: TypeId,
        spec: &str,
    ) -> Result<(), String> {
        // Auto-dereference `&T` / `&mut T` references
        while !self.compiler.raw_ptrs.contains_key(&ty_id)
            && !self.compiler.slices.contains_key(&ty_id)
            && let Type::Ptr { pointee, .. } = self.compiler.program.types[ty_id.0 as usize]
        {
            place.projections.push(Projection::Deref);
            ty_id = pointee;
        }

        while let Some(nt) = self.compiler.distinct_types.get(&ty_id) {
            ty_id = nt.underlying;
        }
        if let Type::Pattern { base, .. } = self.compiler.program.types[ty_id.0 as usize] {
            ty_id = base;
        }

        // 1. `opaque` (`format` hook required) or `struct` (auto-synthesized structural format)
        if let Some(comp) = self.compiler.composites.get(&ty_id).cloned() {
            if comp.is_opaque {
                let Some((hook_fn_id, takes_spec)) = comp.format_fn else {
                    return Err(format!(
                        "Opaque type '{}' does not define a 'format' hook; only transparent types or opaque types with a 'format' hook can be formatted",
                        comp.name
                    ));
                };
                let self_ref_ty = self.compiler.intern_type(Type::Ptr {
                    mutable: false,
                    pointee: ty_id,
                });
                let self_ref_tmp = self.alloc_temp(self_ref_ty);
                self.emit(Statement::Assign(
                    Place::new(self_ref_tmp),
                    Rvalue::Ref {
                        mutable: false,
                        place,
                    },
                ));
                let mut call_args = vec![Operand::Copy(Place::new(self_ref_tmp)), fmt_ref_op];
                if takes_spec {
                    let u8_ty = self.compiler.intern_type(Type::Int {
                        signed: false,
                        bits: 8,
                    });
                    let ptr_u8_ty = self.compiler.intern_type(Type::Ptr {
                        mutable: false,
                        pointee: u8_ty,
                    });
                    let str_ty = self.compiler.intern_str_type();
                    let str_op = Operand::Const(ConstValue::Str(spec.to_string()));
                    let slice_op = self.coerce_operand(str_op, ptr_u8_ty, str_ty)?;
                    call_args.push(slice_op);
                }
                let void_ty = self.compiler.intern_type(Type::Void);
                let dst = self.alloc_temp(void_ty);
                let next_bb = self.new_block();
                self.terminate(Terminator::Call {
                    func: Operand::Const(ConstValue::Func(hook_fn_id)),
                    args: call_args,
                    destination: Place::new(dst),
                    target: next_bb,
                });
                self.body.cur_block = next_bb;
                return Ok(());
            } else {
                // Transparent `record`: `RecordName { f0: v0, f1: v1 }`
                if comp.fields.is_empty() {
                    return self
                        .call_formatter_write_str(fmt_ref_op, &format!("{} {{}}", comp.name));
                }
                self.call_formatter_write_str(fmt_ref_op.clone(), &format!("{} {{ ", comp.name))?;
                for (idx, (fname, f_ty, _, _)) in comp.fields.iter().enumerate() {
                    let prefix = if idx == 0 {
                        format!("{fname}: ")
                    } else {
                        format!(", {fname}: ")
                    };
                    self.call_formatter_write_str(fmt_ref_op.clone(), &prefix)?;
                    if comp.is_packed {
                        let f_loc =
                            self.extract_packed_field(Operand::Copy(place.clone()), ty_id, idx)?;
                        self.emit_format_place(fmt_ref_op.clone(), Place::new(f_loc), *f_ty, "")?;
                    } else {
                        let mut fp = place.clone();
                        fp.projections.push(Projection::Field(idx as u32));
                        self.emit_format_place(fmt_ref_op.clone(), fp, *f_ty, "")?;
                    }
                }
                return self.call_formatter_write_str(fmt_ref_op, " }");
            }
        }

        // 2. `enum` (`EnumName::Variant`)
        if let Some((enum_name, variants)) = self.compiler.enums.get(&ty_id).cloned()
            && (spec.is_empty() || spec == "?")
        {
            let discr_op = Operand::Copy(place);
            let join_bb = self.new_block();
            let otherwise_bb = self.new_block();
            let mut targets = Vec::with_capacity(variants.len());
            let mut branch_bbs = Vec::with_capacity(variants.len());
            for (vname, vval) in &variants {
                let bb = self.new_block();
                targets.push((*vval, bb));
                branch_bbs.push((vname.clone(), bb));
            }
            self.terminate(Terminator::SwitchInt {
                discr: discr_op,
                targets,
                otherwise: otherwise_bb,
            });
            for (vname, bb) in branch_bbs {
                self.body.cur_block = bb;
                self.call_formatter_write_str(
                    fmt_ref_op.clone(),
                    &format!("{enum_name}::{vname}"),
                )?;
                self.terminate(Terminator::Goto { target: join_bb });
            }
            self.body.cur_block = otherwise_bb;
            self.call_formatter_write_str(fmt_ref_op, &format!("{enum_name}::?"))?;
            self.terminate(Terminator::Goto { target: join_bb });
            self.body.cur_block = join_bb;
            return Ok(());
        }

        // 2b. Error types (`ErrorName::Variant` or `ErrorName::Variant(payload)`)
        if let Some(err_info) = self.compiler.errors.get(&ty_id).cloned() {
            let Type::Union { tag, .. } = self.compiler.program.types[ty_id.0 as usize] else {
                return Err("Internal error: expected Type::Union for error type".to_string());
            };
            let discr_tmp = self.alloc_temp(tag);
            self.emit(Statement::Assign(
                Place::new(discr_tmp),
                Rvalue::Discriminant(place.clone()),
            ));
            let join_bb = self.new_block();
            let otherwise_bb = self.new_block();
            let mut targets = Vec::new();
            let mut branch_bbs = Vec::new();
            for (v_idx, leaf) in err_info.leaves.iter().enumerate() {
                let bb = self.new_block();
                targets.push((v_idx as i128, bb));
                branch_bbs.push((v_idx, leaf.clone(), bb));
            }
            self.terminate(Terminator::SwitchInt {
                discr: Operand::Copy(Place::new(discr_tmp)),
                targets,
                otherwise: otherwise_bb,
            });
            let void_ty = self.compiler.intern_type(Type::Void);
            for (v_idx, leaf, bb) in branch_bbs {
                self.body.cur_block = bb;
                let prefix = format!("{}::{}", leaf.key.error_name, leaf.key.variant_name);
                if leaf.payload_ty == void_ty {
                    self.call_formatter_write_str(fmt_ref_op.clone(), &prefix)?;
                } else {
                    self.call_formatter_write_str(fmt_ref_op.clone(), &format!("{prefix}("))?;
                    let mut vp = place.clone();
                    vp.projections.push(Projection::Variant(v_idx as u32));
                    self.emit_format_place(fmt_ref_op.clone(), vp, leaf.payload_ty, spec)?;
                    self.call_formatter_write_str(fmt_ref_op.clone(), ")")?;
                }
                self.terminate(Terminator::Goto { target: join_bb });
            }
            self.body.cur_block = otherwise_bb;
            self.call_formatter_write_str(fmt_ref_op, &format!("{}::?", err_info.name))?;
            self.terminate(Terminator::Goto { target: join_bb });
            self.body.cur_block = join_bb;
            return Ok(());
        }

        // 2c. Tagged unions (`UnionName::Variant` or `UnionName::Variant(payload)`)
        if let Some(u_info) = self.compiler.unions.get(&ty_id).cloned() {
            let Type::Union { tag, .. } = self.compiler.program.types[ty_id.0 as usize] else {
                return Err("Internal error: expected Type::Union for union type".to_string());
            };
            let discr_tmp = self.alloc_temp(tag);
            self.emit(Statement::Assign(
                Place::new(discr_tmp),
                Rvalue::Discriminant(place.clone()),
            ));
            let join_bb = self.new_block();
            let otherwise_bb = self.new_block();
            let mut targets = Vec::new();
            let mut branch_bbs = Vec::new();
            for (v_idx, (vname, v_ty)) in u_info.variants.iter().enumerate() {
                let bb = self.new_block();
                targets.push((v_idx as i128, bb));
                branch_bbs.push((v_idx, vname.clone(), *v_ty, bb));
            }
            self.terminate(Terminator::SwitchInt {
                discr: Operand::Copy(Place::new(discr_tmp)),
                targets,
                otherwise: otherwise_bb,
            });
            let void_ty = self.compiler.intern_type(Type::Void);
            for (v_idx, vname, v_ty, bb) in branch_bbs {
                self.body.cur_block = bb;
                let prefix = format!("{}::{vname}", u_info.name);
                if v_ty == void_ty {
                    self.call_formatter_write_str(fmt_ref_op.clone(), &prefix)?;
                } else {
                    self.call_formatter_write_str(fmt_ref_op.clone(), &format!("{prefix}("))?;
                    let mut vp = place.clone();
                    vp.projections.push(Projection::Variant(v_idx as u32));
                    self.emit_format_place(fmt_ref_op.clone(), vp, v_ty, spec)?;
                    self.call_formatter_write_str(fmt_ref_op.clone(), ")")?;
                }
                self.terminate(Terminator::Goto { target: join_bb });
            }
            self.body.cur_block = otherwise_bb;
            self.call_formatter_write_str(fmt_ref_op, &format!("{}::?", u_info.name))?;
            self.terminate(Terminator::Goto { target: join_bb });
            self.body.cur_block = join_bb;
            return Ok(());
        }

        // 2d. Result types (`E!T`)
        if let Some(res_info) = self.compiler.results.get(&ty_id).cloned() {
            let Type::Union { tag, .. } = self.compiler.program.types[ty_id.0 as usize] else {
                return Err("Internal error: expected Type::Union for result type".to_string());
            };
            let discr_tmp = self.alloc_temp(tag);
            self.emit(Statement::Assign(
                Place::new(discr_tmp),
                Rvalue::Discriminant(place.clone()),
            ));
            let ok_bb = self.new_block();
            let err_bb = self.new_block();
            let join_bb = self.new_block();
            self.terminate(Terminator::SwitchInt {
                discr: Operand::Copy(Place::new(discr_tmp)),
                targets: vec![(0, ok_bb)],
                otherwise: err_bb,
            });
            let void_ty = self.compiler.intern_type(Type::Void);

            self.body.cur_block = ok_bb;
            if res_info.ok_ty == void_ty {
                self.call_formatter_write_str(fmt_ref_op.clone(), "Ok(())")?;
            } else {
                self.call_formatter_write_str(fmt_ref_op.clone(), "Ok(")?;
                let mut ok_place = place.clone();
                ok_place.projections.push(Projection::Variant(0));
                self.emit_format_place(fmt_ref_op.clone(), ok_place, res_info.ok_ty, spec)?;
                self.call_formatter_write_str(fmt_ref_op.clone(), ")")?;
            }
            self.terminate(Terminator::Goto { target: join_bb });

            self.body.cur_block = err_bb;
            let mut err_place = place;
            err_place.projections.push(Projection::Variant(1));
            self.emit_format_place(fmt_ref_op, err_place, res_info.err_ty, spec)?;
            self.terminate(Terminator::Goto { target: join_bb });

            self.body.cur_block = join_bb;
            return Ok(());
        }

        // 3. `&str` or `&[T]` / `&mut [T]` slice
        if let Some(&slice_info) = self.compiler.slices.get(&ty_id) {
            if slice_info.is_str {
                let str_ty = self.compiler.intern_str_type();
                let s_op = self.coerce_operand(Operand::Copy(place), ty_id, str_ty)?;
                let method = if spec == "?" {
                    "write_quoted_str"
                } else {
                    "write_str"
                };
                return self.call_formatter_method(method, fmt_ref_op, vec![s_op]);
            } else {
                self.call_formatter_write_str(fmt_ref_op.clone(), "[")?;
                let usize_ty = self.compiler.intern_type(Type::Int {
                    signed: false,
                    bits: 64,
                });
                let bool_ty = self.compiler.intern_type(Type::Bool);
                let mut len_place = place.clone();
                len_place.projections.push(Projection::Field(1));
                let len_local = self.alloc_temp(usize_ty);
                self.emit(Statement::Assign(
                    Place::new(len_local),
                    Rvalue::Use(Operand::Copy(len_place)),
                ));
                let idx_local = self.alloc_temp(usize_ty);
                self.emit(Statement::Assign(
                    Place::new(idx_local),
                    Rvalue::Use(Operand::Const(ConstValue::I64(0))),
                ));
                let cond_bb = self.new_block();
                let body_bb = self.new_block();
                let exit_bb = self.new_block();
                self.terminate(Terminator::Goto { target: cond_bb });

                self.body.cur_block = cond_bb;
                let cmp_local = self.alloc_temp(bool_ty);
                self.emit(Statement::Assign(
                    Place::new(cmp_local),
                    Rvalue::BinaryOp(
                        BinOp::Lt,
                        Operand::Copy(Place::new(idx_local)),
                        Operand::Copy(Place::new(len_local)),
                    ),
                ));
                self.terminate(Terminator::SwitchInt {
                    discr: Operand::Copy(Place::new(cmp_local)),
                    targets: vec![(1, body_bb)],
                    otherwise: exit_bb,
                });

                self.body.cur_block = body_bb;
                let gt0_local = self.alloc_temp(bool_ty);
                self.emit(Statement::Assign(
                    Place::new(gt0_local),
                    Rvalue::BinaryOp(
                        BinOp::Gt,
                        Operand::Copy(Place::new(idx_local)),
                        Operand::Const(ConstValue::I64(0)),
                    ),
                ));
                let comma_bb = self.new_block();
                let elem_bb = self.new_block();
                self.terminate(Terminator::SwitchInt {
                    discr: Operand::Copy(Place::new(gt0_local)),
                    targets: vec![(1, comma_bb)],
                    otherwise: elem_bb,
                });

                self.body.cur_block = comma_bb;
                self.call_formatter_write_str(fmt_ref_op.clone(), ", ")?;
                self.terminate(Terminator::Goto { target: elem_bb });

                self.body.cur_block = elem_bb;
                let mut elem_place = place;
                elem_place.projections.push(Projection::Field(0));
                elem_place.projections.push(Projection::Deref);
                elem_place.projections.push(Projection::Index(idx_local));
                self.emit_format_place(fmt_ref_op.clone(), elem_place, slice_info.elem, spec)?;
                self.emit(Statement::Assign(
                    Place::new(idx_local),
                    Rvalue::BinaryOp(
                        BinOp::AddWrap,
                        Operand::Copy(Place::new(idx_local)),
                        Operand::Const(ConstValue::I64(1)),
                    ),
                ));
                self.terminate(Terminator::Goto { target: cond_bb });

                self.body.cur_block = exit_bb;
                return self.call_formatter_write_str(fmt_ref_op, "]");
            }
        }

        // 4. Primitives, Arrays, Tuples, Optionals
        match self.compiler.program.types[ty_id.0 as usize].clone() {
            Type::Bool => {
                self.call_formatter_method("write_bool", fmt_ref_op, vec![Operand::Copy(place)])
            }
            Type::Rune => {
                let quoted = Operand::Const(ConstValue::Bool(spec == "?"));
                self.call_formatter_method(
                    "write_rune",
                    fmt_ref_op,
                    vec![Operand::Copy(place), quoted],
                )
            }
            Type::Int { signed, bits } => {
                let (radix, uppercase, min_width, pad_zero) = Self::parse_int_format_spec(spec)?;
                let is_signed_dec = signed && radix == 10;
                let i64_ty = self.compiler.intern_type(Type::Int {
                    signed: true,
                    bits: 64,
                });
                let u64_ty = self.compiler.intern_type(Type::Int {
                    signed: false,
                    bits: 64,
                });
                let val_i64_op = if ty_id == i64_ty {
                    Operand::Copy(place)
                } else if !is_signed_dec && signed && bits < 64 {
                    // Zero-extend signed sub-64-bit integer when formatting as hex/bin/oct
                    let unsigned_same_ty = self.compiler.intern_type(Type::Int {
                        signed: false,
                        bits,
                    });
                    let u_tmp = self.alloc_temp(unsigned_same_ty);
                    self.emit(Statement::Assign(
                        Place::new(u_tmp),
                        Rvalue::Cast(Operand::Copy(place), unsigned_same_ty),
                    ));
                    let u64_tmp = self.alloc_temp(u64_ty);
                    self.emit(Statement::Assign(
                        Place::new(u64_tmp),
                        Rvalue::Cast(Operand::Copy(Place::new(u_tmp)), u64_ty),
                    ));
                    let i64_tmp = self.alloc_temp(i64_ty);
                    self.emit(Statement::Assign(
                        Place::new(i64_tmp),
                        Rvalue::Cast(Operand::Copy(Place::new(u64_tmp)), i64_ty),
                    ));
                    Operand::Copy(Place::new(i64_tmp))
                } else {
                    let i64_tmp = self.alloc_temp(i64_ty);
                    self.emit(Statement::Assign(
                        Place::new(i64_tmp),
                        Rvalue::Cast(Operand::Copy(place), i64_ty),
                    ));
                    Operand::Copy(Place::new(i64_tmp))
                };
                self.call_formatter_method(
                    "write_int",
                    fmt_ref_op,
                    vec![
                        val_i64_op,
                        Operand::Const(ConstValue::Bool(is_signed_dec)),
                        Operand::Const(ConstValue::I64(radix as i128)),
                        Operand::Const(ConstValue::Bool(uppercase)),
                        Operand::Const(ConstValue::I64(min_width as i128)),
                        Operand::Const(ConstValue::Bool(pad_zero)),
                    ],
                )
            }
            Type::F32 | Type::F64 => {
                let prec = Self::parse_float_format_spec(spec)?;
                let f64_ty = self.compiler.intern_type(Type::F64);
                let val_f64_op = if ty_id == f64_ty {
                    Operand::Copy(place)
                } else {
                    let tmp = self.alloc_temp(f64_ty);
                    self.emit(Statement::Assign(
                        Place::new(tmp),
                        Rvalue::Cast(Operand::Copy(place), f64_ty),
                    ));
                    Operand::Copy(Place::new(tmp))
                };
                self.call_formatter_method(
                    "write_f64",
                    fmt_ref_op,
                    vec![val_f64_op, Operand::Const(ConstValue::I64(prec as i128))],
                )
            }
            Type::Array { elem, len } => {
                self.call_formatter_write_str(fmt_ref_op.clone(), "[")?;
                let usize_ty = self.compiler.intern_type(Type::Int {
                    signed: false,
                    bits: 64,
                });
                for i in 0..len {
                    if i > 0 {
                        self.call_formatter_write_str(fmt_ref_op.clone(), ", ")?;
                    }
                    let idx_tmp = self.alloc_temp(usize_ty);
                    self.emit(Statement::Assign(
                        Place::new(idx_tmp),
                        Rvalue::Use(Operand::Const(ConstValue::I64(i as i128))),
                    ));
                    let mut ep = place.clone();
                    ep.projections.push(Projection::Index(idx_tmp));
                    self.emit_format_place(fmt_ref_op.clone(), ep, elem, spec)?;
                }
                self.call_formatter_write_str(fmt_ref_op, "]")
            }
            Type::Struct(field_tys) => {
                if field_tys.is_empty() {
                    return self.call_formatter_write_str(fmt_ref_op, "{}");
                }
                self.call_formatter_write_str(fmt_ref_op.clone(), "{ ")?;
                for (idx, f_ty) in field_tys.into_iter().enumerate() {
                    if idx > 0 {
                        self.call_formatter_write_str(fmt_ref_op.clone(), ", ")?;
                    }
                    let mut fp = place.clone();
                    fp.projections.push(Projection::Field(idx as u32));
                    self.emit_format_place(fmt_ref_op.clone(), fp, f_ty, "")?;
                }
                self.call_formatter_write_str(fmt_ref_op, " }")
            }
            Type::Union { tag, variants }
                if variants.len() == 2
                    && matches!(
                        self.compiler.program.types[variants[0].0 as usize],
                        Type::Void
                    ) =>
            {
                let discr_tmp = self.alloc_temp(tag);
                self.emit(Statement::Assign(
                    Place::new(discr_tmp),
                    Rvalue::Discriminant(place.clone()),
                ));
                let some_bb = self.new_block();
                let none_bb = self.new_block();
                let join_bb = self.new_block();
                self.terminate(Terminator::SwitchInt {
                    discr: Operand::Copy(Place::new(discr_tmp)),
                    targets: vec![(1, some_bb)],
                    otherwise: none_bb,
                });

                self.body.cur_block = none_bb;
                self.call_formatter_write_str(fmt_ref_op.clone(), "null")?;
                self.terminate(Terminator::Goto { target: join_bb });

                self.body.cur_block = some_bb;
                let mut payload_place = place;
                payload_place.projections.push(Projection::Variant(1));
                self.emit_format_place(fmt_ref_op, payload_place, variants[1], spec)?;
                self.terminate(Terminator::Goto { target: join_bb });

                self.body.cur_block = join_bb;
                Ok(())
            }
            other => Err(format!("Type '{other}' cannot be formatted")),
        }
    }

    /// Notes a write to the place `expr` for `capture_binding_writes`, unless it goes through
    /// an explicit dereference.
    fn note_capture_write(&self, expr: &Expr, is_receiver: bool) {
        fn derefs(e: &Expr) -> bool {
            match e {
                Expr::Deref(_) => true,
                Expr::Field { base, .. }
                | Expr::IntrinsicField { base, .. }
                | Expr::IntrinsicVariant { base, .. }
                | Expr::TupleIndex { base, .. }
                | Expr::Index { base, .. }
                | Expr::Slice { base, .. } => derefs(base),
                _ => false,
            }
        }
        if let Some(root) = Self::root_var_of_place_expr(expr)
            && !derefs(expr)
        {
            // A `&mut self` receiver that is a reference variable borrows through it.
            let bare = matches!(expr, Expr::Path(_)) && !is_receiver;
            self.capture_binding_writes.borrow_mut().push((root.to_string(), bare));
        }
    }

    /// Notes that `expr` is used by value, for `capture_moves`, if it names a capture.
    fn note_capture_move(&self, expr: &Expr, bound: &crate::fasthash::FastSet<String>) {
        let inner = if let Expr::Move(inner) = expr { inner } else { expr };
        if let Expr::Path(p) = inner
            && p.len() == 1
            && !bound.contains(&p[0])
        {
            self.capture_moves.borrow_mut().push((p[0].clone(), None));
        }
    }

    /// Whether `method` of the variable `var_name` takes `self` by value.
    pub(super) fn method_consumes_self(&mut self, var_name: &str, method_name: &str) -> Result<bool, String> {
        let by_value = |ty: &TypeExpr| !matches!(ty, TypeExpr::Ref { .. });
        let ty = self
            .lookup_var(var_name)
            .map(|(_, t)| t)
            .or_else(|| self.lookup_capture(var_name).map(|(_, t)| t));
        let Some(ty_id) = ty else {
            return Ok(false);
        };
        let Some(comp) = self.compiler.composites.get(&ty_id) else {
            return Ok(false);
        };
        if let Some((_, mdecl)) = comp.methods.get(method_name) {
            let first = mdecl.params.iter().find(|p| !p.is_comptime);
            return Ok(first.is_some_and(|p| p.name == "self" && by_value(&p.ty)));
        }
        for t in self.compiler.traits_implemented_by(ty_id)? {
            let methods = &self.compiler.traits[&t].methods;
            if let Some(m) = methods.iter().find(|m| m.name == method_name) {
                let first = m.params.iter().find(|p| !p.is_comptime);
                return Ok(first.is_some_and(|p| p.name == "self" && by_value(&p.ty)));
            }
        }
        Ok(false)
    }

    pub(super) fn root_var_of_place_expr(expr: &Expr) -> Option<&str> {
        match expr {
            Expr::Path(p) if p.len() == 1 => Some(&p[0]),
            Expr::Deref(inner)
            | Expr::Field { base: inner, .. }
            | Expr::IntrinsicField { base: inner, .. }
            | Expr::IntrinsicVariant { base: inner, .. }
            | Expr::TupleIndex { base: inner, .. }
            | Expr::Index { base: inner, .. }
            | Expr::Slice { base: inner, .. } => Self::root_var_of_place_expr(inner),
            _ => None,
        }
    }

    pub(super) fn method_requires_mut_self(&self, var_name: &str, method_name: &str) -> bool {
        let Some(mut ty_id) = self
            .lookup_var(var_name)
            .map(|(_, t)| t)
            .or_else(|| self.lookup_capture(var_name).map(|(_, t)| t))
        else {
            return false;
        };
        if let Type::Ptr { pointee, .. } = self.compiler.program.types[ty_id.0 as usize] {
            ty_id = pointee;
        }
        if let Some(comp) = self.compiler.composites.get(&ty_id)
            && let Some((_, mdecl)) = comp.methods.get(method_name)
            && let Some(first_rt) = mdecl.params.iter().find(|p| !p.is_comptime)
        {
            return matches!(first_rt.ty, TypeExpr::Ref { mutable: true, .. });
        }
        if let Ok(cands) = self
            .compiler
            .find_in_scope_functions(&self.mod_path, method_name)
        {
            for (_, _, decl) in cands {
                if let Some(first_rt) = decl.params.iter().find(|p| !p.is_comptime)
                    && first_rt.name == "self"
                    && matches!(first_rt.ty, TypeExpr::Ref { mutable: true, .. })
                {
                    return true;
                }
            }
        }
        false
    }

    pub(super) fn record_capture(
        &self,
        name: &str,
        needs_mut: bool,
        bound: &crate::fasthash::FastSet<String>,
        captures: &mut Vec<(String, bool)>,
    ) {
        if bound.contains(name) {
            return;
        }
        if self.lookup_var(name).is_none() && self.lookup_capture(name).is_none() {
            return;
        }
        if let Some((_, existing_mut)) = captures.iter_mut().find(|(n, _)| n == name) {
            *existing_mut |= needs_mut;
        } else {
            captures.push((name.to_string(), needs_mut));
        }
    }

    pub(super) fn collect_captures_in_block(
        &self,
        block: &Block,
        bound: &crate::fasthash::FastSet<String>,
        captures: &mut Vec<(String, bool)>,
    ) {
        let mut local_bound = bound.clone();
        for stmt in &block.stmts {
            match stmt {
                Stmt::Let { name, init, .. } => {
                    self.note_capture_move(init, &local_bound);
                    self.collect_captures_in_expr(init, &local_bound, captures);
                    local_bound.insert(name.clone());
                }
                Stmt::LetDeferred { name, .. } => {
                    local_bound.insert(name.clone());
                }
                Stmt::LetDestructure { fields, init, .. } => {
                    self.collect_captures_in_expr(init, &local_bound, captures);
                    for (_, binding) in fields {
                        local_bound.insert(binding.clone());
                    }
                }
                Stmt::Assign { target, value, .. } => {
                    if let Some(root) = Self::root_var_of_place_expr(target) {
                        self.record_capture(root, true, &local_bound, captures);
                        self.note_capture_write(target, false);
                    }
                    self.collect_captures_in_expr(target, &local_bound, captures);
                    self.collect_captures_in_expr(value, &local_bound, captures);
                }
                Stmt::If {
                    cond,
                    then_block,
                    else_block,
                } => {
                    self.collect_captures_in_expr(cond, &local_bound, captures);
                    self.collect_captures_in_block(then_block, &local_bound, captures);
                    if let Some(eb) = else_block {
                        self.collect_captures_in_block(eb, &local_bound, captures);
                    }
                }
                Stmt::IfLet {
                    var_name,
                    opt_expr,
                    then_block,
                    else_block,
                } => {
                    self.collect_captures_in_expr(opt_expr, &local_bound, captures);
                    let mut then_bound = local_bound.clone();
                    then_bound.insert(var_name.clone());
                    self.collect_captures_in_block(then_block, &then_bound, captures);
                    if let Some(eb) = else_block {
                        self.collect_captures_in_block(eb, &local_bound, captures);
                    }
                }
                Stmt::While { cond, body } => {
                    self.collect_captures_in_expr(cond, &local_bound, captures);
                    self.collect_captures_in_block(body, &local_bound, captures);
                }
                Stmt::WhileLet {
                    var_name,
                    opt_expr,
                    body,
                } => {
                    self.collect_captures_in_expr(opt_expr, &local_bound, captures);
                    let mut body_bound = local_bound.clone();
                    body_bound.insert(var_name.clone());
                    self.collect_captures_in_block(body, &body_bound, captures);
                }
                Stmt::For {
                    var_name,
                    idx_name,
                    iter,
                    body,
                    ..
                } => {
                    match iter {
                        ForIter::Range { start, end, .. } => {
                            self.collect_captures_in_expr(start, &local_bound, captures);
                            self.collect_captures_in_expr(end, &local_bound, captures);
                        }
                        ForIter::Expr(e) => {
                            self.collect_captures_in_expr(e, &local_bound, captures);
                        }
                    }
                    let mut body_bound = local_bound.clone();
                    body_bound.insert(var_name.clone());
                    if let Some(idx) = idx_name {
                        body_bound.insert(idx.clone());
                    }
                    self.collect_captures_in_block(body, &body_bound, captures);
                }
                Stmt::Labeled { stmt, .. } => {
                    let block = Block {
                        stmts: vec![(**stmt).clone()],
                        lines: Vec::new(),
                    };
                    self.collect_captures_in_block(&block, &local_bound, captures);
                }
                Stmt::Return(opt_e) => {
                    if let Some(e) = opt_e {
                        self.note_capture_move(e, &local_bound);
                        self.collect_captures_in_expr(e, &local_bound, captures);
                    }
                }
                Stmt::Unsafe(blk) | Stmt::NoSuspend(blk) => {
                    self.collect_captures_in_block(blk, &local_bound, captures);
                }
                Stmt::Match { scrutinee, arms } => {
                    self.collect_captures_in_expr(scrutinee, &local_bound, captures);
                    for (pat, body) in arms {
                        let mut arm_bound = local_bound.clone();
                        pat.collect_bound_names(&mut arm_bound);
                        self.collect_captures_in_expr(body, &arm_bound, captures);
                    }
                }
                Stmt::Expr(e) => {
                    self.collect_captures_in_expr(e, &local_bound, captures);
                }
                Stmt::ComptimeFor {
                    var_name,
                    idx_name,
                    iterable,
                    body,
                } => {
                    self.collect_captures_in_expr(iterable, &local_bound, captures);
                    let mut body_bound = local_bound.clone();
                    body_bound.insert(var_name.clone());
                    if let Some(idx) = idx_name {
                        body_bound.insert(idx.clone());
                    }
                    self.collect_captures_in_block(body, &body_bound, captures);
                }
            }
        }
    }

    pub(super) fn collect_captures_in_expr(
        &self,
        expr: &Expr,
        bound: &crate::fasthash::FastSet<String>,
        captures: &mut Vec<(String, bool)>,
    ) {
        match expr {
            Expr::Int(_)
            | Expr::WideInt(_)
            | Expr::Float(_)
            | Expr::Bool(_)
            | Expr::Rune(_)
            | Expr::Str(_)
            | Expr::Null
            | Expr::Uninit(None)
            | Expr::TypeVal(_)
            | Expr::TypeMember { .. }
            | Expr::IntrinsicDefault(_)
            | Expr::IntrinsicLayout { .. }
            | Expr::IntrinsicTypeName(_)
            | Expr::IntrinsicSatisfies { .. }
            | Expr::IntrinsicFields(_)
            | Expr::IntrinsicLeaves(_)
            | Expr::IntrinsicVariants(_)
            | Expr::IntrinsicFnInfo(_)
            | Expr::Break(_)
            | Expr::Continue(_)
            | Expr::IntrinsicCompileError(_)
            | Expr::ZeroInit
            | Expr::IntrinsicTrap => {}
            Expr::Uninit(Some(inner)) => {
                self.collect_captures_in_expr(inner, bound, captures);
            }
            Expr::Move(inner) => {
                self.note_capture_move(inner, bound);
                self.collect_captures_in_expr(inner, bound, captures);
            }
            Expr::Async { call, executor, .. } => {
                self.collect_captures_in_expr(call, bound, captures);
                if let Some(e) = executor {
                    self.collect_captures_in_expr(e, bound, captures);
                }
            }
            Expr::Path(p) => {
                if p.len() == 1 {
                    self.record_capture(&p[0], false, bound, captures);
                }
            }
            Expr::RecordLit(fields) => {
                for (_, v) in fields {
                    self.collect_captures_in_expr(v, bound, captures);
                }
            }
            Expr::DotVariant { payload, .. } => {
                if let Some(p) = payload {
                    self.collect_captures_in_expr(p, bound, captures);
                }
            }
            Expr::RelRef(inner)
            | Expr::Deref(inner)
            | Expr::Field { base: inner, .. }
            | Expr::TupleIndex { base: inner, .. }
            | Expr::Unary { expr: inner, .. }
            | Expr::Cast { expr: inner, .. }
            | Expr::IntrinsicAlloc { len: inner, .. }
            | Expr::IntrinsicDealloc(inner)
            | Expr::IntrinsicRawAlloc(inner)
            | Expr::IntrinsicRawAllocZeroed(inner)
            | Expr::IntrinsicTransmute { src: inner, .. }
            | Expr::IntrinsicForget(inner)
            | Expr::IntrinsicCAbi(inner)
            | Expr::IntrinsicClone(inner)
            | Expr::IntrinsicDrop(inner)
            | Expr::IntrinsicBswap(inner)
            | Expr::Try(inner) => {
                self.collect_captures_in_expr(inner, bound, captures);
            }
            Expr::IntrinsicArithUnchecked { lhs, rhs, .. } => {
                self.collect_captures_in_expr(lhs, bound, captures);
                self.collect_captures_in_expr(rhs, bound, captures);
            }
            Expr::IntrinsicRealloc { ptr, len, .. } => {
                self.collect_captures_in_expr(ptr, bound, captures);
                self.collect_captures_in_expr(len, bound, captures);
            }
            Expr::IntrinsicAtomic { args, .. } => {
                for arg in args {
                    self.collect_captures_in_expr(arg, bound, captures);
                }
            }
            Expr::IntrinsicMemcpy { dest, src, len }
            | Expr::IntrinsicMemmove { dest, src, len } => {
                self.collect_captures_in_expr(dest, bound, captures);
                self.collect_captures_in_expr(src, bound, captures);
                self.collect_captures_in_expr(len, bound, captures);
            }
            Expr::Catch {
                expr: inner,
                err_binding,
                fallback,
            } => {
                self.collect_captures_in_expr(inner, bound, captures);
                let mut h_bound = bound.clone();
                if let Some(en) = err_binding {
                    h_bound.insert(en.clone());
                }
                self.collect_captures_in_expr(fallback, &h_bound, captures);
            }
            Expr::Match { scrutinee, arms } => {
                self.collect_captures_in_expr(scrutinee, bound, captures);
                for (pat, body) in arms {
                    let mut arm_bound = bound.clone();
                    pat.collect_bound_names(&mut arm_bound);
                    self.collect_captures_in_expr(body, &arm_bound, captures);
                }
            }
            Expr::Select { arms } => {
                for arm in arms {
                    let mut arm_bound = bound.clone();
                    match &arm.op {
                        SelectOp::Recv { bind, source } => {
                            self.collect_captures_in_expr(source, bound, captures);
                            if let Some(b) = bind {
                                arm_bound.insert(b.clone());
                            }
                        }
                        SelectOp::Send {
                            channel,
                            value,
                            unsent,
                        } => {
                            self.collect_captures_in_expr(channel, bound, captures);
                            self.collect_captures_in_expr(value, bound, captures);
                            if let Some((name, handler)) = unsent {
                                let mut h_bound = bound.clone();
                                h_bound.insert(name.clone());
                                self.collect_captures_in_expr(handler, &h_bound, captures);
                            }
                        }
                        SelectOp::Default => {}
                    }
                    self.collect_captures_in_expr(&arm.body, &arm_bound, captures);
                }
            }
            Expr::Block(blk) => {
                self.collect_captures_in_block(blk, bound, captures);
            }
            Expr::IntrinsicFormat {
                formatter, value, ..
            } => {
                self.collect_captures_in_expr(formatter, bound, captures);
                self.collect_captures_in_expr(value, bound, captures);
            }
            Expr::FormatStr(segments) => {
                for seg in segments {
                    if let FmtSegment::Interp { expr, .. } = seg {
                        self.collect_captures_in_expr(expr, bound, captures);
                    }
                }
            }
            Expr::Index { base, index } => {
                self.collect_captures_in_expr(base, bound, captures);
                self.collect_captures_in_expr(index, bound, captures);
            }
            Expr::Slice { base, start, end } => {
                self.collect_captures_in_expr(base, bound, captures);
                self.collect_captures_in_expr(start, bound, captures);
                self.collect_captures_in_expr(end, bound, captures);
            }
            Expr::Ref {
                mutable,
                expr: inner,
            }
            | Expr::RawPtr {
                mutable,
                expr: inner,
            } => {
                if *mutable && let Some(root) = Self::root_var_of_place_expr(inner) {
                    self.record_capture(root, true, bound, captures);
                    self.note_capture_write(inner, false);
                }
                self.collect_captures_in_expr(inner, bound, captures);
            }
            Expr::Binary { lhs, rhs, .. }
            | Expr::LogicalAnd(lhs, rhs)
            | Expr::LogicalOr(lhs, rhs)
            | Expr::OrElse {
                opt: lhs,
                fallback: rhs,
            } => {
                self.collect_captures_in_expr(lhs, bound, captures);
                self.collect_captures_in_expr(rhs, bound, captures);
            }
            Expr::TupleLit(elems) | Expr::SimdLit { elems, .. } => {
                for e in elems {
                    self.collect_captures_in_expr(e, bound, captures);
                }
            }
            Expr::StructLit { fields, .. } => {
                for (_, e) in fields {
                    self.note_capture_move(e, bound);
                    self.collect_captures_in_expr(e, bound, captures);
                }
            }
            Expr::Return(opt_e) => {
                if let Some(e) = opt_e {
                    self.note_capture_move(e, bound);
                    self.collect_captures_in_expr(e, bound, captures);
                }
            }
            Expr::UnsafeBlock(blk) => {
                self.collect_captures_in_block(blk, bound, captures);
            }
            Expr::Lambda { params, body, .. } => {
                let mut inner_bound = bound.clone();
                for (_, pname, _) in params {
                    inner_bound.insert(pname.clone());
                }
                self.collect_captures_in_block(body, &inner_bound, captures);
            }
            Expr::Call { callee, args, .. } => {
                if let Expr::Path(p) = callee.as_ref()
                    && p.len() == 1
                    && let Some(ty_id) = self
                        .lookup_var(&p[0])
                        .map(|(_, t)| t)
                        .or_else(|| self.lookup_capture(&p[0]).map(|(_, t)| t))
                    && self
                        .compiler
                        .closures
                        .get(&ty_id)
                        .is_some_and(|c| c.env_mut)
                {
                    self.record_capture(&p[0], true, bound, captures);
                }
                self.collect_captures_in_expr(callee, bound, captures);
                for a in args {
                    self.note_capture_move(a, bound);
                    self.collect_captures_in_expr(a, bound, captures);
                }
            }
            Expr::MethodCall {
                receiver,
                method,
                args,
                ..
            } => {
                if let Some(root) = Self::root_var_of_place_expr(receiver)
                    && self.method_requires_mut_self(root, method)
                {
                    self.record_capture(root, true, bound, captures);
                    self.note_capture_write(receiver, true);
                }
                if let Expr::Path(p) = receiver.as_ref()
                    && p.len() == 1
                    && !bound.contains(&p[0])
                {
                    self.capture_moves.borrow_mut().push((p[0].clone(), Some(method.clone())));
                }
                self.collect_captures_in_expr(receiver, bound, captures);
                for a in args {
                    self.note_capture_move(a, bound);
                    self.collect_captures_in_expr(a, bound, captures);
                }
            }
            Expr::If {
                cond,
                then_block,
                else_block,
            } => {
                self.collect_captures_in_expr(cond, bound, captures);
                self.collect_captures_in_block(then_block, bound, captures);
                if let Some(eb) = else_block {
                    self.collect_captures_in_block(eb, bound, captures);
                }
            }
            Expr::SliceLit { elems, .. } => {
                for e in elems {
                    self.collect_captures_in_expr(e, bound, captures);
                }
            }
            Expr::MapLit(entries) => {
                for (k, v) in entries {
                    self.collect_captures_in_expr(k, bound, captures);
                    self.collect_captures_in_expr(v, bound, captures);
                }
            }
            Expr::IntrinsicInvert(inner)
            | Expr::IntrinsicDeclarations(inner)
            | Expr::IntrinsicEntries(inner)
            | Expr::IntrinsicHasField { name: inner, .. }
            | Expr::IntrinsicHasMethod { name: inner, .. }
            | Expr::IntrinsicAssert { cond: inner, .. } => {
                self.collect_captures_in_expr(inner, bound, captures);
            }
            Expr::IntrinsicField { base, field }
            | Expr::IntrinsicVariant {
                base,
                variant: field,
            } => {
                self.collect_captures_in_expr(base, bound, captures);
                self.collect_captures_in_expr(field, bound, captures);
            }
            Expr::IntrinsicMakeUnion {
                variant, payload, ..
            } => {
                self.collect_captures_in_expr(variant, bound, captures);
                if let Some(p) = payload {
                    self.collect_captures_in_expr(p, bound, captures);
                }
            }
            Expr::IntrinsicMap { entries, .. } => {
                self.collect_captures_in_expr(entries, bound, captures);
            }
        }
    }

    /// Evaluates bracketed comptime arguments; `_` (infer this one) is `None`.
    pub(super) fn eval_ct_args(&mut self, ct: &[Expr]) -> Result<Vec<Option<ComptimeVal>>, String> {
        ct.iter()
            .map(|e| match e {
                _ if Compiler::is_placeholder(e) => Ok(None),
                _ => self
                    .compiler
                    .eval_comptime_val(&self.mod_path, self.owner_ty, &self.comptime_env, e)
                    .map(Some),
            })
            .collect()
    }

    /// The explicit comptime arguments `given`, by parameter name, as a starting point for
    /// inference.
    fn seed_ct_args(
        ct_params: &[(String, TypeExpr)],
        given: &[Option<ComptimeVal>],
    ) -> HashMap<String, ComptimeVal> {
        ct_params
            .iter()
            .zip(given)
            .filter_map(|((n, _), v)| v.clone().map(|v| (n.clone(), v)))
            .collect()
    }

    pub(super) fn lower_call(
        &mut self,
        callee: &Expr,
        ct_args: Option<&[Expr]>,
        args: &[Expr],
    ) -> Result<(Operand, TypeId), String> {
        if let Some(ct) = ct_args {
            // `fs[i](x)`: index a local, then call the element.
            if let Expr::Path(p) = callee
                && p.len() == 1
                && ct.len() == 1
                && (self.lookup_var(&p[0]).is_some() || self.lookup_capture(&p[0]).is_some())
            {
                let elem = Expr::Index {
                    base: Box::new(callee.clone()),
                    index: Box::new(ct[0].clone()),
                };
                return self.lower_call(&elem, None, args);
            }
            if !matches!(callee, Expr::Path(_)) {
                return Err(format!(
                    "Comptime arguments '[...]' can only be passed to a named function, not {callee:?}"
                ));
            }
        }
        let Expr::Path(path) = callee else {
            let (callee_op, callee_ty) = self.lower_expr(callee, None)?;
            if let Type::FnPtr {
                args: param_tys,
                ret: ret_ty,
            } = self.compiler.program.types[callee_ty.0 as usize].clone()
            {
                if args.len() != param_tys.len() {
                    return Err(format!(
                        "A function pointer of type '{}' takes {} argument(s), given {}",
                        self.compiler.type_display_name(callee_ty),
                        param_tys.len(),
                        args.len()
                    ));
                }
                let mut lowered_args = Vec::with_capacity(args.len());
                for (i, arg) in args.iter().enumerate() {
                    let exp = param_tys.get(i).copied();
                    let (op, a_ty) = self.lower_expr(arg, exp)?;
                    let coerced = if let Some(pt) = exp {
                        self.coerce_operand(op, a_ty, pt)?
                    } else {
                        op
                    };
                    lowered_args.push(coerced);
                }
                let dst = self.alloc_temp(ret_ty);
                let next_bb = self.new_block();
                self.check_unsafe_call(None, Some(callee_ty), "a function pointer")?;
                self.terminate(Terminator::Call {
                    func: callee_op,
                    args: lowered_args,
                    destination: Place::new(dst),
                    target: next_bb,
                });
                self.body.cur_block = next_bb;
                if matches!(self.compiler.program.types[ret_ty.0 as usize], Type::Never) {
                    self.terminate(Terminator::Unreachable);
                }
                return Ok((Operand::Move(Place::new(dst)), ret_ty));
            }
            if let Some(closure_info) = self.compiler.closures.get(&callee_ty).cloned() {
                let first_arg = if closure_info.env_by_val {
                    callee_op
                } else {
                    let env_local = self.alloc_temp(callee_ty);
                    self.emit(Statement::Assign(
                        Place::new(env_local),
                        Rvalue::Use(callee_op),
                    ));
                    let env_ref_ty = self.compiler.intern_type(Type::Ptr {
                        mutable: closure_info.env_mut,
                        pointee: callee_ty,
                    });
                    let env_ref_tmp = self.alloc_temp(env_ref_ty);
                    self.emit(Statement::Assign(
                        Place::new(env_ref_tmp),
                        Rvalue::Ref {
                            mutable: closure_info.env_mut,
                            place: Place::new(env_local),
                        },
                    ));
                    Operand::Copy(Place::new(env_ref_tmp))
                };
                let mut lowered_args = Vec::with_capacity(args.len() + 1);
                lowered_args.push(first_arg);
                for (i, arg) in args.iter().enumerate() {
                    let exp = closure_info.param_tys.get(i).copied();
                    let (op, a_ty) = self.lower_expr(arg, exp)?;
                    let coerced = if let Some(pt) = exp {
                        self.coerce_operand(op, a_ty, pt)?
                    } else {
                        op
                    };
                    lowered_args.push(coerced);
                }
                let dst = self.alloc_temp(closure_info.ret_ty);
                let next_bb = self.new_block();
                self.terminate(Terminator::Call {
                    func: Operand::Const(ConstValue::Func(closure_info.call_fn_id)),
                    args: lowered_args,
                    destination: Place::new(dst),
                    target: next_bb,
                });
                self.body.cur_block = next_bb;
                if matches!(
                    self.compiler.program.types[closure_info.ret_ty.0 as usize],
                    Type::Never
                ) {
                    self.terminate(Terminator::Unreachable);
                }
                return Ok((Operand::Move(Place::new(dst)), closure_info.ret_ty));
            }
            return Err(format!("Unsupported callee expression {callee:?}"));
        };

        // Check if `callee` is a local or captured variable holding a function pointer (`fn(...) -> R`) or `closure`:
        if path.len() == 1
            && let Some((var_place, var_ty)) = self
                .lookup_var(&path[0])
                .map(|(l, t)| (Place::new(l), t))
                .or_else(|| self.lookup_capture(&path[0]))
        {
            let (deref_place, pointee_ty, is_ptr, ptr_mut) = if let Type::Ptr { mutable, pointee } =
                self.compiler.program.types[var_ty.0 as usize]
            {
                let mut dp = var_place.clone();
                dp.projections.push(Projection::Deref);
                (dp, pointee, true, mutable)
            } else {
                (var_place.clone(), var_ty, false, true)
            };

            if let Type::FnPtr {
                args: param_tys,
                ret: ret_ty,
            } = self.compiler.program.types[pointee_ty.0 as usize].clone()
            {
                if args.len() != param_tys.len() {
                    return Err(format!(
                        "'{}', of type '{}', takes {} argument(s), given {}",
                        path[0],
                        self.compiler.type_display_name(pointee_ty),
                        param_tys.len(),
                        args.len()
                    ));
                }
                let mut lowered_args = Vec::with_capacity(args.len());
                for (i, arg) in args.iter().enumerate() {
                    let exp = param_tys.get(i).copied();
                    let (op, a_ty) = self.lower_expr(arg, exp)?;
                    let coerced = if let Some(pt) = exp {
                        self.coerce_operand(op, a_ty, pt)?
                    } else {
                        op
                    };
                    lowered_args.push(coerced);
                }
                let dst = self.alloc_temp(ret_ty);
                let next_bb = self.new_block();
                self.check_unsafe_call(None, Some(pointee_ty), &path[0])?;
                self.terminate(Terminator::Call {
                    func: Operand::Copy(deref_place),
                    args: lowered_args,
                    destination: Place::new(dst),
                    target: next_bb,
                });
                self.body.cur_block = next_bb;
                if matches!(self.compiler.program.types[ret_ty.0 as usize], Type::Never) {
                    self.terminate(Terminator::Unreachable);
                }
                return Ok((Operand::Move(Place::new(dst)), ret_ty));
            }

            if let Some(closure_info) = self.compiler.closures.get(&pointee_ty).cloned() {
                if closure_info.env_by_val {
                    if is_ptr {
                        return Err(format!(
                            "Cannot call single-use closure '{}' through a reference; it must be called by value",
                            path[0]
                        ));
                    }
                    let mut lowered_args = Vec::with_capacity(args.len() + 1);
                    lowered_args.push(Operand::Move(deref_place));
                    for (i, arg) in args.iter().enumerate() {
                        let exp = closure_info.param_tys.get(i).copied();
                        let (op, a_ty) = self.lower_expr(arg, exp)?;
                        let coerced = if let Some(pt) = exp {
                            self.coerce_operand(op, a_ty, pt)?
                        } else {
                            op
                        };
                        lowered_args.push(coerced);
                    }
                    let dst = self.alloc_temp(closure_info.ret_ty);
                    let next_bb = self.new_block();
                    self.terminate(Terminator::Call {
                        func: Operand::Const(ConstValue::Func(closure_info.call_fn_id)),
                        args: lowered_args,
                        destination: Place::new(dst),
                        target: next_bb,
                    });
                    self.body.cur_block = next_bb;
                    if matches!(
                        self.compiler.program.types[closure_info.ret_ty.0 as usize],
                        Type::Never
                    ) {
                        self.terminate(Terminator::Unreachable);
                    }
                    return Ok((Operand::Move(Place::new(dst)), closure_info.ret_ty));
                }
                if is_ptr && closure_info.env_mut && !ptr_mut {
                    return Err(format!(
                        "Cannot call mutating closure '{}' through an immutable reference",
                        path[0]
                    ));
                }
                let env_ref_ty = self.compiler.intern_type(Type::Ptr {
                    mutable: closure_info.env_mut,
                    pointee: pointee_ty,
                });
                let env_ref_tmp = self.alloc_temp(env_ref_ty);
                self.emit(Statement::Assign(
                    Place::new(env_ref_tmp),
                    Rvalue::Ref {
                        mutable: closure_info.env_mut,
                        place: deref_place,
                    },
                ));
                let mut lowered_args = Vec::with_capacity(args.len() + 1);
                lowered_args.push(Operand::Copy(Place::new(env_ref_tmp)));
                for (i, arg) in args.iter().enumerate() {
                    let exp = closure_info.param_tys.get(i).copied();
                    let (op, a_ty) = self.lower_expr(arg, exp)?;
                    let coerced = if let Some(pt) = exp {
                        self.coerce_operand(op, a_ty, pt)?
                    } else {
                        op
                    };
                    lowered_args.push(coerced);
                }
                let dst = self.alloc_temp(closure_info.ret_ty);
                let next_bb = self.new_block();
                self.terminate(Terminator::Call {
                    func: Operand::Const(ConstValue::Func(closure_info.call_fn_id)),
                    args: lowered_args,
                    destination: Place::new(dst),
                    target: next_bb,
                });
                self.body.cur_block = next_bb;
                if matches!(
                    self.compiler.program.types[closure_info.ret_ty.0 as usize],
                    Type::Never
                ) {
                    self.terminate(Terminator::Unreachable);
                }
                return Ok((Operand::Move(Place::new(dst)), closure_info.ret_ty));
            }
        }

        // Check static method call on `Self::method(...)` or `Type::method(...)`
        let expanded_path = self.compiler.expand_module_path(&self.comptime_env, path);
        let path = &expanded_path;
        if path.len() >= 2 {
            let method_name = path.last().unwrap();
            let prefix = &path[..path.len() - 1];
            let maybe_ty = if prefix.len() == 1 && prefix[0] == "Self" {
                self.owner_ty
            } else if prefix.len() == 1
                && let Some(ComptimeVal::Type(t)) = self.comptime_env.get(&prefix[0])
            {
                Some(*t)
            } else if let Ok(ResolvedItem::Type(tmod, tname)) =
                self.compiler.resolve_path(&self.mod_path, prefix)
            {
                Some(self.compiler.resolve_named_type(&tmod, &tname)?)
            } else {
                None
            };
            if let Some(comp_ty) = maybe_ty {
                return self.lower_static_type_call(comp_ty, method_name, ct_args, args);
            }
        }

        // Check `TypeCall(comptime_args)::method(...)` isn't here, or direct function call
        match self.compiler.resolve_path(&self.mod_path, path)? {
            ResolvedItem::ExternFunc(emod, ename) => {
                let fn_id = self.compiler.get_or_register_extern(&emod, &ename)?;
                let (param_tys, ret_ty) = self.compiler.func_sigs[&fn_id].clone();
                let mut lowered_args = Vec::with_capacity(args.len());
                for (i, arg) in args.iter().enumerate() {
                    let exp = param_tys.get(i).copied();
                    let (op, a_ty) = self.lower_expr(arg, exp)?;
                    let coerced = if let Some(pt) = exp {
                        self.coerce_operand(op, a_ty, pt)?
                    } else {
                        op
                    };
                    lowered_args.push(coerced);
                }
                let dst = self.alloc_temp(ret_ty);
                let next_bb = self.new_block();
                if self.unsafe_depth == 0
                    && !self.compiler.safe_externs.contains(&(emod.clone(), ename.clone()))
                {
                    return Err(format!(
                        "Calling extern function '{ename}' requires an 'unsafe {{ ... }}' block (declare it 'safe extern fn' if it has no preconditions)"
                    ));
                }
                self.terminate(Terminator::Call {
                    func: Operand::Const(ConstValue::Func(fn_id)),
                    args: lowered_args,
                    destination: Place::new(dst),
                    target: next_bb,
                });
                self.body.cur_block = next_bb;
                if matches!(self.compiler.program.types[ret_ty.0 as usize], Type::Never) {
                    self.terminate(Terminator::Unreachable);
                }
                Ok((Operand::Move(Place::new(dst)), ret_ty))
            }
            ResolvedItem::Func(fmod, fname) => {
                let overloads =
                    self.compiler
                        .find_funcs_in_module(&self.mod_path, &fmod, &fname)?;
                if overloads.is_empty() {
                    return Err(format!("Function '{fname}' not found in '{fmod}'"));
                }

                // Comptime arguments that are not all given (`f(x)`, `f[_, u8](x)`, or a list
                // shorter than the parameters) are inferred from the runtime arguments; what is
                // still missing then takes its default.
                let given = match ct_args {
                    Some(ct) => Some(self.eval_ct_args(ct)?),
                    None => None,
                };
                let has_inferred_candidate = overloads.iter().any(|(_, _, d)| {
                    let ct_count = d.params.iter().filter(|p| p.is_comptime).count();
                    ct_count > 0
                        && d.params.iter().filter(|p| !p.is_comptime).count() == args.len()
                        && given.as_ref().is_none_or(|g| {
                            g.len() < ct_count || g.iter().any(Option::is_none)
                        })
                });
                if !has_inferred_candidate
                    && given.as_ref().is_none_or(|g| g.iter().any(Option::is_none))
                    && overloads
                        .iter()
                        .all(|(_, _, d)| d.params.iter().any(|p| p.is_comptime))
                {
                    let decl = &overloads[0].2;
                    let rt_count = decl.params.iter().filter(|p| !p.is_comptime).count();
                    if rt_count != args.len() {
                        return Err(format!(
                            "Function '{fname}' expects {rt_count} argument(s), got {}",
                            args.len()
                        ));
                    }
                    return Err(format!(
                        "Comptime arguments of '{fname}' cannot be inferred here; pass them in brackets ('{fname}[...](...)')"
                    ));
                }
                let given = given.unwrap_or_default();

                if has_inferred_candidate {
                    let first_rt_params: Vec<_> = overloads[0]
                        .2
                        .params
                        .iter()
                        .filter(|p| !p.is_comptime)
                        .cloned()
                        .collect();
                    let first_ct_params: Vec<(String, TypeExpr)> = overloads[0]
                        .2
                        .params
                        .iter()
                        .filter(|p| p.is_comptime)
                        .map(|p| (p.name.clone(), p.ty.clone()))
                        .collect();
                    let mut prog_env = Self::seed_ct_args(&first_ct_params, &given);
                    let mut pre_lowered = Vec::with_capacity(args.len());
                    for (i, arg_expr) in args.iter().enumerate() {
                        let exp_ty = first_rt_params.get(i).and_then(|rp| {
                            self.compiler
                                .resolve_type_expr(&fmod, None, &prog_env, &rp.ty)
                                .ok()
                        });
                        let (op, a_ty) = self.lower_expr(arg_expr, exp_ty)?;
                        if let Some(rp) = first_rt_params.get(i) {
                            let _ = self.compiler.unify_type_pattern(
                                &fmod,
                                &first_ct_params,
                                &rp.ty,
                                a_ty,
                                &mut prog_env,
                            );
                        }
                        pre_lowered.push((op, a_ty));
                    }

                    let mut best_ct_args: Option<(Vec<ComptimeVal>, u32)> = None;
                    let mut incomplete_err = None;
                    for (_, _, cand_decl) in &overloads {
                        let rt_params: Vec<_> =
                            cand_decl.params.iter().filter(|p| !p.is_comptime).collect();
                        if rt_params.len() != pre_lowered.len() {
                            continue;
                        }
                        let ct_params: Vec<(String, TypeExpr)> = cand_decl
                            .params
                            .iter()
                            .filter(|p| p.is_comptime)
                            .map(|p| (p.name.clone(), p.ty.clone()))
                            .collect();
                        let mut inferred = Self::seed_ct_args(&ct_params, &given);
                        let mut spec_sum = 0u32;
                        let mut matched_all = true;
                        for (rt_p, (_, a_ty)) in rt_params.iter().zip(pre_lowered.iter()) {
                            if let Some(s) = self.compiler.unify_type_pattern(
                                &fmod,
                                &ct_params,
                                &rt_p.ty,
                                *a_ty,
                                &mut inferred,
                            )? {
                                spec_sum += s as u32;
                            } else {
                                matched_all = false;
                                break;
                            }
                        }
                        if !matched_all {
                            continue;
                        }
                        match self.compiler.complete_comptime_args(
                            &fmod, &fname, cand_decl, &given, &inferred,
                        ) {
                            Ok(ct_args)
                                if best_ct_args.as_ref().is_none_or(|(_, bs)| spec_sum > *bs) =>
                            {
                                best_ct_args = Some((ct_args, spec_sum));
                            }
                            Ok(_) => {}
                            Err(e) => incomplete_err = Some(e),
                        }
                    }

                    let (ct_args, _) = match best_ct_args {
                        Some(pair) => pair,
                        None => {
                            if overloads.len() == 1 {
                                let cand_decl = &overloads[0].2;
                                let rt_params: Vec<_> =
                                    cand_decl.params.iter().filter(|p| !p.is_comptime).collect();
                                let unconstrained_ct: Vec<(String, TypeExpr)> = cand_decl
                                    .params
                                    .iter()
                                    .filter(|p| p.is_comptime)
                                    .map(|p| (p.name.clone(), TypeExpr::Constraint(TypeConstraint::Unchecked)))
                                    .collect();
                                let mut inferred = HashMap::default();
                                let mut matched_all = rt_params.len() == pre_lowered.len();
                                for (rt_p, (_, a_ty)) in rt_params.iter().zip(pre_lowered.iter()) {
                                    if self
                                        .compiler
                                        .unify_type_pattern(
                                            &fmod,
                                            &unconstrained_ct,
                                            &rt_p.ty,
                                            *a_ty,
                                            &mut inferred,
                                        )?
                                        .is_none()
                                    {
                                        matched_all = false;
                                        break;
                                    }
                                }
                                if matched_all
                                    && unconstrained_ct
                                        .iter()
                                        .all(|(n, _)| inferred.contains_key(n))
                                {
                                    let ct_args: Vec<ComptimeVal> = unconstrained_ct
                                        .iter()
                                        .map(|(n, _)| inferred[n].clone())
                                        .collect();
                                    if let Err(reason) = self
                                        .compiler
                                        .get_or_instantiate_func(&fmod, &fname, &ct_args)
                                    {
                                        return Err(format!(
                                            "No overload of '{}' in '{}' matches inferred argument types: {}",
                                            fname, fmod, reason
                                        ));
                                    }
                                }
                            }
                            if let Some(e) = incomplete_err {
                                return Err(e);
                            }
                            return Err(format!(
                                "No overload of '{fname}' in '{fmod}' matches inferred argument types; if its comptime arguments cannot be inferred, pass them in brackets ('{fname}[...](...)')"
                            ));
                        }
                    };
                    let fn_id = self
                        .compiler
                        .get_or_instantiate_func(&fmod, &fname, &ct_args)?;
                    let (param_tys, ret_ty) = self.compiler.func_sigs[&fn_id].clone();
                    let mut lowered_args = Vec::with_capacity(pre_lowered.len());
                    for (i, (op, a_ty)) in pre_lowered.into_iter().enumerate() {
                        let coerced = if let Some(&pt) = param_tys.get(i) {
                            self.coerce_operand(op, a_ty, pt)?
                        } else {
                            op
                        };
                        lowered_args.push(coerced);
                    }
                    let dst = self.alloc_temp(ret_ty);
                    let next_bb = self.new_block();
                    self.check_unsafe_call(Some(fn_id), None, &fname)?;
                    self.terminate(Terminator::Call {
                        func: Operand::Const(ConstValue::Func(fn_id)),
                        args: lowered_args,
                        destination: Place::new(dst),
                        target: next_bb,
                    });
                    self.body.cur_block = next_bb;
                    if matches!(self.compiler.program.types[ret_ty.0 as usize], Type::Never) {
                        self.terminate(Terminator::Unreachable);
                    }
                    self.last_call_opaque_bound =
                        self.compiler.opaque_ret_funcs.get(&fn_id).cloned();
                    return Ok((Operand::Move(Place::new(dst)), ret_ty));
                }

                let decl = &overloads[0].2;
                let ct_args =
                    self.compiler
                        .complete_comptime_args(&fmod, &fname, decl, &given, &HashMap::default())?;
                let rt_arg_exprs: Vec<&Expr> = args.iter().collect();
                let fn_id = self
                    .compiler
                    .get_or_instantiate_func(&fmod, &fname, &ct_args)?;
                if ct_args.is_empty()
                    && let Some(wrapper) = self.compiler.c_abi_func_wrappers.get(&fn_id)
                    && args.len() == wrapper.c_abi_param_tys.len()
                    && args.len() != decl.params.len()
                {
                    return Err(format!(
                        "Export function '{}' must be called with its SlopLang signature from SlopLang code ({} arguments); its lowered C ABI is only for C callers (use '@c_abi({})' to obtain a C function pointer)",
                        fname,
                        decl.params.len(),
                        fname
                    ));
                }
                let (param_tys, ret_ty) = self.compiler.func_sigs[&fn_id].clone();
                let mut lowered_args = Vec::with_capacity(rt_arg_exprs.len());
                for (i, arg) in rt_arg_exprs.iter().enumerate() {
                    let exp = param_tys.get(i).copied();
                    let (op, a_ty) = self.lower_expr(arg, exp)?;
                    let coerced = if let Some(pt) = exp {
                        self.coerce_operand(op, a_ty, pt)?
                    } else {
                        op
                    };
                    lowered_args.push(coerced);
                }
                let dst = self.alloc_temp(ret_ty);
                let next_bb = self.new_block();
                self.check_unsafe_call(Some(fn_id), None, &fname)?;
                self.terminate(Terminator::Call {
                    func: Operand::Const(ConstValue::Func(fn_id)),
                    args: lowered_args,
                    destination: Place::new(dst),
                    target: next_bb,
                });
                self.body.cur_block = next_bb;
                if matches!(self.compiler.program.types[ret_ty.0 as usize], Type::Never) {
                    self.terminate(Terminator::Unreachable);
                }
                self.last_call_opaque_bound = self.compiler.opaque_ret_funcs.get(&fn_id).cloned();
                Ok((Operand::Move(Place::new(dst)), ret_ty))
            }
            other => Err(format!("Cannot call {other:?}")),
        }
    }

    /// Rejects calling an `unsafe fn` (`fn_id`), or through an `unsafe fn(...)` pointer type
    /// (`ptr_ty`), outside an `unsafe` block: the caller must uphold the callee's preconditions.
    fn check_unsafe_call(
        &self,
        fn_id: Option<FuncId>,
        ptr_ty: Option<TypeId>,
        name: &str,
    ) -> Result<(), String> {
        if self.unsafe_depth > 0 {
            return Ok(());
        }
        if fn_id.is_some_and(|id| self.compiler.unsafe_fns.contains(&id)) {
            return Err(format!(
                "Calling 'unsafe fn' '{name}' requires an 'unsafe {{ ... }}' block"
            ));
        }
        if ptr_ty.is_some_and(|t| self.compiler.unsafe_fn_ptr_types.contains(&t)) {
            return Err(format!(
                "Calling '{name}' through an unsafe function pointer type ('{}') requires an 'unsafe {{ ... }}' block",
                self.compiler.type_display_name(ptr_ty.unwrap())
            ));
        }
        Ok(())
    }

    pub(super) fn lower_static_type_call(
        &mut self,
        comp_ty: TypeId,
        method_name: &str,
        ct_args: Option<&[Expr]>,
        args: &[Expr],
    ) -> Result<(Operand, TypeId), String> {
        // Qualified trait method call `Trait::method(&recv, ...)`: dispatches statically to the
        // receiver type's `impl Trait`.
        if let Some(trait_info) = self.compiler.traits.get(&comp_ty).cloned() {
            let Some(m_idx) = trait_info.methods.iter().position(|m| m.name == method_name) else {
                return Err(format!(
                    "Trait '{}' has no method '{}'",
                    trait_info.name, method_name
                ));
            };
            let Some((recv_expr, rest)) = args.split_first() else {
                return Err(format!(
                    "Qualified trait call '{}::{}' needs the receiver as its first argument",
                    trait_info.name, method_name
                ));
            };
            let (recv_op, recv_ty) = self.lower_expr(recv_expr, None)?;
            // A method taking `self` by reference is given `&recv`; one taking it by value is
            // given the receiver itself, which may be a reference (`A = &Pool`).
            let by_ref = trait_info.methods[m_idx]
                .params
                .first()
                .is_some_and(|p| matches!(p.ty, TypeExpr::Ref { .. }));
            let concrete = match self.compiler.program.types[recv_ty.0 as usize] {
                Type::Ptr { pointee, .. } if by_ref && !self.compiler.raw_ptrs.contains_key(&recv_ty) => {
                    pointee
                }
                _ => recv_ty,
            };
            let fn_id =
                self.compiler
                    .resolve_trait_impl_method(&self.mod_path, concrete, comp_ty, m_idx, true)?;
            let (param_tys, ret_ty) = self.compiler.func_sigs[&fn_id].clone();
            if rest.len() + 1 != param_tys.len() {
                return Err(format!(
                    "Method '{}::{}' expects {} arguments, got {}",
                    trait_info.name,
                    method_name,
                    param_tys.len(),
                    args.len()
                ));
            }
            let mut lowered = vec![self.coerce_operand(recv_op, recv_ty, param_tys[0])?];
            for (arg, &pt) in rest.iter().zip(&param_tys[1..]) {
                let (op, a_ty) = self.lower_expr(arg, Some(pt))?;
                lowered.push(self.coerce_operand(op, a_ty, pt)?);
            }
            let dst = self.alloc_temp(ret_ty);
            let next_bb = self.new_block();
            self.check_unsafe_call(Some(fn_id), None, method_name)?;
            self.terminate(Terminator::Call {
                func: Operand::Const(ConstValue::Func(fn_id)),
                args: lowered,
                destination: Place::new(dst),
                target: next_bb,
            });
            self.body.cur_block = next_bb;
            if matches!(self.compiler.program.types[ret_ty.0 as usize], Type::Never) {
                self.terminate(Terminator::Unreachable);
            }
            return Ok((Operand::Move(Place::new(dst)), ret_ty));
        }
        if let Some(err_info) = self.compiler.errors.get(&comp_ty).cloned() {
            let mut matched = Vec::new();
            for (v_idx, leaf) in err_info.leaves.iter().enumerate() {
                if leaf.key.variant_name == method_name {
                    matched.push((v_idx, leaf.clone()));
                }
            }
            if matched.is_empty() {
                return Err(format!(
                    "Error type '{}' has no variant '{}'",
                    err_info.name, method_name
                ));
            }
            if matched.len() > 1 {
                return Err(format!(
                    "Variant '{}' is ambiguous in error type '{}'; qualify with the specific error type",
                    method_name, err_info.name
                ));
            }
            let (v_idx, leaf) = &matched[0];
            let void_ty = self.compiler.intern_type(Type::Void);
            if leaf.payload_ty == void_ty {
                if !self.void_payload_args(args)? {
                    return Err(format!(
                        "Error variant '{}::{}' has no payload, but {} arguments were provided",
                        err_info.name,
                        method_name,
                        args.len()
                    ));
                }
                let tmp = self.alloc_temp(comp_ty);
                self.emit(Statement::Assign(
                    Place::new(tmp),
                    Rvalue::Union {
                        ty: comp_ty,
                        variant: *v_idx as u32,
                        payload: Operand::Const(ConstValue::Void),
                    },
                ));
                return Ok((Operand::Move(Place::new(tmp)), comp_ty));
            }
            if args.len() != 1 {
                return Err(format!(
                    "Error variant '{}::{}' expects 1 payload argument, got {}",
                    err_info.name,
                    method_name,
                    args.len()
                ));
            }
            let (op, a_ty) = self.lower_expr(&args[0], Some(leaf.payload_ty))?;
            let coerced = self.coerce_operand(op, a_ty, leaf.payload_ty)?;
            let tmp = self.alloc_temp(comp_ty);
            self.emit(Statement::Assign(
                Place::new(tmp),
                Rvalue::Union {
                    ty: comp_ty,
                    variant: *v_idx as u32,
                    payload: coerced,
                },
            ));
            return Ok((Operand::Move(Place::new(tmp)), comp_ty));
        }
        if let Some(u_info) = self.compiler.unions.get(&comp_ty).cloned() {
            let Some((v_idx, (_, payload_ty))) = u_info
                .variants
                .iter()
                .enumerate()
                .find(|(_, (vn, _))| vn == method_name)
            else {
                return Err(format!(
                    "Union '{}' has no variant '{}'",
                    u_info.name, method_name
                ));
            };
            let payload_ty = *payload_ty;
            let void_ty = self.compiler.intern_type(Type::Void);
            if payload_ty == void_ty {
                if !self.void_payload_args(args)? {
                    return Err(format!(
                        "Union variant '{}::{}' has no payload, but {} arguments were provided",
                        u_info.name,
                        method_name,
                        args.len()
                    ));
                }
                let tmp = self.alloc_temp(comp_ty);
                self.emit(Statement::Assign(
                    Place::new(tmp),
                    Rvalue::Union {
                        ty: comp_ty,
                        variant: v_idx as u32,
                        payload: Operand::Const(ConstValue::Void),
                    },
                ));
                return Ok((Operand::Move(Place::new(tmp)), comp_ty));
            }
            if args.len() != 1 {
                return Err(format!(
                    "Union variant '{}::{}' expects 1 payload argument, got {}",
                    u_info.name,
                    method_name,
                    args.len()
                ));
            }
            let (op, a_ty) = self.lower_expr(&args[0], Some(payload_ty))?;
            let coerced = self.coerce_operand(op, a_ty, payload_ty)?;
            let tmp = self.alloc_temp(comp_ty);
            self.emit(Statement::Assign(
                Place::new(tmp),
                Rvalue::Union {
                    ty: comp_ty,
                    variant: v_idx as u32,
                    payload: coerced,
                },
            ));
            return Ok((Operand::Move(Place::new(tmp)), comp_ty));
        }

        let (type_name, def_mod, ct_env, methods, method_fn_ids) =
            if let Some(comp) = self.compiler.composites.get(&comp_ty).cloned() {
                (
                    comp.name.clone(),
                    comp.def_module.clone(),
                    comp.comptime_env.clone(),
                    comp.methods.clone(),
                    comp.method_fn_ids.clone(),
                )
            } else if let Some(nt) = self.compiler.distinct_types.get(&comp_ty).cloned() {
                (
                    nt.name,
                    nt.def_module,
                    nt.comptime_env,
                    std::sync::Arc::new(nt.methods),
                    nt.method_fn_ids,
                )
            } else {
                return Err(format!(
                    "Type '{}' has no methods",
                    self.compiler.type_display_name(comp_ty)
                ));
            };
        let Some((m_vis, m_decl)) = methods.get(method_name) else {
            if let Some(fn_id) = self.static_trait_method(comp_ty, method_name)? {
                return self.lower_static_trait_call(fn_id, method_name, args);
            }
            return Err(format!(
                "Type '{}' has no method '{}'",
                type_name, method_name
            ));
        };
        self.check_method_visibility(*m_vis, comp_ty, &def_mod, method_name, &type_name)?;
        let ct_count = m_decl.params.iter().filter(|p| p.is_comptime).count();
        if let Some(ct) = ct_args
            && ct.len() > ct_count
        {
            return Err(format!(
                "Method '{}::{}' takes {} comptime argument(s) in brackets, got {}",
                type_name,
                method_name,
                ct_count,
                ct.len()
            ));
        }
        let (fn_id, rt_args): (FuncId, Vec<&Expr>) =
            if !m_decl.params.iter().any(|p| p.is_comptime) {
                self.compiler.check_where_clauses_or_err(
                    &ct_env,
                    &m_decl.where_clauses,
                    &format!("method '{}.{}'", type_name, method_name),
                )?;
                (method_fn_ids[method_name], args.iter().collect())
            } else {
                // Static methods have no receiver to infer from: their comptime arguments are
                // given in brackets or take their defaults.
                let given = match ct_args {
                    Some(ct) => self.eval_ct_args(ct)?,
                    None => Vec::new(),
                };
                let ct_vals = self
                    .compiler
                    .complete_comptime_args_in(
                        &def_mod,
                        method_name,
                        m_decl,
                        &given,
                        &HashMap::default(),
                        &ct_env,
                    )
                    .map_err(|e| {
                        format!(
                            "{e} (pass the comptime arguments of '{type_name}::{method_name}' in brackets, '{type_name}::{method_name}[...](...)')"
                        )
                    })?;
                let mut ct_iter = ct_vals.into_iter();
                let mut args_iter = args.iter();
                let mut ct_args = Vec::new();
                let mut rt_exprs = Vec::new();
                let mut method_env = ct_env.clone();
                for p in &m_decl.params {
                    if p.is_comptime {
                        let val = ct_iter.next().expect("one value per comptime parameter");
                        if let ComptimeVal::Type(arg_ty) = val
                            && let Some(Err(e)) = self.compiler.eval_param_bound(
                                &def_mod,
                                Some(comp_ty),
                                &method_env,
                                &p.ty,
                                arg_ty,
                            )?
                        {
                            return Err(format!(
                                "{} (for parameter '{}' in '{}.{}')",
                                e, p.name, type_name, method_name
                            ));
                        }
                        method_env.insert(p.name.clone(), val.clone());
                        ct_args.push(val);
                    } else if let Some(arg_expr) = args_iter.next() {
                        rt_exprs.push(arg_expr);
                    } else {
                        return Err(format!(
                            "Missing argument '{}' in call to method '{}.{}'",
                            p.name, type_name, method_name
                        ));
                    }
                }
                self.compiler.check_where_clauses_or_err(
                    &method_env,
                    &m_decl.where_clauses,
                    &format!("method '{}.{}'", type_name, method_name),
                )?;
                let key = (comp_ty, method_name.to_string(), ct_args);
                let inst_fn_id = if let Some(&existing_id) =
                    self.compiler.memoized_inherent_methods.get(&key)
                {
                    existing_id
                } else {
                    let new_id =
                        self.compiler
                            .schedule_method(&def_mod, comp_ty, &method_env, m_decl)?;
                    self.compiler.memoized_inherent_methods.insert(key, new_id);
                    new_id
                };
                (inst_fn_id, rt_exprs)
            };
        let (param_tys, ret_ty) = self.compiler.func_sigs[&fn_id].clone();
        if rt_args.len() != param_tys.len() {
            return Err(format!(
                "Method '{}::{}' expects {} arguments, got {}",
                type_name,
                method_name,
                param_tys.len(),
                rt_args.len()
            ));
        }
        let mut lowered_args = Vec::with_capacity(rt_args.len());
        for (i, arg) in rt_args.iter().enumerate() {
            let exp = param_tys.get(i).copied();
            let (op, a_ty) = self.lower_expr(arg, exp)?;
            let coerced = if let Some(pt) = exp {
                self.coerce_operand(op, a_ty, pt)?
            } else {
                op
            };
            lowered_args.push(coerced);
        }
        let dst = self.alloc_temp(ret_ty);
        let next_bb = self.new_block();
        self.check_unsafe_call(Some(fn_id), None, method_name)?;
        self.terminate(Terminator::Call {
            func: Operand::Const(ConstValue::Func(fn_id)),
            args: lowered_args,
            destination: Place::new(dst),
            target: next_bb,
        });
        self.body.cur_block = next_bb;
        if matches!(self.compiler.program.types[ret_ty.0 as usize], Type::Never) {
            self.terminate(Terminator::Unreachable);
        }
        self.last_call_opaque_bound = self.compiler.opaque_ret_funcs.get(&fn_id).cloned();
        Ok((Operand::Move(Place::new(dst)), ret_ty))
    }

    pub(super) fn bound_expr_declares_method(
        &mut self,
        mod_path: &str,
        owner_ty: Option<TypeId>,
        env: &HashMap<String, ComptimeVal>,
        bound_te: &TypeExpr,
        method_name: &str,
    ) -> Result<bool, String> {
        match bound_te {
            TypeExpr::TraitBounds(bounds) => {
                for b in bounds {
                    if self.bound_expr_declares_method(mod_path, owner_ty, env, b, method_name)? {
                        return Ok(true);
                    }
                }
                Ok(false)
            }
            _ => {
                let b_ty = self
                    .compiler
                    .resolve_type_expr(mod_path, owner_ty, env, bound_te)?;
                if let Some(t_info) = self.compiler.traits.get(&b_ty) {
                    Ok(t_info.methods.iter().any(|m| m.name == method_name))
                } else {
                    Ok(false)
                }
            }
        }
    }

    /// Resolves `recv.method(...)` against the traits `comp_ty` implements. Exactly one implemented
    /// trait may declare `method`; otherwise the call must be qualified (`Trait::method(&recv)`).
    fn resolve_trait_method_call(
        &mut self,
        comp_ty: TypeId,
        method_name: &str,
    ) -> Result<Option<FuncId>, String> {
        let mut hits = Vec::new();
        let mut out_of_scope = Vec::new();
        for t in self.compiler.traits_implemented_by(comp_ty)? {
            if let Some(idx) = self.compiler.traits[&t]
                .methods
                .iter()
                .position(|m| m.name == method_name)
            {
                // Only traits in scope in the calling module contribute methods to `x.method()`.
                if self.compiler.trait_in_scope(&self.mod_path, t) {
                    hits.push((t, idx));
                } else {
                    out_of_scope.push(t);
                }
            }
        }
        self.out_of_scope_trait_hint = out_of_scope.first().map(|t| {
            let tr = &self.compiler.traits[t];
            format!(
                "Method '{method_name}' on '{}' is provided by trait '{}', which is not in scope; add 'import {}::{};' or call '{}::{method_name}(&x, ...)'",
                self.compiler.type_display_name(comp_ty),
                tr.name,
                tr.def_module,
                tr.name,
                tr.name
            )
        });
        match hits.as_slice() {
            [] => Ok(None),
            [(t, idx)] => {
                let fn_id = self.compiler.resolve_trait_impl_method(
                    &self.mod_path,
                    comp_ty,
                    *t,
                    *idx,
                    true,
                )?;
                Ok(Some(fn_id))
            }
            [(a, _), (b, _), ..] => Err(format!(
                "Ambiguous method '{method_name}' on '{}': both traits '{}' and '{}' declare it; qualify the call as '{}::{method_name}(&x, ...)'",
                self.compiler.type_display_name(comp_ty),
                self.compiler.traits[a].name,
                self.compiler.traits[b].name,
                self.compiler.traits[a].name
            )),
        }
    }

    /// The implementation for `ty` of a trait method `name` that takes no receiver, if `ty`
    /// implements a trait declaring one. Two such traits make `Type::name` ambiguous.
    fn static_trait_method(&mut self, ty: TypeId, name: &str) -> Result<Option<FuncId>, String> {
        let candidates: Vec<(String, TypeId, usize)> = self
            .compiler
            .traits
            .iter()
            .filter_map(|(&trait_ty, info)| {
                let idx = info.methods.iter().position(|m| {
                    m.name == name && m.params.first().is_none_or(|p| p.name != "self")
                })?;
                Some((info.name.clone(), trait_ty, idx))
            })
            .collect();
        let mut found: Vec<(String, FuncId)> = Vec::new();
        for (trait_name, trait_ty, idx) in candidates {
            let mod_path = self.mod_path.clone();
            if !self.compiler.collect_trait_impls(ty, Some(trait_ty))?.is_empty() {
                let fn_id = self.compiler.resolve_trait_impl_method(&mod_path, ty, trait_ty, idx, false)?;
                found.push((trait_name, fn_id));
            }
        }
        found.sort();
        if let [(first, _), (second, _), ..] = found.as_slice() {
            return Err(format!(
                "'{}::{name}' is ambiguous: traits '{first}' and '{second}' both declare it",
                self.compiler.type_display_name(ty)
            ));
        }
        Ok(found.pop().map(|(_, fn_id)| fn_id))
    }

    /// Calls the receiver-less trait method `fn_id`, whose implementation is known.
    fn lower_static_trait_call(
        &mut self,
        fn_id: FuncId,
        name: &str,
        args: &[Expr],
    ) -> Result<(Operand, TypeId), String> {
        let (arg_tys, ret_ty) = self.compiler.func_sigs[&fn_id].clone();
        if args.len() != arg_tys.len() {
            return Err(format!(
                "Trait method '{name}' expects {} args, found {}",
                arg_tys.len(),
                args.len()
            ));
        }
        let mut lowered = Vec::with_capacity(args.len());
        for (arg, &ty) in args.iter().zip(&arg_tys) {
            let (op, arg_ty) = self.lower_expr(arg, Some(ty))?;
            lowered.push(self.coerce_operand(op, arg_ty, ty)?);
        }
        let dst = self.alloc_temp(ret_ty);
        let next_bb = self.new_block();
        self.check_unsafe_call(Some(fn_id), None, name)?;
        self.terminate(Terminator::Call {
            func: Operand::Const(ConstValue::Func(fn_id)),
            args: lowered,
            destination: Place::new(dst),
            target: next_bb,
        });
        self.body.cur_block = next_bb;
        if matches!(self.compiler.program.types[ret_ty.0 as usize], Type::Never) {
            self.terminate(Terminator::Unreachable);
        }
        Ok((Operand::Move(Place::new(dst)), ret_ty))
    }

    /// Reads arguments that are places (`s.n` in `s.r(s.n)`) into temporaries, so they are read
    /// before the `&mut self` borrow that starts after them, as a call's result already is.
    fn read_args_before_borrow(&mut self, args: &mut [Operand]) {
        for arg in args {
            let (Operand::Copy(place) | Operand::Move(place)) = &*arg else {
                continue;
            };
            let ty = self.place_type(place);
            let tmp = self.alloc_temp(ty);
            let taken = std::mem::replace(arg, Operand::Move(Place::new(tmp)));
            if let Operand::Copy(_) = taken {
                *arg = Operand::Copy(Place::new(tmp));
            }
            self.emit(Statement::Assign(Place::new(tmp), Rvalue::Use(taken)));
        }
    }

    pub(super) fn lower_method_call(
        &mut self,
        receiver: &Expr,
        method_name: &str,
        ct_args: Option<&[Expr]>,
        args: &[Expr],
    ) -> Result<(Operand, TypeId), String> {
        if method_name == "get"
            && ct_args.is_none()
            && args.len() == 1
            && let Some(map_id) = self.compiler.resolve_map_expr(
                &self.mod_path,
                self.owner_ty,
                &self.comptime_env,
                receiver,
            )?
        {
            return self.lower_map_get(map_id, &args[0]);
        }
        // `Type(args)::f(...)` (the parser gives `::` calls a type receiver).
        if let Expr::TypeVal(te) = receiver {
            let comp_ty = self.compiler.resolve_type_expr(
                &self.mod_path,
                self.owner_ty,
                &self.comptime_env,
                te,
            )?;
            return self.lower_static_type_call(comp_ty, method_name, ct_args, args);
        }
        if let Expr::Path(path) = receiver
            && !(path.len() == 1
                && (self.lookup_var(&path[0]).is_some() || self.lookup_capture(&path[0]).is_some()))
        {
            let maybe_ty = if path.len() == 1 && path[0] == "Self" {
                self.owner_ty
            } else if path.len() == 1
                && let Some(ComptimeVal::Type(t)) = self.comptime_env.get(&path[0])
            {
                Some(*t)
            } else if let Ok(ResolvedItem::Type(tmod, tname)) =
                self.compiler.resolve_path(&self.mod_path, path)
            {
                Some(self.compiler.resolve_named_type(&tmod, &tname)?)
            } else {
                None
            };
            if maybe_ty.is_some() {
                let shown = path.join("::");
                return Err(format!(
                    "'{shown}.{method_name}(...)' calls through a type; write '{shown}::{method_name}(...)' ('.' is for values)"
                ));
            }
        }
        if let Some(root_var) = Self::root_var_of_place_expr(receiver)
            && let Some(ob) = self.lookup_var_opaque_bound(root_var)
            && !self.bound_expr_declares_method(
                &ob.bound_mod,
                ob.owner_ty,
                &ob.env,
                &ob.bound_expr,
                method_name,
            )?
        {
            return Err(format!(
                "Cannot call method '{}' on opaque return value '{}': method '{}' is not declared in its trait bound",
                method_name, root_var, method_name
            ));
        }
        let (recv_place, recv_ty) = self.lower_place(receiver, false)?;
        let comp_ty =
            if let Type::Ptr { pointee, .. } = self.compiler.program.types[recv_ty.0 as usize] {
                pointee
            } else {
                recv_ty
            };
        // `recv.f[i](x)`: call an element of field `f` rather than a method `f[T]`.
        if let Some([index]) = ct_args
            && let Some(comp) = self.compiler.composites.get(&comp_ty)
            && !comp.methods.contains_key(method_name)
            && comp.fields.iter().any(|(n, _, _, _)| n == method_name)
        {
            let elem = Expr::Index {
                base: Box::new(Expr::Field {
                    base: Box::new(receiver.clone()),
                    field: method_name.to_string(),
                }),
                index: Box::new(index.clone()),
            };
            return self.lower_call(&elem, None, args);
        }

        // 0. Check dynamic trait object method dispatch (`&MyTrait` / `&mut MyTrait`)
        if let Some(tobj_info) = self.compiler.trait_objs.get(&comp_ty).cloned() {
            if ct_args.is_some() {
                return Err(format!(
                    "Trait object method '{method_name}' takes no comptime arguments"
                ));
            }
            let trait_info = self.compiler.traits[&tobj_info.trait_ty].clone();
            let Some((m_idx, m_decl)) = trait_info
                .methods
                .iter()
                .enumerate()
                .find(|(_, m)| m.name == method_name)
            else {
                return Err(format!(
                    "Trait '{}' has no method '{}'",
                    trait_info.name, method_name
                ));
            };
            let method_needs_mut =
                matches!(&m_decl.params[0].ty, TypeExpr::Ref { mutable: true, .. });
            if method_needs_mut {
                if !tobj_info.mutable {
                    return Err(format!(
                        "Cannot call '&mut Self' method '{}.{}' on shared trait object '&{}'",
                        trait_info.name, method_name, trait_info.name
                    ));
                }
                if recv_ty != comp_ty
                    && matches!(
                        self.compiler.program.types[recv_ty.0 as usize],
                        Type::Ptr { mutable: false, .. }
                    )
                {
                    return Err(format!(
                        "Cannot call '&mut Self' method '{}.{}' through an immutable reference",
                        trait_info.name, method_name
                    ));
                }
            }
            let obj_place = if recv_ty == comp_ty {
                recv_place
            } else {
                let mut dp = recv_place;
                dp.projections.push(Projection::Deref);
                dp
            };
            let fn_ptr_ty = tobj_info.method_fn_ptr_tys[m_idx];
            let Type::FnPtr {
                args: param_tys,
                ret: ret_ty,
            } = self.compiler.program.types[fn_ptr_ty.0 as usize].clone()
            else {
                unreachable!()
            };
            if args.len() + 1 != param_tys.len() {
                return Err(format!(
                    "Method '{}.{}' expects {} arguments, got {}",
                    trait_info.name,
                    method_name,
                    param_tys.len() - 1,
                    args.len()
                ));
            }
            let mut receiver_borrow = None;
            let self_arg = if tobj_info.mutable {
                let mut deref_data = obj_place.clone();
                deref_data.projections.push(Projection::Field(0));
                deref_data.projections.push(Projection::Deref);
                let self_tmp = self.alloc_temp(param_tys[0]);
                let borrow = Statement::Assign(
                    Place::new(self_tmp),
                    Rvalue::Ref {
                        mutable: method_needs_mut,
                        place: deref_data,
                    },
                );
                // As for a method call, a `&mut self` borrow starts after the arguments.
                if method_needs_mut {
                    receiver_borrow = Some(borrow);
                } else {
                    self.emit(borrow);
                }
                Operand::Move(Place::new(self_tmp))
            } else {
                let mut data_field = obj_place.clone();
                data_field.projections.push(Projection::Field(0));
                Operand::Copy(data_field)
            };
            let mut vt_fn_place = obj_place;
            vt_fn_place.projections.push(Projection::Field(1));
            vt_fn_place.projections.push(Projection::Deref);
            vt_fn_place
                .projections
                .push(Projection::Field(m_idx as u32));
            let fn_ptr_tmp = self.alloc_temp(fn_ptr_ty);
            self.emit(Statement::Assign(
                Place::new(fn_ptr_tmp),
                Rvalue::Use(Operand::Copy(vt_fn_place)),
            ));

            let mut lowered_args = Vec::with_capacity(param_tys.len());
            lowered_args.push(self_arg);
            for (i, arg_expr) in args.iter().enumerate() {
                let exp = param_tys.get(i + 1).copied();
                let (op, a_ty) = self.lower_expr(arg_expr, exp)?;
                let coerced = if let Some(pt) = exp {
                    self.coerce_operand(op, a_ty, pt)?
                } else {
                    op
                };
                lowered_args.push(coerced);
            }
            if let Some(borrow) = receiver_borrow {
                self.read_args_before_borrow(&mut lowered_args[1..]);
                self.emit(borrow);
            }
            let dst = self.alloc_temp(ret_ty);
            let next_bb = self.new_block();
            self.check_unsafe_call(None, Some(fn_ptr_ty), method_name)?;
            self.terminate(Terminator::Call {
                func: Operand::Copy(Place::new(fn_ptr_tmp)),
                args: lowered_args,
                destination: Place::new(dst),
                target: next_bb,
            });
            self.body.cur_block = next_bb;
            if matches!(self.compiler.program.types[ret_ty.0 as usize], Type::Never) {
                self.terminate(Terminator::Unreachable);
            }
            return Ok((Operand::Move(Place::new(dst)), ret_ty));
        }

        // 1. Check inherent methods defined inside `struct { ... }` or `opaque { ... }` first
        let mut pre_lowered_rt_args: Option<Vec<(Operand, TypeId)>> = None;
        let inherent_info = if let Some(comp) = self.compiler.composites.get(&comp_ty).cloned() {
            Some((
                comp.name.clone(),
                comp.def_module.clone(),
                comp.comptime_env.clone(),
                comp.methods.clone(),
                comp.method_fn_ids.clone(),
            ))
        } else {
            self.compiler
                .distinct_types
                .get(&comp_ty)
                .cloned()
                .map(|nt| {
                    (
                        nt.name,
                        nt.def_module,
                        nt.comptime_env,
                        std::sync::Arc::new(nt.methods),
                        nt.method_fn_ids,
                    )
                })
        };
        let (fn_id, rt_arg_exprs): (FuncId, Vec<&Expr>) = if let Some((
            type_name,
            def_mod,
            ct_env,
            methods,
            method_fn_ids,
        )) = inherent_info
            && let Some((m_vis, m_decl)) = methods.get(method_name)
        {
            self.check_method_visibility(*m_vis, comp_ty, &def_mod, method_name, &type_name)?;
            if !m_decl.params.iter().any(|p| p.is_comptime) {
                self.compiler.check_where_clauses_or_err(
                    &ct_env,
                    &m_decl.where_clauses,
                    &format!("method '{}.{}'", type_name, method_name),
                )?;
                (method_fn_ids[method_name], args.iter().collect())
            } else {
                let rt_params_after_self: Vec<_> = m_decl
                    .params
                    .iter()
                    .filter(|p| !p.is_comptime)
                    .skip(1)
                    .collect();
                let ct_params: Vec<(String, TypeExpr)> = m_decl
                    .params
                    .iter()
                    .filter(|p| p.is_comptime)
                    .map(|p| (p.name.clone(), p.ty.clone()))
                    .collect();
                let mut ct_vals = Vec::with_capacity(ct_params.len());
                let mut rt_exprs = Vec::new();
                if let Some(explicit) = ct_args {
                    if args.len() != rt_params_after_self.len() {
                        return Err(format!(
                            "Method '{}.{}' expects {} argument(s), got {}",
                            type_name,
                            method_name,
                            rt_params_after_self.len(),
                            args.len()
                        ));
                    }
                    let given = self.eval_ct_args(explicit)?;
                    ct_vals = self.compiler.complete_comptime_args_in(
                        &def_mod,
                        method_name,
                        m_decl,
                        &given,
                        &HashMap::default(),
                        &ct_env,
                    )?;
                    let mut bound_env = ct_env.clone();
                    for ((p_name, bound_te), val) in ct_params.iter().zip(&ct_vals) {
                        if let ComptimeVal::Type(arg_ty) = val
                            && let Some(Err(e)) = self.compiler.eval_param_bound(
                                &def_mod,
                                Some(comp_ty),
                                &bound_env,
                                bound_te,
                                *arg_ty,
                            )?
                        {
                            return Err(format!(
                                "{} (for parameter '{}' in '{}.{}')",
                                e, p_name, type_name, method_name
                            ));
                        }
                        bound_env.insert(p_name.clone(), val.clone());
                    }
                    rt_exprs = args.iter().collect();
                } else if args.len() == rt_params_after_self.len() {
                    let mut lowered = Vec::with_capacity(args.len());
                    for (i, arg_expr) in args.iter().enumerate() {
                        let exp_ty = rt_params_after_self.get(i).and_then(|rp| {
                            self.compiler
                                .resolve_type_expr(&def_mod, Some(comp_ty), &ct_env, &rp.ty)
                                .ok()
                        });
                        lowered.push(self.lower_expr(arg_expr, exp_ty)?);
                    }
                    // Any type, for inference; the bounds are checked once it is done.
                    let unconstrained_ct: Vec<(String, TypeExpr)> = ct_params
                        .iter()
                        .map(|(n, _)| (n.clone(), TypeExpr::Constraint(TypeConstraint::Unchecked)))
                        .collect();
                    let mut inferred = ct_env.clone();
                    for (rt_p, (_, a_ty)) in rt_params_after_self.iter().zip(lowered.iter()) {
                        if self
                            .compiler
                            .unify_type_pattern(
                                &def_mod,
                                &unconstrained_ct,
                                &rt_p.ty,
                                *a_ty,
                                &mut inferred,
                            )?
                            .is_none()
                        {
                            return Err(format!(
                                "Argument type {} does not match parameter '{}' of method '{}.{}'",
                                self.compiler.type_display_name(*a_ty),
                                rt_p.name,
                                type_name,
                                method_name
                            ));
                        }
                    }
                    let completed = self
                        .compiler
                        .complete_comptime_args_in(
                            &def_mod,
                            method_name,
                            m_decl,
                            &[],
                            &inferred,
                            &ct_env,
                        )
                        .map_err(|_| {
                            format!(
                                "Could not infer the comptime arguments of method '{type_name}.{method_name}'; pass them in brackets ('.{method_name}[...](...)')"
                            )
                        })?;
                    for ((p_name, bound_te), val) in ct_params.iter().zip(completed) {
                        if let ComptimeVal::Type(arg_ty) = val
                            && let Some(Err(e)) = self.compiler.eval_param_bound(
                                &def_mod,
                                Some(comp_ty),
                                &inferred,
                                bound_te,
                                arg_ty,
                            )?
                        {
                            return Err(format!(
                                "{} (for parameter '{}' in '{}.{}')",
                                e, p_name, type_name, method_name
                            ));
                        }
                        ct_vals.push(val);
                    }
                    pre_lowered_rt_args = Some(lowered);
                } else {
                    return Err(format!(
                        "Method '{}.{}' expects {} argument(s), got {}",
                        type_name,
                        method_name,
                        rt_params_after_self.len(),
                        args.len()
                    ));
                }
                let mut method_env = ct_env.clone();
                for ((p_name, _), val) in ct_params.iter().zip(ct_vals.iter()) {
                    method_env.insert(p_name.clone(), val.clone());
                }
                self.compiler.check_where_clauses_or_err(
                    &method_env,
                    &m_decl.where_clauses,
                    &format!("method '{}.{}'", type_name, method_name),
                )?;
                let key = (comp_ty, method_name.to_string(), ct_vals.clone());
                let inst_fn_id = if let Some(&existing_id) =
                    self.compiler.memoized_inherent_methods.get(&key)
                {
                    existing_id
                } else {
                    let new_id =
                        self.compiler
                            .schedule_method(&def_mod, comp_ty, &method_env, m_decl)?;
                    self.compiler.memoized_inherent_methods.insert(key, new_id);
                    new_id
                };
                (inst_fn_id, rt_exprs)
            }
        } else if let Some(trait_fn) = self.resolve_trait_method_call(comp_ty, method_name)? {
            // 2. Methods of traits the type implements (`impl Tr { ... }` / `impl Tr for T`)
            if ct_args.is_some() {
                return Err(format!(
                    "Trait method '{method_name}' takes no comptime arguments"
                ));
            }
            (trait_fn, args.iter().collect())
        } else {
            // 3. Fall back to in-scope `self`-receiver extension functions
            let hint = self.out_of_scope_trait_hint.take();
            let (ext_mod, _, ext_decl, inferred) = self
                .compiler
                .resolve_extension_method(&self.mod_path, comp_ty, method_name)
                .map_err(|e| hint.unwrap_or(e))?;
            // Comptime arguments come from the brackets, else from the receiver, else from
            // their defaults.
            let given = match ct_args {
                Some(ct) => self.eval_ct_args(ct)?,
                None => Vec::new(),
            };
            let ct_vals = self
                .compiler
                .complete_comptime_args(&ext_mod, method_name, &ext_decl, &given, &inferred)
                .map_err(|e| {
                    format!(
                        "{e} (extension method '{method_name}': comptime arguments not inferred from the receiver go in brackets, '.{method_name}[...](...)')"
                    )
                })?;
            let mut args_iter = args.iter();
            let mut rt_exprs = Vec::new();
            let mut seen_self = false;
            for p in &ext_decl.params {
                if p.is_comptime {
                    continue;
                }
                if !seen_self {
                    seen_self = true;
                } else if let Some(arg_expr) = args_iter.next() {
                    rt_exprs.push(arg_expr);
                } else {
                    return Err(format!(
                        "Missing argument '{}' in call to extension method '{}'",
                        p.name, method_name
                    ));
                }
            }
            let ext_fn_id = self
                .compiler
                .instantiate_specific_func_decl(&ext_mod, &ext_decl, &ct_vals)?;
            (ext_fn_id, rt_exprs)
        };

        let (param_tys, ret_ty) = self.compiler.func_sigs[&fn_id].clone();
        let self_param_ty = param_tys[0];

        // Automatically borrow or deref `recv_place` to match `self` parameter type (`&Self`, `&mut Self`, `*const Self`, `*mut Self`, or `Self`)
        let mut receiver_borrow = None;
        let self_arg = if let Type::Ptr { mutable, pointee } =
            self.compiler.program.types[self_param_ty.0 as usize]
            && pointee == comp_ty
            && !self.compiler.raw_ptrs.contains_key(&self_param_ty)
        {
            let target_place = if recv_ty == comp_ty {
                recv_place
            } else {
                if self.compiler.raw_ptrs.contains_key(&recv_ty) && self.unsafe_depth == 0 {
                    return Err(format!(
                        "Dereferencing raw pointer of type '{}' to call method '{}' is unsafe and requires an 'unsafe {{ ... }}' block",
                        self.compiler.type_display_name(recv_ty),
                        method_name
                    ));
                }
                let mut deref_p = recv_place;
                deref_p.projections.push(Projection::Deref);
                deref_p
            };
            if let Some((stat_name, true)) = self.static_locals.get(&target_place.local) {
                return Err(format!(
                    "Cannot auto-borrow mutable static '{}' as a safe reference for method '{}'; copy the value to a local or use raw pointers instead",
                    stat_name, method_name
                ));
            }
            if mutable {
                self.check_binding_writable(&target_place, "call a '&mut self' method on")?;
            }
            if mutable && self.place_traverses_immutable_ptr(&target_place) {
                if let Some((stat_name, false)) = self.static_locals.get(&target_place.local) {
                    return Err(format!(
                        "Cannot call '&mut self' method '{}' on immutable static variable '{}'",
                        method_name, stat_name
                    ));
                }
                return Err(format!(
                    "Cannot call '&mut self' method '{}' through an immutable reference or pointer",
                    method_name
                ));
            }
            let ref_tmp = self.alloc_temp(self_param_ty);
            let borrow = Statement::Assign(
                Place::new(ref_tmp),
                Rvalue::Ref {
                    mutable,
                    place: target_place,
                },
            );
            // A `&mut self` borrow starts after the arguments, so they can read the receiver:
            // `v.push(v.len())`. An argument still holding a borrow of it conflicts as usual.
            if mutable {
                receiver_borrow = Some(borrow);
            } else {
                self.emit(borrow);
            }
            Operand::Move(Place::new(ref_tmp))
        } else if recv_ty == self_param_ty {
            if self.is_copy_type(recv_ty) {
                Operand::Copy(recv_place)
            } else {
                Operand::Move(recv_place)
            }
        } else if self.compiler.raw_ptrs.contains_key(&self_param_ty) {
            let op = if self.is_copy_type(recv_ty) {
                Operand::Copy(recv_place)
            } else {
                Operand::Move(recv_place)
            };
            self.coerce_operand(op, recv_ty, self_param_ty)?
        } else {
            return Err(format!(
                "Receiver type '{}' does not match method '{method_name}' self parameter '{}'",
                self.compiler.type_display_name(recv_ty),
                self.compiler.type_display_name(self_param_ty)
            ));
        };

        let mut lowered_args = Vec::with_capacity(param_tys.len());
        lowered_args.push(self_arg);
        if let Some(pre_lowered) = pre_lowered_rt_args {
            for (i, (op, a_ty)) in pre_lowered.into_iter().enumerate() {
                let coerced = if let Some(&pt) = param_tys.get(i + 1) {
                    self.coerce_operand(op, a_ty, pt)?
                } else {
                    op
                };
                lowered_args.push(coerced);
            }
        } else {
            for (i, arg) in rt_arg_exprs.iter().enumerate() {
                let exp = param_tys.get(i + 1).copied();
                let (op, a_ty) = self.lower_expr(arg, exp)?;
                let coerced = if let Some(pt) = exp {
                    self.coerce_operand(op, a_ty, pt)?
                } else {
                    op
                };
                let final_arg = if let Some(pt) = exp
                    && matches!(&coerced, Operand::Const(ConstValue::I64(_)))
                    && matches!(
                        self.compiler.program.types[pt.0 as usize],
                        Type::Int { .. } | Type::Pattern { .. }
                    )
                {
                    let tmp = self.alloc_temp(pt);
                    self.emit(Statement::Assign(Place::new(tmp), Rvalue::Use(coerced)));
                    Operand::Copy(Place::new(tmp))
                } else {
                    coerced
                };
                lowered_args.push(final_arg);
            }
        }
        if let Some(borrow) = receiver_borrow {
            self.read_args_before_borrow(&mut lowered_args[1..]);
            self.emit(borrow);
        }

        let dst = self.alloc_temp(ret_ty);
        let next_bb = self.new_block();
        self.check_unsafe_call(Some(fn_id), None, method_name)?;
        self.terminate(Terminator::Call {
            func: Operand::Const(ConstValue::Func(fn_id)),
            args: lowered_args,
            destination: Place::new(dst),
            target: next_bb,
        });
        self.body.cur_block = next_bb;
        if matches!(self.compiler.program.types[ret_ty.0 as usize], Type::Never) {
            self.terminate(Terminator::Unreachable);
        }
        self.last_call_opaque_bound = self.compiler.opaque_ret_funcs.get(&fn_id).cloned();
        Ok((Operand::Move(Place::new(dst)), ret_ty))
    }
}
