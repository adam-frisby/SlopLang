use super::*;

impl<'a> FuncLowerer<'a> {
    pub(super) fn lower_expr(
        &mut self,
        expr: &Expr,
        expected_ty: Option<TypeId>,
    ) -> Result<(Operand, TypeId), String> {
        match expr {
            Expr::Int(n) => {
                let unwrapped_expected = expected_ty.map(|mut t| {
                    if let Some(&res_info) = self.compiler.results.get(&t) {
                        t = res_info.ok_ty;
                    }
                    if !self.compiler.results.contains_key(&t)
                        && !self.compiler.errors.contains_key(&t)
                        && !self.compiler.unions.contains_key(&t)
                        && let Type::Union { variants, .. } =
                            &self.compiler.program.types[t.0 as usize]
                        && variants.len() == 2
                        && matches!(
                            self.compiler.program.types[variants[0].0 as usize],
                            Type::Void
                        )
                    {
                        variants[1]
                    } else {
                        t
                    }
                });
                if let Some(t) = unwrapped_expected
                    && let Some(nt) = self.compiler.opaque_newtypes.get(&t)
                    && nt.def_module != self.mod_path
                {
                    return Err(format!(
                        "Cannot initialize opaque newtype '{}' directly from an integer literal outside module '{}'; use a constructor or explicit 'as {}' cast",
                        nt.name, nt.def_module, nt.name
                    ));
                }
                if let Some(t) = unwrapped_expected
                    && matches!(
                        self.compiler.program.types[t.0 as usize],
                        Type::F32 | Type::F64
                    )
                {
                    return Ok((
                        Operand::Const(ConstValue::F64((*n as f64).to_bits())),
                        t,
                    ));
                }
                let ty = match unwrapped_expected {
                    Some(t)
                        if matches!(
                            self.compiler.program.types[t.0 as usize],
                            Type::Int { .. } | Type::Pattern { .. }
                        ) =>
                    {
                        if let Type::Pattern { base, .. } =
                            self.compiler.program.types[t.0 as usize]
                        {
                            self.verify_pattern_const(t, *n)?;
                            base
                        } else {
                            t
                        }
                    }
                    _ => self.compiler.intern_type(Type::Int {
                        signed: true,
                        bits: 64,
                    }),
                };
                Ok((Operand::Const(ConstValue::I64(*n)), ty))
            }
            Expr::Float(bits) => {
                if let Some(t) = expected_ty
                    && let Some(nt) = self.compiler.opaque_newtypes.get(&t)
                    && nt.def_module != self.mod_path
                {
                    return Err(format!(
                        "Cannot initialize opaque newtype '{}' directly from a float literal outside module '{}'; use a constructor or explicit 'as {}' cast",
                        nt.name, nt.def_module, nt.name
                    ));
                }
                let ty = match expected_ty {
                    Some(t)
                        if matches!(
                            self.compiler.program.types[t.0 as usize],
                            Type::F32 | Type::F64
                        ) =>
                    {
                        t
                    }
                    _ => self.compiler.intern_type(Type::F64),
                };
                Ok((Operand::Const(ConstValue::F64(*bits)), ty))
            }
            Expr::Bool(b) => {
                let ty = self.compiler.intern_type(Type::Bool);
                Ok((Operand::Const(ConstValue::Bool(*b)), ty))
            }
            Expr::Rune(ch) => {
                let ty = self.compiler.intern_type(Type::Rune);
                let tmp = self.alloc_temp(ty);
                self.emit(Statement::Assign(
                    Place::new(tmp),
                    Rvalue::Use(Operand::Const(ConstValue::I64(u32::from(*ch) as i128))),
                ));
                Ok((Operand::Copy(Place::new(tmp)), ty))
            }
            Expr::Str(s) => {
                let u8_ty = self.compiler.intern_type(Type::Int {
                    signed: false,
                    bits: 8,
                });
                let ptr_ty = self.compiler.intern_type(Type::Ptr {
                    mutable: false,
                    pointee: u8_ty,
                });
                Ok((Operand::Const(ConstValue::Str(s.clone())), ptr_ty))
            }
            Expr::Null => {
                let opt_ty = expected_ty
                    .ok_or_else(|| "`null` requires a known optional `?T` type context".to_string())?;
                let tmp = self.alloc_temp(opt_ty);
                self.emit(Statement::Assign(
                    Place::new(tmp),
                    Rvalue::Union {
                        ty: opt_ty,
                        variant: 0,
                        payload: Operand::Const(ConstValue::Void),
                    },
                ));
                Ok((Operand::Move(Place::new(tmp)), opt_ty))
            }
            Expr::TypeVal(te) => {
                let t_id = self.compiler.resolve_type_expr(
                    &self.mod_path,
                    self.owner_ty,
                    &self.comptime_env,
                    te,
                )?;
                let meta_ty = self.compiler.intern_type(Type::MetaType);
                Ok((Operand::Const(ConstValue::Type(t_id)), meta_ty))
            }
            Expr::Path(p) => {
                if p.len() == 1 {
                    if let Some((local, ty)) = self.lookup_var(&p[0]) {
                        let op = if self.is_copy_type(ty) {
                            Operand::Copy(Place::new(local))
                        } else {
                            Operand::Move(Place::new(local))
                        };
                        return Ok((op, ty));
                    }
                    if let Some((cap_place, ty)) = self.lookup_capture(&p[0]) {
                        let op = if self.is_copy_type(ty) {
                            Operand::Copy(cap_place)
                        } else {
                            Operand::Move(cap_place)
                        };
                        return Ok((op, ty));
                    }
                    if let Some(ComptimeVal::Int(n)) = self.comptime_env.get(&p[0]).cloned() {
                        let ty = expected_ty.unwrap_or_else(|| {
                            self.compiler.intern_type(Type::Int {
                                signed: true,
                                bits: 64,
                            })
                        });
                        return Ok((Operand::Const(ConstValue::I64(n)), ty));
                    }
                    if let Some(ComptimeVal::Bool(b)) = self.comptime_env.get(&p[0]).cloned() {
                        let ty = self.compiler.intern_type(Type::Bool);
                        return Ok((Operand::Const(ConstValue::Bool(b)), ty));
                    }
                } else if p.len() >= 2 {
                    let type_prefix = &p[..p.len() - 1];
                    let vname = p.last().unwrap();
                    let enum_ty_opt = if type_prefix.len() == 1
                        && let Some(ComptimeVal::Type(t_id)) = self.comptime_env.get(&type_prefix[0])
                    {
                        Some(*t_id)
                    } else if let Ok(ResolvedItem::Type(tmod, tname)) =
                        self.compiler.resolve_path(&self.mod_path, type_prefix)
                    {
                        Some(self.compiler.resolve_named_type(&tmod, &tname)?)
                    } else {
                        None
                    };
                    if let Some(enum_ty) = enum_ty_opt {
                        if let Some((_, variants)) = self.compiler.enums.get(&enum_ty)
                            && let Some((_, val)) = variants.iter().find(|(vn, _)| vn == vname)
                        {
                            return Ok((Operand::Const(ConstValue::I64(*val)), enum_ty));
                        }
                        if let Some(err_info) = self.compiler.errors.get(&enum_ty).cloned() {
                            let found = err_info
                                .leaves
                                .iter()
                                .enumerate()
                                .find(|(_, l)| {
                                    l.key.error_name == err_info.name
                                        && l.key.variant_name == *vname
                                })
                                .or_else(|| {
                                    err_info
                                        .leaves
                                        .iter()
                                        .enumerate()
                                        .find(|(_, l)| l.key.variant_name == *vname)
                                });
                            if let Some((v_idx, leaf)) = found {
                                if !matches!(
                                    self.compiler.program.types[leaf.payload_ty.0 as usize],
                                    Type::Void
                                ) {
                                    return Err(format!(
                                        "Error variant '{}::{}' carries a payload and must be constructed with arguments",
                                        err_info.name, vname
                                    ));
                                }
                                let tmp = self.alloc_temp(enum_ty);
                                self.emit(Statement::Assign(
                                    Place::new(tmp),
                                    Rvalue::Union {
                                        ty: enum_ty,
                                        variant: v_idx as u32,
                                        payload: Operand::Const(ConstValue::Void),
                                    },
                                ));
                                let op = if self.is_copy_type(enum_ty) {
                                    Operand::Copy(Place::new(tmp))
                                } else {
                                    Operand::Move(Place::new(tmp))
                                };
                                return Ok((op, enum_ty));
                            }
                        }
                        if let Some(union_info) = self.compiler.unions.get(&enum_ty).cloned()
                            && let Some((v_idx, (_, payload_ty))) = union_info
                                .variants
                                .iter()
                                .enumerate()
                                .find(|(_, (vn, _))| vn == vname)
                        {
                            if !matches!(
                                self.compiler.program.types[payload_ty.0 as usize],
                                Type::Void
                            ) {
                                return Err(format!(
                                    "Union variant '{}::{}' carries a payload and must be constructed with arguments",
                                    union_info.name, vname
                                ));
                            }
                            let tmp = self.alloc_temp(enum_ty);
                            self.emit(Statement::Assign(
                                Place::new(tmp),
                                Rvalue::Union {
                                    ty: enum_ty,
                                    variant: v_idx as u32,
                                    payload: Operand::Const(ConstValue::Void),
                                },
                            ));
                            let op = if self.is_copy_type(enum_ty) {
                                Operand::Copy(Place::new(tmp))
                            } else {
                                Operand::Move(Place::new(tmp))
                            };
                            return Ok((op, enum_ty));
                        }
                    }
                }
                if let Some(res) = self.try_resolve_const_or_static_path(p, expected_ty)? {
                    match res {
                        Ok((cval, cty)) => {
                            let op = match &cval {
                                ConstValue::Aggregate(_) => {
                                    let tmp = self.alloc_temp(cty);
                                    self.emit(Statement::Assign(
                                        Place::new(tmp),
                                        Rvalue::Use(Operand::Const(cval)),
                                    ));
                                    if self.is_copy_type(cty) {
                                        Operand::Copy(Place::new(tmp))
                                    } else {
                                        Operand::Move(Place::new(tmp))
                                    }
                                }
                                _ => Operand::Const(cval),
                            };
                            return Ok((op, cty));
                        }
                        Err((gl_id, sty, is_mut, disp)) => {
                            let (place, ty) =
                                self.materialize_static_place(gl_id, sty, is_mut, &disp, false)?;
                            if !self.is_copy_type(ty) {
                                return Err(format!(
                                    "Cannot move non-copy value of type '{}' out of static variable '{}'",
                                    self.compiler.type_display_name(ty),
                                    disp
                                ));
                            }
                            return Ok((Operand::Copy(place), ty));
                        }
                    }
                }
                if let Ok(ResolvedItem::Func(fmod, fname)) =
                    self.compiler.resolve_path(&self.mod_path, p)
                {
                    let fn_id = self.compiler.get_or_instantiate_func(&fmod, &fname, &[])?;
                    let (args, ret) = self.compiler.func_sigs[&fn_id].clone();
                    let fn_ptr_ty = self.compiler.intern_type(Type::FnPtr { args, ret });
                    return Ok((Operand::Const(ConstValue::Func(fn_id)), fn_ptr_ty));
                }
                Err(format!("Cannot resolve value path '{}'", p.join("::")))
            }
            Expr::Move(inner) => {
                if let Expr::Field { base, .. } = inner.as_ref() {
                    let (_, mut base_ty) = self.lower_place(base, true)?;
                    if let Type::Ptr { pointee, .. } =
                        self.compiler.program.types[base_ty.0 as usize]
                    {
                        base_ty = pointee;
                    }
                    if let Some(comp) = self.compiler.composites.get(&base_ty)
                        && comp.is_struct
                    {
                        return Err(format!(
                            "Cannot partially move field out of struct '{}'; only 'record' and 'tuple' allow partial moves",
                            comp.name
                        ));
                    }
                }
                let (place, ty) = self.lower_place(inner, true)?;
                if let Some((stat_name, _)) = self.static_locals.get(&place.local) {
                    return Err(format!(
                        "Cannot move out of static variable '{}'",
                        stat_name
                    ));
                }
                if self.place_traverses_safe_ref(&place) {
                    return Err(format!(
                        "Cannot move out of dereferenced safe reference '{}'",
                        place
                    ));
                }
                Ok((Operand::Move(place), ty))
            }
            Expr::Field { .. } | Expr::TupleIndex { .. } | Expr::Index { .. } | Expr::Deref(_) => {
                let want_mut = matches!(expr, Expr::Field { .. })
                    && expected_ty.is_some_and(|t| {
                        matches!(
                            self.compiler.program.types[t.0 as usize],
                            Type::Ptr { mutable: true, .. }
                        ) || self
                            .compiler
                            .slices
                            .get(&t)
                            .is_some_and(|info| info.mutable)
                            || self
                                .compiler
                                .trait_objs
                                .get(&t)
                                .is_some_and(|info| info.mutable)
                    });
                let (place, ty) = self.lower_place(expr, want_mut)?;
                let op = if self.is_copy_type(ty) {
                    Operand::Copy(place)
                } else if let Some(exp_ty) = expected_ty
                    && let (
                        Type::Ptr {
                            mutable: true,
                            pointee: src_pt,
                        },
                        Type::Ptr {
                            mutable: dst_mut,
                            pointee: dst_pt,
                        },
                    ) = (
                        self.compiler.program.types[ty.0 as usize].clone(),
                        self.compiler.program.types[exp_ty.0 as usize].clone(),
                    )
                    && (src_pt == dst_pt || self.compiler.is_universal_opaque_type(dst_pt))
                    && !self.compiler.raw_ptrs.contains_key(&ty)
                    && !self.compiler.raw_ptrs.contains_key(&exp_ty)
                {
                    if dst_mut && self.place_traverses_immutable_ptr(&place) {
                        return Err(format!(
                            "Cannot mutably reborrow '{}' through an immutable reference",
                            place
                        ));
                    }
                    let mut deref_p = place;
                    deref_p.projections.push(Projection::Deref);
                    let tmp = self.alloc_temp(exp_ty);
                    self.emit(Statement::Assign(
                        Place::new(tmp),
                        Rvalue::Ref {
                            mutable: dst_mut,
                            place: deref_p,
                        },
                    ));
                    return Ok((Operand::Move(Place::new(tmp)), exp_ty));
                } else {
                    if let Some((stat_name, _)) = self.static_locals.get(&place.local) {
                        return Err(format!(
                            "Cannot move non-copy value out of static variable '{}'",
                            stat_name
                        ));
                    }
                    if self.place_traverses_safe_ref(&place) {
                        return Err(format!(
                            "Cannot move out of dereferenced safe reference '{}'",
                            place
                        ));
                    }
                    Operand::Move(place)
                };
                Ok((op, ty))
            }
            Expr::RelRef(_) => Err(
                "'&rel' expressions are only permitted when initializing or assigning a '&rel' struct field"
                    .to_string(),
            ),
            Expr::Ref { mutable, expr: inner } => {
                if let Expr::Slice { base, start, end } = inner.as_ref() {
                    return self.lower_slice(base, start, end, Some(*mutable), expected_ty);
                }
                let (place, inner_ty) = self.lower_place(inner, *mutable)?;
                if let Some((stat_name, true)) = self.static_locals.get(&place.local) {
                    return Err(format!(
                        "Taking a safe reference ('&' or '&mut') to mutable static '{}' is forbidden; use '&raw const' or '&raw mut' instead",
                        stat_name
                    ));
                }
                if *mutable && self.place_traverses_immutable_ptr(&place) {
                    if let Some((stat_name, false)) = self.static_locals.get(&place.local) {
                        return Err(format!(
                            "Cannot take mutable reference '&mut' to immutable static variable '{}'",
                            stat_name
                        ));
                    }
                    return Err(format!(
                        "Cannot take mutable reference '&mut' to '{}' through an immutable reference or pointer",
                        place
                    ));
                }
                let ref_ty = self.compiler.intern_type(Type::Ptr {
                    mutable: *mutable,
                    pointee: inner_ty,
                });
                let tmp = self.alloc_temp(ref_ty);
                self.emit(Statement::Assign(
                    Place::new(tmp),
                    Rvalue::Ref {
                        mutable: *mutable,
                        place,
                    },
                ));
                Ok((Operand::Copy(Place::new(tmp)), ref_ty))
            }
            Expr::RawPtr { mutable, expr: inner } => {
                self.raw_addr_of_depth += 1;
                let place_res = self.lower_place(inner, *mutable);
                self.raw_addr_of_depth -= 1;
                let (place, inner_ty) = place_res?;
                if *mutable && self.place_traverses_immutable_ptr(&place) {
                    if let Some((stat_name, false)) = self.static_locals.get(&place.local) {
                        return Err(format!(
                            "Cannot take mutable raw pointer '&raw mut' to immutable static variable '{}'",
                            stat_name
                        ));
                    }
                    return Err(format!(
                        "Cannot take mutable raw pointer '&raw mut' to '{}' through an immutable reference or pointer",
                        place
                    ));
                }
                let raw_ptr_ty = self.compiler.intern_raw_ptr_type(*mutable, inner_ty);
                let tmp = self.alloc_temp(raw_ptr_ty);
                self.emit(Statement::Assign(
                    Place::new(tmp),
                    Rvalue::Ref {
                        mutable: *mutable,
                        place,
                    },
                ));
                Ok((Operand::Copy(Place::new(tmp)), raw_ptr_ty))
            }
            Expr::Slice { base, start, end } => {
                self.lower_slice(base, start, end, None, expected_ty)
            }
            Expr::Unary { op, expr: inner } => {
                let (inner_op, ty) = self.lower_expr(inner, expected_ty)?;
                let tmp = self.alloc_temp(ty);
                self.emit(Statement::Assign(
                    Place::new(tmp),
                    Rvalue::UnaryOp(*op, inner_op),
                ));
                Ok((Operand::Copy(Place::new(tmp)), ty))
            }
            Expr::Binary { op, lhs, rhs } => {
                let (l_op, l_ty, r_op, r_ty) = if expected_ty.is_none()
                    && matches!(lhs.as_ref(), Expr::Int(_) | Expr::Float(_))
                    && !matches!(rhs.as_ref(), Expr::Int(_) | Expr::Float(_))
                {
                    let (r_op, r_ty) = self.lower_expr(rhs, None)?;
                    let (l_op, l_ty) = self.lower_expr(lhs, Some(r_ty))?;
                    (l_op, l_ty, r_op, r_ty)
                } else {
                    let (l_op, l_ty) = self.lower_expr(lhs, expected_ty)?;
                    let rhs_exp = if matches!(
                        self.compiler.program.types[l_ty.0 as usize],
                        Type::Ptr { .. }
                    ) {
                        Some(self.compiler.intern_type(Type::Int {
                            signed: true,
                            bits: 64,
                        }))
                    } else {
                        Some(l_ty)
                    };
                    let (r_op, r_ty) = self.lower_expr(rhs, rhs_exp)?;
                    (l_op, l_ty, r_op, r_ty)
                };
                if let Type::Ptr { pointee, .. } = self.compiler.program.types[l_ty.0 as usize] {
                    if self.compiler.is_opaque_type(pointee)
                        && matches!(op, BinOp::Add | BinOp::AddWrap | BinOp::Sub | BinOp::SubWrap)
                    {
                        return Err(format!(
                            "Cannot perform element-scaled pointer arithmetic on '{}'; cast to '*const u8' or '*mut u8' for byte offsets",
                            self.compiler.type_display_name(l_ty)
                        ));
                    }
                } else {
                    if let Some(nt) = self.compiler.opaque_newtypes.get(&l_ty)
                        && nt.def_module != self.mod_path
                    {
                        return Err(format!(
                            "Cannot perform binary operator '{}' directly on opaque newtype '{}' outside module '{}'",
                            op, nt.name, nt.def_module
                        ));
                    }
                    if let Some(nt) = self.compiler.opaque_newtypes.get(&r_ty)
                        && nt.def_module != self.mod_path
                    {
                        return Err(format!(
                            "Cannot perform binary operator '{}' directly on opaque newtype '{}' outside module '{}'",
                            op, nt.name, nt.def_module
                        ));
                    }
                    if r_ty != l_ty
                        && (self.compiler.c_ints.contains_key(&l_ty)
                            || self.compiler.c_ints.contains_key(&r_ty))
                    {
                        return Err(format!(
                            "Type mismatch in binary operation '{}': cannot mix '{}' and '{}' without an explicit 'as' cast",
                            op,
                            self.compiler.type_display_name(l_ty),
                            self.compiler.type_display_name(r_ty)
                        ));
                    }
                    if r_ty != l_ty
                        && let (Some(l_nt), Some(r_nt)) = (
                            self.compiler.opaque_newtypes.get(&l_ty),
                            self.compiler.opaque_newtypes.get(&r_ty),
                        )
                    {
                        return Err(format!(
                            "Type mismatch in binary operation '{}': cannot mix distinct opaque newtypes '{}' and '{}'",
                            op, l_nt.name, r_nt.name
                        ));
                    }
                }
                let res_ty = match op {
                    BinOp::Eq
                    | BinOp::Ne
                    | BinOp::Lt
                    | BinOp::Le
                    | BinOp::Gt
                    | BinOp::Ge => self.compiler.intern_type(Type::Bool),
                    _ => l_ty,
                };
                let tmp = self.alloc_temp(res_ty);
                self.emit(Statement::Assign(
                    Place::new(tmp),
                    Rvalue::BinaryOp(*op, l_op, r_op),
                ));
                Ok((Operand::Copy(Place::new(tmp)), res_ty))
            }
            Expr::LogicalAnd(lhs, rhs) => {
                let bool_ty = self.compiler.intern_type(Type::Bool);
                let res_local = self.alloc_temp(bool_ty);
                let (l_op, _) = self.lower_expr(lhs, Some(bool_ty))?;
                let rhs_bb = self.new_block();
                let short_bb = self.new_block();
                let join_bb = self.new_block();
                self.terminate(Terminator::SwitchInt {
                    discr: l_op,
                    targets: vec![(1, rhs_bb)],
                    otherwise: short_bb,
                });

                self.cur_block = short_bb;
                self.emit(Statement::Assign(
                    Place::new(res_local),
                    Rvalue::Use(Operand::Const(ConstValue::Bool(false))),
                ));
                self.terminate(Terminator::Goto { target: join_bb });

                self.cur_block = rhs_bb;
                let (r_op, _) = self.lower_expr(rhs, Some(bool_ty))?;
                self.emit(Statement::Assign(Place::new(res_local), Rvalue::Use(r_op)));
                self.terminate(Terminator::Goto { target: join_bb });

                self.cur_block = join_bb;
                Ok((Operand::Copy(Place::new(res_local)), bool_ty))
            }
            Expr::LogicalOr(lhs, rhs) => {
                let bool_ty = self.compiler.intern_type(Type::Bool);
                let res_local = self.alloc_temp(bool_ty);
                let (l_op, _) = self.lower_expr(lhs, Some(bool_ty))?;
                let rhs_bb = self.new_block();
                let short_bb = self.new_block();
                let join_bb = self.new_block();
                self.terminate(Terminator::SwitchInt {
                    discr: l_op,
                    targets: vec![(1, short_bb)],
                    otherwise: rhs_bb,
                });

                self.cur_block = short_bb;
                self.emit(Statement::Assign(
                    Place::new(res_local),
                    Rvalue::Use(Operand::Const(ConstValue::Bool(true))),
                ));
                self.terminate(Terminator::Goto { target: join_bb });

                self.cur_block = rhs_bb;
                let (r_op, _) = self.lower_expr(rhs, Some(bool_ty))?;
                self.emit(Statement::Assign(Place::new(res_local), Rvalue::Use(r_op)));
                self.terminate(Terminator::Goto { target: join_bb });

                self.cur_block = join_bb;
                Ok((Operand::Copy(Place::new(res_local)), bool_ty))
            }
            Expr::Cast { expr: inner, ty } => {
                let target_ty = self.compiler.resolve_type_expr(
                    &self.mod_path,
                    self.owner_ty,
                    &self.comptime_env,
                    ty,
                )?;
                if self.compiler.is_opaque_type(target_ty) {
                    return Err(
                        "Cannot cast a value to unsized type 'opaque' by value; cast to '*const opaque' or '*mut opaque' instead"
                            .to_string(),
                    );
                }
                let (op, src_ty) = self.lower_expr(inner, None)?;
                if let Operand::Const(ConstValue::I64(n)) = &op {
                    self.verify_pattern_const(target_ty, *n)?;
                }
                let src_place_op = if matches!(op, Operand::Const(_)) {
                    let src_tmp = self.alloc_temp(src_ty);
                    self.emit(Statement::Assign(Place::new(src_tmp), Rvalue::Use(op)));
                    Operand::Copy(Place::new(src_tmp))
                } else {
                    op
                };
                let dst_tmp = self.alloc_temp(target_ty);
                self.emit(Statement::Assign(
                    Place::new(dst_tmp),
                    Rvalue::Cast(src_place_op, target_ty),
                ));
                Ok((Operand::Copy(Place::new(dst_tmp)), target_ty))
            }
            Expr::OrElse { opt, fallback } => {
                let (opt_op, opt_ty) = self.lower_expr(opt, None)?;
                let Type::Union { tag, variants } =
                    self.compiler.program.types[opt_ty.0 as usize].clone()
                else {
                    return Err("`orelse` requires an optional `?T` left-hand side".to_string());
                };
                let payload_ty = variants[1];
                let opt_local = self.alloc_temp(opt_ty);
                self.emit(Statement::Assign(
                    Place::new(opt_local),
                    Rvalue::Use(opt_op),
                ));
                let discr_local = self.alloc_temp(tag);
                self.emit(Statement::Assign(
                    Place::new(discr_local),
                    Rvalue::Discriminant(Place::new(opt_local)),
                ));

                let res_local = self.alloc_temp(payload_ty);
                let some_bb = self.new_block();
                let none_bb = self.new_block();
                let join_bb = self.new_block();
                self.terminate(Terminator::SwitchInt {
                    discr: Operand::Copy(Place::new(discr_local)),
                    targets: vec![(1, some_bb)],
                    otherwise: none_bb,
                });

                self.cur_block = some_bb;
                let mut payload_place = Place::new(opt_local);
                payload_place.projections.push(Projection::Variant(1));
                let p_op = if self.is_copy_type(payload_ty) {
                    Operand::Copy(payload_place)
                } else {
                    Operand::Move(payload_place)
                };
                self.emit(Statement::Assign(Place::new(res_local), Rvalue::Use(p_op)));
                self.terminate(Terminator::Goto { target: join_bb });

                self.cur_block = none_bb;
                let (fb_op, fb_ty) = self.lower_expr(fallback, Some(payload_ty))?;
                if !self.is_terminated() {
                    let coerced = self.coerce_operand(fb_op, fb_ty, payload_ty)?;
                    self.emit(Statement::Assign(Place::new(res_local), Rvalue::Use(coerced)));
                    self.terminate(Terminator::Goto { target: join_bb });
                }

                self.cur_block = join_bb;
                Ok((Operand::Move(Place::new(res_local)), payload_ty))
            }
            Expr::Try(inner) => {
                let (res_op, res_ty) = self.lower_expr(inner, None)?;
                let Some(&src_res) = self.compiler.results.get(&res_ty) else {
                    return Err("`try` requires a fallible `E!T` result expression".to_string());
                };
                let ret_ty = self.locals[0];
                let Some(&fn_res) = self.compiler.results.get(&ret_ty) else {
                    return Err(format!(
                        "`try` can only be used inside a function returning a fallible `E!T` result (function '{}' returns {})",
                        self.decl.name,
                        self.compiler.program.types[ret_ty.0 as usize]
                    ));
                };
                let u8_ty = self.compiler.intern_type(Type::Int {
                    signed: false,
                    bits: 8,
                });
                let res_local = self.alloc_temp(res_ty);
                self.emit(Statement::Assign(Place::new(res_local), Rvalue::Use(res_op)));
                let discr_local = self.alloc_temp(u8_ty);
                self.emit(Statement::Assign(
                    Place::new(discr_local),
                    Rvalue::Discriminant(Place::new(res_local)),
                ));

                let ok_bb = self.new_block();
                let err_bb = self.new_block();
                self.terminate(Terminator::SwitchInt {
                    discr: Operand::Copy(Place::new(discr_local)),
                    targets: vec![(0, ok_bb)],
                    otherwise: err_bb,
                });

                self.cur_block = err_bb;
                let mut err_place = Place::new(res_local);
                err_place.projections.push(Projection::Variant(1));
                let err_op = if self.is_copy_type(src_res.err_ty) {
                    Operand::Copy(err_place)
                } else {
                    Operand::Move(err_place)
                };
                let widened_err =
                    self.widen_error_operand(err_op, src_res.err_ty, fn_res.err_ty)?;
                self.emit(Statement::Assign(
                    Place::new(LocalId(0)),
                    Rvalue::Union {
                        ty: ret_ty,
                        variant: 1,
                        payload: widened_err,
                    },
                ));
                self.cleanup_all_scopes();
                self.terminate(Terminator::Return);

                self.cur_block = ok_bb;
                if matches!(
                    self.compiler.program.types[src_res.ok_ty.0 as usize],
                    Type::Void
                ) {
                    return Ok((Operand::Const(ConstValue::Void), src_res.ok_ty));
                }
                let mut ok_place = Place::new(res_local);
                ok_place.projections.push(Projection::Variant(0));
                let ok_op = if self.is_copy_type(src_res.ok_ty) {
                    Operand::Copy(ok_place)
                } else {
                    Operand::Move(ok_place)
                };
                let ok_local = self.alloc_temp(src_res.ok_ty);
                self.emit(Statement::Assign(Place::new(ok_local), Rvalue::Use(ok_op)));
                let out_op = if self.is_copy_type(src_res.ok_ty) {
                    Operand::Copy(Place::new(ok_local))
                } else {
                    Operand::Move(Place::new(ok_local))
                };
                Ok((out_op, src_res.ok_ty))
            }
            Expr::Catch {
                expr: inner,
                err_binding,
                fallback,
            } => {
                let (res_op, res_ty) = self.lower_expr(inner, None)?;
                let Some(&src_res) = self.compiler.results.get(&res_ty) else {
                    return Err("`catch` requires a fallible `E!T` left-hand side".to_string());
                };
                let ok_ty = src_res.ok_ty;
                let err_ty = src_res.err_ty;
                let u8_ty = self.compiler.intern_type(Type::Int {
                    signed: false,
                    bits: 8,
                });
                let res_local = self.alloc_temp(res_ty);
                self.emit(Statement::Assign(Place::new(res_local), Rvalue::Use(res_op)));
                let discr_local = self.alloc_temp(u8_ty);
                self.emit(Statement::Assign(
                    Place::new(discr_local),
                    Rvalue::Discriminant(Place::new(res_local)),
                ));

                let out_local = self.alloc_temp(ok_ty);
                let ok_bb = self.new_block();
                let err_bb = self.new_block();
                let join_bb = self.new_block();
                self.terminate(Terminator::SwitchInt {
                    discr: Operand::Copy(Place::new(discr_local)),
                    targets: vec![(0, ok_bb)],
                    otherwise: err_bb,
                });

                self.cur_block = ok_bb;
                if matches!(self.compiler.program.types[ok_ty.0 as usize], Type::Void) {
                    self.emit(Statement::Assign(
                        Place::new(out_local),
                        Rvalue::Use(Operand::Const(ConstValue::Void)),
                    ));
                } else {
                    let mut ok_place = Place::new(res_local);
                    ok_place.projections.push(Projection::Variant(0));
                    let ok_op = if self.is_copy_type(ok_ty) {
                        Operand::Copy(ok_place)
                    } else {
                        Operand::Move(ok_place)
                    };
                    self.emit(Statement::Assign(Place::new(out_local), Rvalue::Use(ok_op)));
                }
                self.terminate(Terminator::Goto { target: join_bb });

                self.cur_block = err_bb;
                self.scopes.push(Vec::new());
                if let Some(b_name) = err_binding
                    && b_name != "_"
                {
                    let err_var = self.alloc_temp(err_ty);
                    self.emit(Statement::StorageLive(err_var));
                    let mut err_place = Place::new(res_local);
                    err_place.projections.push(Projection::Variant(1));
                    let err_op = if self.is_copy_type(err_ty) {
                        Operand::Copy(err_place)
                    } else {
                        Operand::Move(err_place)
                    };
                    self.emit(Statement::Assign(Place::new(err_var), Rvalue::Use(err_op)));
                    self.scopes.last_mut().unwrap().push(ScopeVar {
                        name: b_name.clone(),
                        local: err_var,
                        ty: err_ty,
                        opaque_bound: None,
                    });
                }
                let (fb_op, fb_ty) = self.lower_expr(fallback, Some(ok_ty))?;
                if !self.is_terminated() {
                    let coerced = self.coerce_operand(fb_op, fb_ty, ok_ty)?;
                    self.emit(Statement::Assign(
                        Place::new(out_local),
                        Rvalue::Use(coerced),
                    ));
                    self.cleanup_top_scope();
                    self.terminate(Terminator::Goto { target: join_bb });
                }
                self.scopes.pop();

                self.cur_block = join_bb;
                let out_op = if self.is_copy_type(ok_ty) {
                    Operand::Copy(Place::new(out_local))
                } else {
                    Operand::Move(Place::new(out_local))
                };
                Ok((out_op, ok_ty))
            }
            Expr::Match { scrutinee, arms } => {
                self.lower_match(scrutinee, arms, expected_ty, false)
            }
            Expr::Block(blk) => {
                let void_ty = self.compiler.intern_type(Type::Void);
                let never_ty = self.compiler.intern_type(Type::Never);
                if expected_ty != Some(void_ty)
                    && let Some(Stmt::Expr(tail_expr)) = blk.stmts.last()
                {
                    self.scopes.push(Vec::new());
                    for s in &blk.stmts[..blk.stmts.len() - 1] {
                        if self.is_terminated() {
                            break;
                        }
                        self.lower_stmt(s)?;
                    }
                    if self.is_terminated() {
                        self.scopes.pop();
                        return Ok((Operand::Const(ConstValue::Void), never_ty));
                    }
                    let (tail_op, tail_ty) = self.lower_expr(tail_expr, expected_ty)?;
                    if self.is_terminated() {
                        self.scopes.pop();
                        return Ok((Operand::Const(ConstValue::Void), never_ty));
                    }
                    if matches!(self.compiler.program.types[tail_ty.0 as usize], Type::Void) {
                        self.cleanup_top_scope();
                        self.scopes.pop();
                        return Ok((Operand::Const(ConstValue::Void), void_ty));
                    }
                    let res_local = self.alloc_temp(tail_ty);
                    self.emit(Statement::Assign(Place::new(res_local), Rvalue::Use(tail_op)));
                    self.cleanup_top_scope();
                    self.scopes.pop();
                    let out_op = if self.is_copy_type(tail_ty) {
                        Operand::Copy(Place::new(res_local))
                    } else {
                        Operand::Move(Place::new(res_local))
                    };
                    Ok((out_op, tail_ty))
                } else {
                    self.lower_scoped_block(blk)?;
                    if self.is_terminated() {
                        Ok((Operand::Const(ConstValue::Void), never_ty))
                    } else {
                        Ok((Operand::Const(ConstValue::Void), void_ty))
                    }
                }
            }
            Expr::TupleLit(elems) => {
                if let Some(t) = expected_ty
                    && let Type::Array { elem, len } = self.compiler.program.types[t.0 as usize]
                    && elems.len() == len as usize
                {
                    let mut ops = Vec::with_capacity(elems.len());
                    for e in elems {
                        let (op, ety) = self.lower_expr(e, Some(elem))?;
                        let coerced = self.coerce_operand(op, ety, elem)?;
                        ops.push(coerced);
                    }
                    let tmp = self.alloc_temp(t);
                    self.emit(Statement::Assign(
                        Place::new(tmp),
                        Rvalue::Aggregate(t, ops),
                    ));
                    let res_op = if self.is_copy_type(t) {
                        Operand::Copy(Place::new(tmp))
                    } else {
                        Operand::Move(Place::new(tmp))
                    };
                    return Ok((res_op, t));
                }
                let expected_fields = if let Some(t) = expected_ty
                    && let Type::Struct(ftys) = &self.compiler.program.types[t.0 as usize]
                {
                    Some(ftys.clone())
                } else {
                    None
                };
                let mut ops = Vec::with_capacity(elems.len());
                let mut tys = Vec::with_capacity(elems.len());
                for (i, e) in elems.iter().enumerate() {
                    let exp = expected_fields.as_ref().and_then(|v| v.get(i).copied());
                    let (op, ty) = self.lower_expr(e, exp)?;
                    ops.push(op);
                    tys.push(ty);
                }
                let tup_ty = self.compiler.intern_type(Type::Struct(tys));
                let tmp = self.alloc_temp(tup_ty);
                self.emit(Statement::Assign(
                    Place::new(tmp),
                    Rvalue::Aggregate(tup_ty, ops),
                ));
                Ok((Operand::Move(Place::new(tmp)), tup_ty))
            }
            Expr::SimdLit { ty, elems } => {
                let simd_ty = self.compiler.resolve_type_expr(
                    &self.mod_path,
                    self.owner_ty,
                    &self.comptime_env,
                    ty,
                )?;
                let elem = match self.compiler.program.types[simd_ty.0 as usize] {
                    Type::Simd { elem, .. } | Type::Array { elem, .. } => elem,
                    _ => {
                        return Err(format!(
                            "Expected SIMD or Array type in literal, got {simd_ty}"
                        ));
                    }
                };
                let mut ops = Vec::with_capacity(elems.len());
                for e in elems {
                    let (op, ety) = self.lower_expr(e, Some(elem))?;
                    let coerced = self.coerce_operand(op, ety, elem)?;
                    ops.push(coerced);
                }
                let tmp = self.alloc_temp(simd_ty);
                self.emit(Statement::Assign(
                    Place::new(tmp),
                    Rvalue::Aggregate(simd_ty, ops),
                ));
                let res_op = if self.is_copy_type(simd_ty) {
                    Operand::Copy(Place::new(tmp))
                } else {
                    Operand::Move(Place::new(tmp))
                };
                Ok((res_op, simd_ty))
            }
            Expr::StructLit { ty, fields } => {
                let mut wrap_union: Option<(TypeId, u32)> = None;
                let comp_ty = if let TypeExpr::Named(path) = ty
                    && path.len() >= 2
                    && self
                        .compiler
                        .resolve_path(&self.mod_path, path)
                        .is_err()
                {
                    let prefix = &path[..path.len() - 1];
                    let vname = path.last().unwrap();
                    let owner_ty = if prefix.len() == 1
                        && let Some(ComptimeVal::Type(t_id)) = self.comptime_env.get(&prefix[0])
                    {
                        *t_id
                    } else if let Ok(ResolvedItem::Type(tmod, tname)) =
                        self.compiler.resolve_path(&self.mod_path, prefix)
                    {
                        self.compiler.resolve_named_type(&tmod, &tname)?
                    } else {
                        return Err(format!("Cannot resolve type path '{}'", path.join("::")));
                    };
                    if let Some(err_info) = self.compiler.errors.get(&owner_ty).cloned() {
                        let Some((v_idx, leaf)) = err_info
                            .leaves
                            .iter()
                            .enumerate()
                            .find(|(_, l)| {
                                l.key.error_name == err_info.name && l.key.variant_name == *vname
                            })
                            .or_else(|| {
                                err_info
                                    .leaves
                                    .iter()
                                    .enumerate()
                                    .find(|(_, l)| l.key.variant_name == *vname)
                            })
                        else {
                            return Err(format!(
                                "Error '{}' has no variant '{}'",
                                err_info.name, vname
                            ));
                        };
                        wrap_union = Some((owner_ty, v_idx as u32));
                        leaf.payload_ty
                    } else if let Some(union_info) = self.compiler.unions.get(&owner_ty).cloned() {
                        let Some((v_idx, (_, payload_ty))) = union_info
                            .variants
                            .iter()
                            .enumerate()
                            .find(|(_, (vn, _))| vn == vname)
                        else {
                            return Err(format!(
                                "Union '{}' has no variant '{}'",
                                union_info.name, vname
                            ));
                        };
                        wrap_union = Some((owner_ty, v_idx as u32));
                        *payload_ty
                    } else {
                        return Err(format!("Cannot resolve type path '{}'", path.join("::")));
                    }
                } else {
                    self.compiler.resolve_type_expr(
                        &self.mod_path,
                        self.owner_ty,
                        &self.comptime_env,
                        ty,
                    )?
                };
                let Some(comp) = self.compiler.composites.get(&comp_ty).cloned() else {
                    return Err(format!("Cannot construct non-struct/opaque type {comp_ty}"));
                };
                // Enforce `opaque` private field encapsulation on literal construction!
                if comp.is_struct && comp.fields.is_empty() && self.owner_ty != Some(comp_ty) {
                    return Err(format!(
                        "Cannot construct opaque type '{}' outside its 'opaque {{ ... }}' block",
                        comp.name
                    ));
                }
                for (f_name, _, f_vis, _) in &comp.fields {
                    if comp.is_struct
                        && *f_vis == Visibility::Private
                        && self.owner_ty != Some(comp_ty)
                    {
                        return Err(format!(
                            "Cannot construct opaque '{}' with private field '{}' outside its 'opaque {{ ... }}' block",
                            comp.name, f_name
                        ));
                    }
                }
                if !comp.rel_fields.is_empty() {
                    let mut initial_field_ops = Vec::with_capacity(comp.fields.len());
                    for (idx, (f_name, f_ty, _, f_default)) in comp.fields.iter().enumerate() {
                        if let Some(&rel_kind) = comp.rel_fields.get(&(idx as u32)) {
                            match rel_kind {
                                RelFieldKind::Elem(_) => {
                                    initial_field_ops.push(Operand::Const(ConstValue::I64(0)));
                                }
                                RelFieldKind::Slice(_) | RelFieldKind::Str => {
                                    let zero_rel = self.alloc_temp(*f_ty);
                                    self.emit(Statement::Assign(
                                        Place::new(zero_rel),
                                        Rvalue::Aggregate(
                                            *f_ty,
                                            vec![
                                                Operand::Const(ConstValue::I64(0)),
                                                Operand::Const(ConstValue::I64(0)),
                                            ],
                                        ),
                                    ));
                                    initial_field_ops.push(Operand::Copy(Place::new(zero_rel)));
                                }
                            }
                            continue;
                        }
                        if let Some((_, val_expr)) = fields.iter().find(|(n, _)| n == f_name) {
                            let (op, val_ty) = self.lower_expr(val_expr, Some(*f_ty))?;
                            let coerced = self.coerce_operand(op, val_ty, *f_ty)?;
                            initial_field_ops.push(coerced);
                        } else if let Some(def_expr) = f_default {
                            let (op, val_ty) = self.lower_expr(def_expr, Some(*f_ty))?;
                            let coerced = self.coerce_operand(op, val_ty, *f_ty)?;
                            initial_field_ops.push(coerced);
                        } else {
                            return Err(format!(
                                "Missing field '{}' in '{}' literal",
                                f_name, comp.name
                            ));
                        }
                    }
                    let tmp = self.alloc_temp(comp_ty);
                    self.emit(Statement::Assign(
                        Place::new(tmp),
                        Rvalue::Aggregate(comp_ty, initial_field_ops),
                    ));
                    // Bind `self` to `tmp` in a temporary scope so `&rel self.<field>` resolves to `tmp`!
                    self.scopes.push(vec![ScopeVar {
                        name: "self".to_string(),
                        local: tmp,
                        ty: comp_ty,
                        opaque_bound: None,
                    }]);
                    let base_place = Place::new(tmp);
                    let mut rel_res = Ok(());
                    for (idx, (f_name, _, _, f_default)) in comp.fields.iter().enumerate() {
                        let Some(&rel_kind) = comp.rel_fields.get(&(idx as u32)) else {
                            continue;
                        };
                        let val_expr =
                            if let Some((_, ve)) = fields.iter().find(|(n, _)| n == f_name) {
                                ve
                            } else if let Some(def_expr) = f_default {
                                def_expr
                            } else {
                                rel_res = Err(format!(
                                    "Missing field '{}' in '{}' literal",
                                    f_name, comp.name
                                ));
                                break;
                            };
                        let mut dest_field_place = Place::new(tmp);
                        dest_field_place.projections.push(Projection::Field(idx as u32));
                        if let Err(e) = self.assign_rel_field(
                            &comp.name,
                            f_name,
                            &base_place,
                            dest_field_place,
                            rel_kind,
                            val_expr,
                        ) {
                            rel_res = Err(e);
                            break;
                        }
                    }
                    self.scopes.pop();
                    rel_res?;
                    let res_op = if self.is_copy_type(comp_ty) {
                        Operand::Copy(Place::new(tmp))
                    } else {
                        Operand::Move(Place::new(tmp))
                    };
                    return Ok((res_op, comp_ty));
                }
                let mut field_ops = Vec::with_capacity(comp.fields.len());
                for (f_name, f_ty, _, f_default) in &comp.fields {
                    if let Some((_, val_expr)) = fields.iter().find(|(n, _)| n == f_name) {
                        let (op, val_ty) = self.lower_expr(val_expr, Some(*f_ty))?;
                        let coerced = self.coerce_operand(op, val_ty, *f_ty)?;
                        field_ops.push(coerced);
                    } else if let Some(def_expr) = f_default {
                        let (op, val_ty) = self.lower_expr(def_expr, Some(*f_ty))?;
                        let coerced = self.coerce_operand(op, val_ty, *f_ty)?;
                        field_ops.push(coerced);
                    } else {
                        return Err(format!(
                            "Missing field '{}' in '{}' literal",
                            f_name, comp.name
                        ));
                    }
                }
                let tmp = self.alloc_temp(comp_ty);
                self.emit(Statement::Assign(
                    Place::new(tmp),
                    Rvalue::Aggregate(comp_ty, field_ops),
                ));
                let res_op = if self.is_copy_type(comp_ty) {
                    Operand::Copy(Place::new(tmp))
                } else {
                    Operand::Move(Place::new(tmp))
                };
                if let Some((owner_ty, v_idx)) = wrap_union {
                    let u_tmp = self.alloc_temp(owner_ty);
                    self.emit(Statement::Assign(
                        Place::new(u_tmp),
                        Rvalue::Union {
                            ty: owner_ty,
                            variant: v_idx,
                            payload: res_op,
                        },
                    ));
                    let u_op = if self.is_copy_type(owner_ty) {
                        Operand::Copy(Place::new(u_tmp))
                    } else {
                        Operand::Move(Place::new(u_tmp))
                    };
                    return Ok((u_op, owner_ty));
                }
                Ok((res_op, comp_ty))
            }
            Expr::IntrinsicDefault(ty_expr) => {
                let ty_id = self.compiler.resolve_type_expr(
                    &self.mod_path,
                    self.owner_ty,
                    &self.comptime_env,
                    ty_expr,
                )?;
                self.lower_default_for_type(ty_id)
            }
            Expr::IntrinsicClone(inner) => {
                let (mut place, mut ty_id) = match inner.as_ref() {
                    Expr::Ref { expr, .. } => self.lower_place(expr, false)?,
                    _ => self.lower_place(inner, false)?,
                };
                if let Type::Ptr { pointee, .. } = self.compiler.program.types[ty_id.0 as usize]
                    && !self.compiler.raw_ptrs.contains_key(&ty_id)
                {
                    place.projections.push(Projection::Deref);
                    ty_id = pointee;
                }
                self.lower_clone_for_place(place, ty_id)
            }
            Expr::IntrinsicDrop(inner) => {
                let (place, _) = self.lower_place(inner, true)?;
                let drop_target = if let Type::Ptr { .. } =
                    self.compiler.program.types[self.place_type(&place).0 as usize]
                {
                    let mut deref_p = place;
                    deref_p.projections.push(Projection::Deref);
                    deref_p
                } else {
                    place
                };
                let target_ty = self.place_type(&drop_target);
                if self.compiler.is_linear_type(target_ty) {
                    let t_disp = self
                        .compiler
                        .composites
                        .get(&target_ty)
                        .map(|c| c.name.clone())
                        .unwrap_or_else(|| {
                            self.compiler.program.types[target_ty.0 as usize].to_string()
                        });
                    return Err(format!(
                        "Linear value '{}' of type '{}' cannot be dropped via '@drop'; call a consuming method instead",
                        drop_target, t_disp
                    ));
                }
                let next_bb = self.new_block();
                self.terminate(Terminator::Drop {
                    place: drop_target,
                    target: next_bb,
                });
                self.cur_block = next_bb;
                let void_ty = self.compiler.intern_type(Type::Void);
                Ok((Operand::Const(ConstValue::Void), void_ty))
            }
            Expr::IntrinsicFormat {
                formatter,
                value,
                spec,
            } => {
                let (fmt_op, _) = self.lower_expr(formatter, None)?;
                let fmt_ref_op = match fmt_op {
                    Operand::Copy(p) => Operand::Copy(p),
                    Operand::Move(p) => Operand::Copy(p),
                    other => other,
                };
                let (val_place, val_ty) = self.lower_place(value, false)?;
                let spec_str = spec.as_deref().unwrap_or("");
                self.emit_format_place(fmt_ref_op, val_place, val_ty, spec_str)?;
                let void_ty = self.compiler.intern_type(Type::Void);
                Ok((Operand::Const(ConstValue::Void), void_ty))
            }
            Expr::FormatStr(segments) => self.lower_format_str(segments),
            Expr::IntrinsicTrap => {
                self.terminate(Terminator::Unreachable);
                let never_ty = self.compiler.intern_type(Type::Never);
                Ok((Operand::Const(ConstValue::Void), never_ty))
            }
            Expr::Return(opt_expr) => {
                if let TypeExpr::OpaqueTrait(bound_expr) = self.decl.ret_ty.clone() {
                    if let Some(expr) = opt_expr {
                        let exp_ty = self.inferred_opaque_ret;
                        let (op, expr_ty) = self.lower_expr(expr, exp_ty)?;
                        if !self.is_terminated() {
                            let target_ty = self.check_opaque_ret_expr(&bound_expr, expr_ty)?;
                            let coerced = self.coerce_operand(op, expr_ty, target_ty)?;
                            self.emit(Statement::Assign(
                                Place::new(LocalId(0)),
                                Rvalue::Use(coerced),
                            ));
                        }
                    } else {
                        let void_ty = self.compiler.intern_type(Type::Void);
                        let _ = self.check_opaque_ret_expr(&bound_expr, void_ty)?;
                        self.emit(Statement::Assign(
                            Place::new(LocalId(0)),
                            Rvalue::Use(Operand::Const(ConstValue::Void)),
                        ));
                    }
                    if !self.is_terminated() {
                        self.cleanup_all_scopes();
                        self.terminate(Terminator::Return);
                    }
                    let never_ty = self.compiler.intern_type(Type::Never);
                    return Ok((Operand::Const(ConstValue::Void), never_ty));
                }
                let ret_ty = self.locals[0];
                if let Some(expr) = opt_expr {
                    let (op, expr_ty) = self.lower_expr(expr, Some(ret_ty))?;
                    if !self.is_terminated() {
                        let coerced = self.coerce_operand(op, expr_ty, ret_ty)?;
                        self.emit(Statement::Assign(
                            Place::new(LocalId(0)),
                            Rvalue::Use(coerced),
                        ));
                    }
                } else if let Some(&res_info) = self.compiler.results.get(&ret_ty)
                    && matches!(
                        self.compiler.program.types[res_info.ok_ty.0 as usize],
                        Type::Void
                    )
                {
                    self.emit(Statement::Assign(
                        Place::new(LocalId(0)),
                        Rvalue::Union {
                            ty: ret_ty,
                            variant: 0,
                            payload: Operand::Const(ConstValue::Void),
                        },
                    ));
                } else {
                    self.emit(Statement::Assign(
                        Place::new(LocalId(0)),
                        Rvalue::Use(Operand::Const(ConstValue::Void)),
                    ));
                }
                if !self.is_terminated() {
                    self.cleanup_all_scopes();
                    self.terminate(Terminator::Return);
                }
                let never_ty = self.compiler.intern_type(Type::Never);
                Ok((Operand::Const(ConstValue::Void), never_ty))
            }
            Expr::UnsafeBlock(blk) => {
                self.unsafe_depth += 1;
                let void_ty = self.compiler.intern_type(Type::Void);
                let never_ty = self.compiler.intern_type(Type::Never);
                let res = if expected_ty != Some(void_ty)
                    && let Some(Stmt::Expr(tail_expr)) = blk.stmts.last()
                {
                    self.scopes.push(Vec::new());
                    let mut stmt_err = None;
                    for s in &blk.stmts[..blk.stmts.len() - 1] {
                        if self.is_terminated() {
                            break;
                        }
                        if let Err(e) = self.lower_stmt(s) {
                            stmt_err = Some(e);
                            break;
                        }
                    }
                    if let Some(e) = stmt_err {
                        self.scopes.pop();
                        Err(e)
                    } else if self.is_terminated() {
                        self.scopes.pop();
                        Ok((Operand::Const(ConstValue::Void), never_ty))
                    } else {
                        match self.lower_expr(tail_expr, expected_ty) {
                            Err(e) => {
                                self.scopes.pop();
                                Err(e)
                            }
                            Ok((tail_op, tail_ty)) => {
                                if self.is_terminated() {
                                    self.scopes.pop();
                                    Ok((Operand::Const(ConstValue::Void), never_ty))
                                } else if matches!(
                                    self.compiler.program.types[tail_ty.0 as usize],
                                    Type::Void
                                ) {
                                    self.cleanup_top_scope();
                                    self.scopes.pop();
                                    Ok((Operand::Const(ConstValue::Void), void_ty))
                                } else {
                                    let res_local = self.alloc_temp(tail_ty);
                                    self.emit(Statement::Assign(
                                        Place::new(res_local),
                                        Rvalue::Use(tail_op),
                                    ));
                                    self.cleanup_top_scope();
                                    self.scopes.pop();
                                    let out_op = if self.is_copy_type(tail_ty) {
                                        Operand::Copy(Place::new(res_local))
                                    } else {
                                        Operand::Move(Place::new(res_local))
                                    };
                                    Ok((out_op, tail_ty))
                                }
                            }
                        }
                    }
                } else {
                    match self.lower_scoped_block(blk) {
                        Err(e) => Err(e),
                        Ok(()) => {
                            if self.is_terminated() {
                                Ok((Operand::Const(ConstValue::Void), never_ty))
                            } else {
                                Ok((Operand::Const(ConstValue::Void), void_ty))
                            }
                        }
                    }
                };
                self.unsafe_depth -= 1;
                res
            }
            Expr::Lambda {
                is_move,
                params,
                ret_ty,
                body,
            } => {
                let mut param_tys = Vec::with_capacity(params.len());
                let mut ast_params = Vec::with_capacity(params.len());
                let mut initial_bound = std::collections::HashSet::new();
                for (is_mut, pname, pty_expr) in params {
                    let pty = self.compiler.resolve_type_expr(
                        &self.mod_path,
                        self.owner_ty,
                        &self.comptime_env,
                        pty_expr,
                    )?;
                    param_tys.push(pty);
                    ast_params.push(crate::ast::Param {
                        is_comptime: false,
                        is_mut: *is_mut,
                        name: pname.clone(),
                        ty: pty_expr.clone(),
                    });
                    initial_bound.insert(pname.clone());
                }
                let ret_ty_id = self.compiler.resolve_type_expr(
                    &self.mod_path,
                    self.owner_ty,
                    &self.comptime_env,
                    ret_ty,
                )?;

                let mut captures: Vec<(String, bool)> = Vec::new();
                self.collect_captures_in_block(body, &initial_bound, &mut captures);

                if captures.is_empty() {
                    // Non-capturing lambda decays directly to a `fn(...) -> R` function pointer (`Type::FnPtr`).
                    let fn_id = self.compiler.reserve_function(
                        Visibility::Private,
                        None,
                        &param_tys,
                        ret_ty_id,
                    );
                    let decl = FuncDecl {
                        vis: Visibility::Private,
                        name: format!("<lambda_{}>", fn_id.0),
                        params: ast_params,
                        ret_ty: ret_ty.clone(),
                        borrows: None,
                        where_clauses: Vec::new(),
                        body: body.clone(),
                    };
                    self.compiler.pending_funcs.push(PendingFunc {
                        func_id: fn_id,
                        module_path: self.mod_path.clone(),
                        owner_ty: self.owner_ty,
                        decl,
                        comptime_env: self.comptime_env.clone(),
                        closure_captures: Vec::new(),
                    });
                    let fn_ptr_ty = self.compiler.intern_type(Type::FnPtr {
                        args: param_tys,
                        ret: ret_ty_id,
                    });
                    Ok((Operand::Const(ConstValue::Func(fn_id)), fn_ptr_ty))
                } else {
                    // Capturing closure: synthesize unique environment struct type & hidden `__env` parameter.
                    let env_mut = captures.iter().any(|(_, needs_mut)| *needs_mut);
                    let mut env_field_tys = Vec::with_capacity(captures.len());
                    let mut env_field_ops = Vec::with_capacity(captures.len());
                    let mut closure_captures = Vec::with_capacity(captures.len());

                    for (cap_name, needs_mut) in &captures {
                        let (outer_place, outer_ty) = self
                            .lookup_var(cap_name)
                            .map(|(l, t)| (Place::new(l), t))
                            .or_else(|| self.lookup_capture(cap_name))
                            .ok_or_else(|| format!("Undefined captured variable '{cap_name}'"))?;

                        if *is_move {
                            env_field_tys.push(outer_ty);
                            let op = if self.is_copy_type(outer_ty) {
                                Operand::Copy(outer_place)
                            } else {
                                Operand::Move(outer_place)
                            };
                            env_field_ops.push(op);
                            closure_captures.push((cap_name.clone(), outer_ty, false));
                        } else {
                            let ref_ty = self.compiler.intern_type(Type::Ptr {
                                mutable: *needs_mut,
                                pointee: outer_ty,
                            });
                            let ref_tmp = self.alloc_temp(ref_ty);
                            self.emit(Statement::Assign(
                                Place::new(ref_tmp),
                                Rvalue::Ref {
                                    mutable: *needs_mut,
                                    place: outer_place,
                                },
                            ));
                            env_field_tys.push(ref_ty);
                            env_field_ops.push(Operand::Copy(Place::new(ref_tmp)));
                            closure_captures.push((cap_name.clone(), outer_ty, true));
                        }
                    }

                    let closure_ty = self
                        .compiler
                        .alloc_distinct_type(Type::Struct(env_field_tys));
                    let env_by_val = *is_move && self.compiler.is_linear_type(closure_ty);
                    let env_param_ty = if env_by_val {
                        closure_ty
                    } else {
                        self.compiler.intern_type(Type::Ptr {
                            mutable: env_mut,
                            pointee: closure_ty,
                        })
                    };

                    let mut call_param_tys = Vec::with_capacity(param_tys.len() + 1);
                    call_param_tys.push(env_param_ty);
                    call_param_tys.extend_from_slice(&param_tys);

                    let call_fn_id = self.compiler.reserve_function(
                        Visibility::Private,
                        None,
                        &call_param_tys,
                        ret_ty_id,
                    );
                    self.compiler.closures.insert(
                        closure_ty,
                        ClosureInfo {
                            call_fn_id,
                            env_mut,
                            env_by_val,
                            param_tys,
                            ret_ty: ret_ty_id,
                        },
                    );

                    let decl = FuncDecl {
                        vis: Visibility::Private,
                        name: format!("<closure_{}>", call_fn_id.0),
                        params: ast_params,
                        ret_ty: ret_ty.clone(),
                        borrows: None,
                        where_clauses: Vec::new(),
                        body: body.clone(),
                    };
                    self.compiler.pending_funcs.push(PendingFunc {
                        func_id: call_fn_id,
                        module_path: self.mod_path.clone(),
                        owner_ty: self.owner_ty,
                        decl,
                        comptime_env: self.comptime_env.clone(),
                        closure_captures,
                    });

                    let env_tmp = self.alloc_temp(closure_ty);
                    self.emit(Statement::Assign(
                        Place::new(env_tmp),
                        Rvalue::Aggregate(closure_ty, env_field_ops),
                    ));
                    let res_op = if self.is_copy_type(closure_ty) {
                        Operand::Copy(Place::new(env_tmp))
                    } else {
                        Operand::Move(Place::new(env_tmp))
                    };
                    Ok((res_op, closure_ty))
                }
            }
            Expr::Call { callee, args } => self.lower_call(callee, args),
            Expr::MethodCall {
                receiver,
                method,
                args,
            } => self.lower_method_call(receiver, method, args),
        }
    }

    pub(super) fn resolve_match_type_path(&mut self, path: &[String]) -> Option<TypeId> {
        if path.len() == 1
            && let Some(ComptimeVal::Type(t_id)) = self.comptime_env.get(&path[0])
        {
            return Some(*t_id);
        }
        if let Ok(ResolvedItem::Type(tmod, tname)) =
            self.compiler.resolve_path(&self.mod_path, path)
            && let Ok(t_id) = self.compiler.resolve_named_type(&tmod, &tname)
        {
            return Some(t_id);
        }
        None
    }

    pub(super) fn lower_match(
        &mut self,
        scrutinee: &Expr,
        arms: &[(MatchPat, Expr)],
        expected_ty: Option<TypeId>,
        is_stmt: bool,
    ) -> Result<(Operand, TypeId), String> {
        let (scrut_op, raw_scrut_ty) = self.lower_expr(scrutinee, None)?;
        let raw_scrut_local = self.alloc_temp(raw_scrut_ty);
        self.emit(Statement::Assign(
            Place::new(raw_scrut_local),
            Rvalue::Use(scrut_op),
        ));
        let (scrut_place, scrut_ty) = if let Type::Ptr { pointee, .. } =
            self.compiler.program.types[raw_scrut_ty.0 as usize]
            && !self.compiler.raw_ptrs.contains_key(&raw_scrut_ty)
            && !self.compiler.slices.contains_key(&raw_scrut_ty)
        {
            (
                Place {
                    local: raw_scrut_local,
                    projections: vec![Projection::Deref],
                },
                pointee,
            )
        } else {
            (Place::new(raw_scrut_local), raw_scrut_ty)
        };

        let void_ty = self.compiler.intern_type(Type::Void);
        let never_ty = self.compiler.intern_type(Type::Never);
        let entry_bb = self.cur_block;

        // 1. `error` scrutinee
        if let Some(err_info) = self.compiler.errors.get(&scrut_ty).cloned() {
            let tag_ty = self.compiler.intern_type(Type::Int {
                signed: false,
                bits: 32,
            });
            let discr_local = self.alloc_temp(tag_ty);
            self.emit(Statement::Assign(
                Place::new(discr_local),
                Rvalue::Discriminant(scrut_place.clone()),
            ));

            let mut covered = vec![false; err_info.leaves.len()];
            let mut has_wildcard = false;
            let mut switch_targets: Vec<(i128, BlockId)> = Vec::new();
            let mut wildcard_bb: Option<BlockId> = None;
            let mut arm_end_bbs: Vec<(BlockId, Operand, TypeId)> = Vec::new();
            let mut inferred_res_ty: Option<TypeId> = expected_ty;

            for (raw_pat, arm_expr) in arms {
                let pat = match raw_pat {
                    MatchPat::CatchAllBind { name, .. }
                        if self
                            .resolve_match_type_path(std::slice::from_ref(name))
                            .is_some_and(|t| self.compiler.errors.contains_key(&t)) =>
                    {
                        MatchPat::Variant {
                            path: vec![name.clone()],
                            binding: None,
                        }
                    }
                    other => other.clone(),
                };

                let arm_bb = self.new_block();
                let mut arm_binding: Option<(String, LocalId, TypeId)> = None;

                match &pat {
                    MatchPat::Wildcard => {
                        has_wildcard = true;
                        for c in &mut covered {
                            *c = true;
                        }
                        if wildcard_bb.is_none() {
                            wildcard_bb = Some(arm_bb);
                        }
                    }
                    MatchPat::CatchAllBind { name, .. } => {
                        has_wildcard = true;
                        for c in &mut covered {
                            *c = true;
                        }
                        if wildcard_bb.is_none() {
                            wildcard_bb = Some(arm_bb);
                        }
                        if name != "_" {
                            let bind_local = self.alloc_temp(scrut_ty);
                            self.cur_block = arm_bb;
                            self.emit(Statement::StorageLive(bind_local));
                            let s_op = if self.is_copy_type(scrut_ty) {
                                Operand::Copy(scrut_place.clone())
                            } else {
                                Operand::Move(scrut_place.clone())
                            };
                            self.emit(Statement::Assign(Place::new(bind_local), Rvalue::Use(s_op)));
                            arm_binding = Some((name.clone(), bind_local, scrut_ty));
                        }
                    }
                    MatchPat::Variant { path, binding } => {
                        // First check if `path` resolves directly to a subtype `error` (e.g. `IoError(io_err)`)
                        if let Some(sub_ty) = self.resolve_match_type_path(path)
                            && let Some(sub_err) = self.compiler.errors.get(&sub_ty).cloned()
                        {
                            let bind_local_opt = binding
                                .as_ref()
                                .filter(|(_, n)| n != "_")
                                .map(|(_, n)| (n.clone(), self.alloc_temp(sub_ty)));
                            for (sub_idx, sub_leaf) in sub_err.leaves.iter().enumerate() {
                                let Some((scrut_idx, scrut_leaf)) = err_info
                                    .leaves
                                    .iter()
                                    .enumerate()
                                    .find(|(_, sl)| sl.key == sub_leaf.key)
                                else {
                                    return Err(format!(
                                        "Error subtype '{}' in match pattern is not a subset of '{}': missing variant '{}::{}'",
                                        sub_err.name,
                                        err_info.name,
                                        sub_leaf.key.error_name,
                                        sub_leaf.key.variant_name
                                    ));
                                };
                                if scrut_leaf.payload_ty != sub_leaf.payload_ty {
                                    return Err(format!(
                                        "Payload type mismatch for variant '{}::{}' in match",
                                        sub_leaf.key.error_name, sub_leaf.key.variant_name
                                    ));
                                }
                                if covered[scrut_idx] {
                                    continue;
                                }
                                covered[scrut_idx] = true;
                                if let Some((_, sub_local)) = &bind_local_opt {
                                    let tramp_bb = self.new_block();
                                    switch_targets.push((scrut_idx as i128, tramp_bb));
                                    self.cur_block = tramp_bb;
                                    self.emit(Statement::StorageLive(*sub_local));
                                    let p_ty = scrut_leaf.payload_ty;
                                    let p_op = if matches!(
                                        self.compiler.program.types[p_ty.0 as usize],
                                        Type::Void
                                    ) {
                                        Operand::Const(ConstValue::Void)
                                    } else {
                                        let mut p_place = scrut_place.clone();
                                        p_place
                                            .projections
                                            .push(Projection::Variant(scrut_idx as u32));
                                        if self.is_copy_type(p_ty) {
                                            Operand::Copy(p_place)
                                        } else {
                                            Operand::Move(p_place)
                                        }
                                    };
                                    self.emit(Statement::Assign(
                                        Place::new(*sub_local),
                                        Rvalue::Union {
                                            ty: sub_ty,
                                            variant: sub_idx as u32,
                                            payload: p_op,
                                        },
                                    ));
                                    self.terminate(Terminator::Goto { target: arm_bb });
                                } else {
                                    switch_targets.push((scrut_idx as i128, arm_bb));
                                }
                            }
                            if let Some((b_name, sub_local)) = bind_local_opt {
                                arm_binding = Some((b_name, sub_local, sub_ty));
                            }
                        } else {
                            // Leaf variant pattern: `IoError::Timeout` or `ParseError::UnexpectedToken(tok)`
                            if path.len() < 2 {
                                return Err(format!(
                                    "Unqualified error variant '{}' in `match`; qualify as 'ErrorType::{}'",
                                    path.join("::"),
                                    path.join("::")
                                ));
                            }
                            let prefix = &path[..path.len() - 1];
                            let vname = path.last().unwrap();
                            let Some(pat_err_ty) = self.resolve_match_type_path(prefix) else {
                                return Err(format!(
                                    "Cannot resolve error type '{}' in match pattern",
                                    prefix.join("::")
                                ));
                            };
                            let Some(pat_err) = self.compiler.errors.get(&pat_err_ty).cloned()
                            else {
                                return Err(format!(
                                    "'{}' in match pattern is not an `error` type",
                                    prefix.join("::")
                                ));
                            };
                            let Some(pat_leaf) = pat_err
                                .leaves
                                .iter()
                                .find(|l| {
                                    l.key.error_name == pat_err.name && l.key.variant_name == *vname
                                })
                                .or_else(|| {
                                    pat_err.leaves.iter().find(|l| l.key.variant_name == *vname)
                                })
                            else {
                                return Err(format!(
                                    "Error type '{}' has no variant '{}'",
                                    pat_err.name, vname
                                ));
                            };
                            let Some((scrut_idx, scrut_leaf)) = err_info
                                .leaves
                                .iter()
                                .enumerate()
                                .find(|(_, sl)| sl.key == pat_leaf.key)
                            else {
                                return Err(format!(
                                    "Error variant '{}::{}' is not a member of scrutinee error type '{}'",
                                    pat_leaf.key.error_name,
                                    pat_leaf.key.variant_name,
                                    err_info.name
                                ));
                            };
                            covered[scrut_idx] = true;
                            switch_targets.push((scrut_idx as i128, arm_bb));
                            if let Some((_, b_name)) = binding
                                && b_name != "_"
                            {
                                let p_ty = scrut_leaf.payload_ty;
                                let var_local = self.alloc_temp(p_ty);
                                self.cur_block = arm_bb;
                                self.emit(Statement::StorageLive(var_local));
                                let mut p_place = scrut_place.clone();
                                p_place
                                    .projections
                                    .push(Projection::Variant(scrut_idx as u32));
                                let p_op = if self.is_copy_type(p_ty) {
                                    Operand::Copy(p_place)
                                } else {
                                    Operand::Move(p_place)
                                };
                                self.emit(Statement::Assign(
                                    Place::new(var_local),
                                    Rvalue::Use(p_op),
                                ));
                                arm_binding = Some((b_name.clone(), var_local, p_ty));
                            }
                        }
                    }
                    MatchPat::Int(_) => {
                        return Err("Cannot match integer literal against `error` type".to_string());
                    }
                }

                self.cur_block = arm_bb;
                self.scopes.push(Vec::new());
                if let Some((b_name, b_local, b_ty)) = arm_binding {
                    self.scopes.last_mut().unwrap().push(ScopeVar {
                        name: b_name,
                        local: b_local,
                        ty: b_ty,
                        opaque_bound: None,
                    });
                }
                let arm_exp = if is_stmt {
                    Some(void_ty)
                } else {
                    inferred_res_ty
                };
                let (arm_op, arm_ty) = self.lower_expr(arm_expr, arm_exp)?;
                if !self.is_terminated() {
                    if !is_stmt && inferred_res_ty.is_none() && arm_ty != never_ty {
                        inferred_res_ty = Some(arm_ty);
                    }
                    let saved_op = if is_stmt || arm_ty == void_ty || arm_ty == never_ty {
                        Operand::Const(ConstValue::Void)
                    } else {
                        let tmp = self.alloc_temp(arm_ty);
                        self.emit(Statement::Assign(Place::new(tmp), Rvalue::Use(arm_op)));
                        if self.is_copy_type(arm_ty) {
                            Operand::Copy(Place::new(tmp))
                        } else {
                            Operand::Move(Place::new(tmp))
                        }
                    };
                    self.cleanup_top_scope();
                    arm_end_bbs.push((self.cur_block, saved_op, arm_ty));
                }
                self.scopes.pop();
            }

            if !has_wildcard && covered.iter().any(|&c| !c) {
                let missing: Vec<String> = err_info
                    .leaves
                    .iter()
                    .enumerate()
                    .filter(|(i, _)| !covered[*i])
                    .map(|(_, l)| format!("{}::{}", l.key.error_name, l.key.variant_name))
                    .collect();
                return Err(format!(
                    "Non-exhaustive `match` on error type '{}': missing variants: {}",
                    err_info.name,
                    missing.join(", ")
                ));
            }

            let otherwise_bb = wildcard_bb.unwrap_or_else(|| {
                let u_bb = self.new_block();
                self.blocks[u_bb.0 as usize].terminator = Terminator::Unreachable;
                self.terminated[u_bb.0 as usize] = true;
                u_bb
            });
            self.blocks[entry_bb.0 as usize].terminator = Terminator::SwitchInt {
                discr: Operand::Copy(Place::new(discr_local)),
                targets: switch_targets,
                otherwise: otherwise_bb,
            };
            self.terminated[entry_bb.0 as usize] = true;

            let final_ty = if is_stmt {
                void_ty
            } else {
                inferred_res_ty.unwrap_or(never_ty)
            };
            if arm_end_bbs.is_empty() {
                let unreach_after = self.new_block();
                self.cur_block = unreach_after;
                self.terminate(Terminator::Unreachable);
                return Ok((Operand::Const(ConstValue::Void), never_ty));
            }
            let join_bb = self.new_block();
            let res_local = self.alloc_temp(final_ty);
            for (end_bb, saved_op, arm_ty) in arm_end_bbs {
                self.cur_block = end_bb;
                if !is_stmt && final_ty != void_ty && final_ty != never_ty {
                    let coerced = self.coerce_operand(saved_op, arm_ty, final_ty)?;
                    self.emit(Statement::Assign(
                        Place::new(res_local),
                        Rvalue::Use(coerced),
                    ));
                }
                self.terminate(Terminator::Goto { target: join_bb });
            }
            self.cur_block = join_bb;
            if is_stmt || final_ty == void_ty {
                return Ok((Operand::Const(ConstValue::Void), void_ty));
            }
            let out_op = if self.is_copy_type(final_ty) {
                Operand::Copy(Place::new(res_local))
            } else {
                Operand::Move(Place::new(res_local))
            };
            return Ok((out_op, final_ty));
        }

        // 2. `union` scrutinee
        if let Some(union_info) = self.compiler.unions.get(&scrut_ty).cloned() {
            let tag_ty = self.compiler.intern_type(Type::Int {
                signed: false,
                bits: 32,
            });
            let discr_local = self.alloc_temp(tag_ty);
            self.emit(Statement::Assign(
                Place::new(discr_local),
                Rvalue::Discriminant(scrut_place.clone()),
            ));

            let mut covered = vec![false; union_info.variants.len()];
            let mut has_wildcard = false;
            let mut switch_targets: Vec<(i128, BlockId)> = Vec::new();
            let mut wildcard_bb: Option<BlockId> = None;
            let mut arm_end_bbs: Vec<(BlockId, Operand, TypeId)> = Vec::new();
            let mut inferred_res_ty: Option<TypeId> = expected_ty;

            for (raw_pat, arm_expr) in arms {
                let pat = match raw_pat {
                    MatchPat::CatchAllBind { name, .. }
                        if union_info.variants.iter().any(|(vn, _)| vn == name) =>
                    {
                        MatchPat::Variant {
                            path: vec![name.clone()],
                            binding: None,
                        }
                    }
                    other => other.clone(),
                };

                let arm_bb = self.new_block();
                let mut arm_binding: Option<(String, LocalId, TypeId)> = None;

                match &pat {
                    MatchPat::Wildcard => {
                        has_wildcard = true;
                        for c in &mut covered {
                            *c = true;
                        }
                        if wildcard_bb.is_none() {
                            wildcard_bb = Some(arm_bb);
                        }
                    }
                    MatchPat::CatchAllBind { name, .. } => {
                        has_wildcard = true;
                        for c in &mut covered {
                            *c = true;
                        }
                        if wildcard_bb.is_none() {
                            wildcard_bb = Some(arm_bb);
                        }
                        if name != "_" {
                            let bind_local = self.alloc_temp(scrut_ty);
                            self.cur_block = arm_bb;
                            self.emit(Statement::StorageLive(bind_local));
                            let s_op = if self.is_copy_type(scrut_ty) {
                                Operand::Copy(scrut_place.clone())
                            } else {
                                Operand::Move(scrut_place.clone())
                            };
                            self.emit(Statement::Assign(Place::new(bind_local), Rvalue::Use(s_op)));
                            arm_binding = Some((name.clone(), bind_local, scrut_ty));
                        }
                    }
                    MatchPat::Variant { path, binding } => {
                        let vname = path.last().unwrap();
                        let Some((v_idx, (_, payload_ty))) = union_info
                            .variants
                            .iter()
                            .enumerate()
                            .find(|(_, (vn, _))| vn == vname)
                        else {
                            return Err(format!(
                                "Union '{}' has no variant '{}'",
                                union_info.name, vname
                            ));
                        };
                        covered[v_idx] = true;
                        switch_targets.push((v_idx as i128, arm_bb));
                        if let Some((_, b_name)) = binding
                            && b_name != "_"
                        {
                            let var_local = self.alloc_temp(*payload_ty);
                            self.cur_block = arm_bb;
                            self.emit(Statement::StorageLive(var_local));
                            let mut p_place = scrut_place.clone();
                            p_place.projections.push(Projection::Variant(v_idx as u32));
                            let p_op = if self.is_copy_type(*payload_ty) {
                                Operand::Copy(p_place)
                            } else {
                                Operand::Move(p_place)
                            };
                            self.emit(Statement::Assign(Place::new(var_local), Rvalue::Use(p_op)));
                            arm_binding = Some((b_name.clone(), var_local, *payload_ty));
                        }
                    }
                    MatchPat::Int(_) => {
                        return Err("Cannot match integer literal against `union` type".to_string());
                    }
                }

                self.cur_block = arm_bb;
                self.scopes.push(Vec::new());
                if let Some((b_name, b_local, b_ty)) = arm_binding {
                    self.scopes.last_mut().unwrap().push(ScopeVar {
                        name: b_name,
                        local: b_local,
                        ty: b_ty,
                        opaque_bound: None,
                    });
                }
                let arm_exp = if is_stmt {
                    Some(void_ty)
                } else {
                    inferred_res_ty
                };
                let (arm_op, arm_ty) = self.lower_expr(arm_expr, arm_exp)?;
                if !self.is_terminated() {
                    if !is_stmt && inferred_res_ty.is_none() && arm_ty != never_ty {
                        inferred_res_ty = Some(arm_ty);
                    }
                    let saved_op = if is_stmt || arm_ty == void_ty || arm_ty == never_ty {
                        Operand::Const(ConstValue::Void)
                    } else {
                        let tmp = self.alloc_temp(arm_ty);
                        self.emit(Statement::Assign(Place::new(tmp), Rvalue::Use(arm_op)));
                        if self.is_copy_type(arm_ty) {
                            Operand::Copy(Place::new(tmp))
                        } else {
                            Operand::Move(Place::new(tmp))
                        }
                    };
                    self.cleanup_top_scope();
                    arm_end_bbs.push((self.cur_block, saved_op, arm_ty));
                }
                self.scopes.pop();
            }

            if !has_wildcard && covered.iter().any(|&c| !c) {
                let missing: Vec<String> = union_info
                    .variants
                    .iter()
                    .enumerate()
                    .filter(|(i, _)| !covered[*i])
                    .map(|(_, (vn, _))| format!("{}::{}", union_info.name, vn))
                    .collect();
                return Err(format!(
                    "Non-exhaustive `match` on union '{}': missing variants: {}",
                    union_info.name,
                    missing.join(", ")
                ));
            }

            let otherwise_bb = wildcard_bb.unwrap_or_else(|| {
                let u_bb = self.new_block();
                self.blocks[u_bb.0 as usize].terminator = Terminator::Unreachable;
                self.terminated[u_bb.0 as usize] = true;
                u_bb
            });
            self.blocks[entry_bb.0 as usize].terminator = Terminator::SwitchInt {
                discr: Operand::Copy(Place::new(discr_local)),
                targets: switch_targets,
                otherwise: otherwise_bb,
            };
            self.terminated[entry_bb.0 as usize] = true;

            let final_ty = if is_stmt {
                void_ty
            } else {
                inferred_res_ty.unwrap_or(never_ty)
            };
            if arm_end_bbs.is_empty() {
                let unreach_after = self.new_block();
                self.cur_block = unreach_after;
                self.terminate(Terminator::Unreachable);
                return Ok((Operand::Const(ConstValue::Void), never_ty));
            }
            let join_bb = self.new_block();
            let res_local = self.alloc_temp(final_ty);
            for (end_bb, saved_op, arm_ty) in arm_end_bbs {
                self.cur_block = end_bb;
                if !is_stmt && final_ty != void_ty && final_ty != never_ty {
                    let coerced = self.coerce_operand(saved_op, arm_ty, final_ty)?;
                    self.emit(Statement::Assign(
                        Place::new(res_local),
                        Rvalue::Use(coerced),
                    ));
                }
                self.terminate(Terminator::Goto { target: join_bb });
            }
            self.cur_block = join_bb;
            if is_stmt || final_ty == void_ty {
                return Ok((Operand::Const(ConstValue::Void), void_ty));
            }
            let out_op = if self.is_copy_type(final_ty) {
                Operand::Copy(Place::new(res_local))
            } else {
                Operand::Move(Place::new(res_local))
            };
            return Ok((out_op, final_ty));
        }

        // 3. `enum` or integer scrutinee
        let enum_info = self.compiler.enums.get(&scrut_ty).cloned();
        let mut covered = enum_info
            .as_ref()
            .map(|(_, vs)| vec![false; vs.len()])
            .unwrap_or_default();
        let mut has_wildcard = false;
        let mut switch_targets: Vec<(i128, BlockId)> = Vec::new();
        let mut wildcard_bb: Option<BlockId> = None;
        let mut arm_end_bbs: Vec<(BlockId, Operand, TypeId)> = Vec::new();
        let mut inferred_res_ty: Option<TypeId> = expected_ty;

        for (raw_pat, arm_expr) in arms {
            let pat = match (raw_pat, &enum_info) {
                (MatchPat::CatchAllBind { name, .. }, Some((_, vs)))
                    if vs.iter().any(|(vn, _)| vn == name) =>
                {
                    MatchPat::Variant {
                        path: vec![name.clone()],
                        binding: None,
                    }
                }
                (other, _) => other.clone(),
            };

            let arm_bb = self.new_block();
            let mut arm_binding: Option<(String, LocalId, TypeId)> = None;

            match &pat {
                MatchPat::Wildcard => {
                    has_wildcard = true;
                    for c in &mut covered {
                        *c = true;
                    }
                    if wildcard_bb.is_none() {
                        wildcard_bb = Some(arm_bb);
                    }
                }
                MatchPat::CatchAllBind { name, .. } => {
                    has_wildcard = true;
                    for c in &mut covered {
                        *c = true;
                    }
                    if wildcard_bb.is_none() {
                        wildcard_bb = Some(arm_bb);
                    }
                    if name != "_" {
                        let bind_local = self.alloc_temp(scrut_ty);
                        self.cur_block = arm_bb;
                        self.emit(Statement::StorageLive(bind_local));
                        self.emit(Statement::Assign(
                            Place::new(bind_local),
                            Rvalue::Use(Operand::Copy(scrut_place.clone())),
                        ));
                        arm_binding = Some((name.clone(), bind_local, scrut_ty));
                    }
                }
                MatchPat::Variant { path, binding } => {
                    if binding.is_some() {
                        return Err("Enum variant cannot bind a payload in `match`".to_string());
                    }
                    let Some((enum_name, variants)) = &enum_info else {
                        return Err(format!(
                            "Cannot match variant pattern '{}' against non-enum/union/error type {}",
                            path.join("::"),
                            self.compiler.program.types[scrut_ty.0 as usize]
                        ));
                    };
                    let vname = path.last().unwrap();
                    let Some((v_idx, (_, v_val))) =
                        variants.iter().enumerate().find(|(_, (vn, _))| vn == vname)
                    else {
                        return Err(format!("Enum '{}' has no variant '{}'", enum_name, vname));
                    };
                    covered[v_idx] = true;
                    switch_targets.push((*v_val, arm_bb));
                }
                MatchPat::Int(val) => {
                    switch_targets.push((*val, arm_bb));
                }
            }

            self.cur_block = arm_bb;
            self.scopes.push(Vec::new());
            if let Some((b_name, b_local, b_ty)) = arm_binding {
                self.scopes.last_mut().unwrap().push(ScopeVar {
                    name: b_name,
                    local: b_local,
                    ty: b_ty,
                    opaque_bound: None,
                });
            }
            let arm_exp = if is_stmt {
                Some(void_ty)
            } else {
                inferred_res_ty
            };
            let (arm_op, arm_ty) = self.lower_expr(arm_expr, arm_exp)?;
            if !self.is_terminated() {
                if !is_stmt && inferred_res_ty.is_none() && arm_ty != never_ty {
                    inferred_res_ty = Some(arm_ty);
                }
                let saved_op = if is_stmt || arm_ty == void_ty || arm_ty == never_ty {
                    Operand::Const(ConstValue::Void)
                } else {
                    let tmp = self.alloc_temp(arm_ty);
                    self.emit(Statement::Assign(Place::new(tmp), Rvalue::Use(arm_op)));
                    if self.is_copy_type(arm_ty) {
                        Operand::Copy(Place::new(tmp))
                    } else {
                        Operand::Move(Place::new(tmp))
                    }
                };
                self.cleanup_top_scope();
                arm_end_bbs.push((self.cur_block, saved_op, arm_ty));
            }
            self.scopes.pop();
        }

        if let Some((enum_name, variants)) = &enum_info {
            if !has_wildcard && covered.iter().any(|&c| !c) {
                let missing: Vec<String> = variants
                    .iter()
                    .enumerate()
                    .filter(|(i, _)| !covered[*i])
                    .map(|(_, (vn, _))| format!("{enum_name}::{vn}"))
                    .collect();
                return Err(format!(
                    "Non-exhaustive `match` on enum '{}': missing variants: {}",
                    enum_name,
                    missing.join(", ")
                ));
            }
        } else if !has_wildcard {
            return Err(
                "Non-exhaustive `match` on integer requires a wildcard `_` arm".to_string(),
            );
        }

        let otherwise_bb = wildcard_bb.unwrap_or_else(|| {
            let u_bb = self.new_block();
            self.blocks[u_bb.0 as usize].terminator = Terminator::Unreachable;
            self.terminated[u_bb.0 as usize] = true;
            u_bb
        });
        self.blocks[entry_bb.0 as usize].terminator = Terminator::SwitchInt {
            discr: Operand::Copy(scrut_place),
            targets: switch_targets,
            otherwise: otherwise_bb,
        };
        self.terminated[entry_bb.0 as usize] = true;

        let final_ty = if is_stmt {
            void_ty
        } else {
            inferred_res_ty.unwrap_or(never_ty)
        };
        if arm_end_bbs.is_empty() {
            let unreach_after = self.new_block();
            self.cur_block = unreach_after;
            self.terminate(Terminator::Unreachable);
            return Ok((Operand::Const(ConstValue::Void), never_ty));
        }
        let join_bb = self.new_block();
        let res_local = self.alloc_temp(final_ty);
        for (end_bb, saved_op, arm_ty) in arm_end_bbs {
            self.cur_block = end_bb;
            if !is_stmt && final_ty != void_ty && final_ty != never_ty {
                let coerced = self.coerce_operand(saved_op, arm_ty, final_ty)?;
                self.emit(Statement::Assign(
                    Place::new(res_local),
                    Rvalue::Use(coerced),
                ));
            }
            self.terminate(Terminator::Goto { target: join_bb });
        }
        self.cur_block = join_bb;
        if is_stmt || final_ty == void_ty {
            return Ok((Operand::Const(ConstValue::Void), void_ty));
        }
        let out_op = if self.is_copy_type(final_ty) {
            Operand::Copy(Place::new(res_local))
        } else {
            Operand::Move(Place::new(res_local))
        };
        Ok((out_op, final_ty))
    }

    pub(super) fn lower_slice(
        &mut self,
        base: &Expr,
        start: &Expr,
        end: &Expr,
        explicit_mut: Option<bool>,
        expected_ty: Option<TypeId>,
    ) -> Result<(Operand, TypeId), String> {
        let want_mut = explicit_mut.unwrap_or_else(|| {
            expected_ty
                .and_then(|t| self.compiler.slices.get(&t))
                .is_some_and(|info| info.mutable)
        });
        let (mut base_place, mut base_ty) = self.lower_place(base, want_mut)?;
        if let Some((stat_name, true)) = self.static_locals.get(&base_place.local) {
            return Err(format!(
                "Taking a safe slice reference to mutable static '{}' is forbidden; use '&raw const' or '&raw mut' instead",
                stat_name
            ));
        }
        if want_mut && self.place_traverses_immutable_ptr(&base_place) {
            if let Some((stat_name, false)) = self.static_locals.get(&base_place.local) {
                return Err(format!(
                    "Cannot mutably slice immutable static variable '{}'",
                    stat_name
                ));
            }
            return Err("Cannot mutably slice through an immutable reference".to_string());
        }
        if let Type::Ptr {
            mutable: ptr_mut,
            pointee,
        } = self.compiler.program.types[base_ty.0 as usize]
        {
            if want_mut && !ptr_mut {
                return Err("Cannot mutably slice through an immutable reference".to_string());
            }
            base_place.projections.push(Projection::Deref);
            base_ty = pointee;
        }
        let elem_ty = if let Some(&slice_info) = self.compiler.slices.get(&base_ty) {
            if want_mut && !slice_info.mutable {
                return Err("Cannot take mutable subslice of an immutable slice".to_string());
            }
            base_place.projections.push(Projection::Field(0));
            base_place.projections.push(Projection::Deref);
            slice_info.elem
        } else if let Type::Array { elem, .. } = self.compiler.program.types[base_ty.0 as usize] {
            elem
        } else {
            return Err(format!("Cannot slice non-array/slice type {base_ty}"));
        };

        let usize_ty = self.compiler.intern_type(Type::Int {
            signed: false,
            bits: 64,
        });
        let (start_op, _) = self.lower_expr(start, Some(usize_ty))?;
        let start_local = self.alloc_temp(usize_ty);
        self.emit(Statement::Assign(
            Place::new(start_local),
            Rvalue::Use(start_op),
        ));
        let (end_op, _) = self.lower_expr(end, Some(usize_ty))?;

        let mut elem_start_place = base_place;
        elem_start_place
            .projections
            .push(Projection::Index(start_local));
        let elem_ptr_ty = self.compiler.intern_type(Type::Ptr {
            mutable: want_mut,
            pointee: elem_ty,
        });
        let elem_ptr_tmp = self.alloc_temp(elem_ptr_ty);
        self.emit(Statement::Assign(
            Place::new(elem_ptr_tmp),
            Rvalue::Ref {
                mutable: want_mut,
                place: elem_start_place,
            },
        ));

        let want_str = expected_ty
            .and_then(|t| self.compiler.slices.get(&t))
            .is_some_and(|info| info.is_str)
            || self
                .compiler
                .slices
                .get(&base_ty)
                .is_some_and(|info| info.is_str);
        let slice_ty = if want_str && !want_mut {
            self.compiler.intern_str_type()
        } else {
            self.compiler.intern_slice_type(want_mut, elem_ty)
        };
        let slice_info = self.compiler.slices[&slice_ty];
        let data_ptr_tmp = self.alloc_temp(slice_info.ptr_ty);
        self.emit(Statement::Assign(
            Place::new(data_ptr_tmp),
            Rvalue::Cast(Operand::Copy(Place::new(elem_ptr_tmp)), slice_info.ptr_ty),
        ));

        let len_tmp = self.alloc_temp(usize_ty);
        self.emit(Statement::Assign(
            Place::new(len_tmp),
            Rvalue::BinaryOp(BinOp::Sub, end_op, Operand::Copy(Place::new(start_local))),
        ));

        let slice_tmp = self.alloc_temp(slice_ty);
        self.emit(Statement::Assign(
            Place::new(slice_tmp),
            Rvalue::Aggregate(
                slice_ty,
                vec![
                    Operand::Copy(Place::new(data_ptr_tmp)),
                    Operand::Copy(Place::new(len_tmp)),
                ],
            ),
        ));
        Ok((Operand::Copy(Place::new(slice_tmp)), slice_ty))
    }

    pub(super) fn lower_default_for_type(
        &mut self,
        ty_id: TypeId,
    ) -> Result<(Operand, TypeId), String> {
        if let Some(comp) = self.compiler.composites.get(&ty_id).cloned() {
            if let Some(def_fn) = comp.default_fn {
                let dst = self.alloc_temp(ty_id);
                let next_bb = self.new_block();
                self.terminate(Terminator::Call {
                    func: Operand::Const(ConstValue::Func(def_fn)),
                    args: vec![],
                    destination: Place::new(dst),
                    target: next_bb,
                });
                self.cur_block = next_bb;
                return Ok((Operand::Move(Place::new(dst)), ty_id));
            } else if comp.is_struct {
                return Err(format!(
                    "Struct '{}' does not implement a `default()` hook",
                    comp.name
                ));
            } else {
                // Record auto-synthesizes default from field defaults or field `@default`
                let mut f_ops = Vec::with_capacity(comp.fields.len());
                for (_, f_ty, _, f_def) in &comp.fields {
                    if let Some(def_expr) = f_def {
                        let (op, _) = self.lower_expr(def_expr, Some(*f_ty))?;
                        f_ops.push(op);
                    } else {
                        let (op, _) = self.lower_default_for_type(*f_ty)?;
                        f_ops.push(op);
                    }
                }
                let dst = self.alloc_temp(ty_id);
                self.emit(Statement::Assign(
                    Place::new(dst),
                    Rvalue::Aggregate(ty_id, f_ops),
                ));
                return Ok((Operand::Move(Place::new(dst)), ty_id));
            }
        }

        match self.compiler.program.types[ty_id.0 as usize].clone() {
            Type::Bool => Ok((Operand::Const(ConstValue::Bool(false)), ty_id)),
            Type::Int { .. } | Type::Rune => Ok((Operand::Const(ConstValue::I64(0)), ty_id)),
            Type::F32 | Type::F64 => Ok((Operand::Const(ConstValue::F64(0)), ty_id)),
            Type::Struct(fields) => {
                let mut ops = Vec::with_capacity(fields.len());
                for f in fields {
                    let (op, _) = self.lower_default_for_type(f)?;
                    ops.push(op);
                }
                let dst = self.alloc_temp(ty_id);
                self.emit(Statement::Assign(
                    Place::new(dst),
                    Rvalue::Aggregate(ty_id, ops),
                ));
                Ok((Operand::Move(Place::new(dst)), ty_id))
            }
            Type::Array { elem, len } | Type::Simd { elem, len } => {
                let mut ops = Vec::with_capacity(len as usize);
                for _ in 0..len {
                    let (op, _) = self.lower_default_for_type(elem)?;
                    ops.push(op);
                }
                let dst = self.alloc_temp(ty_id);
                self.emit(Statement::Assign(
                    Place::new(dst),
                    Rvalue::Aggregate(ty_id, ops),
                ));
                Ok((Operand::Move(Place::new(dst)), ty_id))
            }
            Type::Union { variants, .. }
                if !variants.is_empty()
                    && matches!(
                        self.compiler.program.types[variants[0].0 as usize],
                        Type::Void
                    ) =>
            {
                let dst = self.alloc_temp(ty_id);
                self.emit(Statement::Assign(
                    Place::new(dst),
                    Rvalue::Union {
                        ty: ty_id,
                        variant: 0,
                        payload: Operand::Const(ConstValue::Void),
                    },
                ));
                Ok((Operand::Move(Place::new(dst)), ty_id))
            }
            _ => Err(format!("Type {ty_id} does not support `@default`")),
        }
    }

    pub(super) fn lower_clone_for_place(
        &mut self,
        place: Place,
        ty_id: TypeId,
    ) -> Result<(Operand, TypeId), String> {
        if let Some(comp) = self.compiler.composites.get(&ty_id).cloned() {
            if let Some(clone_fn) = comp.clone_fn {
                let ref_ty = self.compiler.intern_type(Type::Ptr {
                    mutable: false,
                    pointee: ty_id,
                });
                let ref_tmp = self.alloc_temp(ref_ty);
                self.emit(Statement::Assign(
                    Place::new(ref_tmp),
                    Rvalue::Ref {
                        mutable: false,
                        place,
                    },
                ));
                let dst = self.alloc_temp(ty_id);
                let next_bb = self.new_block();
                self.terminate(Terminator::Call {
                    func: Operand::Const(ConstValue::Func(clone_fn)),
                    args: vec![Operand::Copy(Place::new(ref_tmp))],
                    destination: Place::new(dst),
                    target: next_bb,
                });
                self.cur_block = next_bb;
                return Ok((Operand::Move(Place::new(dst)), ty_id));
            } else if comp.is_struct {
                if comp.ownership != StructOwnership::Copy {
                    return Err(format!("Struct '{}' does not implement `clone`", comp.name));
                }
            } else {
                // Record structural clone
                let mut ops = Vec::with_capacity(comp.fields.len());
                for (idx, (_, f_ty, _, _)) in comp.fields.iter().enumerate() {
                    let mut fp = place.clone();
                    fp.projections.push(Projection::Field(idx as u32));
                    let (f_op, _) = self.lower_clone_for_place(fp, *f_ty)?;
                    ops.push(f_op);
                }
                let dst = self.alloc_temp(ty_id);
                self.emit(Statement::Assign(
                    Place::new(dst),
                    Rvalue::Aggregate(ty_id, ops),
                ));
                return Ok((Operand::Move(Place::new(dst)), ty_id));
            }
        }
        if self.is_copy_type(ty_id) {
            let dst = self.alloc_temp(ty_id);
            self.emit(Statement::Assign(
                Place::new(dst),
                Rvalue::Use(Operand::Copy(place)),
            ));
            Ok((Operand::Copy(Place::new(dst)), ty_id))
        } else {
            Err(format!("Type {ty_id} is not clonable"))
        }
    }
}
