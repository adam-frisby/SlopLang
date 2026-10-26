use super::*;

impl<'a> FuncLowerer<'a> {
    pub(super) fn new(compiler: &'a mut Compiler, pending: PendingFunc) -> Self {
        let existing_locals = compiler
            .program
            .functions
            .iter()
            .find(|f| f.id == pending.func_id)
            .unwrap()
            .locals
            .clone();
        let private_access = !compiler.no_private_access_fns.contains(&pending.func_id);
        Self {
            compiler,
            private_access,
            func_id: pending.func_id,
            mod_path: pending.module_path,
            owner_ty: pending.owner_ty,
            decl: pending.decl,
            comptime_env: pending.comptime_env,
            closure_captures: pending.closure_captures,
            locals: existing_locals,
            blocks: vec![BasicBlock {
                statements: Vec::new(),
                terminator: Terminator::Unreachable,
            }],
            terminated: vec![false],
            cur_block: BlockId(0),
            scopes: vec![Vec::new()],
            inferred_opaque_ret: None,
            last_call_opaque_bound: None,
            unsafe_depth: 0,
            raw_addr_of_depth: 0,
            static_locals: HashMap::new(),
        }
    }

    /// Whether this function body may access private members of `ty`: true only inside `ty`'s own
    /// block (inherent methods, lifecycle hooks, inline `impl Tr { ... }` methods, and their lambdas).
    pub(super) fn has_private_access(&self, ty: TypeId) -> bool {
        self.private_access && self.owner_ty == Some(ty)
    }

    pub(super) fn new_block(&mut self) -> BlockId {
        let id = BlockId(self.blocks.len() as u32);
        self.blocks.push(BasicBlock {
            statements: Vec::new(),
            terminator: Terminator::Unreachable,
        });
        self.terminated.push(false);
        id
    }

    pub(super) fn alloc_temp(&mut self, ty: TypeId) -> LocalId {
        let id = LocalId(self.locals.len() as u32);
        self.locals.push(ty);
        id
    }

    pub(super) fn emit(&mut self, stmt: Statement) {
        self.blocks[self.cur_block.0 as usize].statements.push(stmt);
    }

    pub(super) fn terminate(&mut self, term: Terminator) {
        self.blocks[self.cur_block.0 as usize].terminator = term;
        self.terminated[self.cur_block.0 as usize] = true;
    }

    pub(super) fn is_terminated(&self) -> bool {
        self.terminated[self.cur_block.0 as usize]
    }

    pub(super) fn lookup_var(&self, name: &str) -> Option<(LocalId, TypeId)> {
        for scope in self.scopes.iter().rev() {
            for var in scope.iter().rev() {
                if var.name == name {
                    return Some((var.local, var.ty));
                }
            }
        }
        None
    }

    pub(super) fn lookup_var_opaque_bound(&self, name: &str) -> Option<OpaqueRetBound> {
        for scope in self.scopes.iter().rev() {
            for var in scope.iter().rev() {
                if var.name == name {
                    return var.opaque_bound.clone();
                }
            }
        }
        None
    }

    pub(super) fn check_opaque_ret_expr(
        &mut self,
        bound_expr: &TypeExpr,
        expr_ty: TypeId,
    ) -> Result<TypeId, String> {
        let check_res = self.compiler.eval_comptime_type_bound(
            &self.mod_path,
            self.owner_ty,
            &self.comptime_env,
            bound_expr,
            expr_ty,
        )?;
        match check_res {
            Some(Ok(_)) => {}
            Some(Err(e)) => {
                return Err(format!(
                    "Return type '{}' in '{}' does not satisfy 'opaque' return bound: {}",
                    self.compiler.type_display_name(expr_ty),
                    self.decl.name,
                    e
                ));
            }
            None => {
                return Err(format!(
                    "Invalid trait or constraint bound in '-> opaque ...' on '{}'",
                    self.decl.name
                ));
            }
        }
        if let Some(prev_ty) = self.inferred_opaque_ret {
            if prev_ty != expr_ty {
                return Err(format!(
                    "Conflicting concrete return types in '-> opaque ...' function '{}': '{}' vs '{}'; all return paths must return the same concrete type",
                    self.decl.name,
                    self.compiler.type_display_name(prev_ty),
                    self.compiler.type_display_name(expr_ty)
                ));
            }
        } else {
            self.inferred_opaque_ret = Some(expr_ty);
            self.locals[0] = expr_ty;
            if let Some(sig) = self.compiler.func_sigs.get_mut(&self.func_id) {
                sig.1 = expr_ty;
            }
        }
        Ok(expr_ty)
    }

    pub(super) fn lookup_capture(&self, name: &str) -> Option<(Place, TypeId)> {
        let (idx, (_, outer_ty, is_by_ref)) = self
            .closure_captures
            .iter()
            .enumerate()
            .find(|(_, (n, _, _))| n == name)?;
        let mut place = Place::new(LocalId(1));
        if matches!(
            self.compiler.program.types[self.locals[1].0 as usize],
            Type::Ptr { .. }
        ) {
            place.projections.push(Projection::Deref);
        }
        place.projections.push(Projection::Field(idx as u32));
        if *is_by_ref {
            place.projections.push(Projection::Deref);
        }
        Some((place, *outer_ty))
    }

    pub(super) fn emit_drop_and_dead(&mut self, local: LocalId) {
        let arg_count = self.decl.params.iter().filter(|p| !p.is_comptime).count() as u32
            + u32::from(!self.closure_captures.is_empty());
        let next_bb = self.new_block();
        self.terminate(Terminator::Drop {
            place: Place::new(local),
            target: next_bb,
        });
        self.cur_block = next_bb;
        if local.0 > arg_count {
            self.emit(Statement::StorageDead(local));
        }
    }

    pub(super) fn cleanup_top_scope(&mut self) {
        if let Some(top) = self.scopes.last().cloned() {
            for var in top.iter().rev() {
                self.emit_drop_and_dead(var.local);
            }
        }
    }

    pub(super) fn cleanup_all_scopes(&mut self) {
        let all_scopes = self.scopes.clone();
        for scope in all_scopes.iter().rev() {
            for var in scope.iter().rev() {
                self.emit_drop_and_dead(var.local);
            }
        }
    }

    pub(super) fn lower(&mut self) -> Result<(), String> {
        // Bind runtime parameters into root scope (`LocalId(1)` is `__env` when `closure_captures` is non-empty)
        let mut arg_local_idx = if self.closure_captures.is_empty() {
            1u32
        } else {
            if !matches!(
                self.compiler.program.types[self.locals[1].0 as usize],
                Type::Ptr { .. }
            ) {
                self.scopes[0].push(ScopeVar {
                    name: "__env".to_string(),
                    local: LocalId(1),
                    ty: self.locals[1],
                    opaque_bound: None,
                });
            }
            2u32
        };
        for p in &self.decl.params.clone() {
            if !p.is_comptime {
                let local = LocalId(arg_local_idx);
                let ty = self.locals[arg_local_idx as usize];
                self.comptime_env
                    .insert(format!("__var_ty:{}", p.name), ComptimeVal::Type(ty));
                self.scopes[0].push(ScopeVar {
                    name: p.name.clone(),
                    local,
                    ty,
                    opaque_bound: None,
                });
                arg_local_idx += 1;
            } else if let Some(ComptimeVal::ConstExpr(_, const_expr)) =
                self.comptime_env.get(&p.name).cloned()
            {
                match &const_expr {
                    Expr::Ref {
                        mutable,
                        expr: inner,
                    } => {
                        let (val_op, val_ty) = self.lower_expr(inner, None)?;
                        let val_loc = self.alloc_temp(val_ty);
                        self.emit(Statement::StorageLive(val_loc));
                        self.emit(Statement::Assign(Place::new(val_loc), Rvalue::Use(val_op)));
                        let ref_ty = self.compiler.intern_type(Type::Ptr {
                            mutable: *mutable,
                            pointee: val_ty,
                        });
                        let ref_loc = self.alloc_temp(ref_ty);
                        self.emit(Statement::StorageLive(ref_loc));
                        self.emit(Statement::Assign(
                            Place::new(ref_loc),
                            Rvalue::Ref {
                                mutable: *mutable,
                                place: Place::new(val_loc),
                            },
                        ));
                        self.scopes[0].push(ScopeVar {
                            name: p.name.clone(),
                            local: ref_loc,
                            ty: ref_ty,
                            opaque_bound: None,
                        });
                    }
                    _ => {
                        let exp_ty = self
                            .compiler
                            .resolve_type_expr(
                                &self.mod_path,
                                self.owner_ty,
                                &self.comptime_env,
                                &p.ty,
                            )
                            .ok();
                        let (val_op, val_ty) = self.lower_expr(&const_expr, exp_ty)?;
                        let val_loc = self.alloc_temp(val_ty);
                        self.emit(Statement::StorageLive(val_loc));
                        self.emit(Statement::Assign(Place::new(val_loc), Rvalue::Use(val_op)));
                        self.scopes[0].push(ScopeVar {
                            name: p.name.clone(),
                            local: val_loc,
                            ty: val_ty,
                            opaque_bound: None,
                        });
                    }
                }
            }
        }

        // Entry null checks for `export fn` raw-pointer parameters live in the C-ABI wrapper
        // (`Compiler::build_c_abi_export_wrapper`), so Lrrr callers never pay for them.
        let body = self.decl.body.clone();
        self.lower_block_stmts(&body)?;

        if matches!(self.decl.ret_ty, TypeExpr::OpaqueTrait(_))
            && self.inferred_opaque_ret.is_none()
        {
            return Err(format!(
                "Function '{}' with '-> opaque ...' return type must return a concrete value",
                self.decl.name
            ));
        }

        let ret_ty = self.locals[0];
        if !self.is_terminated() {
            if matches!(self.compiler.program.types[ret_ty.0 as usize], Type::Void) {
                self.emit(Statement::Assign(
                    Place::new(LocalId(0)),
                    Rvalue::Use(Operand::Const(ConstValue::Void)),
                ));
                self.cleanup_all_scopes();
                self.terminate(Terminator::Return);
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
                self.cleanup_all_scopes();
                self.terminate(Terminator::Return);
            } else if matches!(self.compiler.program.types[ret_ty.0 as usize], Type::Never) {
                return Err(format!(
                    "Function '{}' declared '-> never' reaches end of function without diverging",
                    self.decl.name
                ));
            } else {
                return Err(format!(
                    "Function '{}' reaches end of non-void function without returning",
                    self.decl.name
                ));
            }
        }

        let func = self
            .compiler
            .program
            .functions
            .iter_mut()
            .find(|f| f.id == self.func_id)
            .unwrap();
        func.locals = self.locals.clone();
        func.blocks = self.blocks.clone();
        Ok(())
    }

    pub(super) fn lower_scoped_block(&mut self, block: &Block) -> Result<(), String> {
        self.scopes.push(Vec::new());
        self.lower_block_stmts(block)?;
        if !self.is_terminated() {
            self.cleanup_top_scope();
        }
        self.scopes.pop();
        Ok(())
    }

    pub(super) fn lower_block_stmts(&mut self, block: &Block) -> Result<(), String> {
        for stmt in &block.stmts {
            if self.is_terminated() {
                break;
            }
            self.lower_stmt(stmt)?;
        }
        Ok(())
    }

    pub(super) fn verify_pattern_const(&self, ty_id: TypeId, val: i128) -> Result<(), String> {
        if let Type::Pattern { ranges, .. } = &self.compiler.program.types[ty_id.0 as usize] {
            let valid = ranges.iter().any(|&(lo, hi)| val >= lo && val <= hi);
            if !valid {
                return Err(format!(
                    "Compile-time value {val} is outside valid pattern ranges of {}",
                    self.compiler.program.types[ty_id.0 as usize]
                ));
            }
        }
        Ok(())
    }

    pub(super) fn coerce_operand(
        &mut self,
        op: Operand,
        src_ty: TypeId,
        target_ty: TypeId,
    ) -> Result<Operand, String> {
        // Function-pointer types differing only in their borrow contract: a function constant may take
        // any contract (Stage 3c verifies the function against it); a pointer value may only widen.
        if src_ty != target_ty
            && let (Type::FnPtr { args: sa, ret: sr }, Type::FnPtr { args: ta, ret: tr }) = (
                &self.compiler.program.types[src_ty.0 as usize],
                &self.compiler.program.types[target_ty.0 as usize],
            )
            && sa == ta
            && sr == tr
        {
            if matches!(op, Operand::Const(ConstValue::Func(_))) {
                return Ok(op);
            }
            let src_c = self.compiler.fn_ptr_contract(src_ty).cloned().unwrap_or_default();
            let dst_c = self.compiler.fn_ptr_contract(target_ty).cloned().unwrap_or_default();
            if src_c.ret.iter().all(|p| dst_c.ret.contains(p))
                && src_c.flows.iter().all(|f| dst_c.flows.contains(f))
            {
                return Ok(op);
            }
            return Err(format!(
                "Function pointer of type '{}' has a wider borrow contract than the expected '{}'",
                self.compiler.type_display_name(src_ty),
                self.compiler.type_display_name(target_ty)
            ));
        }
        // Automatic reborrowing of a named `&mut T` local or field when passed to `&mut T`/`&T` (or `&mut opaque`/`&opaque`)
        if let (
            Type::Ptr {
                mutable: true,
                pointee: src_pt,
            },
            Type::Ptr {
                mutable: dst_mut,
                pointee: dst_pt,
            },
        ) = (
            self.compiler.program.types[src_ty.0 as usize].clone(),
            self.compiler.program.types[target_ty.0 as usize].clone(),
        ) && (src_pt == dst_pt || self.compiler.is_universal_opaque_type(dst_pt))
            && !self.compiler.raw_ptrs.contains_key(&src_ty)
            && !self.compiler.raw_ptrs.contains_key(&target_ty)
            && let Operand::Move(mut place) = op.clone()
            && (!place.projections.is_empty()
                || self.scopes.iter().flatten().any(|v| v.local == place.local))
        {
            place.projections.push(Projection::Deref);
            let tmp = self.alloc_temp(target_ty);
            self.emit(Statement::Assign(
                Place::new(tmp),
                Rvalue::Ref {
                    mutable: dst_mut,
                    place,
                },
            ));
            return Ok(Operand::Move(Place::new(tmp)));
        }

        // Automatic reborrowing of a named `&mut [T]` slice local when passed to `&mut [T]` or `&[T]`
        if let (Some(&src_slice), Some(&target_slice)) = (
            self.compiler.slices.get(&src_ty),
            self.compiler.slices.get(&target_ty),
        ) && src_slice.mutable
            && src_slice.elem == target_slice.elem
            && let Operand::Move(place) = op.clone()
            && place.projections.is_empty()
            && self.scopes.iter().flatten().any(|v| v.local == place.local)
        {
            let mut deref_ptr = Place::new(place.local);
            deref_ptr.projections.push(Projection::Field(0));
            deref_ptr.projections.push(Projection::Deref);
            let mut len_field = Place::new(place.local);
            len_field.projections.push(Projection::Field(1));
            let reborrow_ptr = self.alloc_temp(target_slice.ptr_ty);
            self.emit(Statement::Assign(
                Place::new(reborrow_ptr),
                Rvalue::Ref {
                    mutable: target_slice.mutable,
                    place: deref_ptr,
                },
            ));
            let dst = self.alloc_temp(target_ty);
            self.emit(Statement::Assign(
                Place::new(dst),
                Rvalue::Aggregate(
                    target_ty,
                    vec![
                        Operand::Move(Place::new(reborrow_ptr)),
                        Operand::Copy(len_field),
                    ],
                ),
            ));
            return Ok(Operand::Move(Place::new(dst)));
        }

        // Automatic reborrowing of a named `&mut MyTrait` trait object local when passed to `&mut MyTrait` or `&MyTrait`
        if let (Some(src_tobj), Some(target_tobj)) = (
            self.compiler.trait_objs.get(&src_ty).cloned(),
            self.compiler.trait_objs.get(&target_ty).cloned(),
        ) && src_tobj.mutable
            && src_tobj.trait_ty == target_tobj.trait_ty
            && let Operand::Move(place) = op.clone()
            && place.projections.is_empty()
            && self.scopes.iter().flatten().any(|v| v.local == place.local)
        {
            let mut deref_ptr = Place::new(place.local);
            deref_ptr.projections.push(Projection::Field(0));
            deref_ptr.projections.push(Projection::Deref);
            let mut vt_field = Place::new(place.local);
            vt_field.projections.push(Projection::Field(1));
            let reborrow_ptr = self.alloc_temp(target_tobj.data_ptr_ty);
            self.emit(Statement::Assign(
                Place::new(reborrow_ptr),
                Rvalue::Ref {
                    mutable: target_tobj.mutable,
                    place: deref_ptr,
                },
            ));
            let dst = self.alloc_temp(target_ty);
            self.emit(Statement::Assign(
                Place::new(dst),
                Rvalue::Aggregate(
                    target_ty,
                    vec![
                        Operand::Move(Place::new(reborrow_ptr)),
                        Operand::Copy(vt_field),
                    ],
                ),
            ));
            return Ok(Operand::Move(Place::new(dst)));
        }

        if src_ty == target_ty {
            if let Operand::Const(ConstValue::I64(n)) = &op {
                self.verify_pattern_const(target_ty, *n)?;
            }
            return Ok(op);
        }

        // Coerce `&T`/`&mut T` -> `&MyTrait`/`&mut MyTrait` and `&mut MyTrait` -> `&MyTrait`
        if let Some(target_tobj) = self.compiler.trait_objs.get(&target_ty).cloned() {
            if let Some(src_tobj) = self.compiler.trait_objs.get(&src_ty).cloned()
                && src_tobj.trait_ty == target_tobj.trait_ty
            {
                if target_tobj.mutable && !src_tobj.mutable {
                    return Err(format!(
                        "Cannot coerce shared trait object '&{}' to mutable trait object '&mut {}'",
                        self.compiler.type_display_name(target_tobj.trait_ty),
                        self.compiler.type_display_name(target_tobj.trait_ty)
                    ));
                }
                let src_local = match op {
                    Operand::Copy(p) | Operand::Move(p) if p.projections.is_empty() => p.local,
                    other => {
                        let tmp = self.alloc_temp(src_ty);
                        self.emit(Statement::Assign(Place::new(tmp), Rvalue::Use(other)));
                        tmp
                    }
                };
                let mut ptr_field = Place::new(src_local);
                ptr_field.projections.push(Projection::Field(0));
                let mut vt_field = Place::new(src_local);
                vt_field.projections.push(Projection::Field(1));
                let cast_ptr = self.alloc_temp(target_tobj.data_ptr_ty);
                self.emit(Statement::Assign(
                    Place::new(cast_ptr),
                    Rvalue::Cast(Operand::Copy(ptr_field), target_tobj.data_ptr_ty),
                ));
                let dst = self.alloc_temp(target_ty);
                self.emit(Statement::Assign(
                    Place::new(dst),
                    Rvalue::Aggregate(
                        target_ty,
                        vec![Operand::Copy(Place::new(cast_ptr)), Operand::Copy(vt_field)],
                    ),
                ));
                return Ok(Operand::Copy(Place::new(dst)));
            }
            if let Type::Ptr {
                mutable: src_mut,
                pointee: concrete_ty,
            } = self.compiler.program.types[src_ty.0 as usize]
                && !self.compiler.raw_ptrs.contains_key(&src_ty)
            {
                if target_tobj.mutable && !src_mut {
                    return Err(format!(
                        "Cannot coerce immutable reference '&{}' to mutable trait object '&mut {}'",
                        self.compiler.type_display_name(concrete_ty),
                        self.compiler.type_display_name(target_tobj.trait_ty)
                    ));
                }
                let (gl_id, thunk_ids) = self.compiler.get_or_create_vtable(
                    &self.mod_path,
                    concrete_ty,
                    target_tobj.trait_ty,
                )?;
                let gl_mut_ptr_ty = self.compiler.intern_type(Type::Ptr {
                    mutable: true,
                    pointee: target_tobj.vtable_ty,
                });
                let gl_mut_ptr_tmp = self.alloc_temp(gl_mut_ptr_ty);
                self.emit(Statement::Assign(
                    Place::new(gl_mut_ptr_tmp),
                    Rvalue::Use(Operand::Const(ConstValue::Global(gl_id))),
                ));
                let mut deref_gl = Place::new(gl_mut_ptr_tmp);
                deref_gl.projections.push(Projection::Deref);
                let thunk_ops = thunk_ids
                    .into_iter()
                    .map(|id| Operand::Const(ConstValue::Func(id)))
                    .collect();
                self.emit(Statement::Assign(
                    deref_gl,
                    Rvalue::Aggregate(target_tobj.vtable_ty, thunk_ops),
                ));
                let vt_ptr_tmp = self.alloc_temp(target_tobj.vtable_ptr_ty);
                self.emit(Statement::Assign(
                    Place::new(vt_ptr_tmp),
                    Rvalue::Cast(
                        Operand::Copy(Place::new(gl_mut_ptr_tmp)),
                        target_tobj.vtable_ptr_ty,
                    ),
                ));
                let data_ptr_tmp = self.alloc_temp(target_tobj.data_ptr_ty);
                self.emit(Statement::Assign(
                    Place::new(data_ptr_tmp),
                    Rvalue::Cast(op, target_tobj.data_ptr_ty),
                ));
                let dst = self.alloc_temp(target_ty);
                self.emit(Statement::Assign(
                    Place::new(dst),
                    Rvalue::Aggregate(
                        target_ty,
                        vec![
                            if target_tobj.mutable {
                                Operand::Move(Place::new(data_ptr_tmp))
                            } else {
                                Operand::Copy(Place::new(data_ptr_tmp))
                            },
                            Operand::Copy(Place::new(vt_ptr_tmp)),
                        ],
                    ),
                ));
                return Ok(if target_tobj.mutable {
                    Operand::Move(Place::new(dst))
                } else {
                    Operand::Copy(Place::new(dst))
                });
            }
            return Err(format!(
                "Cannot coerce '{}' to trait object '{}'",
                self.compiler.type_display_name(src_ty),
                self.compiler.type_display_name(target_ty)
            ));
        }
        // Coerce safe references (`&mut T` -> `&T`, `&T`/`&mut T` -> `*const T`/`*mut T`, `&T`/`&mut T` -> `&opaque`/`&mut opaque`) and raw pointers (`*mut T` -> `*const T`, `*const T`/`*mut T` -> `*const opaque`/`*mut opaque`)
        if let (
            Type::Ptr {
                mutable: src_mut,
                pointee: src_pt,
            },
            Type::Ptr {
                mutable: dst_mut,
                pointee: dst_pt,
            },
        ) = (
            self.compiler.program.types[src_ty.0 as usize].clone(),
            self.compiler.program.types[target_ty.0 as usize].clone(),
        ) && (src_pt == dst_pt || self.compiler.is_universal_opaque_type(dst_pt))
            && (!dst_mut || src_mut)
            && (!self.compiler.raw_ptrs.contains_key(&src_ty)
                || self.compiler.raw_ptrs.contains_key(&target_ty))
        {
            let tmp = self.alloc_temp(target_ty);
            self.emit(Statement::Assign(
                Place::new(tmp),
                Rvalue::Cast(op, target_ty),
            ));
            return Ok(
                if dst_mut && !self.compiler.raw_ptrs.contains_key(&target_ty) {
                    Operand::Move(Place::new(tmp))
                } else {
                    Operand::Copy(Place::new(tmp))
                },
            );
        }
        // Coerce `&[T; N]` / `&mut [T; N]` into `&[T]` / `&mut [T]`, string literals into `&str`, and `&mut [T]` into `&[T]`
        if let Some(&target_slice) = self.compiler.slices.get(&target_ty) {
            if let Operand::Const(ConstValue::Str(s)) = &op
                && !target_slice.mutable
                && matches!(
                    self.compiler.program.types[target_slice.elem.0 as usize],
                    Type::Int {
                        signed: false,
                        bits: 8
                    }
                )
            {
                let str_len = s.len() as i128;
                let str_tmp = self.alloc_temp(src_ty);
                self.emit(Statement::Assign(Place::new(str_tmp), Rvalue::Use(op)));
                let cast_ptr = self.alloc_temp(target_slice.ptr_ty);
                self.emit(Statement::Assign(
                    Place::new(cast_ptr),
                    Rvalue::Cast(Operand::Copy(Place::new(str_tmp)), target_slice.ptr_ty),
                ));
                let len_op = Operand::Const(ConstValue::I64(str_len));
                let dst = self.alloc_temp(target_ty);
                self.emit(Statement::Assign(
                    Place::new(dst),
                    Rvalue::Aggregate(target_ty, vec![Operand::Copy(Place::new(cast_ptr)), len_op]),
                ));
                return Ok(Operand::Copy(Place::new(dst)));
            }
            if let Type::Ptr {
                mutable: src_mut,
                pointee,
            } = self.compiler.program.types[src_ty.0 as usize]
                && let Type::Array {
                    elem: src_elem,
                    len: src_len,
                } = self.compiler.program.types[pointee.0 as usize]
                && src_elem == target_slice.elem
                && (!target_slice.mutable || src_mut)
            {
                let cast_ptr = self.alloc_temp(target_slice.ptr_ty);
                self.emit(Statement::Assign(
                    Place::new(cast_ptr),
                    Rvalue::Cast(op, target_slice.ptr_ty),
                ));
                let len_op = Operand::Const(ConstValue::I64(src_len as i128));
                let dst = self.alloc_temp(target_ty);
                self.emit(Statement::Assign(
                    Place::new(dst),
                    Rvalue::Aggregate(target_ty, vec![Operand::Copy(Place::new(cast_ptr)), len_op]),
                ));
                return Ok(Operand::Copy(Place::new(dst)));
            }
            if let Some(&src_slice) = self.compiler.slices.get(&src_ty)
                && src_slice.elem == target_slice.elem
                && (!target_slice.mutable || src_slice.mutable)
            {
                let src_local = match op {
                    Operand::Copy(p) | Operand::Move(p) if p.projections.is_empty() => p.local,
                    other => {
                        let tmp = self.alloc_temp(src_ty);
                        self.emit(Statement::Assign(Place::new(tmp), Rvalue::Use(other)));
                        tmp
                    }
                };
                let mut ptr_field = Place::new(src_local);
                ptr_field.projections.push(Projection::Field(0));
                let mut len_field = Place::new(src_local);
                len_field.projections.push(Projection::Field(1));
                let cast_ptr = self.alloc_temp(target_slice.ptr_ty);
                self.emit(Statement::Assign(
                    Place::new(cast_ptr),
                    Rvalue::Cast(Operand::Copy(ptr_field), target_slice.ptr_ty),
                ));
                let dst = self.alloc_temp(target_ty);
                self.emit(Statement::Assign(
                    Place::new(dst),
                    Rvalue::Aggregate(
                        target_ty,
                        vec![
                            Operand::Copy(Place::new(cast_ptr)),
                            Operand::Copy(len_field),
                        ],
                    ),
                ));
                return Ok(Operand::Copy(Place::new(dst)));
            }
        }

        // Widening coercion between `error` types (`E_src` -> `E_dst` when `E_src` is a subset of `E_dst`)
        if self.compiler.errors.contains_key(&src_ty)
            && self.compiler.errors.contains_key(&target_ty)
        {
            return self.widen_error_operand(op, src_ty, target_ty);
        }

        // Coercions into `E_dst!T_dst` (`Result` type)
        if let Some(&dst_res) = self.compiler.results.get(&target_ty) {
            if let Some(&src_res) = self.compiler.results.get(&src_ty)
                && src_res.ok_ty == dst_res.ok_ty
            {
                let u8_ty = self.compiler.intern_type(Type::Int {
                    signed: false,
                    bits: 8,
                });
                let src_local = self.alloc_temp(src_ty);
                self.emit(Statement::Assign(Place::new(src_local), Rvalue::Use(op)));
                let discr_local = self.alloc_temp(u8_ty);
                self.emit(Statement::Assign(
                    Place::new(discr_local),
                    Rvalue::Discriminant(Place::new(src_local)),
                ));
                let dst_local = self.alloc_temp(target_ty);
                let ok_bb = self.new_block();
                let err_bb = self.new_block();
                let join_bb = self.new_block();
                self.terminate(Terminator::SwitchInt {
                    discr: Operand::Copy(Place::new(discr_local)),
                    targets: vec![(0, ok_bb)],
                    otherwise: err_bb,
                });

                self.cur_block = ok_bb;
                let mut ok_place = Place::new(src_local);
                ok_place.projections.push(Projection::Variant(0));
                let ok_op = if self.is_copy_type(src_res.ok_ty) {
                    Operand::Copy(ok_place)
                } else {
                    Operand::Move(ok_place)
                };
                self.emit(Statement::Assign(
                    Place::new(dst_local),
                    Rvalue::Union {
                        ty: target_ty,
                        variant: 0,
                        payload: ok_op,
                    },
                ));
                self.terminate(Terminator::Goto { target: join_bb });

                self.cur_block = err_bb;
                let mut err_place = Place::new(src_local);
                err_place.projections.push(Projection::Variant(1));
                let err_op = if self.is_copy_type(src_res.err_ty) {
                    Operand::Copy(err_place)
                } else {
                    Operand::Move(err_place)
                };
                let widened_err =
                    self.widen_error_operand(err_op, src_res.err_ty, dst_res.err_ty)?;
                self.emit(Statement::Assign(
                    Place::new(dst_local),
                    Rvalue::Union {
                        ty: target_ty,
                        variant: 1,
                        payload: widened_err,
                    },
                ));
                self.terminate(Terminator::Goto { target: join_bb });

                self.cur_block = join_bb;
                let res_op = if self.is_copy_type(target_ty) {
                    Operand::Copy(Place::new(dst_local))
                } else {
                    Operand::Move(Place::new(dst_local))
                };
                return Ok(res_op);
            }
            if self.compiler.errors.contains_key(&src_ty)
                && !self.compiler.errors.contains_key(&dst_res.ok_ty)
            {
                let widened_err = self.widen_error_operand(op, src_ty, dst_res.err_ty)?;
                let dst_local = self.alloc_temp(target_ty);
                self.emit(Statement::Assign(
                    Place::new(dst_local),
                    Rvalue::Union {
                        ty: target_ty,
                        variant: 1,
                        payload: widened_err,
                    },
                ));
                let res_op = if self.is_copy_type(target_ty) {
                    Operand::Copy(Place::new(dst_local))
                } else {
                    Operand::Move(Place::new(dst_local))
                };
                return Ok(res_op);
            }
            let ok_op = self.coerce_operand(op, src_ty, dst_res.ok_ty)?;
            let dst_local = self.alloc_temp(target_ty);
            self.emit(Statement::Assign(
                Place::new(dst_local),
                Rvalue::Union {
                    ty: target_ty,
                    variant: 0,
                    payload: ok_op,
                },
            ));
            let res_op = if self.is_copy_type(target_ty) {
                Operand::Copy(Place::new(dst_local))
            } else {
                Operand::Move(Place::new(dst_local))
            };
            return Ok(res_op);
        }

        // Coerce `T` into `?T` (`union u8 { void, T }`)
        if !self.compiler.results.contains_key(&target_ty)
            && !self.compiler.errors.contains_key(&target_ty)
            && !self.compiler.unions.contains_key(&target_ty)
            && let Type::Union { variants, .. } = &self.compiler.program.types[target_ty.0 as usize]
            && variants.len() == 2
            && matches!(
                self.compiler.program.types[variants[0].0 as usize],
                Type::Void
            )
        {
            let inner_ty = variants[1];
            if src_ty == inner_ty && self.compiler.raw_ptrs.contains_key(&inner_ty) {
                let usize_ty = self.compiler.intern_type(Type::Int {
                    signed: false,
                    bits: 64,
                });
                let ptr_tmp = self.alloc_temp(inner_ty);
                self.emit(Statement::Assign(Place::new(ptr_tmp), Rvalue::Use(op)));
                let addr_tmp = self.alloc_temp(usize_ty);
                self.emit(Statement::Assign(
                    Place::new(addr_tmp),
                    Rvalue::Cast(Operand::Copy(Place::new(ptr_tmp)), usize_ty),
                ));
                let tmp = self.alloc_temp(target_ty);
                let null_bb = self.new_block();
                let some_bb = self.new_block();
                let join_bb = self.new_block();
                self.terminate(Terminator::SwitchInt {
                    discr: Operand::Copy(Place::new(addr_tmp)),
                    targets: vec![(0, null_bb)],
                    otherwise: some_bb,
                });
                self.cur_block = null_bb;
                self.emit(Statement::Assign(
                    Place::new(tmp),
                    Rvalue::Union {
                        ty: target_ty,
                        variant: 0,
                        payload: Operand::Const(ConstValue::Void),
                    },
                ));
                self.terminate(Terminator::Goto { target: join_bb });

                self.cur_block = some_bb;
                self.emit(Statement::Assign(
                    Place::new(tmp),
                    Rvalue::Union {
                        ty: target_ty,
                        variant: 1,
                        payload: Operand::Copy(Place::new(ptr_tmp)),
                    },
                ));
                self.terminate(Terminator::Goto { target: join_bb });

                self.cur_block = join_bb;
                return Ok(Operand::Move(Place::new(tmp)));
            }
            if src_ty == inner_ty {
                let tmp = self.alloc_temp(target_ty);
                self.emit(Statement::Assign(
                    Place::new(tmp),
                    Rvalue::Union {
                        ty: target_ty,
                        variant: 1,
                        payload: op,
                    },
                ));
                return Ok(Operand::Move(Place::new(tmp)));
            }
            if self.compiler.raw_ptrs.contains_key(&inner_ty)
                && matches!(
                    self.compiler.program.types[src_ty.0 as usize],
                    Type::Ptr { .. }
                )
            {
                let coerced_ptr = self.coerce_operand(op, src_ty, inner_ty)?;
                let tmp = self.alloc_temp(target_ty);
                self.emit(Statement::Assign(
                    Place::new(tmp),
                    Rvalue::Union {
                        ty: target_ty,
                        variant: 1,
                        payload: coerced_ptr,
                    },
                ));
                return Ok(Operand::Move(Place::new(tmp)));
            }
        }

        // Pattern type constant or subset widening
        if let Type::Pattern { base, .. } = self.compiler.program.types[target_ty.0 as usize]
            && src_ty == base
        {
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
            let tmp = self.alloc_temp(target_ty);
            self.emit(Statement::Assign(
                Place::new(tmp),
                Rvalue::Cast(src_place_op, target_ty),
            ));
            return Ok(Operand::Copy(Place::new(tmp)));
        }

        if let Type::Pattern { base, .. } = self.compiler.program.types[src_ty.0 as usize]
            && target_ty == base
        {
            let src_place_op = if matches!(op, Operand::Const(_)) {
                let src_tmp = self.alloc_temp(src_ty);
                self.emit(Statement::Assign(Place::new(src_tmp), Rvalue::Use(op)));
                Operand::Copy(Place::new(src_tmp))
            } else {
                op
            };
            let tmp = self.alloc_temp(target_ty);
            self.emit(Statement::Assign(
                Place::new(tmp),
                Rvalue::Cast(src_place_op, target_ty),
            ));
            return Ok(Operand::Copy(Place::new(tmp)));
        }

        // Opaque newtype coercion (`UserId` <-> `u64` inside `def_module`; rejected outside `def_module`)
        if let Some(nt) = self.compiler.opaque_newtypes.get(&target_ty).cloned() {
            if nt.def_module == self.mod_path && src_ty == nt.underlying {
                if matches!(op, Operand::Const(_)) {
                    return Ok(op);
                }
                let tmp = self.alloc_temp(target_ty);
                self.emit(Statement::Assign(
                    Place::new(tmp),
                    Rvalue::Cast(op, target_ty),
                ));
                return Ok(if self.is_copy_type(target_ty) {
                    Operand::Copy(Place::new(tmp))
                } else {
                    Operand::Move(Place::new(tmp))
                });
            }
            return Err(format!(
                "Type mismatch: '{}' is an opaque newtype outside module '{}' and cannot be implicitly converted from '{}'; use a constructor or explicit 'as {}' cast",
                self.compiler.type_display_name(target_ty),
                nt.def_module,
                self.compiler.type_display_name(src_ty),
                self.compiler.type_display_name(target_ty)
            ));
        }
        if let Some(nt) = self.compiler.opaque_newtypes.get(&src_ty).cloned() {
            if nt.def_module == self.mod_path && target_ty == nt.underlying {
                if matches!(op, Operand::Const(_)) {
                    return Ok(op);
                }
                let tmp = self.alloc_temp(target_ty);
                self.emit(Statement::Assign(
                    Place::new(tmp),
                    Rvalue::Cast(op, target_ty),
                ));
                return Ok(if self.is_copy_type(target_ty) {
                    Operand::Copy(Place::new(tmp))
                } else {
                    Operand::Move(Place::new(tmp))
                });
            }
            return Err(format!(
                "Type mismatch: '{}' is an opaque newtype outside module '{}' and cannot be implicitly converted to '{}'; use an explicit 'as {}' cast",
                self.compiler.type_display_name(src_ty),
                nt.def_module,
                self.compiler.type_display_name(target_ty),
                self.compiler.type_display_name(target_ty)
            ));
        }

        if !matches!(self.compiler.program.types[src_ty.0 as usize], Type::Never) {
            if self.compiler.c_ints.contains_key(&src_ty)
                || self.compiler.c_ints.contains_key(&target_ty)
            {
                return Err(format!(
                    "Type mismatch: cannot implicitly convert '{}' to '{}'; use an explicit 'as {}' cast",
                    self.compiler.type_display_name(src_ty),
                    self.compiler.type_display_name(target_ty),
                    self.compiler.type_display_name(target_ty)
                ));
            }
            if matches!(
                self.compiler.program.types[src_ty.0 as usize],
                Type::Ptr { .. }
            ) && matches!(
                self.compiler.program.types[target_ty.0 as usize],
                Type::Ptr { .. }
            ) {
                return Err(format!(
                    "Type mismatch: cannot implicitly convert '{}' to '{}'",
                    self.compiler.type_display_name(src_ty),
                    self.compiler.type_display_name(target_ty)
                ));
            }
        }

        Ok(op)
    }

    pub(super) fn widen_error_operand(
        &mut self,
        op: Operand,
        src_err_ty: TypeId,
        dst_err_ty: TypeId,
    ) -> Result<Operand, String> {
        if src_err_ty == dst_err_ty {
            return Ok(op);
        }
        let Some(src_err) = self.compiler.errors.get(&src_err_ty).cloned() else {
            return Err(format!("Type {src_err_ty} is not an `error` type"));
        };
        let Some(dst_err) = self.compiler.errors.get(&dst_err_ty).cloned() else {
            return Err(format!("Type {dst_err_ty} is not an `error` type"));
        };
        let mut mapping: Vec<(usize, usize, TypeId)> = Vec::with_capacity(src_err.leaves.len());
        for (src_idx, src_leaf) in src_err.leaves.iter().enumerate() {
            let Some((dst_idx, dst_leaf)) = dst_err
                .leaves
                .iter()
                .enumerate()
                .find(|(_, dl)| dl.key == src_leaf.key)
            else {
                return Err(format!(
                    "Error type '{}' is not a subset of '{}': missing variant '{}::{}'",
                    src_err.name, dst_err.name, src_leaf.key.error_name, src_leaf.key.variant_name
                ));
            };
            if dst_leaf.payload_ty != src_leaf.payload_ty {
                return Err(format!(
                    "Error variant '{}::{}' has conflicting payload types in '{}' and '{}'",
                    src_leaf.key.error_name, src_leaf.key.variant_name, src_err.name, dst_err.name
                ));
            }
            mapping.push((src_idx, dst_idx, src_leaf.payload_ty));
        }

        let tag_ty = self.compiler.intern_type(Type::Int {
            signed: false,
            bits: 32,
        });
        let src_local = self.alloc_temp(src_err_ty);
        self.emit(Statement::Assign(Place::new(src_local), Rvalue::Use(op)));
        let discr_local = self.alloc_temp(tag_ty);
        self.emit(Statement::Assign(
            Place::new(discr_local),
            Rvalue::Discriminant(Place::new(src_local)),
        ));
        let dst_local = self.alloc_temp(dst_err_ty);
        let join_bb = self.new_block();
        let unreach_bb = self.new_block();
        self.blocks[unreach_bb.0 as usize].terminator = Terminator::Unreachable;
        self.terminated[unreach_bb.0 as usize] = true;

        let mut targets = Vec::with_capacity(mapping.len());
        let mut branch_bbs = Vec::with_capacity(mapping.len());
        for &(src_idx, dst_idx, p_ty) in &mapping {
            let bb = self.new_block();
            targets.push((src_idx as i128, bb));
            branch_bbs.push((src_idx, dst_idx, p_ty, bb));
        }
        self.terminate(Terminator::SwitchInt {
            discr: Operand::Copy(Place::new(discr_local)),
            targets,
            otherwise: unreach_bb,
        });

        for (src_idx, dst_idx, p_ty, bb) in branch_bbs {
            self.cur_block = bb;
            let payload_op = if matches!(self.compiler.program.types[p_ty.0 as usize], Type::Void) {
                Operand::Const(ConstValue::Void)
            } else {
                let mut p_place = Place::new(src_local);
                p_place
                    .projections
                    .push(Projection::Variant(src_idx as u32));
                if self.is_copy_type(p_ty) {
                    Operand::Copy(p_place)
                } else {
                    Operand::Move(p_place)
                }
            };
            self.emit(Statement::Assign(
                Place::new(dst_local),
                Rvalue::Union {
                    ty: dst_err_ty,
                    variant: dst_idx as u32,
                    payload: payload_op,
                },
            ));
            self.terminate(Terminator::Goto { target: join_bb });
        }

        self.cur_block = join_bb;
        let res_op = if self.is_copy_type(dst_err_ty) {
            Operand::Copy(Place::new(dst_local))
        } else {
            Operand::Move(Place::new(dst_local))
        };
        Ok(res_op)
    }

    pub(super) fn lower_stmt(&mut self, stmt: &Stmt) -> Result<(), String> {
        match stmt {
            Stmt::Let { name, ty, init, .. } => {
                if matches!(ty, Some(TypeExpr::Constraint(TypeConstraint::Module))) {
                    let (_, _, ct_val) = self.compiler.eval_const_expr_typed(
                        &self.mod_path,
                        self.owner_ty,
                        &self.comptime_env,
                        init,
                        None,
                    )?;
                    if !matches!(ct_val, ComptimeVal::Module(_)) {
                        return Err(format!(
                            "Expected a module value for 'module' binding '{}'",
                            name
                        ));
                    }
                    self.comptime_env.insert(name.clone(), ct_val);
                    return Ok(());
                }
                let expected_ty = if let Some(te) = ty {
                    let resolved = self.compiler.resolve_type_expr(
                        &self.mod_path,
                        self.owner_ty,
                        &self.comptime_env,
                        te,
                    )?;
                    if let Some(tr) = self.compiler.traits.get(&resolved) {
                        return Err(format!(
                            "Trait '{}' is an unsized meta-type constraint and cannot be bound by value in 'let {}'; use '&{}' or '&mut {}'",
                            tr.name, name, tr.name, tr.name
                        ));
                    }
                    if self.compiler.is_opaque_type(resolved) {
                        return Err(format!(
                            "Unsized type '{}' cannot be bound by value in 'let {}'; use '*const {0}', '*mut {0}', '&{0}', or '&mut {0}'",
                            self.compiler.type_display_name(resolved),
                            name
                        ));
                    }
                    Some(resolved)
                } else {
                    None
                };
                if expected_ty.is_some_and(|t| self.compiler.maps.contains_key(&t))
                    || matches!(init, Expr::MapLit(_) | Expr::IntrinsicInvert(_))
                {
                    let (_, _, ct_val) = self.compiler.eval_const_expr_typed(
                        &self.mod_path,
                        self.owner_ty,
                        &self.comptime_env,
                        init,
                        expected_ty,
                    )?;
                    self.comptime_env.insert(name.clone(), ct_val);
                    return Ok(());
                }
                if matches!(init, Expr::Uninit(None))
                    && let Some(var_ty) = expected_ty
                    && self.compiler.is_uninit_compatible_type(var_ty)
                {
                    let local = self.alloc_temp(var_ty);
                    self.emit(Statement::StorageLive(local));
                    let mut init_place = Place::new(local);
                    if matches!(
                        self.compiler.program.types[var_ty.0 as usize],
                        Type::Overlay(_)
                    ) {
                        init_place.projections.push(Projection::Field(0));
                    }
                    self.emit(Statement::Assign(
                        init_place,
                        Rvalue::Use(Operand::Const(ConstValue::Void)),
                    ));
                    self.comptime_env
                        .insert(format!("__var_ty:{name}"), ComptimeVal::Type(var_ty));
                    self.scopes.last_mut().unwrap().push(ScopeVar {
                        name: name.clone(),
                        local,
                        ty: var_ty,
                        opaque_bound: None,
                    });
                    return Ok(());
                }
                self.last_call_opaque_bound = None;
                let (init_op, inferred_ty) = self.lower_expr(init, expected_ty)?;
                let mut call_opaque_bound = self.last_call_opaque_bound.take();
                if call_opaque_bound.is_none() {
                    if let Expr::Path(p) = init
                        && p.len() == 1
                    {
                        call_opaque_bound = self.lookup_var_opaque_bound(&p[0]);
                    } else if let Expr::Move(inner) = init
                        && let Expr::Path(p) = inner.as_ref()
                        && p.len() == 1
                    {
                        call_opaque_bound = self.lookup_var_opaque_bound(&p[0]);
                    }
                }
                if let Some(ref ob) = call_opaque_bound
                    && let Some(exp_ty) = expected_ty
                {
                    return Err(format!(
                        "Cannot bind existential 'opaque {:?}' return value to explicit concrete type '{}' in 'let {}'; omit the type annotation or borrow via '&Trait'",
                        ob.bound_expr,
                        self.compiler.type_display_name(exp_ty),
                        name
                    ));
                }
                if self.is_terminated() {
                    return Ok(());
                }
                let var_ty = expected_ty.unwrap_or(inferred_ty);
                let coerced_op = if inferred_ty == var_ty
                    && !matches!(
                        self.compiler.program.types[var_ty.0 as usize],
                        Type::Pattern { .. }
                    ) {
                    init_op
                } else {
                    self.coerce_operand(init_op, inferred_ty, var_ty)?
                };
                let local = self.alloc_temp(var_ty);
                self.emit(Statement::StorageLive(local));
                self.emit(Statement::Assign(
                    Place::new(local),
                    Rvalue::Use(coerced_op),
                ));
                self.comptime_env
                    .insert(format!("__var_ty:{name}"), ComptimeVal::Type(var_ty));
                self.scopes.last_mut().unwrap().push(ScopeVar {
                    name: name.clone(),
                    local,
                    ty: var_ty,
                    opaque_bound: call_opaque_bound,
                });
                Ok(())
            }
            Stmt::Assign { target, op, value } => {
                if let Expr::Field { .. } = target
                    && self.try_assign_packed_field(target, *op, value)?
                {
                    return Ok(());
                }
                if let Expr::Field { base, field } = target {
                    let (mut base_place, mut base_ty) = self.lower_place(base, true)?;
                    if let Type::Ptr { pointee, .. } =
                        self.compiler.program.types[base_ty.0 as usize]
                    {
                        base_place.projections.push(Projection::Deref);
                        base_ty = pointee;
                    }
                    if let Some(comp) = self.compiler.composites.get(&base_ty).cloned()
                        && let Ok((f_idx, _)) = self.check_field_access(base_ty, field)
                        && let Some(&rel_kind) = comp.rel_fields.get(&f_idx)
                    {
                        if op.is_some() {
                            return Err(format!(
                                "Cannot use compound assignment on '&rel' field '{}.{}'",
                                comp.name, field
                            ));
                        }
                        if self.place_traverses_immutable_ptr(&base_place) {
                            return Err(format!(
                                "Cannot assign to '&rel' field '{}.{}' through an immutable '&Self' reference",
                                comp.name, field
                            ));
                        }
                        let mut dest_field_place = base_place.clone();
                        dest_field_place.projections.push(Projection::Field(f_idx));
                        return self.assign_rel_field(
                            &comp.name,
                            field,
                            &base_place,
                            dest_field_place,
                            rel_kind,
                            value,
                        );
                    }
                    if let Some(ov_info) = self.compiler.overlays.get(&base_ty).cloned()
                        && op.is_none()
                    {
                        let Some((f_idx, (_, f_ty))) = ov_info
                            .fields
                            .iter()
                            .enumerate()
                            .find(|(_, (n, _))| n == field)
                        else {
                            return Err(format!(
                                "Overlay '{}' has no field '{}'",
                                ov_info.name, field
                            ));
                        };
                        if !self.is_copy_type(base_ty) && self.unsafe_depth == 0 {
                            return Err(format!(
                                "Writing field '{}' of non-copy overlay '{}' is unsafe and requires an 'unsafe {{ ... }}' block",
                                field, ov_info.name
                            ));
                        }
                        if self.place_traverses_immutable_ptr(&base_place) {
                            return Err(format!(
                                "Cannot assign to '{}' through an immutable reference or pointer",
                                base_place
                            ));
                        }
                        let (val_op, val_ty) = self.lower_expr(value, Some(*f_ty))?;
                        let coerced = self.coerce_operand(val_op, val_ty, *f_ty)?;
                        base_place
                            .projections
                            .push(Projection::Field(f_idx as u32));
                        self.emit(Statement::Assign(base_place, Rvalue::Use(coerced)));
                        return Ok(());
                    }
                }
                let (mut place, target_ty) = self.lower_place(target, true)?;
                if self.place_traverses_immutable_ptr(&place) {
                    if let Some((stat_name, false)) = self.static_locals.get(&place.local) {
                        return Err(format!(
                            "Cannot mutate immutable static variable '{}'",
                            stat_name
                        ));
                    }
                    return Err(format!(
                        "Cannot assign to '{}' through an immutable reference or pointer",
                        place
                    ));
                }
                if let Some(binop) = op {
                    if let Type::Ptr { pointee, .. } =
                        self.compiler.program.types[target_ty.0 as usize]
                        && self.compiler.is_opaque_type(pointee)
                        && matches!(
                            binop,
                            BinOp::Add | BinOp::AddWrap | BinOp::Sub | BinOp::SubWrap
                        )
                    {
                        return Err(format!(
                            "Cannot perform element-scaled pointer arithmetic on '{}'; cast to '*const u8' or '*mut u8' for byte offsets",
                            self.compiler.type_display_name(target_ty)
                        ));
                    }
                    let (rhs_op, rhs_ty) = self.lower_expr(value, Some(target_ty))?;
                    if let Some(nt) = self.compiler.opaque_newtypes.get(&target_ty)
                        && nt.def_module != self.mod_path
                    {
                        return Err(format!(
                            "Cannot perform operator '{}=' directly on opaque newtype '{}' outside module '{}'",
                            binop, nt.name, nt.def_module
                        ));
                    }
                    if !matches!(
                        self.compiler.program.types[target_ty.0 as usize],
                        Type::Ptr { .. }
                    ) && rhs_ty != target_ty
                        && (self.compiler.c_ints.contains_key(&target_ty)
                            || self.compiler.c_ints.contains_key(&rhs_ty))
                    {
                        return Err(format!(
                            "Type mismatch in compound assignment '{}=': cannot mix '{}' and '{}' without an explicit 'as' cast",
                            binop,
                            self.compiler.type_display_name(target_ty),
                            self.compiler.type_display_name(rhs_ty)
                        ));
                    }
                    let cur_op = Operand::Copy(place.clone());
                    self.emit(Statement::Assign(
                        place,
                        Rvalue::BinaryOp(*binop, cur_op, rhs_op),
                    ));
                } else {
                    if let Expr::Uninit(Some(inner_expr)) = value
                        && let Some(&inner_ty) = self.compiler.uninit_types.get(&target_ty)
                    {
                        let (val_op, val_ty) = self.lower_expr(inner_expr, Some(inner_ty))?;
                        let coerced = self.coerce_operand(val_op, val_ty, inner_ty)?;
                        place.projections.push(Projection::Field(1));
                        self.emit(Statement::Assign(place, Rvalue::Use(coerced)));
                        return Ok(());
                    }
                    if matches!(value, Expr::Uninit(None))
                        && self.compiler.is_uninit_compatible_type(target_ty)
                    {
                        if matches!(
                            self.compiler.program.types[target_ty.0 as usize],
                            Type::Overlay(_)
                        ) {
                            place.projections.push(Projection::Field(0));
                        }
                        self.emit(Statement::Assign(
                            place,
                            Rvalue::Use(Operand::Const(ConstValue::Void)),
                        ));
                        return Ok(());
                    }
                    // A place reached through a safe reference always holds an initialized value, so
                    // overwriting it would silently discard a linear value (raw-pointer writes into
                    // uninitialized storage, as in `Vec::push`, remain allowed).
                    if self.compiler.is_linear_type(target_ty) && self.place_traverses_safe_ref(&place)
                    {
                        return Err(format!(
                            "Cannot overwrite linear value '{}' of type '{}' through a reference; the old value would be discarded unconsumed (use 'core::mem::replace' or 'core::mem::swap')",
                            place,
                            self.compiler.type_display_name(target_ty)
                        ));
                    }
                    let (val_op, val_ty) = self.lower_expr(value, Some(target_ty))?;
                    let coerced = self.coerce_operand(val_op, val_ty, target_ty)?;
                    // Overwriting a local or a plain field path of a local drops the previous value
                    // first; drop elaboration turns this into a no-op when the path was moved out
                    // and rejects it when a still-live linear value would be discarded.
                    if self.is_local_field_path(&place) && !self.is_copy_type(target_ty) {
                        let next_bb = self.new_block();
                        self.terminate(Terminator::Drop {
                            place: place.clone(),
                            target: next_bb,
                        });
                        self.cur_block = next_bb;
                    }
                    self.emit(Statement::Assign(place, Rvalue::Use(coerced)));
                }
                Ok(())
            }
            Stmt::If {
                cond,
                then_block,
                else_block,
            } => {
                let (cond_op, _) = self.lower_expr(cond, None)?;
                let then_bb = self.new_block();
                let else_bb = self.new_block();
                self.terminate(Terminator::SwitchInt {
                    discr: cond_op,
                    targets: vec![(1, then_bb)],
                    otherwise: else_bb,
                });

                self.cur_block = then_bb;
                self.lower_scoped_block(then_block)?;
                let then_end_bb = self.cur_block;
                let then_open = !self.is_terminated();

                self.cur_block = else_bb;
                if let Some(eb) = else_block {
                    self.lower_scoped_block(eb)?;
                }
                let else_end_bb = self.cur_block;
                let else_open = !self.is_terminated();

                if then_open || else_open {
                    let join_bb = self.new_block();
                    if then_open {
                        self.blocks[then_end_bb.0 as usize].terminator =
                            Terminator::Goto { target: join_bb };
                    }
                    if else_open {
                        self.blocks[else_end_bb.0 as usize].terminator =
                            Terminator::Goto { target: join_bb };
                    }
                    self.cur_block = join_bb;
                }
                Ok(())
            }
            Stmt::IfLet {
                var_name,
                opt_expr,
                then_block,
                else_block,
            } => {
                let (opt_op, opt_ty) = self.lower_expr(opt_expr, None)?;
                let Type::Union { tag, variants } =
                    self.compiler.program.types[opt_ty.0 as usize].clone()
                else {
                    return Err("`if let` requires an optional `?T` expression".to_string());
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

                let then_bb = self.new_block();
                let else_bb = self.new_block();
                self.terminate(Terminator::SwitchInt {
                    discr: Operand::Copy(Place::new(discr_local)),
                    targets: vec![(1, then_bb)],
                    otherwise: else_bb,
                });

                self.cur_block = then_bb;
                self.scopes.push(Vec::new());
                let var_local = self.alloc_temp(payload_ty);
                self.emit(Statement::StorageLive(var_local));
                let mut payload_place = Place::new(opt_local);
                payload_place.projections.push(Projection::Variant(1));
                let payload_op = if self.is_copy_type(payload_ty) {
                    Operand::Copy(payload_place)
                } else {
                    Operand::Move(payload_place)
                };
                self.emit(Statement::Assign(
                    Place::new(var_local),
                    Rvalue::Use(payload_op),
                ));
                self.comptime_env
                    .insert(format!("__var_ty:{var_name}"), ComptimeVal::Type(payload_ty));
                self.scopes.last_mut().unwrap().push(ScopeVar {
                    name: var_name.clone(),
                    local: var_local,
                    ty: payload_ty,
                    opaque_bound: None,
                });
                self.lower_block_stmts(then_block)?;
                if !self.is_terminated() {
                    self.cleanup_top_scope();
                }
                let then_end_bb = self.cur_block;
                let then_open = !self.is_terminated();
                self.scopes.pop();

                self.cur_block = else_bb;
                if let Some(eb) = else_block {
                    self.lower_scoped_block(eb)?;
                }
                let else_end_bb = self.cur_block;
                let else_open = !self.is_terminated();

                if then_open || else_open {
                    let join_bb = self.new_block();
                    if then_open {
                        self.blocks[then_end_bb.0 as usize].terminator =
                            Terminator::Goto { target: join_bb };
                    }
                    if else_open {
                        self.blocks[else_end_bb.0 as usize].terminator =
                            Terminator::Goto { target: join_bb };
                    }
                    self.cur_block = join_bb;
                }
                Ok(())
            }
            Stmt::While { cond, body } => {
                let cond_bb = self.new_block();
                let body_bb = self.new_block();
                let exit_bb = self.new_block();
                self.terminate(Terminator::Goto { target: cond_bb });

                self.cur_block = cond_bb;
                let (cond_op, _) = self.lower_expr(cond, None)?;
                self.terminate(Terminator::SwitchInt {
                    discr: cond_op,
                    targets: vec![(1, body_bb)],
                    otherwise: exit_bb,
                });

                self.cur_block = body_bb;
                self.lower_scoped_block(body)?;
                if !self.is_terminated() {
                    self.terminate(Terminator::Goto { target: cond_bb });
                }

                self.cur_block = exit_bb;
                Ok(())
            }
            Stmt::Match { scrutinee, arms } => {
                let void_ty = self.compiler.intern_type(Type::Void);
                let _ = self.lower_match(scrutinee, arms, Some(void_ty), true)?;
                Ok(())
            }
            Stmt::Return(opt_expr) => {
                if let TypeExpr::OpaqueTrait(bound_expr) = self.decl.ret_ty.clone() {
                    let Some(expr) = opt_expr else {
                        return Err(format!(
                            "Function '{}' with '-> opaque ...' return type must return a value",
                            self.decl.name
                        ));
                    };
                    let (op, expr_ty) = self.lower_expr(expr, self.inferred_opaque_ret)?;
                    if self.is_terminated() {
                        return Ok(());
                    }
                    let ret_ty = self.check_opaque_ret_expr(&bound_expr, expr_ty)?;
                    let coerced = self.coerce_operand(op, expr_ty, ret_ty)?;
                    self.emit(Statement::Assign(
                        Place::new(LocalId(0)),
                        Rvalue::Use(coerced),
                    ));
                    self.cleanup_all_scopes();
                    self.terminate(Terminator::Return);
                    return Ok(());
                }
                let ret_ty = self.locals[0];
                if let Some(expr) = opt_expr {
                    let (op, expr_ty) = self.lower_expr(expr, Some(ret_ty))?;
                    if self.is_terminated() {
                        return Ok(());
                    }
                    let coerced = self.coerce_operand(op, expr_ty, ret_ty)?;
                    self.emit(Statement::Assign(
                        Place::new(LocalId(0)),
                        Rvalue::Use(coerced),
                    ));
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
                self.cleanup_all_scopes();
                self.terminate(Terminator::Return);
                Ok(())
            }
            Stmt::Unsafe(blk) => {
                self.unsafe_depth += 1;
                let res = self.lower_scoped_block(blk);
                self.unsafe_depth -= 1;
                res
            }
            Stmt::Expr(expr) => {
                let (op, ty) = self.lower_expr(expr, None)?;
                if !self.is_terminated()
                    && !self.is_copy_type(ty)
                    && let Operand::Move(place) = op
                {
                    let next_bb = self.new_block();
                    self.terminate(Terminator::Drop {
                        place,
                        target: next_bb,
                    });
                    self.cur_block = next_bb;
                }
                Ok(())
            }
        }
    }

    pub(super) fn is_copy_type(&self, ty_id: TypeId) -> bool {
        self.compiler.is_copy_type(ty_id)
    }

    pub(super) fn check_field_access(
        &self,
        comp_ty: TypeId,
        field_name: &str,
    ) -> Result<(u32, TypeId), String> {
        let Some(comp) = self.compiler.composites.get(&comp_ty) else {
            return Err(format!("Type {comp_ty} has no named fields"));
        };
        let Some((idx, (_, f_ty, f_vis, _))) = comp
            .fields
            .iter()
            .enumerate()
            .find(|(_, (n, _, _, _))| n == field_name)
        else {
            return Err(format!(
                "Type '{}' has no field '{}'",
                comp.name, field_name
            ));
        };
        if comp.is_struct && *f_vis == Visibility::Private && !self.has_private_access(comp_ty) {
            return Err(format!(
                "Cannot access private field '{}' of opaque '{}' outside its 'opaque {{ ... }}' block",
                field_name, comp.name
            ));
        }
        if *f_vis == Visibility::Private && comp.def_module != self.mod_path {
            return Err(format!(
                "Field '{}' of '{}' is private to module '{}'",
                field_name, comp.name, comp.def_module
            ));
        }
        Ok((idx as u32, *f_ty))
    }

    pub(super) fn materialize_static_place(
        &mut self,
        gl_id: GlobalId,
        ty: TypeId,
        is_mut: bool,
        display_name: &str,
        for_write_or_move: bool,
    ) -> Result<(Place, TypeId), String> {
        if !is_mut && for_write_or_move && self.raw_addr_of_depth == 0 {
            return Err(format!(
                "Cannot mutate or mutably borrow immutable static variable '{}'",
                display_name
            ));
        }
        if is_mut && self.unsafe_depth == 0 && self.raw_addr_of_depth == 0 {
            return Err(format!(
                "Use of mutable static '{}' is unsafe and requires an 'unsafe {{ ... }}' block",
                display_name
            ));
        }
        let ptr_ty = self.compiler.intern_type(Type::Ptr {
            mutable: is_mut,
            pointee: ty,
        });
        let ptr_local = self.alloc_temp(ptr_ty);
        self.static_locals
            .insert(ptr_local, (display_name.to_string(), is_mut));
        self.emit(Statement::Assign(
            Place::new(ptr_local),
            Rvalue::Use(Operand::Const(ConstValue::Global(gl_id))),
        ));
        Ok((
            Place {
                local: ptr_local,
                projections: vec![Projection::Deref],
            },
            ty,
        ))
    }

    pub(super) fn try_resolve_const_or_static_path(
        &mut self,
        p: &[String],
        expected_ty: Option<TypeId>,
    ) -> Result<Option<Result<(ConstValue, TypeId), (GlobalId, TypeId, bool, String)>>, String>
    {
        let expanded = self.compiler.expand_module_path(&self.comptime_env, p);
        let p = &expanded;
        if p.len() >= 2 {
            let prefix = &p[..p.len() - 1];
            let member = p.last().unwrap();
            let comp_ty_opt = if prefix.len() == 1 && prefix[0] == "Self" {
                self.owner_ty
            } else if prefix.len() == 1
                && let Some(ComptimeVal::Type(t_id)) = self.comptime_env.get(&prefix[0])
            {
                Some(*t_id)
            } else if let Ok(ResolvedItem::Type(tmod, tname)) =
                self.compiler.resolve_path(&self.mod_path, prefix)
            {
                Some(self.compiler.resolve_named_type(&tmod, &tname)?)
            } else {
                None
            };
            if let Some(comp_ty) = comp_ty_opt {
                if let Some(comp) = self.compiler.composites.get(&comp_ty)
                    && comp.consts.contains_key(member)
                {
                    let (cval, cty, _, cvis, has_explicit_ty) =
                        self.compiler.resolve_associated_const(comp_ty, member)?;
                    let comp = &self.compiler.composites[&comp_ty];
                    if comp.is_struct
                        && cvis == Visibility::Private
                        && !self.has_private_access(comp_ty)
                    {
                        return Err(format!(
                            "Cannot access private constant '{}::{}' outside its 'opaque {{ ... }}' block",
                            comp.name, member
                        ));
                    }
                    if cvis == Visibility::Private && comp.def_module != self.mod_path {
                        return Err(format!(
                            "Constant '{}::{}' is private to module '{}'",
                            comp.name, member, comp.def_module
                        ));
                    }
                    let final_ty = if !has_explicit_ty
                        && matches!(cval, ConstValue::I64(_))
                        && let Some(exp) = expected_ty
                        && matches!(
                            self.compiler.program.types[exp.0 as usize],
                            Type::Int { .. } | Type::Pattern { .. }
                        ) {
                        exp
                    } else {
                        cty
                    };
                    return Ok(Some(Ok((cval, final_ty))));
                }
                if let Some(comp) = self.compiler.composites.get(&comp_ty)
                    && comp.statics.contains_key(member)
                {
                    let (gl_id, sty, is_mut, svis) =
                        self.compiler.resolve_associated_static(comp_ty, member)?;
                    let comp = &self.compiler.composites[&comp_ty];
                    if comp.is_struct
                        && svis == Visibility::Private
                        && !self.has_private_access(comp_ty)
                    {
                        return Err(format!(
                            "Cannot access private static '{}::{}' outside its 'opaque {{ ... }}' block",
                            comp.name, member
                        ));
                    }
                    if svis == Visibility::Private && comp.def_module != self.mod_path {
                        return Err(format!(
                            "Static '{}::{}' is private to module '{}'",
                            comp.name, member, comp.def_module
                        ));
                    }
                    return Ok(Some(Err((gl_id, sty, is_mut, p.join("::")))));
                }
            }
        }
        match self.compiler.resolve_path(&self.mod_path, p) {
            Ok(ResolvedItem::Const(cmod, cname)) => {
                let (cval, cty, _, has_explicit_ty) =
                    self.compiler.resolve_top_const(&cmod, &cname)?;
                let final_ty = if !has_explicit_ty
                    && matches!(cval, ConstValue::I64(_))
                    && let Some(exp) = expected_ty
                    && matches!(
                        self.compiler.program.types[exp.0 as usize],
                        Type::Int { .. } | Type::Pattern { .. }
                    ) {
                    exp
                } else {
                    cty
                };
                Ok(Some(Ok((cval, final_ty))))
            }
            Ok(ResolvedItem::Static(smod, sname)) => {
                let (gl_id, sty, is_mut) = self.compiler.resolve_top_static(&smod, &sname)?;
                Ok(Some(Err((gl_id, sty, is_mut, p.join("::")))))
            }
            _ => Ok(None),
        }
    }

    #[allow(clippy::only_used_in_recursion)]
    pub(super) fn lower_place(
        &mut self,
        expr: &Expr,
        for_write_or_move: bool,
    ) -> Result<(Place, TypeId), String> {
        match expr {
            Expr::Path(p) => {
                if p.len() == 1 {
                    if let Some((local, ty)) = self.lookup_var(&p[0]) {
                        return Ok((Place::new(local), ty));
                    }
                    if let Some((cap_place, ty)) = self.lookup_capture(&p[0]) {
                        return Ok((cap_place, ty));
                    }
                }
                if let Some(res) = self.try_resolve_const_or_static_path(p, None)? {
                    match res {
                        Ok((cval, cty)) => {
                            if for_write_or_move {
                                return Err(format!(
                                    "Cannot mutate or mutably borrow constant '{}'",
                                    p.join("::")
                                ));
                            }
                            let tmp = self.alloc_temp(cty);
                            self.emit(Statement::Assign(
                                Place::new(tmp),
                                Rvalue::Use(Operand::Const(cval)),
                            ));
                            return Ok((Place::new(tmp), cty));
                        }
                        Err((gl_id, sty, is_mut, disp)) => {
                            return self.materialize_static_place(
                                gl_id,
                                sty,
                                is_mut,
                                &disp,
                                for_write_or_move,
                            );
                        }
                    }
                }
                if p.len() == 1 {
                    Err(format!("Undefined local variable '{}'", p[0]))
                } else {
                    let saved_raw = self.raw_addr_of_depth;
                    self.raw_addr_of_depth = 0;
                    let res = self.lower_expr(expr, None);
                    self.raw_addr_of_depth = saved_raw;
                    let (op, ty) = res?;
                    let tmp = self.alloc_temp(ty);
                    self.emit(Statement::Assign(Place::new(tmp), Rvalue::Use(op)));
                    Ok((Place::new(tmp), ty))
                }
            }
            Expr::Deref(inner) => {
                let (mut place, ty) = self.lower_place(inner, for_write_or_move)?;
                let Type::Ptr { pointee, .. } = self.compiler.program.types[ty.0 as usize] else {
                    return Err(format!("Cannot dereference non-pointer type {ty}"));
                };
                if self.compiler.is_opaque_type(pointee) {
                    return Err(format!(
                        "Cannot dereference pointer of type '{}'; 'opaque' has unknown size and layout (cast to a concrete pointer type first)",
                        self.compiler.type_display_name(ty)
                    ));
                }
                if self.compiler.raw_ptrs.contains_key(&ty) && self.unsafe_depth == 0 {
                    return Err(format!(
                        "Dereferencing raw pointer of type '{}' is unsafe and requires an 'unsafe {{ ... }}' block",
                        self.compiler.type_display_name(ty)
                    ));
                }
                place.projections.push(Projection::Deref);
                Ok((place, pointee))
            }
            Expr::Field { base, field } => {
                if let Some(root_var) = Self::root_var_of_place_expr(base)
                    && let Some(ob) = self.lookup_var_opaque_bound(root_var)
                {
                    return Err(format!(
                        "Cannot access concrete field '{}' on existential 'opaque {:?}' value '{}'; only methods from its trait bound are accessible",
                        field, ob.bound_expr, root_var
                    ));
                }
                let (mut place, mut base_ty) = self.lower_place(base, for_write_or_move)?;
                // Auto-deref reference/pointer on field access (`self.x`)
                if let Type::Ptr { pointee, .. } = self.compiler.program.types[base_ty.0 as usize] {
                    if self.compiler.raw_ptrs.contains_key(&base_ty) && self.unsafe_depth == 0 {
                        return Err(format!(
                            "Dereferencing raw pointer of type '{}' for field access '{}' is unsafe and requires an 'unsafe {{ ... }}' block",
                            self.compiler.type_display_name(base_ty),
                            field
                        ));
                    }
                    place.projections.push(Projection::Deref);
                    base_ty = pointee;
                }
                if field == "len" {
                    let usize_ty = self.compiler.intern_type(Type::Int {
                        signed: false,
                        bits: 64,
                    });
                    if self.compiler.slices.contains_key(&base_ty) {
                        place.projections.push(Projection::Field(1));
                        return Ok((place, usize_ty));
                    }
                    if let Type::Array { len, .. } | Type::Simd { len, .. } =
                        self.compiler.program.types[base_ty.0 as usize]
                    {
                        let len_tmp = self.alloc_temp(usize_ty);
                        self.emit(Statement::Assign(
                            Place::new(len_tmp),
                            Rvalue::Use(Operand::Const(ConstValue::I64(len as i128))),
                        ));
                        return Ok((Place::new(len_tmp), usize_ty));
                    }
                }
                if let Some(&inner_ty) = self.compiler.uninit_types.get(&base_ty) {
                    if field != "assume_init" {
                        return Err(format!(
                            "Type '{}' has no field '{}'; use '.assume_init' inside an 'unsafe {{ ... }}' block",
                            self.compiler.type_display_name(base_ty),
                            field
                        ));
                    }
                    if self.unsafe_depth == 0 {
                        return Err(format!(
                            "Accessing '.assume_init' on '{}' is unsafe and requires an 'unsafe {{ ... }}' block",
                            self.compiler.type_display_name(base_ty)
                        ));
                    }
                    place.projections.push(Projection::Field(1));
                    return Ok((place, inner_ty));
                }
                if let Some(ov_info) = self.compiler.overlays.get(&base_ty).cloned() {
                    let Some((f_idx, (_, f_ty))) = ov_info
                        .fields
                        .iter()
                        .enumerate()
                        .find(|(_, (n, _))| n == field)
                    else {
                        return Err(format!(
                            "Overlay '{}' has no field '{}'",
                            ov_info.name, field
                        ));
                    };
                    if self.unsafe_depth == 0 {
                        return Err(format!(
                            "Accessing field '{}' of overlay '{}' is unsafe and requires an 'unsafe {{ ... }}' block",
                            field, ov_info.name
                        ));
                    }
                    place.projections.push(Projection::Field(f_idx as u32));
                    return Ok((place, *f_ty));
                }
                let (f_idx, f_ty) = self.check_field_access(base_ty, field)?;
                if let Some(comp) = self.compiler.composites.get(&base_ty) {
                    if comp.is_packed {
                        return Err(format!(
                            "Cannot take a reference or pointer to bit-packed field '{}.{}' of packed type '{}' because it is not guaranteed to be byte-aligned",
                            comp.name, field, comp.name
                        ));
                    }
                    if let Some(&rel_kind) = comp.rel_fields.get(&f_idx) {
                        let comp_name = comp.name.clone();
                        return self.resolve_rel_field_access(
                            &comp_name,
                            field,
                            place,
                            f_idx,
                            base_ty,
                            rel_kind,
                            for_write_or_move,
                        );
                    }
                }
                place.projections.push(Projection::Field(f_idx));
                Ok((place, f_ty))
            }
            Expr::TupleIndex { base, index } => {
                let (mut place, mut base_ty) = self.lower_place(base, for_write_or_move)?;
                if let Type::Ptr { pointee, .. } = self.compiler.program.types[base_ty.0 as usize] {
                    if self.compiler.raw_ptrs.contains_key(&base_ty) && self.unsafe_depth == 0 {
                        return Err(format!(
                            "Dereferencing raw pointer of type '{}' is unsafe and requires an 'unsafe {{ ... }}' block",
                            self.compiler.type_display_name(base_ty)
                        ));
                    }
                    place.projections.push(Projection::Deref);
                    base_ty = pointee;
                }
                let fields = match &self.compiler.program.types[base_ty.0 as usize] {
                    Type::Struct(fields) => fields,
                    Type::Overlay(fields) => {
                        if self.unsafe_depth == 0 && !for_write_or_move {
                            return Err(format!(
                                "Accessing field '.{index}' of overlay '{}' is unsafe and requires an 'unsafe {{ ... }}' block",
                                self.compiler.type_display_name(base_ty)
                            ));
                        }
                        fields
                    }
                    _ => return Err(format!("Cannot tuple-index non-tuple type {base_ty}")),
                };
                let &elem_ty = fields
                    .get(*index as usize)
                    .ok_or_else(|| format!("Tuple index .{index} out of bounds"))?;
                place.projections.push(Projection::Field(*index));
                Ok((place, elem_ty))
            }
            Expr::Index { base, index } => {
                let (mut place, mut base_ty) = self.lower_place(base, for_write_or_move)?;
                if let Type::Ptr { pointee, .. } = self.compiler.program.types[base_ty.0 as usize] {
                    if self.compiler.raw_ptrs.contains_key(&base_ty) && self.unsafe_depth == 0 {
                        return Err(format!(
                            "Dereferencing raw pointer of type '{}' is unsafe and requires an 'unsafe {{ ... }}' block",
                            self.compiler.type_display_name(base_ty)
                        ));
                    }
                    place.projections.push(Projection::Deref);
                    base_ty = pointee;
                }
                // The bound checked before indexing: the slice's `len` field, or a static length.
                let (elem_ty, bound) = if let Some(&slice_info) = self.compiler.slices.get(&base_ty) {
                    let mut len_place = place.clone();
                    len_place.projections.push(Projection::Field(1));
                    place.projections.push(Projection::Field(0));
                    place.projections.push(Projection::Deref);
                    (slice_info.elem, IndexBound::Dynamic(len_place))
                } else {
                    match self.compiler.program.types[base_ty.0 as usize] {
                        // `[T; 0]` reached through a raw pointer or inside `unsafe` is the C
                        // flexible-array idiom: unchecked.
                        Type::Array { elem, len: 0 }
                            if self.unsafe_depth > 0 || self.place_traverses_raw_ptr(&place) =>
                        {
                            (elem, IndexBound::Unchecked)
                        }
                        Type::Array { elem, len } | Type::Simd { elem, len } => {
                            (elem, IndexBound::Static(len))
                        }
                        _ => {
                            return Err(format!(
                                "Cannot index non-array/slice/simd type {base_ty}"
                            ));
                        }
                    }
                };
                let u64_ty = self.compiler.intern_type(Type::Int {
                    signed: false,
                    bits: 64,
                });
                let saved_raw = self.raw_addr_of_depth;
                self.raw_addr_of_depth = 0;
                let idx_res = self.lower_expr(index, Some(u64_ty));
                self.raw_addr_of_depth = saved_raw;
                let (idx_op, idx_ty) = idx_res?;
                let const_idx = match &idx_op {
                    Operand::Const(ConstValue::I64(n)) => Some(*n),
                    _ => None,
                };
                let idx_local = self.alloc_temp(u64_ty);
                self.emit(Statement::Assign(
                    Place::new(idx_local),
                    Rvalue::Use(idx_op),
                ));
                self.emit_index_bounds_check(idx_local, idx_ty, const_idx, bound)?;
                place.projections.push(Projection::Index(idx_local));
                Ok((place, elem_ty))
            }
            _ => {
                // Materialize rvalue into a temporary local place
                let saved_raw = self.raw_addr_of_depth;
                self.raw_addr_of_depth = 0;
                let res = self.lower_expr(expr, None);
                self.raw_addr_of_depth = saved_raw;
                let (op, ty) = res?;
                let tmp = self.alloc_temp(ty);
                self.emit(Statement::Assign(Place::new(tmp), Rvalue::Use(op)));
                Ok((Place::new(tmp), ty))
            }
        }
    }

    pub(super) fn place_type(&self, place: &Place) -> TypeId {
        let mut ty = self.locals[place.local.0 as usize];
        for proj in &place.projections {
            match proj {
                Projection::Deref => {
                    if let Type::Ptr { pointee, .. } = self.compiler.program.types[ty.0 as usize] {
                        ty = pointee;
                    }
                }
                Projection::Field(idx) => {
                    if let Type::Struct(fields) | Type::Overlay(fields) =
                        &self.compiler.program.types[ty.0 as usize]
                    {
                        ty = fields[*idx as usize];
                    }
                }
                Projection::Variant(idx) => {
                    if let Type::Union { variants, .. } =
                        &self.compiler.program.types[ty.0 as usize]
                    {
                        ty = variants[*idx as usize];
                    }
                }
                Projection::Index(_) => match self.compiler.program.types[ty.0 as usize] {
                    Type::Array { elem, .. } | Type::Simd { elem, .. } => ty = elem,
                    _ => {}
                },
            }
        }
        ty
    }

    /// Traps (`@llvm.trap()` / VM error) unless `idx_local < bound`. Skipped when the bound is
    /// statically proven: a constant index below a static length, or a pattern-typed index
    /// (`usize in Lo..=Hi`) whose largest value is below it. A constant index at or past a static
    /// length is a compile-time error.
    pub(super) fn emit_index_bounds_check(
        &mut self,
        idx_local: LocalId,
        idx_ty: TypeId,
        const_idx: Option<i128>,
        bound: IndexBound,
    ) -> Result<(), String> {
        let len_op = match bound {
            IndexBound::Unchecked => return Ok(()),
            IndexBound::Static(len) => {
                if let Some(n) = const_idx {
                    if n < 0 || n as u128 >= u128::from(len) {
                        return Err(format!(
                            "Index {n} is out of bounds for length {len}"
                        ));
                    }
                    return Ok(());
                }
                if let Type::Pattern { ranges, .. } = &self.compiler.program.types[idx_ty.0 as usize]
                    && ranges.iter().all(|&(lo, hi)| lo >= 0 && (hi as u128) < u128::from(len))
                {
                    return Ok(());
                }
                Operand::Const(ConstValue::I64(i128::from(len)))
            }
            IndexBound::Dynamic(len_place) => Operand::Copy(len_place),
        };
        let bool_ty = self.compiler.intern_type(Type::Bool);
        let in_bounds = self.alloc_temp(bool_ty);
        self.emit(Statement::Assign(
            Place::new(in_bounds),
            Rvalue::BinaryOp(BinOp::Lt, Operand::Copy(Place::new(idx_local)), len_op),
        ));
        let trap_bb = self.new_block();
        let ok_bb = self.new_block();
        self.terminate(Terminator::SwitchInt {
            discr: Operand::Copy(Place::new(in_bounds)),
            targets: vec![(0, trap_bb)],
            otherwise: ok_bb,
        });
        self.cur_block = trap_bb;
        self.terminate(Terminator::Unreachable);
        self.cur_block = ok_bb;
        Ok(())
    }

    /// Traps unless `end_local <= bound` (the end of a range slice may equal the length). A constant
    /// end past a static length is a compile-time error.
    pub(super) fn emit_range_end_check(
        &mut self,
        end_local: LocalId,
        end_ty: TypeId,
        const_end: Option<i128>,
        bound: IndexBound,
    ) -> Result<(), String> {
        let len_op = match bound {
            IndexBound::Unchecked => return Ok(()),
            IndexBound::Static(len) => {
                if let Some(n) = const_end {
                    if n < 0 || n as u128 > u128::from(len) {
                        return Err(format!(
                            "Slice end {n} is out of bounds for length {len}"
                        ));
                    }
                    return Ok(());
                }
                if let Type::Pattern { ranges, .. } = &self.compiler.program.types[end_ty.0 as usize]
                    && ranges.iter().all(|&(lo, hi)| lo >= 0 && (hi as u128) <= u128::from(len))
                {
                    return Ok(());
                }
                Operand::Const(ConstValue::I64(i128::from(len)))
            }
            IndexBound::Dynamic(len_place) => Operand::Copy(len_place),
        };
        let bool_ty = self.compiler.intern_type(Type::Bool);
        let in_bounds = self.alloc_temp(bool_ty);
        self.emit(Statement::Assign(
            Place::new(in_bounds),
            Rvalue::BinaryOp(BinOp::Le, Operand::Copy(Place::new(end_local)), len_op),
        ));
        let trap_bb = self.new_block();
        let ok_bb = self.new_block();
        self.terminate(Terminator::SwitchInt {
            discr: Operand::Copy(Place::new(in_bounds)),
            targets: vec![(0, trap_bb)],
            otherwise: ok_bb,
        });
        self.cur_block = trap_bb;
        self.terminate(Terminator::Unreachable);
        self.cur_block = ok_bb;
        Ok(())
    }

    /// Whether `place` dereferences a raw pointer (`*const T` / `*mut T`) anywhere along its path.
    pub(super) fn place_traverses_raw_ptr(&self, place: &Place) -> bool {
        let mut ty = self.locals[place.local.0 as usize];
        for proj in &place.projections {
            match proj {
                Projection::Deref => {
                    if self.compiler.raw_ptrs.contains_key(&ty) {
                        return true;
                    }
                    if let Type::Ptr { pointee, .. } = self.compiler.program.types[ty.0 as usize] {
                        ty = pointee;
                    }
                }
                Projection::Field(idx) => {
                    if let Type::Struct(fields) | Type::Overlay(fields) =
                        &self.compiler.program.types[ty.0 as usize]
                    {
                        ty = fields[*idx as usize];
                    }
                }
                Projection::Variant(idx) => {
                    if let Type::Union { variants, .. } =
                        &self.compiler.program.types[ty.0 as usize]
                    {
                        ty = variants[*idx as usize];
                    }
                }
                Projection::Index(_) => {
                    if let Type::Array { elem, .. } | Type::Simd { elem, .. } =
                        self.compiler.program.types[ty.0 as usize]
                    {
                        ty = elem;
                    }
                }
            }
        }
        false
    }

    /// Whether `place` is a local or a chain of struct field projections on a local (no derefs,
    /// indexing, variants, or overlay fields), i.e. a path tracked by Stage 3b move analysis.
    pub(super) fn is_local_field_path(&self, place: &Place) -> bool {
        let mut ty = self.locals[place.local.0 as usize];
        for proj in &place.projections {
            let Projection::Field(idx) = proj else {
                return false;
            };
            let Type::Struct(fields) = &self.compiler.program.types[ty.0 as usize] else {
                return false;
            };
            ty = fields[*idx as usize];
        }
        true
    }

    pub(super) fn place_traverses_safe_ref(&self, place: &Place) -> bool {
        let mut ty = self.locals[place.local.0 as usize];
        let mut traverses = false;
        for proj in &place.projections {
            match proj {
                Projection::Deref => {
                    if !self.compiler.raw_ptrs.contains_key(&ty) {
                        traverses = true;
                    }
                    if let Type::Ptr { pointee, .. } = self.compiler.program.types[ty.0 as usize] {
                        ty = pointee;
                    }
                }
                Projection::Field(idx) => match &self.compiler.program.types[ty.0 as usize] {
                    Type::Struct(fields) => {
                        ty = fields[*idx as usize];
                    }
                    Type::Overlay(fields) => {
                        // Moving out of an overlay / `uninit T` field (e.g., `.assume_init` in `unsafe`)
                        // through a mutable reference is permitted because the overlay container is left intact.
                        if !self.place_traverses_immutable_ptr(place) {
                            traverses = false;
                        }
                        ty = fields[*idx as usize];
                    }
                    _ => {}
                },
                Projection::Variant(idx) => {
                    if let Type::Union { variants, .. } =
                        &self.compiler.program.types[ty.0 as usize]
                    {
                        ty = variants[*idx as usize];
                    }
                }
                Projection::Index(_) => match self.compiler.program.types[ty.0 as usize] {
                    Type::Array { elem, .. } | Type::Simd { elem, .. } => ty = elem,
                    _ => {}
                },
            }
        }
        traverses
    }

    pub(super) fn place_traverses_immutable_ptr(&self, place: &Place) -> bool {
        let mut ty = self.locals[place.local.0 as usize];
        for proj in &place.projections {
            match proj {
                Projection::Deref => {
                    if let Type::Ptr { mutable, pointee } =
                        self.compiler.program.types[ty.0 as usize]
                    {
                        if !mutable {
                            return true;
                        }
                        ty = pointee;
                    }
                }
                Projection::Field(idx) => {
                    if let Type::Struct(fields) | Type::Overlay(fields) =
                        &self.compiler.program.types[ty.0 as usize]
                    {
                        ty = fields[*idx as usize];
                    }
                }
                Projection::Variant(idx) => {
                    if let Type::Union { variants, .. } =
                        &self.compiler.program.types[ty.0 as usize]
                    {
                        ty = variants[*idx as usize];
                    }
                }
                Projection::Index(_) => match self.compiler.program.types[ty.0 as usize] {
                    Type::Array { elem, .. } | Type::Simd { elem, .. } => ty = elem,
                    _ => {}
                },
            }
        }
        false
    }

    pub(super) fn verify_rel_coresidence(
        &self,
        struct_name: &str,
        field_name: &str,
        base_place: &Place,
        dest_field_place: &Place,
        rhs_place: &Place,
    ) -> Result<(), String> {
        if rhs_place.local != base_place.local
            || !rhs_place.projections.starts_with(&base_place.projections)
            || rhs_place.projections.len() <= base_place.projections.len()
        {
            return Err(format!(
                "Co-Residence violation on '{}.{}': '&rel' target must reside inside the enclosing struct 'self' (cannot reference an outer local variable or temporary)",
                struct_name, field_name
            ));
        }
        let rel_projs = &rhs_place.projections[base_place.projections.len()..];
        let mut cur_ty = self.place_type(base_place);
        for proj in rel_projs {
            match proj {
                Projection::Deref => {
                    return Err(format!(
                        "Co-Residence violation on '{}.{}': '&rel' target must be inline storage within 'self' and cannot traverse a pointer or slice dereference",
                        struct_name, field_name
                    ));
                }
                Projection::Variant(_) => {
                    return Err(format!(
                        "Co-Residence violation on '{}.{}': '&rel' target cannot reside inside a union variant or overlay field",
                        struct_name, field_name
                    ));
                }
                Projection::Field(idx) => match &self.compiler.program.types[cur_ty.0 as usize] {
                    Type::Struct(fields) => {
                        if let Some(&fty) = fields.get(*idx as usize) {
                            cur_ty = fty;
                        }
                    }
                    Type::Overlay(_) | Type::Union { .. } => {
                        return Err(format!(
                            "Co-Residence violation on '{}.{}': '&rel' target cannot reside inside a union variant or overlay field",
                            struct_name, field_name
                        ));
                    }
                    _ => {}
                },
                Projection::Index(_) => {
                    if let Type::Array { elem, .. } | Type::Simd { elem, .. } =
                        self.compiler.program.types[cur_ty.0 as usize]
                    {
                        cur_ty = elem;
                    }
                }
            }
        }
        if rhs_place
            .projections
            .starts_with(&dest_field_place.projections)
        {
            return Err(format!(
                "Co-Residence violation on '{}.{}': '&rel' field cannot point to itself",
                struct_name, field_name
            ));
        }
        Ok(())
    }

    pub(super) fn assign_rel_field(
        &mut self,
        struct_name: &str,
        field_name: &str,
        base_place: &Place,
        dest_field_place: Place,
        rel_kind: RelFieldKind,
        val_expr: &Expr,
    ) -> Result<(), String> {
        let Expr::RelRef(target_expr) = val_expr else {
            return Err(format!(
                "Field '{}' of struct '{}' is a relative reference and must be initialized or assigned with '&rel <place>'",
                field_name, struct_name
            ));
        };
        let isize_ty = self.compiler.intern_type(Type::Int {
            signed: true,
            bits: 64,
        });
        let usize_ty = self.compiler.intern_type(Type::Int {
            signed: false,
            bits: 64,
        });
        match rel_kind {
            RelFieldKind::Elem(expected_elem_ty) => {
                let (rhs_place, rhs_ty) = self.lower_place(target_expr, false)?;
                if rhs_ty != expected_elem_ty {
                    return Err(format!(
                        "Type mismatch in '&rel' assignment to '{}.{}': expected target of type {}, found {}",
                        struct_name,
                        field_name,
                        self.compiler.program.types[expected_elem_ty.0 as usize],
                        self.compiler.program.types[rhs_ty.0 as usize]
                    ));
                }
                self.verify_rel_coresidence(
                    struct_name,
                    field_name,
                    base_place,
                    &dest_field_place,
                    &rhs_place,
                )?;
                let target_ptr_ty = self.compiler.intern_type(Type::Ptr {
                    mutable: false,
                    pointee: rhs_ty,
                });
                let target_ptr_tmp = self.alloc_temp(target_ptr_ty);
                self.emit(Statement::Assign(
                    Place::new(target_ptr_tmp),
                    Rvalue::Ref {
                        mutable: false,
                        place: rhs_place,
                    },
                ));
                let target_addr_tmp = self.alloc_temp(isize_ty);
                self.emit(Statement::Assign(
                    Place::new(target_addr_tmp),
                    Rvalue::Cast(Operand::Copy(Place::new(target_ptr_tmp)), isize_ty),
                ));

                let field_ptr_ty = self.compiler.intern_type(Type::Ptr {
                    mutable: false,
                    pointee: isize_ty,
                });
                let field_ptr_tmp = self.alloc_temp(field_ptr_ty);
                self.emit(Statement::Assign(
                    Place::new(field_ptr_tmp),
                    Rvalue::Ref {
                        mutable: false,
                        place: dest_field_place.clone(),
                    },
                ));
                let field_addr_tmp = self.alloc_temp(isize_ty);
                self.emit(Statement::Assign(
                    Place::new(field_addr_tmp),
                    Rvalue::Cast(Operand::Copy(Place::new(field_ptr_tmp)), isize_ty),
                ));

                let offset_tmp = self.alloc_temp(isize_ty);
                self.emit(Statement::Assign(
                    Place::new(offset_tmp),
                    Rvalue::BinaryOp(
                        BinOp::SubWrap,
                        Operand::Copy(Place::new(target_addr_tmp)),
                        Operand::Copy(Place::new(field_addr_tmp)),
                    ),
                ));
                self.emit(Statement::Assign(
                    dest_field_place,
                    Rvalue::Use(Operand::Copy(Place::new(offset_tmp))),
                ));
                Ok(())
            }
            RelFieldKind::Slice(_) | RelFieldKind::Str => {
                let expected_elem = match rel_kind {
                    RelFieldKind::Slice(t) => t,
                    RelFieldKind::Str => self.compiler.intern_type(Type::Int {
                        signed: false,
                        bits: 8,
                    }),
                    RelFieldKind::Elem(_) => unreachable!(),
                };
                let (target_place, target_place_ty, len_op) = if let Expr::Slice {
                    base,
                    start,
                    end,
                } = target_expr.as_ref()
                {
                    let (mut arr_place, mut arr_ty) = self.lower_place(base, false)?;
                    if let Type::Ptr { pointee, .. } =
                        self.compiler.program.types[arr_ty.0 as usize]
                    {
                        arr_place.projections.push(Projection::Deref);
                        arr_ty = pointee;
                    }
                    if self.compiler.slices.contains_key(&arr_ty) {
                        arr_place.projections.push(Projection::Field(0));
                        arr_place.projections.push(Projection::Deref);
                    }
                    self.verify_rel_coresidence(
                        struct_name,
                        field_name,
                        base_place,
                        &dest_field_place,
                        &arr_place,
                    )?;
                    let Type::Array { elem, len: arr_len } =
                        self.compiler.program.types[arr_ty.0 as usize]
                    else {
                        return Err(format!(
                            "'&rel' slice '{}.{}' requires an inline array field, found {}",
                            struct_name, field_name, self.compiler.program.types[arr_ty.0 as usize]
                        ));
                    };
                    if elem != expected_elem {
                        return Err(format!(
                            "Element type mismatch in '&rel' slice '{}.{}': expected {}, found {}",
                            struct_name,
                            field_name,
                            self.compiler.program.types[expected_elem.0 as usize],
                            self.compiler.program.types[elem.0 as usize]
                        ));
                    }
                    let (start_op, _) = self.lower_expr(start, Some(usize_ty))?;
                    let start_local = self.alloc_temp(usize_ty);
                    self.emit(Statement::Assign(
                        Place::new(start_local),
                        Rvalue::Use(start_op),
                    ));
                    let (end_op, end_ty) = self.lower_expr(end, Some(usize_ty))?;
                    let const_end = match &end_op {
                        Operand::Const(ConstValue::I64(n)) => Some(*n),
                        _ => None,
                    };
                    let end_local = self.alloc_temp(usize_ty);
                    self.emit(Statement::Assign(Place::new(end_local), Rvalue::Use(end_op)));
                    self.emit_range_end_check(
                        end_local,
                        end_ty,
                        const_end,
                        IndexBound::Static(arr_len),
                    )?;
                    let len_tmp = self.alloc_temp(usize_ty);
                    self.emit(Statement::Assign(
                        Place::new(len_tmp),
                        Rvalue::BinaryOp(
                            BinOp::Sub,
                            Operand::Copy(Place::new(end_local)),
                            Operand::Copy(Place::new(start_local)),
                        ),
                    ));
                    let mut elem_start_place = arr_place;
                    elem_start_place
                        .projections
                        .push(Projection::Index(start_local));
                    (elem_start_place, elem, Operand::Copy(Place::new(len_tmp)))
                } else {
                    let (arr_place, arr_ty) = self.lower_place(target_expr, false)?;
                    self.verify_rel_coresidence(
                        struct_name,
                        field_name,
                        base_place,
                        &dest_field_place,
                        &arr_place,
                    )?;
                    let Type::Array { elem, len } = self.compiler.program.types[arr_ty.0 as usize]
                    else {
                        return Err(format!(
                            "'&rel' slice '{}.{}' requires an inline array or slice expression, found {}",
                            struct_name, field_name, self.compiler.program.types[arr_ty.0 as usize]
                        ));
                    };
                    if elem != expected_elem {
                        return Err(format!(
                            "Element type mismatch in '&rel' slice '{}.{}': expected {}, found {}",
                            struct_name,
                            field_name,
                            self.compiler.program.types[expected_elem.0 as usize],
                            self.compiler.program.types[elem.0 as usize]
                        ));
                    }
                    (
                        arr_place,
                        arr_ty,
                        Operand::Const(ConstValue::I64(len as i128)),
                    )
                };

                let target_ptr_ty = self.compiler.intern_type(Type::Ptr {
                    mutable: false,
                    pointee: target_place_ty,
                });
                let target_ptr_tmp = self.alloc_temp(target_ptr_ty);
                self.emit(Statement::Assign(
                    Place::new(target_ptr_tmp),
                    Rvalue::Ref {
                        mutable: false,
                        place: target_place,
                    },
                ));
                let target_addr_tmp = self.alloc_temp(isize_ty);
                self.emit(Statement::Assign(
                    Place::new(target_addr_tmp),
                    Rvalue::Cast(Operand::Copy(Place::new(target_ptr_tmp)), isize_ty),
                ));

                let repr_ty = self
                    .compiler
                    .intern_type(Type::Struct(vec![isize_ty, usize_ty]));
                let field_ptr_ty = self.compiler.intern_type(Type::Ptr {
                    mutable: false,
                    pointee: repr_ty,
                });
                let field_ptr_tmp = self.alloc_temp(field_ptr_ty);
                self.emit(Statement::Assign(
                    Place::new(field_ptr_tmp),
                    Rvalue::Ref {
                        mutable: false,
                        place: dest_field_place.clone(),
                    },
                ));
                let field_addr_tmp = self.alloc_temp(isize_ty);
                self.emit(Statement::Assign(
                    Place::new(field_addr_tmp),
                    Rvalue::Cast(Operand::Copy(Place::new(field_ptr_tmp)), isize_ty),
                ));

                let offset_tmp = self.alloc_temp(isize_ty);
                self.emit(Statement::Assign(
                    Place::new(offset_tmp),
                    Rvalue::BinaryOp(
                        BinOp::SubWrap,
                        Operand::Copy(Place::new(target_addr_tmp)),
                        Operand::Copy(Place::new(field_addr_tmp)),
                    ),
                ));
                self.emit(Statement::Assign(
                    dest_field_place,
                    Rvalue::Aggregate(repr_ty, vec![Operand::Copy(Place::new(offset_tmp)), len_op]),
                ));
                Ok(())
            }
        }
    }

    #[allow(clippy::too_many_arguments)]
    pub(super) fn resolve_rel_field_access(
        &mut self,
        struct_name: &str,
        field_name: &str,
        base_place: Place,
        f_idx: u32,
        base_ty: TypeId,
        rel_kind: RelFieldKind,
        want_mut: bool,
    ) -> Result<(Place, TypeId), String> {
        if want_mut && matches!(rel_kind, RelFieldKind::Str) {
            return Err(format!(
                "Cannot mutably access '&rel str' field '{}.{}'; string slices (&str) are immutable",
                struct_name, field_name
            ));
        }
        if want_mut && self.place_traverses_immutable_ptr(&base_place) {
            return Err(format!(
                "Cannot mutably access '&rel' field '{}.{}' through an immutable '&Self' reference",
                struct_name, field_name
            ));
        }
        let isize_ty = self.compiler.intern_type(Type::Int {
            signed: true,
            bits: 64,
        });
        let usize_ty = self.compiler.intern_type(Type::Int {
            signed: false,
            bits: 64,
        });
        let mut field_place = base_place.clone();
        field_place.projections.push(Projection::Field(f_idx));

        // 1. Read `offset: isize` (and `len: usize` for slice/str) from `field_place` FIRST
        // so that reading `field_place` happens before `base_place` is borrowed.
        let (offset_tmp, len_tmp_opt) = match rel_kind {
            RelFieldKind::Elem(_) => {
                let off = self.alloc_temp(isize_ty);
                self.emit(Statement::Assign(
                    Place::new(off),
                    Rvalue::Use(Operand::Copy(field_place.clone())),
                ));
                (off, None)
            }
            RelFieldKind::Slice(_) | RelFieldKind::Str => {
                let mut off_p = field_place.clone();
                off_p.projections.push(Projection::Field(0));
                let off = self.alloc_temp(isize_ty);
                self.emit(Statement::Assign(
                    Place::new(off),
                    Rvalue::Use(Operand::Copy(off_p)),
                ));
                let mut len_p = field_place.clone();
                len_p.projections.push(Projection::Field(1));
                let len_t = self.alloc_temp(usize_ty);
                self.emit(Statement::Assign(
                    Place::new(len_t),
                    Rvalue::Use(Operand::Copy(len_p)),
                ));
                (off, Some(len_t))
            }
        };

        // 2. Compute `field_addr: isize` and `base_addr: isize` (temporary refs die immediately at `Cast` to `isize_ty`).
        let field_storage_ty = self.place_type(&field_place);
        let field_ptr_ty = self.compiler.intern_type(Type::Ptr {
            mutable: false,
            pointee: field_storage_ty,
        });
        let field_ptr_tmp = self.alloc_temp(field_ptr_ty);
        self.emit(Statement::Assign(
            Place::new(field_ptr_tmp),
            Rvalue::Ref {
                mutable: false,
                place: field_place,
            },
        ));
        let field_addr_tmp = self.alloc_temp(isize_ty);
        self.emit(Statement::Assign(
            Place::new(field_addr_tmp),
            Rvalue::Cast(Operand::Copy(Place::new(field_ptr_tmp)), isize_ty),
        ));

        let base_addr_ptr_ty = self.compiler.intern_type(Type::Ptr {
            mutable: false,
            pointee: base_ty,
        });
        let base_addr_ptr_tmp = self.alloc_temp(base_addr_ptr_ty);
        self.emit(Statement::Assign(
            Place::new(base_addr_ptr_tmp),
            Rvalue::Ref {
                mutable: false,
                place: base_place.clone(),
            },
        ));
        let base_addr_tmp = self.alloc_temp(isize_ty);
        self.emit(Statement::Assign(
            Place::new(base_addr_tmp),
            Rvalue::Cast(Operand::Copy(Place::new(base_addr_ptr_tmp)), isize_ty),
        ));

        // 3. Compute `target_addr = field_addr +% offset` and `total_offset_from_base = target_addr -% base_addr`.
        let target_addr_tmp = self.alloc_temp(isize_ty);
        self.emit(Statement::Assign(
            Place::new(target_addr_tmp),
            Rvalue::BinaryOp(
                BinOp::AddWrap,
                Operand::Copy(Place::new(field_addr_tmp)),
                Operand::Copy(Place::new(offset_tmp)),
            ),
        ));
        let total_offset_tmp = self.alloc_temp(isize_ty);
        self.emit(Statement::Assign(
            Place::new(total_offset_tmp),
            Rvalue::BinaryOp(
                BinOp::SubWrap,
                Operand::Copy(Place::new(target_addr_tmp)),
                Operand::Copy(Place::new(base_addr_tmp)),
            ),
        ));

        // 4. Take NLL borrow `Rvalue::Ref { mutable: want_mut, place: base_place }` of the enclosing struct
        // and derive the resolved pointer via `BinOp::AddWrap` (byte-offset GEP).
        let base_borrow_ptr_ty = self.compiler.intern_type(Type::Ptr {
            mutable: want_mut,
            pointee: base_ty,
        });
        let base_borrow_ptr_tmp = self.alloc_temp(base_borrow_ptr_ty);
        self.emit(Statement::Assign(
            Place::new(base_borrow_ptr_tmp),
            Rvalue::Ref {
                mutable: want_mut,
                place: base_place,
            },
        ));

        match rel_kind {
            RelFieldKind::Elem(elem_ty) => {
                let target_ptr_ty = self.compiler.intern_type(Type::Ptr {
                    mutable: want_mut,
                    pointee: elem_ty,
                });
                let target_ptr_tmp = self.alloc_temp(target_ptr_ty);
                self.emit(Statement::Assign(
                    Place::new(target_ptr_tmp),
                    Rvalue::BinaryOp(
                        BinOp::AddWrap,
                        Operand::Copy(Place::new(base_borrow_ptr_tmp)),
                        Operand::Copy(Place::new(total_offset_tmp)),
                    ),
                ));
                Ok((Place::new(target_ptr_tmp), target_ptr_ty))
            }
            RelFieldKind::Slice(_) | RelFieldKind::Str => {
                let slice_ty = match rel_kind {
                    RelFieldKind::Slice(elem) => self.compiler.intern_slice_type(want_mut, elem),
                    RelFieldKind::Str => self.compiler.intern_str_type(),
                    RelFieldKind::Elem(_) => unreachable!(),
                };
                let slice_info = self.compiler.slices[&slice_ty];
                let data_ptr_tmp = self.alloc_temp(slice_info.ptr_ty);
                self.emit(Statement::Assign(
                    Place::new(data_ptr_tmp),
                    Rvalue::BinaryOp(
                        BinOp::AddWrap,
                        Operand::Copy(Place::new(base_borrow_ptr_tmp)),
                        Operand::Copy(Place::new(total_offset_tmp)),
                    ),
                ));
                let len_tmp = len_tmp_opt.unwrap();
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
                Ok((Place::new(slice_tmp), slice_ty))
            }
        }
    }
}
