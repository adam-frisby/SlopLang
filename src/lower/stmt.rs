use super::*;

/// A resolved constant `(value, type)`, or a static `(global, type, mutable, path)`.
type ConstOrStatic = Result<(ConstValue, TypeId), (GlobalId, TypeId, bool, String)>;

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
        let type_fn = compiler.type_fn_instances.get(&pending.func_id).cloned();
        let in_unsafe = compiler.unsafe_closures.contains(&pending.func_id);
        Self {
            compiler,
            private_access,
            func_id: pending.func_id,
            mod_path: pending.module_path,
            owner_ty: pending.owner_ty,
            decl: pending.decl,
            comptime_env: pending.comptime_env,
            closure_captures: pending.closure_captures,
            body: BodyBuilder::new(existing_locals),
            type_fn,
            scopes: vec![Vec::new()],
            inferred_opaque_ret: None,
            last_call_opaque_bound: None,
            call_expected: None,
            lowered_base: None,
            unsafe_depth: usize::from(in_unsafe),
            nosuspend_depth: 0,
            raw_addr_of_depth: 0,
            static_locals: HashMap::default(),
            loops: Vec::new(),
            out_of_scope_trait_hint: None,
            capture_binding_writes: std::cell::RefCell::new(Vec::new()),
            capture_moves: std::cell::RefCell::new(Vec::new()),
            line: None,
            last_call: None,
            local_names: Vec::new(),
            pending_loop_label: None,
            type_var_hints: Vec::new(),
            learned_type_hints: Vec::new(),
            type_vars: Vec::new(),
            allow_type_var: false,
        }
    }

    /// Whether this function body may access private members of `ty`: true only inside `ty`'s own
    /// block (inherent methods, lifecycle hooks, inline `impl Tr { ... }` methods, and their lambdas).
    pub(super) fn has_private_access(&self, ty: TypeId) -> bool {
        self.private_access && self.owner_ty == Some(ty)
    }

    pub(super) fn new_block(&mut self) -> BlockId {
        self.body.new_block()
    }

    pub(super) fn alloc_temp(&mut self, ty: TypeId) -> LocalId {
        let ty = self.resolve_type_var(ty);
        self.body.alloc_temp(ty)
    }

    pub(super) fn emit(&mut self, stmt: Statement) {
        self.body.emit(stmt);
    }

    pub(super) fn terminate(&mut self, term: Terminator) {
        if self.nosuspend_depth > 0 && matches!(term, Terminator::Call { .. } | Terminator::Drop { .. }) {
            self.compiler.nosuspend_sites.push((self.func_id, self.body.cur_block));
        }
        if let Terminator::Call { func, .. } = &term {
            self.last_call = match func {
                Operand::Const(ConstValue::Func(f)) => Some(*f),
                _ => None,
            };
        }
        self.body.terminate(term);
    }

    pub(super) fn is_terminated(&self) -> bool {
        self.body.is_terminated()
    }

    /// Pops the innermost scope, keeping its variables' names for diagnostics.
    pub(super) fn pop_scope(&mut self) {
        if let Some(scope) = self.scopes.pop() {
            self.local_names.extend(scope.into_iter().map(|v| (v.local, v.name)));
        }
    }

    pub(super) fn lookup_var(&self, name: &str) -> Option<(LocalId, TypeId)> {
        for scope in self.scopes.iter().rev() {
            for var in scope.iter().rev() {
                if var.name == name {
                    return Some((var.local, self.resolve_type_var(var.ty)));
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
            self.body.locals[0] = expr_ty;
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
            self.compiler.program.types[self.body.locals[1].0 as usize],
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
        self.body.cur_block = next_bb;
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

    /// Drops the variables of every scope at index `depth` and deeper (innermost first), without
    /// popping the scopes: used when `break` / `continue` jump out of them.
    pub(super) fn cleanup_scopes_from(&mut self, depth: usize) {
        let inner: Vec<Vec<ScopeVar>> = self.scopes[depth.min(self.scopes.len())..].to_vec();
        for scope in inner.iter().rev() {
            for var in scope.iter().rev() {
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
                self.compiler.program.types[self.body.locals[1].0 as usize],
                Type::Ptr { .. }
            ) {
                self.scopes[0].push(ScopeVar {
                    name: "__env".to_string(),
                    local: LocalId(1),
                    ty: self.body.locals[1],
                    opaque_bound: None,
                    mutable: true,
                });
            }
            2u32
        };
        for p in &self.decl.params.clone() {
            if !p.is_comptime {
                let local = LocalId(arg_local_idx);
                let ty = self.body.locals[arg_local_idx as usize];
                self.comptime_env
                    .insert(format!("__var_ty:{}", p.name), ComptimeVal::Type(ty));
                self.scopes[0].push(ScopeVar {
                    name: p.name.clone(),
                    local,
                    ty,
                    opaque_bound: None,
                    mutable: p.is_mut,
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
                            mutable: p.is_mut,
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
                            mutable: p.is_mut,
                        });
                    }
                }
            }
        }

        // Entry null checks for `export fn` raw-pointer parameters live in the C-ABI wrapper
        // (`Compiler::build_c_abi_export_wrapper`), so SlopLang callers never pay for them.
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

        let ret_ty = self.body.locals[0];
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

        self.default_all_type_vars(false)?;
        self.compiler.check_c_call_results(&mut self.body);
        let func = self
            .compiler
            .program
            .functions
            .iter_mut()
            .find(|f| f.id == self.func_id)
            .unwrap();
        func.locals = self.body.locals.clone();
        func.blocks = self.body.blocks.clone();
        func.local_names = std::mem::take(&mut self.local_names);
        func.local_names.extend(
            self.scopes.iter().flatten().map(|v| (v.local, v.name.clone())),
        );
        Ok(())
    }

    /// Lowers `let { a, b } = e;` / `let P { x, y: py, .. } = e;`: `e` is held in a hidden local
    /// and each named field is copied or moved out of it; fields left to `..` are dropped with
    /// it at scope exit.
    fn lower_let_destructure(
        &mut self,
        mutable: bool,
        ty_path: Option<&[String]>,
        fields: &[(String, String)],
        rest: bool,
        init: &Expr,
    ) -> Result<(), String> {
        let expected = match ty_path {
            Some(path) => Some(self.compiler.resolve_type_expr(
                &self.mod_path,
                self.owner_ty,
                &self.comptime_env,
                &TypeExpr::Named(path.to_vec()),
            )?),
            None => None,
        };
        let (op, init_ty) = self.lower_expr(init, expected)?;
        if self.is_terminated() {
            return Ok(());
        }
        let ty = expected.unwrap_or(init_ty);
        let op = self.coerce_operand(op, init_ty, ty)?;
        let ty_name = self.compiler.type_display_name(ty);
        // Each pattern field's index and type, and the names of all of the type's fields.
        let mut resolved = Vec::with_capacity(fields.len());
        let all_fields: Vec<String> = if ty_path.is_some() {
            match self.compiler.composites.get(&ty) {
                Some(c) if c.is_opaque => {
                    return Err(format!(
                        "Cannot destructure opaque '{ty_name}': its fields are private"
                    ));
                }
                Some(_) => {}
                None => {
                    return Err(format!(
                        "Cannot destructure '{ty_name}' with a struct pattern; it is not a struct"
                    ));
                }
            }
            for (field, binding) in fields {
                let (idx, f_ty) = self.check_field_access(ty, field)?;
                resolved.push((idx, f_ty, binding));
            }
            self.compiler.composites[&ty]
                .fields
                .iter()
                .map(|(n, ..)| n.clone())
                .collect()
        } else {
            let Type::Struct(elems) = self.compiler.program.types[ty.0 as usize].clone() else {
                return Err(format!(
                    "Cannot destructure '{ty_name}' with a tuple pattern '{{ ... }}'; it is not a tuple"
                ));
            };
            if self.compiler.type_kind(ty).is_some() {
                return Err(format!(
                    "Cannot destructure '{ty_name}' with a tuple pattern '{{ ... }}'; it is not a tuple"
                ));
            }
            if fields.len() > elems.len() || (!rest && fields.len() < elems.len()) {
                return Err(format!(
                    "Tuple pattern has {} names but '{ty_name}' has {} elements{}",
                    fields.len(),
                    elems.len(),
                    if rest { "" } else { "; use '..' to skip the rest" }
                ));
            }
            for (i, (_, binding)) in fields.iter().enumerate() {
                resolved.push((i as u32, elems[i], binding));
            }
            (0..elems.len()).map(|i| i.to_string()).collect()
        };
        if !rest {
            let missing: Vec<&String> = all_fields
                .iter()
                .filter(|f| !fields.iter().any(|(pf, _)| pf == *f))
                .collect();
            if !missing.is_empty() {
                let missing: Vec<&str> = missing.iter().map(|s| s.as_str()).collect();
                return Err(format!(
                    "Pattern for '{ty_name}' does not name field(s) {}; add '..' to ignore them",
                    missing.join(", ")
                ));
            }
        }
        let holder = self.alloc_temp(ty);
        self.emit(Statement::StorageLive(holder));
        self.emit(Statement::Assign(Place::new(holder), Rvalue::Use(op)));
        self.scopes.last_mut().unwrap().push(ScopeVar {
            name: format!("__destructure{}", holder.0),
            local: holder,
            ty,
            opaque_bound: None,
            mutable: true,
        });
        for (idx, f_ty, binding) in resolved {
            // A `_` part is dropped here, as `let _ = ...` drops its value.
            if binding == "_" {
                if self.compiler.is_linear_type(f_ty) {
                    return Err(format!(
                        "'_' would discard a linear value of type '{}', which must be consumed; bind it to a name",
                        self.compiler.type_display_name(f_ty)
                    ));
                }
                if !self.is_copy_type(f_ty) {
                    let value = self.copy_or_move(holder, Projection::Field(idx), f_ty);
                    let local = self.alloc_temp(f_ty);
                    self.emit(Statement::StorageLive(local));
                    self.emit(Statement::Assign(Place::new(local), Rvalue::Use(value)));
                    self.emit_drop_and_dead(local);
                }
                continue;
            }
            let value = self.copy_or_move(holder, Projection::Field(idx), f_ty);
            let local = self.alloc_temp(f_ty);
            self.emit(Statement::StorageLive(local));
            self.emit(Statement::Assign(Place::new(local), Rvalue::Use(value)));
            self.comptime_env
                .insert(format!("__var_ty:{binding}"), ComptimeVal::Type(f_ty));
            self.scopes.last_mut().unwrap().push(ScopeVar {
                name: binding.clone(),
                local,
                ty: f_ty,
                opaque_bound: None,
                mutable,
            });
        }
        Ok(())
    }

    /// Lowers `for`: a range or an array / slice runs a counter over its elements; any other
    /// value is an iterator, run as `let mut it = value; while let x = it.next() { ... }`.
    fn lower_for(
        &mut self,
        var_name: &str,
        mode: BindMode,
        idx_name: Option<&str>,
        iter: &ForIter,
        body: &Block,
    ) -> Result<(), String> {
        let iterable = match iter {
            ForIter::Range {
                start,
                end,
                inclusive,
            } => {
                if mode != BindMode::Default || idx_name.is_some() {
                    return Err(format!(
                        "A range 'for' binds only its value: 'for {var_name} in a..b'"
                    ));
                }
                return self.lower_range_for(var_name, start, end, *inclusive, body);
            }
            ForIter::Expr(e) => e.as_ref(),
        };
        // Arrays and slices: borrowing modes need a place, by-value iteration reads elements
        // of the evaluated value.
        let (op, ty) = match mode {
            BindMode::Ref { mutable } if Self::is_place_expr(iterable) => {
                let (place, ty) = self.lower_place(iterable, mutable)?;
                (Operand::Copy(place), ty)
            }
            _ => self.lower_expr(iterable, None)?,
        };
        let mut base = match op {
            Operand::Copy(p) | Operand::Move(p) => p,
            other => {
                let tmp = self.alloc_temp(ty);
                self.emit(Statement::Assign(Place::new(tmp), Rvalue::Use(other)));
                Place::new(tmp)
            }
        };
        let mut seq_ty = ty;
        if let Type::Ptr { pointee, .. } = self.compiler.program.types[ty.0 as usize]
            && !self.compiler.raw_ptrs.contains_key(&ty)
            && !self.compiler.slices.contains_key(&ty)
            && matches!(self.compiler.program.types[pointee.0 as usize], Type::Array { .. })
        {
            base.projections.push(Projection::Deref);
            seq_ty = pointee;
        }
        let usize_ty = self.compiler.intern_type(Type::Int {
            signed: false,
            bits: 64,
        });
        let (elem_ty, len_op, data) = if let Type::Array { elem, len } =
            self.compiler.program.types[seq_ty.0 as usize]
        {
            (elem, Operand::Const(ConstValue::I64(i128::from(len))), base)
        } else if let Some(&slice) = self.compiler.slices.get(&seq_ty) {
            let mut len_place = base.clone();
            len_place.projections.push(Projection::Field(1));
            let mut data = base;
            data.projections.push(Projection::Field(0));
            data.projections.push(Projection::Deref);
            (slice.elem, Operand::Copy(len_place), data)
        } else {
            if mode != BindMode::Default || idx_name.is_some() {
                return Err(format!(
                    "'for ref' and 'for (x, i)' iterate arrays and slices; '{}' is not one",
                    self.compiler.type_display_name(ty)
                ));
            }
            return self.lower_iterator_for(var_name, base, ty, body);
        };
        if let BindMode::Ref { mutable: true } = mode {
            self.check_binding_writable(&data, "borrow mutably")?;
        }
        if let BindMode::Ref { mutable: true } = mode
            && self.place_traverses_immutable_ptr(&data)
        {
            return Err(format!(
                "Cannot iterate with 'for ref mut {var_name}' through an immutable reference"
            ));
        }
        if mode == BindMode::Default && !self.is_copy_type(elem_ty) {
            return Err(format!(
                "'for {var_name} in ...' would move elements of type '{}' out of the sequence; iterate with 'for ref {var_name} in ...'",
                self.compiler.type_display_name(elem_ty)
            ));
        }
        let len_local = self.alloc_temp(usize_ty);
        self.emit(Statement::Assign(Place::new(len_local), Rvalue::Use(len_op)));
        let counter = self.alloc_temp(usize_ty);
        self.emit(Statement::Assign(
            Place::new(counter),
            Rvalue::Use(Operand::Const(ConstValue::I64(0))),
        ));
        let mut elem_place = data;
        elem_place.projections.push(Projection::Index(counter));
        let (var_ty, value) = match mode {
            BindMode::Ref { mutable } => (
                self.compiler.intern_type(Type::Ptr {
                    mutable,
                    pointee: elem_ty,
                }),
                Rvalue::Ref {
                    mutable,
                    place: elem_place,
                },
            ),
            _ => (elem_ty, Rvalue::Use(Operand::Copy(elem_place))),
        };
        let mut bindings = vec![(var_name.to_string(), var_ty, value)];
        if let Some(idx) = idx_name {
            let index = Rvalue::Use(Operand::Copy(Place::new(counter)));
            bindings.push((idx.to_string(), usize_ty, index));
        }
        self.lower_counted_loop(counter, len_local, false, bindings, body)
    }

    /// Whether `e` names a place (a variable, field, element, or dereference).
    fn is_place_expr(e: &Expr) -> bool {
        matches!(
            e,
            Expr::Path(_)
                | Expr::Field { .. }
                | Expr::TupleIndex { .. }
                | Expr::Index { .. }
                | Expr::Deref(_)
        )
    }

    /// `for x in start..end` / `start..=end`: the counter takes a bound's type, or a type
    /// variable when both bounds are literals.
    fn lower_range_for(
        &mut self,
        var_name: &str,
        start: &Expr,
        end: &Expr,
        inclusive: bool,
        body: &Block,
    ) -> Result<(), String> {
        let is_literal = |e: &Expr| match e {
            Expr::Int(_) => true,
            Expr::Unary {
                op: UnOp::Neg,
                expr,
            } => matches!(expr.as_ref(), Expr::Int(_)),
            _ => false,
        };
        let (start_op, end_op, ty) = if !is_literal(start) {
            let (s, t) = self.lower_expr_open(start, None)?;
            let t = self.pattern_base(t);
            let (e, et) = self.lower_expr_open(end, Some(t))?;
            let e = self.coerce_operand(e, et, t)?;
            (s, e, t)
        } else if !is_literal(end) {
            let (e, t) = self.lower_expr_open(end, None)?;
            let t = self.pattern_base(t);
            let (s, st) = self.lower_expr_open(start, Some(t))?;
            let s = self.coerce_operand(s, st, t)?;
            (s, e, t)
        } else {
            let t = self.new_type_var(false);
            let (s, _) = self.lower_expr_open(start, Some(t))?;
            let (e, _) = self.lower_expr_open(end, Some(t))?;
            (s, e, t)
        };
        let ty = self.resolve_type_var(ty);
        if !self.is_open_type_var(ty)
            && !matches!(self.compiler.program.types[ty.0 as usize], Type::Int { .. })
        {
            return Err(format!(
                "Range bounds in 'for {var_name} in ...' must be integers, found '{}'",
                self.compiler.type_display_name(ty)
            ));
        }
        let counter = self.alloc_temp(ty);
        self.emit(Statement::Assign(Place::new(counter), Rvalue::Use(start_op)));
        let end_local = self.alloc_temp(ty);
        self.emit(Statement::Assign(Place::new(end_local), Rvalue::Use(end_op)));
        let bindings = vec![(
            var_name.to_string(),
            ty,
            Rvalue::Use(Operand::Copy(Place::new(counter))),
        )];
        self.lower_counted_loop(counter, end_local, inclusive, bindings, body)
    }

    /// The loop shared by ranges and sequences: while `counter < end` (`<=` when `inclusive`),
    /// bind `bindings` and run `body`; `continue` steps the counter. An inclusive loop leaves
    /// before stepping past `end`, so `0..=255` over `u8` never overflows.
    fn lower_counted_loop(
        &mut self,
        counter: LocalId,
        end: LocalId,
        inclusive: bool,
        bindings: Vec<(String, TypeId, Rvalue)>,
        body: &Block,
    ) -> Result<(), String> {
        let bool_ty = self.compiler.intern_type(Type::Bool);
        let ty = self.body.locals[counter.0 as usize];
        let cond_bb = self.new_block();
        let body_bb = self.new_block();
        let step_bb = self.new_block();
        let exit_bb = self.new_block();
        self.terminate(Terminator::Goto { target: cond_bb });

        self.body.cur_block = cond_bb;
        let in_range = self.alloc_temp(bool_ty);
        self.emit(Statement::Assign(
            Place::new(in_range),
            Rvalue::BinaryOp(
                if inclusive { BinOp::Le } else { BinOp::Lt },
                Operand::Copy(Place::new(counter)),
                Operand::Copy(Place::new(end)),
            ),
        ));
        self.terminate(Terminator::SwitchInt {
            discr: Operand::Copy(Place::new(in_range)),
            targets: vec![(1, body_bb)],
            otherwise: exit_bb,
        });

        self.body.cur_block = body_bb;
        self.loops.push(LoopCtx {
            continue_bb: step_bb,
            break_bb: exit_bb,
            scope_depth: self.scopes.len(),
            label: self.pending_loop_label.take(),
        });
        self.scopes.push(Vec::new());
        for (name, var_ty, value) in bindings {
            let local = self.alloc_temp(var_ty);
            self.emit(Statement::StorageLive(local));
            self.emit(Statement::Assign(Place::new(local), value));
            self.comptime_env
                .insert(format!("__var_ty:{name}"), ComptimeVal::Type(var_ty));
            self.scopes.last_mut().unwrap().push(ScopeVar {
                name,
                local,
                ty: var_ty,
                opaque_bound: None,
                mutable: false,
            });
        }
        let res = self.lower_block_stmts(body);
        self.loops.pop();
        res?;
        if !self.is_terminated() {
            self.cleanup_top_scope();
            self.terminate(Terminator::Goto { target: step_bb });
        }
        self.pop_scope();

        self.body.cur_block = step_bb;
        let advance_bb = self.new_block();
        if inclusive {
            let at_end = self.alloc_temp(bool_ty);
            self.emit(Statement::Assign(
                Place::new(at_end),
                Rvalue::BinaryOp(
                    BinOp::Eq,
                    Operand::Copy(Place::new(counter)),
                    Operand::Copy(Place::new(end)),
                ),
            ));
            self.terminate(Terminator::SwitchInt {
                discr: Operand::Copy(Place::new(at_end)),
                targets: vec![(1, exit_bb)],
                otherwise: advance_bb,
            });
        } else {
            self.terminate(Terminator::Goto { target: advance_bb });
        }
        self.body.cur_block = advance_bb;
        let next = self.alloc_temp(ty);
        self.emit(Statement::Assign(
            Place::new(next),
            Rvalue::BinaryOp(
                BinOp::AddWrap,
                Operand::Copy(Place::new(counter)),
                Operand::Const(ConstValue::I64(1)),
            ),
        ));
        self.emit(Statement::Assign(
            Place::new(counter),
            Rvalue::Use(Operand::Copy(Place::new(next))),
        ));
        self.terminate(Terminator::Goto { target: cond_bb });

        self.body.cur_block = exit_bb;
        Ok(())
    }

    /// `for x in it`: `let mut __it = it; while let x = __it.next() { ... }`.
    fn lower_iterator_for(
        &mut self,
        var_name: &str,
        value: Place,
        ty: TypeId,
        body: &Block,
    ) -> Result<(), String> {
        let it_name = format!("__for_it{}", self.body.locals.len());
        let it_local = self.alloc_temp(ty);
        let op = if self.is_copy_type(ty) {
            Operand::Copy(value)
        } else {
            Operand::Move(value)
        };
        self.emit(Statement::StorageLive(it_local));
        self.emit(Statement::Assign(Place::new(it_local), Rvalue::Use(op)));
        self.scopes.push(vec![ScopeVar {
            name: it_name.clone(),
            local: it_local,
            ty,
            opaque_bound: None,
            mutable: true,
        }]);
        let res = self.lower_stmt(&Stmt::WhileLet {
            var_name: var_name.to_string(),
            opt_expr: Expr::MethodCall {
                receiver: Box::new(Expr::Path(vec![it_name])),
                method: "next".to_string(),
                ct_args: None,
                args: Vec::new(),
                at: crate::ast::At::default(),
            },
            body: body.clone(),
        });
        if res.is_ok() && !self.is_terminated() {
            self.cleanup_top_scope();
        }
        self.pop_scope();
        res
    }

    pub(super) fn lower_scoped_block(&mut self, block: &Block) -> Result<(), String> {
        self.scopes.push(Vec::new());
        self.lower_block_stmts(block)?;
        if !self.is_terminated() {
            self.cleanup_top_scope();
        }
        self.pop_scope();
        Ok(())
    }

    pub(super) fn lower_block_stmts(&mut self, block: &Block) -> Result<(), String> {
        for (i, stmt) in block.stmts.iter().enumerate() {
            if self.is_terminated() {
                break;
            }
            self.mark_line(block, i);
            self.lower_stmt(stmt).map_err(|e| self.located(e, block.lines.get(i)))?;
            let keep = matches!(stmt, Stmt::Let { init: Expr::Ref { .. }, .. });
            self.drop_statement_temps(keep);
        }
        if !self.is_terminated() {
            self.mark_line(block, block.stmts.len());
        }
        Ok(())
    }

    /// `err` with where the statement it came from starts, unless an inner statement, or the
    /// check that found it, already said where.
    pub(super) fn located(&self, err: String, pos: Option<&crate::ir::Pos>) -> String {
        let first = err.lines().next().unwrap_or_default();
        match pos {
            Some(pos) if !first.contains("(line ") && !first.contains(" at line ") => {
                let (head, rest) = err.split_once('\n').map_or((err.as_str(), ""), |(h, r)| (h, r));
                let module = if self.mod_path == "root" {
                    String::new()
                } else {
                    format!(" of module '{}'", self.mod_path)
                };
                if rest.is_empty() {
                    format!("{head} ({pos}{module})")
                } else {
                    format!("{head} ({pos}{module})\n{rest}")
                }
            }
            _ => err,
        }
    }

    /// Records the source position of statement `i` of `block` for diagnostics.
    fn mark_line(&mut self, block: &Block, i: usize) {
        if let Some(&pos) = block.lines.get(i) {
            self.emit(Statement::Line(pos));
            self.line = Some(pos);
        }
    }

    /// Makes `pos` the source position of what is lowered next.
    pub(super) fn set_line(&mut self, pos: crate::ir::Pos) {
        if self.line != Some(pos) && !self.is_terminated() {
            self.emit(Statement::Line(pos));
            self.line = Some(pos);
        }
    }

    /// Lowers a call at `at` with its position in force, so that what the checkers find in it
    /// (a moved argument, a conflicting borrow) is placed there, and then the enclosing one
    /// again.
    pub(super) fn at_call<T>(
        &mut self,
        at: Option<crate::ir::Pos>,
        lower: impl FnOnce(&mut Self) -> Result<T, String>,
    ) -> Result<T, String> {
        let Some(pos) = at else {
            return lower(self);
        };
        let outer = self.line;
        self.set_line(pos);
        let result = lower(self);
        if let Some(outer) = outer {
            self.set_line(outer);
        }
        result
    }

    pub(super) fn verify_pattern_const(&self, ty_id: TypeId, val: &Wide) -> Result<(), String> {
        if let Type::Pattern { ranges, .. } = &self.compiler.program.types[ty_id.0 as usize] {
            let valid = crate::ir::pattern_contains(ranges, val);
            if !valid {
                return Err(format!(
                    "Compile-time value {val} is outside valid pattern ranges of '{}'",
                    self.compiler.type_display_name(ty_id)
                ));
            }
        }
        Ok(())
    }

    /// Picks the implicit conversion from `src_ty` to `target_ty`, in priority order. This is the
    /// complete list of implicit conversions: any other mismatch is a type error.
    fn classify_coercion(
        &self,
        op: &Operand,
        src_ty: TypeId,
        target_ty: TypeId,
    ) -> Result<Coercion, String> {
        let types = &self.compiler.program.types;
        let src = &types[src_ty.0 as usize];
        let dst = &types[target_ty.0 as usize];
        let is_raw = |t: TypeId| self.compiler.raw_ptrs.contains_key(&t);
        let named = |t: TypeId| self.compiler.type_display_name(t);
        let is_named_local = |place: &Place| {
            place.projections.is_empty()
                && self.scopes.iter().flatten().any(|v| v.local == place.local)
        };

        // Function-pointer types differing only in their borrow contract: a function constant may
        // take any contract (Stage 3c verifies the function against it); a pointer value may only
        // widen.
        let is_c_fn = |t: TypeId| self.compiler.program.c_fn_ptr_types.contains(&t);
        if src_ty != target_ty
            && matches!((src, dst), (Type::FnPtr { .. }, Type::FnPtr { .. }))
            && is_c_fn(src_ty) != is_c_fn(target_ty)
        {
            return Err(format!(
                "Cannot convert '{}' to '{}': C ('extern fn') and SlopLang function pointers use different calling conventions",
                named(src_ty),
                named(target_ty)
            ));
        }
        // A safe function may be called where an `unsafe fn` is expected, but not the reverse:
        // that would let safe code call it without an `unsafe` block.
        let is_unsafe_fn = |t: TypeId| self.compiler.unsafe_fn_ptr_types.contains(&t);
        if src_ty != target_ty
            && matches!((src, dst), (Type::FnPtr { .. }, Type::FnPtr { .. }))
            && is_unsafe_fn(src_ty)
            && !is_unsafe_fn(target_ty)
        {
            return Err(format!(
                "Cannot convert '{}' to '{}': an 'unsafe fn' pointer cannot become a safe one",
                named(src_ty),
                named(target_ty)
            ));
        }
        if src_ty != target_ty
            && let (Type::FnPtr { args: sa, ret: sr }, Type::FnPtr { args: ta, ret: tr }) =
                (src, dst)
            && sa == ta
            && sr == tr
        {
            if matches!(op, Operand::Const(ConstValue::Func(_))) {
                return Ok(Coercion::Identity);
            }
            let src_c = self.compiler.fn_ptr_contract(src_ty).cloned().unwrap_or_default();
            let dst_c = self.compiler.fn_ptr_contract(target_ty).cloned().unwrap_or_default();
            if src_c.ret.iter().all(|p| dst_c.ret.contains(p))
                && src_c.flows.iter().all(|f| dst_c.flows.contains(f))
            {
                return Ok(Coercion::Identity);
            }
            return Err(format!(
                "Function pointer of type '{}' has a wider borrow contract than the expected '{}'",
                named(src_ty),
                named(target_ty)
            ));
        }

        // Reborrow a named `&mut T` local or field passed as `&mut T` / `&T` (or `&opaque`).
        if let (
            &Type::Ptr {
                mutable: true,
                pointee: src_pt,
            },
            &Type::Ptr {
                mutable: dst_mut,
                pointee: dst_pt,
            },
        ) = (src, dst)
            && (src_pt == dst_pt || self.compiler.is_universal_opaque_type(dst_pt))
            && !is_raw(src_ty)
            && !is_raw(target_ty)
            && let Operand::Move(place) = op
            && (!place.projections.is_empty() || is_named_local(place))
        {
            return Ok(Coercion::ReborrowRef { mutable: dst_mut });
        }
        // Reborrow a named `&mut [T]` local passed as `&mut [T]` / `&[T]`.
        if let (Some(&src_slice), Some(&target_slice)) = (
            self.compiler.slices.get(&src_ty),
            self.compiler.slices.get(&target_ty),
        ) && src_slice.mutable
            && src_slice.elem == target_slice.elem
            && let Operand::Move(place) = op
            && is_named_local(place)
        {
            return Ok(Coercion::ReborrowSlice(target_slice));
        }
        // Reborrow a named `&mut Trait` local passed as `&mut Trait` / `&Trait`.
        if let (Some(src_tobj), Some(target_tobj)) = (
            self.compiler.trait_objs.get(&src_ty),
            self.compiler.trait_objs.get(&target_ty),
        ) && src_tobj.mutable
            && src_tobj.trait_ty == target_tobj.trait_ty
            && let Operand::Move(place) = op
            && is_named_local(place)
        {
            return Ok(Coercion::ReborrowTraitObj(target_tobj.clone()));
        }

        if src_ty == target_ty {
            if let Operand::Const(c @ (ConstValue::I64(_) | ConstValue::Wide(_))) = op {
                self.verify_pattern_const(target_ty, &const_to_wide(c))?;
            }
            return Ok(Coercion::Identity);
        }

        // `&T` / `&mut T` -> `&Trait` / `&mut Trait`, and `&mut Trait` -> `&Trait`.
        if let Some(target_tobj) = self.compiler.trait_objs.get(&target_ty) {
            if let Some(src_tobj) = self.compiler.trait_objs.get(&src_ty)
                && src_tobj.trait_ty == target_tobj.trait_ty
            {
                if target_tobj.mutable && !src_tobj.mutable {
                    return Err(format!(
                        "Cannot coerce shared trait object '&{}' to mutable trait object '&mut {}'",
                        named(target_tobj.trait_ty),
                        named(target_tobj.trait_ty)
                    ));
                }
                return Ok(Coercion::TraitObjToTraitObj(target_tobj.clone()));
            }
            if let &Type::Ptr {
                mutable: src_mut,
                pointee: concrete,
            } = src
                && !is_raw(src_ty)
            {
                if target_tobj.mutable && !src_mut {
                    return Err(format!(
                        "Cannot coerce immutable reference '&{}' to mutable trait object '&mut {}'",
                        named(concrete),
                        named(target_tobj.trait_ty)
                    ));
                }
                return Ok(Coercion::RefToTraitObj {
                    target: target_tobj.clone(),
                    concrete,
                });
            }
            return Err(format!(
                "Cannot coerce '{}' to trait object '{}'",
                named(src_ty),
                named(target_ty)
            ));
        }

        // Safe references (`&mut T` -> `&T`, `&T` / `&mut T` -> `*const T` / `*mut T` / `*ref T`,
        // `&T` -> `&opaque`) and raw pointers (`*mut T` -> `*const T`, `*T` -> `*opaque`). Nothing
        // converts implicitly into an owning pointer, or into a view except from a reference: those
        // claim something about the pointee that only `as` inside `unsafe` may assert.
        let kind_ok = match (self.compiler.ptr_kind(src_ty), self.compiler.ptr_kind(target_ty)) {
            (_, None | Some(PtrKind::Raw)) => true,
            (None, Some(PtrKind::View)) => true,
            (Some(from), Some(to)) => from == to,
            (None, Some(PtrKind::Own)) => false,
        };
        if let (
            &Type::Ptr {
                mutable: src_mut,
                pointee: src_pt,
            },
            &Type::Ptr {
                mutable: dst_mut,
                pointee: dst_pt,
            },
        ) = (src, dst)
            && (src_pt == dst_pt || self.compiler.is_universal_opaque_type(dst_pt))
            && (!dst_mut || src_mut)
            && (!is_raw(src_ty) || is_raw(target_ty))
            && kind_ok
        {
            return Ok(Coercion::PtrCast {
                move_result: dst_mut && !is_raw(target_ty),
            });
        }

        // String literals -> `&str`, `&[T; N]` -> `&[T]`, and `&mut [T]` -> `&[T]`.
        if let Some(&target_slice) = self.compiler.slices.get(&target_ty) {
            if let Operand::Const(ConstValue::Str(s)) = op
                && !target_slice.mutable
                && matches!(
                    types[target_slice.elem.0 as usize],
                    Type::Int {
                        signed: false,
                        bits: 8
                    }
                )
            {
                return Ok(Coercion::StrToSlice {
                    slice: target_slice,
                    len: s.len() as i128,
                });
            }
            if let &Type::Ptr {
                mutable: src_mut,
                pointee,
            } = src
                && let Type::Array { elem, len } = types[pointee.0 as usize]
                && elem == target_slice.elem
                && (!target_slice.mutable || src_mut)
            {
                return Ok(Coercion::ArrayRefToSlice {
                    slice: target_slice,
                    len: len as i128,
                });
            }
            if let Some(&src_slice) = self.compiler.slices.get(&src_ty)
                && src_slice.elem == target_slice.elem
                && (!target_slice.mutable || src_slice.mutable)
            {
                return Ok(Coercion::SliceToSlice(target_slice));
            }
        }

        // `error` widening (`E_src` -> `E_dst` when `E_src`'s variants are a subset).
        if self.compiler.errors.contains_key(&src_ty)
            && self.compiler.errors.contains_key(&target_ty)
        {
            return Ok(Coercion::WidenError);
        }

        // Into `E!T`: from `E'!T` (widening the error), from an error, or from an ok value.
        if let Some(&dst_res) = self.compiler.results.get(&target_ty) {
            if let Some(&src_res) = self.compiler.results.get(&src_ty)
                && src_res.ok_ty == dst_res.ok_ty
            {
                return Ok(Coercion::ResultToResult {
                    src: src_res,
                    dst: dst_res,
                });
            }
            if self.compiler.errors.contains_key(&src_ty)
                && !self.compiler.errors.contains_key(&dst_res.ok_ty)
            {
                return Ok(Coercion::ErrorToResult(dst_res));
            }
            return Ok(Coercion::OkToResult(dst_res));
        }

        // Into `?T` (`union { void, T }`): `T`, a raw pointer (null-checked), or a pointer that
        // coerces to the raw pointer `T`.
        if let Some(inner) = self.compiler.as_optional_type(target_ty) {
            if src_ty == inner && is_raw(inner) {
                return Ok(Coercion::RawPtrToOptional);
            }
            if src_ty == inner {
                return Ok(Coercion::WrapOptional);
            }
            if is_raw(inner) && matches!(src, Type::Ptr { .. }) {
                return Ok(Coercion::PtrToOptionalPtr(inner));
            }
        }

        // A base-typed constant narrows to a pattern type once verified; a runtime value needs an
        // explicit `as P` (trapping) or `as ?P` (checked).
        if let &Type::Pattern { base, .. } = dst
            && src_ty == base
        {
            if let Operand::Const(c @ (ConstValue::I64(_) | ConstValue::Wide(_))) = op {
                self.verify_pattern_const(target_ty, &const_to_wide(c))?;
                return Ok(Coercion::ValueCast);
            }
            let name = named(target_ty);
            return Err(format!(
                "Cannot implicitly narrow a runtime '{}' to pattern type '{name}'; use 'as {name}' (traps when out of range) or 'as ?{name}' (checked)",
                named(src_ty)
            ));
        }
        // A pattern type widens to its base type.
        if let &Type::Pattern { base, .. } = src
            && target_ty == base
        {
            return Ok(Coercion::ValueCast);
        }

        // A distinct type converts to and from its underlying type only with `as`.
        if self.compiler.distinct_types.contains_key(&target_ty) {
            return Err(format!(
                "Type mismatch: '{}' is a distinct type and does not convert implicitly from '{}'; use 'as {}'",
                named(target_ty),
                named(src_ty),
                named(target_ty)
            ));
        }
        if self.compiler.distinct_types.contains_key(&src_ty) {
            return Err(format!(
                "Type mismatch: '{}' is a distinct type and does not convert implicitly to '{}'; use 'as {}'",
                named(src_ty),
                named(target_ty),
                named(target_ty)
            ));
        }

        // `never` (a diverging expression) fits any type.
        if matches!(src, Type::Never) {
            return Ok(Coercion::Identity);
        }
        if self.compiler.c_ints.contains_key(&src_ty)
            || self.compiler.c_ints.contains_key(&target_ty)
        {
            return Err(format!(
                "Type mismatch: cannot implicitly convert '{}' to '{}'; use an explicit 'as {}' cast",
                named(src_ty),
                named(target_ty),
                named(target_ty)
            ));
        }
        Err(format!(
            "Type mismatch: cannot implicitly convert '{}' to '{}'",
            self.compiler.type_display_name(src_ty),
            self.compiler.type_display_name(target_ty)
        ))
    }

    /// Converts `op` from `src_ty` to `target_ty` using the implicit conversion chosen by
    /// [`Self::classify_coercion`].
    pub(super) fn coerce_operand(
        &mut self,
        op: Operand,
        src_ty: TypeId,
        target_ty: TypeId,
    ) -> Result<Operand, String> {
        // An open type variable meeting a concrete type is bound to it (see `infer.rs`).
        let (src_ty, target_ty) = (self.resolve_type_var(src_ty), self.resolve_type_var(target_ty));
        if self.is_open_type_var(src_ty) {
            self.bind_type_var(src_ty, target_ty)?;
        } else if self.is_open_type_var(target_ty) {
            self.bind_type_var(target_ty, src_ty)?;
        }
        let (src_ty, target_ty) = (self.resolve_type_var(src_ty), self.resolve_type_var(target_ty));
        let coercion = match self.classify_coercion(&op, src_ty, target_ty) {
            Ok(c) => c,
            Err(e) => {
                self.learn_type_hint(Self::operand_local_id(&op), target_ty);
                return Err(e);
            }
        };
        match coercion {
            Coercion::Identity => Ok(op),
            Coercion::ReborrowRef { mutable } => {
                let Operand::Move(mut place) = op else { unreachable!() };
                place.projections.push(Projection::Deref);
                let tmp = self.alloc_temp(target_ty);
                self.emit(Statement::Assign(Place::new(tmp), Rvalue::Ref { mutable, place }));
                Ok(Operand::Move(Place::new(tmp)))
            }
            Coercion::ReborrowSlice(target_slice) => {
                let Operand::Move(place) = op else { unreachable!() };
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
                Ok(self.emit_fat_pointer(
                    target_ty,
                    Operand::Move(Place::new(reborrow_ptr)),
                    Operand::Copy(len_field),
                    true,
                ))
            }
            Coercion::ReborrowTraitObj(target_tobj) => {
                let Operand::Move(place) = op else { unreachable!() };
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
                Ok(self.emit_fat_pointer(
                    target_ty,
                    Operand::Move(Place::new(reborrow_ptr)),
                    Operand::Copy(vt_field),
                    true,
                ))
            }
            Coercion::TraitObjToTraitObj(target_tobj) => {
                let src_local = self.operand_local(op, src_ty);
                let (ptr_field, vt_field) = Self::fat_pointer_fields(src_local);
                let cast_ptr = self.alloc_temp(target_tobj.data_ptr_ty);
                self.emit(Statement::Assign(
                    Place::new(cast_ptr),
                    Rvalue::Cast(Operand::Copy(ptr_field), target_tobj.data_ptr_ty),
                ));
                Ok(self.emit_fat_pointer(
                    target_ty,
                    Operand::Copy(Place::new(cast_ptr)),
                    Operand::Copy(vt_field),
                    false,
                ))
            }
            Coercion::RefToTraitObj { target, concrete } => {
                let (gl_id, thunk_ids) =
                    self.compiler.get_or_create_vtable(&self.mod_path, concrete, target.trait_ty)?;
                let gl_mut_ptr_ty = self.compiler.intern_type(Type::Ptr {
                    mutable: true,
                    pointee: target.vtable_ty,
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
                    Rvalue::Aggregate(target.vtable_ty, thunk_ops),
                ));
                let vt_ptr_tmp = self.alloc_temp(target.vtable_ptr_ty);
                self.emit(Statement::Assign(
                    Place::new(vt_ptr_tmp),
                    Rvalue::Cast(Operand::Copy(Place::new(gl_mut_ptr_tmp)), target.vtable_ptr_ty),
                ));
                let data_ptr_tmp = self.alloc_temp(target.data_ptr_ty);
                self.emit(Statement::Assign(
                    Place::new(data_ptr_tmp),
                    Rvalue::Cast(op, target.data_ptr_ty),
                ));
                let data = if target.mutable {
                    Operand::Move(Place::new(data_ptr_tmp))
                } else {
                    Operand::Copy(Place::new(data_ptr_tmp))
                };
                Ok(self.emit_fat_pointer(
                    target_ty,
                    data,
                    Operand::Copy(Place::new(vt_ptr_tmp)),
                    target.mutable,
                ))
            }
            Coercion::PtrCast { move_result } => {
                let tmp = self.alloc_temp(target_ty);
                self.emit(Statement::Assign(Place::new(tmp), Rvalue::Cast(op, target_ty)));
                Ok(if move_result {
                    Operand::Move(Place::new(tmp))
                } else {
                    Operand::Copy(Place::new(tmp))
                })
            }
            Coercion::StrToSlice { slice, len } => {
                let str_tmp = self.alloc_temp(src_ty);
                self.emit(Statement::Assign(Place::new(str_tmp), Rvalue::Use(op)));
                let cast_ptr = self.alloc_temp(slice.ptr_ty);
                self.emit(Statement::Assign(
                    Place::new(cast_ptr),
                    Rvalue::Cast(Operand::Copy(Place::new(str_tmp)), slice.ptr_ty),
                ));
                Ok(self.emit_fat_pointer(
                    target_ty,
                    Operand::Copy(Place::new(cast_ptr)),
                    Operand::Const(ConstValue::I64(len)),
                    false,
                ))
            }
            Coercion::ArrayRefToSlice { slice, len } => {
                let cast_ptr = self.alloc_temp(slice.ptr_ty);
                self.emit(Statement::Assign(
                    Place::new(cast_ptr),
                    Rvalue::Cast(op, slice.ptr_ty),
                ));
                Ok(self.emit_fat_pointer(
                    target_ty,
                    Operand::Copy(Place::new(cast_ptr)),
                    Operand::Const(ConstValue::I64(len)),
                    false,
                ))
            }
            Coercion::SliceToSlice(target_slice) => {
                let src_local = self.operand_local(op, src_ty);
                let (ptr_field, len_field) = Self::fat_pointer_fields(src_local);
                let cast_ptr = self.alloc_temp(target_slice.ptr_ty);
                self.emit(Statement::Assign(
                    Place::new(cast_ptr),
                    Rvalue::Cast(Operand::Copy(ptr_field), target_slice.ptr_ty),
                ));
                Ok(self.emit_fat_pointer(
                    target_ty,
                    Operand::Copy(Place::new(cast_ptr)),
                    Operand::Copy(len_field),
                    false,
                ))
            }
            Coercion::WidenError => self.widen_error_operand(op, src_ty, target_ty),
            Coercion::ResultToResult { src, dst } => {
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

                self.body.cur_block = ok_bb;
                let ok_op = self.copy_or_move(src_local, Projection::Variant(0), src.ok_ty);
                self.emit(Statement::Assign(
                    Place::new(dst_local),
                    Rvalue::Union {
                        ty: target_ty,
                        variant: 0,
                        payload: ok_op,
                    },
                ));
                self.terminate(Terminator::Goto { target: join_bb });

                self.body.cur_block = err_bb;
                let err_op = self.copy_or_move(src_local, Projection::Variant(1), src.err_ty);
                let widened_err = self.widen_error_operand(err_op, src.err_ty, dst.err_ty)?;
                self.emit(Statement::Assign(
                    Place::new(dst_local),
                    Rvalue::Union {
                        ty: target_ty,
                        variant: 1,
                        payload: widened_err,
                    },
                ));
                self.terminate(Terminator::Goto { target: join_bb });

                self.body.cur_block = join_bb;
                Ok(self.local_operand(dst_local, target_ty))
            }
            Coercion::ErrorToResult(dst) => {
                let widened_err = self.widen_error_operand(op, src_ty, dst.err_ty)?;
                Ok(self.emit_union(target_ty, 1, widened_err))
            }
            Coercion::OkToResult(dst) => {
                let ok_op = self.coerce_operand(op, src_ty, dst.ok_ty)?;
                Ok(self.emit_union(target_ty, 0, ok_op))
            }
            Coercion::RawPtrToOptional => {
                let usize_ty = self.compiler.intern_type(Type::Int {
                    signed: false,
                    bits: 64,
                });
                let ptr_tmp = self.alloc_temp(src_ty);
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
                self.body.cur_block = null_bb;
                self.emit(Statement::Assign(
                    Place::new(tmp),
                    Rvalue::Union {
                        ty: target_ty,
                        variant: 0,
                        payload: Operand::Const(ConstValue::Void),
                    },
                ));
                self.terminate(Terminator::Goto { target: join_bb });

                self.body.cur_block = some_bb;
                self.emit(Statement::Assign(
                    Place::new(tmp),
                    Rvalue::Union {
                        ty: target_ty,
                        variant: 1,
                        payload: Operand::Copy(Place::new(ptr_tmp)),
                    },
                ));
                self.terminate(Terminator::Goto { target: join_bb });

                self.body.cur_block = join_bb;
                Ok(Operand::Move(Place::new(tmp)))
            }
            Coercion::WrapOptional => Ok(self.emit_union_move(target_ty, 1, op)),
            Coercion::PtrToOptionalPtr(inner) => {
                let coerced_ptr = self.coerce_operand(op, src_ty, inner)?;
                Ok(self.emit_union_move(target_ty, 1, coerced_ptr))
            }
            Coercion::ValueCast => {
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
                Ok(Operand::Copy(Place::new(tmp)))
            }
        }
    }

    /// The local `op` reads, when it reads a whole local.
    pub(super) fn operand_local_id(op: &Operand) -> Option<LocalId> {
        match op {
            Operand::Copy(p) | Operand::Move(p) if p.projections.is_empty() => Some(p.local),
            _ => None,
        }
    }

    /// `op` as a local without projections, spilling it to a temporary if needed.
    fn operand_local(&mut self, op: Operand, ty: TypeId) -> LocalId {
        match op {
            Operand::Copy(p) | Operand::Move(p) if p.projections.is_empty() => p.local,
            other => {
                let tmp = self.alloc_temp(ty);
                self.emit(Statement::Assign(Place::new(tmp), Rvalue::Use(other)));
                tmp
            }
        }
    }

    /// The two fields (`.0` data pointer, `.1` length or vtable) of a slice or trait object.
    fn fat_pointer_fields(local: LocalId) -> (Place, Place) {
        let mut first = Place::new(local);
        first.projections.push(Projection::Field(0));
        let mut second = Place::new(local);
        second.projections.push(Projection::Field(1));
        (first, second)
    }

    /// Builds a slice or trait object `{ data, meta }` of type `ty` in a new temporary.
    fn emit_fat_pointer(
        &mut self,
        ty: TypeId,
        data: Operand,
        meta: Operand,
        moved: bool,
    ) -> Operand {
        let dst = self.alloc_temp(ty);
        self.emit(Statement::Assign(Place::new(dst), Rvalue::Aggregate(ty, vec![data, meta])));
        if moved {
            Operand::Move(Place::new(dst))
        } else {
            Operand::Copy(Place::new(dst))
        }
    }

    /// Builds variant `variant` of union `ty` in a new temporary, as a copy or move per its type.
    fn emit_union(&mut self, ty: TypeId, variant: u32, payload: Operand) -> Operand {
        let dst = self.alloc_temp(ty);
        self.emit(Statement::Assign(Place::new(dst), Rvalue::Union { ty, variant, payload }));
        self.local_operand(dst, ty)
    }

    /// Builds variant `variant` of union `ty` in a new temporary, always moved out.
    fn emit_union_move(&mut self, ty: TypeId, variant: u32, payload: Operand) -> Operand {
        let dst = self.alloc_temp(ty);
        self.emit(Statement::Assign(Place::new(dst), Rvalue::Union { ty, variant, payload }));
        Operand::Move(Place::new(dst))
    }

    /// `local` as an operand: copied if `ty` is `copy`, otherwise moved.
    pub(super) fn local_operand(&self, local: LocalId, ty: TypeId) -> Operand {
        if self.is_copy_type(ty) {
            Operand::Copy(Place::new(local))
        } else {
            Operand::Move(Place::new(local))
        }
    }

    /// `local.<proj>` of type `ty`, copied if `copy`, otherwise moved.
    fn copy_or_move(&self, local: LocalId, proj: Projection, ty: TypeId) -> Operand {
        let mut place = Place::new(local);
        place.projections.push(proj);
        if self.is_copy_type(ty) {
            Operand::Copy(place)
        } else {
            Operand::Move(place)
        }
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

        let Type::Union { tag: tag_ty, .. } =
            self.compiler.program.types[src_err_ty.0 as usize]
        else {
            unreachable!()
        };
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
        self.body.blocks[unreach_bb.0 as usize].terminator = Terminator::Unreachable;
        self.body.terminated[unreach_bb.0 as usize] = true;

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
            self.body.cur_block = bb;
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

        self.body.cur_block = join_bb;
        let res_op = if self.is_copy_type(dst_err_ty) {
            Operand::Copy(Place::new(dst_local))
        } else {
            Operand::Move(Place::new(dst_local))
        };
        Ok(res_op)
    }

    pub(super) fn lower_stmt(&mut self, stmt: &Stmt) -> Result<(), String> {
        match stmt {
            Stmt::Let {
                mutable: _,
                name,
                ty,
                init,
            } if name == "_" => self.lower_discard(ty.as_ref(), init),
            Stmt::Let {
                mutable,
                name,
                ty,
                init,
            } => {
                self.lower_let_stmt(mutable, name, ty, init)
            }
            Stmt::LetDeferred { name, ty } => self.lower_let_deferred(name, ty),
            Stmt::Assign { target: Expr::Path(p), op: None, value } if p.len() == 1 && p[0] == "_" => {
                self.lower_discard(None, value)
            }
            Stmt::Assign { target, op, value } => {
                self.lower_assign_stmt(target, op, value)
            }
            Stmt::If {
                cond,
                then_block,
                else_block,
            } => {
                if let Some(const_b) = self.try_eval_comptime_branch_cond(cond) {
                    if const_b {
                        self.lower_scoped_block(then_block)?;
                    } else if let Some(eb) = else_block {
                        self.lower_scoped_block(eb)?;
                    }
                    return Ok(());
                }
                let (cond_op, _) = self.lower_expr(cond, None)?;
                let then_bb = self.new_block();
                let else_bb = self.new_block();
                self.terminate(Terminator::SwitchInt {
                    discr: cond_op,
                    targets: vec![(1, then_bb)],
                    otherwise: else_bb,
                });

                self.body.cur_block = then_bb;
                self.lower_scoped_block(then_block)?;
                let then_end_bb = self.body.cur_block;
                let then_open = !self.is_terminated();

                self.body.cur_block = else_bb;
                if let Some(eb) = else_block {
                    self.lower_scoped_block(eb)?;
                }
                let else_end_bb = self.body.cur_block;
                let else_open = !self.is_terminated();

                if then_open || else_open {
                    let join_bb = self.new_block();
                    if then_open {
                        self.body.blocks[then_end_bb.0 as usize].terminator =
                            Terminator::Goto { target: join_bb };
                    }
                    if else_open {
                        self.body.blocks[else_end_bb.0 as usize].terminator =
                            Terminator::Goto { target: join_bb };
                    }
                    self.body.cur_block = join_bb;
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

                self.body.cur_block = then_bb;
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
                    mutable: false,
                });
                self.lower_block_stmts(then_block)?;
                if !self.is_terminated() {
                    self.cleanup_top_scope();
                }
                let then_end_bb = self.body.cur_block;
                let then_open = !self.is_terminated();
                self.pop_scope();

                self.body.cur_block = else_bb;
                if let Some(eb) = else_block {
                    self.lower_scoped_block(eb)?;
                }
                let else_end_bb = self.body.cur_block;
                let else_open = !self.is_terminated();

                if then_open || else_open {
                    let join_bb = self.new_block();
                    if then_open {
                        self.body.blocks[then_end_bb.0 as usize].terminator =
                            Terminator::Goto { target: join_bb };
                    }
                    if else_open {
                        self.body.blocks[else_end_bb.0 as usize].terminator =
                            Terminator::Goto { target: join_bb };
                    }
                    self.body.cur_block = join_bb;
                }
                Ok(())
            }
            Stmt::While { cond, body } => {
                let cond_bb = self.new_block();
                let body_bb = self.new_block();
                let exit_bb = self.new_block();
                self.terminate(Terminator::Goto { target: cond_bb });

                self.body.cur_block = cond_bb;
                let (cond_op, _) = self.lower_expr(cond, None)?;
                // Each time round has temporaries of its own.
                self.drop_statement_temps(false);
                self.terminate(Terminator::SwitchInt {
                    discr: cond_op,
                    targets: vec![(1, body_bb)],
                    otherwise: exit_bb,
                });

                self.body.cur_block = body_bb;
                self.loops.push(LoopCtx {
                    continue_bb: cond_bb,
                    break_bb: exit_bb,
                    scope_depth: self.scopes.len(),
                    label: self.pending_loop_label.take(),
                });
                let res = self.lower_scoped_block(body);
                self.loops.pop();
                res?;
                if !self.is_terminated() {
                    self.terminate(Terminator::Goto { target: cond_bb });
                }

                self.body.cur_block = exit_bb;
                Ok(())
            }
            Stmt::WhileLet {
                var_name,
                opt_expr,
                body,
            } => {
                let cond_bb = self.new_block();
                let body_bb = self.new_block();
                let exit_bb = self.new_block();
                self.terminate(Terminator::Goto { target: cond_bb });

                self.body.cur_block = cond_bb;
                // Each time round has temporaries of its own, which the body can borrow from.
                let loop_depth = self.scopes.len();
                self.scopes.push(Vec::new());
                let (opt_op, opt_ty) = self.lower_expr(opt_expr, None)?;
                let Type::Union { tag, variants } =
                    self.compiler.program.types[opt_ty.0 as usize].clone()
                else {
                    return Err("`while let` requires an optional `?T` expression".to_string());
                };
                let payload_ty = variants[1];
                let opt_local = self.alloc_temp(opt_ty);
                self.emit(Statement::Assign(Place::new(opt_local), Rvalue::Use(opt_op)));
                let discr_local = self.alloc_temp(tag);
                self.emit(Statement::Assign(
                    Place::new(discr_local),
                    Rvalue::Discriminant(Place::new(opt_local)),
                ));
                let finished_bb = self.new_block();
                self.terminate(Terminator::SwitchInt {
                    discr: Operand::Copy(Place::new(discr_local)),
                    targets: vec![(1, body_bb)],
                    otherwise: finished_bb,
                });
                self.body.cur_block = finished_bb;
                self.cleanup_top_scope();
                self.terminate(Terminator::Goto { target: exit_bb });

                self.body.cur_block = body_bb;
                self.loops.push(LoopCtx {
                    continue_bb: cond_bb,
                    break_bb: exit_bb,
                    scope_depth: loop_depth,
                    label: self.pending_loop_label.take(),
                });
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
                self.emit(Statement::Assign(Place::new(var_local), Rvalue::Use(payload_op)));
                self.comptime_env
                    .insert(format!("__var_ty:{var_name}"), ComptimeVal::Type(payload_ty));
                self.scopes.last_mut().unwrap().push(ScopeVar {
                    name: var_name.clone(),
                    local: var_local,
                    ty: payload_ty,
                    opaque_bound: None,
                    mutable: false,
                });
                let res = self.lower_block_stmts(body);
                self.loops.pop();
                res?;
                let falls_through = !self.is_terminated();
                if falls_through {
                    self.cleanup_top_scope();
                }
                self.pop_scope();
                if falls_through {
                    self.cleanup_top_scope();
                    self.terminate(Terminator::Goto { target: cond_bb });
                }
                self.pop_scope();

                self.body.cur_block = exit_bb;
                Ok(())
            }
            Stmt::For {
                var_name,
                mode,
                idx_name,
                iter,
                body,
            } => self.lower_for(var_name, *mode, idx_name.as_deref(), iter, body),
            Stmt::LetDestructure {
                mutable,
                ty,
                ty_args,
                fields,
                rest,
                init,
            } => {
                let path = match ty {
                    Some(path) if !ty_args.is_empty() => {
                        let te = TypeExpr::TypeCall {
                            path: path.clone(),
                            args: ty_args.clone(),
                        };
                        Some(vec![self.name_type_for_paths(&te)?])
                    }
                    other => other.clone(),
                };
                self.lower_let_destructure(*mutable, path.as_deref(), fields, *rest, init)
            }
            Stmt::Match { scrutinee, arms } => {
                let void_ty = self.compiler.intern_type(Type::Void);
                let _ = self.lower_match(scrutinee, arms, Some(void_ty), true)?;
                Ok(())
            }
            Stmt::Labeled { label, stmt } => {
                if self.loops.iter().any(|c| c.label.as_deref() == Some(label)) {
                    return Err(format!(
                        "Loop label '{label}' is already used by an enclosing loop"
                    ));
                }
                self.pending_loop_label = Some(label.clone());
                let res = self.lower_stmt(stmt);
                self.pending_loop_label = None;
                res
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
                let ret_ty = self.body.locals[0];
                if let Some(expr) = opt_expr {
                    let (op, expr_ty) = self.lower_returned_expr(expr, ret_ty)?;
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
            Stmt::NoSuspend(blk) => {
                self.nosuspend_depth += 1;
                let res = self.lower_scoped_block(blk);
                self.nosuspend_depth -= 1;
                res
            }
            Stmt::ComptimeFor {
                var_name,
                idx_name,
                iterable,
                body,
            } => {
                let iter_val = self.compiler.eval_comptime_val(
                    &self.mod_path,
                    self.owner_ty,
                    &self.comptime_env,
                    iterable,
                )?;
                let ComptimeVal::List(items, elem_ty_opt) = iter_val else {
                    return Err(format!(
                        "'comptime for' requires a compile-time slice or reflection list, found {}",
                        self.compiler.comptime_val_label(&iter_val)
                    ));
                };
                let prev_var = self.comptime_env.get(var_name).cloned();
                let var_ty_key = format!("__var_ty:{var_name}");
                let prev_var_ty = self.comptime_env.get(&var_ty_key).cloned();
                let prev_idx = idx_name.as_ref().map(|inm| {
                    (
                        inm.clone(),
                        self.comptime_env.get(inm).cloned(),
                        self.comptime_env.get(&format!("__var_ty:{inm}")).cloned(),
                    )
                });
                let usize_ty = self.compiler.intern_type(Type::Int {
                    signed: false,
                    bits: 64,
                });
                let mut loop_err: Option<String> = None;
                for (idx, item) in items.into_iter().enumerate() {
                    if self.is_terminated() {
                        break;
                    }
                    self.comptime_env.insert(var_name.clone(), item);
                    if let Some(et) = elem_ty_opt {
                        self.comptime_env
                            .insert(var_ty_key.clone(), ComptimeVal::Type(et));
                    } else {
                        self.comptime_env.remove(&var_ty_key);
                    }
                    if let Some(iname) = idx_name {
                        self.comptime_env
                            .insert(iname.clone(), ComptimeVal::Int(idx as i128));
                        self.comptime_env
                            .insert(format!("__var_ty:{iname}"), ComptimeVal::Type(usize_ty));
                    }
                    self.scopes.push(Vec::new());
                    let mut iter_err = None;
                    for (i, s) in body.stmts.iter().enumerate() {
                        if self.is_terminated() {
                            break;
                        }
                        self.mark_line(body, i);
                        if let Err(e) = self.lower_stmt(s) {
                            iter_err =
                                Some(format!("{e} (in comptime for '{var_name}' at index {idx})"));
                            break;
                        }
                    }
                    if !self.is_terminated() && iter_err.is_none() {
                        self.cleanup_top_scope();
                    }
                    self.pop_scope();
                    if let Some(e) = iter_err {
                        loop_err = Some(e);
                        break;
                    }
                }
                if let Some(pv) = prev_var {
                    self.comptime_env.insert(var_name.clone(), pv);
                } else {
                    self.comptime_env.remove(var_name);
                }
                if let Some(pvt) = prev_var_ty {
                    self.comptime_env.insert(var_ty_key, pvt);
                } else {
                    self.comptime_env.remove(&var_ty_key);
                }
                if let Some((inm, piv, pivt)) = prev_idx {
                    if let Some(v) = piv {
                        self.comptime_env.insert(inm.clone(), v);
                    } else {
                        self.comptime_env.remove(&inm);
                    }
                    let ity_key = format!("__var_ty:{inm}");
                    if let Some(vt) = pivt {
                        self.comptime_env.insert(ity_key, vt);
                    } else {
                        self.comptime_env.remove(&ity_key);
                    }
                }
                if let Some(e) = loop_err {
                    return Err(e);
                }
                Ok(())
            }
            Stmt::Expr(expr) => {
                self.last_call = None;
                let (op, ty) = self.lower_expr(expr, None)?;
                self.check_discarded(expr, ty)?;
                if !self.is_terminated()
                    && !self.is_copy_type(ty)
                    && let Operand::Move(place) = op
                {
                    let next_bb = self.new_block();
                    self.terminate(Terminator::Drop {
                        place,
                        target: next_bb,
                    });
                    self.body.cur_block = next_bb;
                }
                Ok(())
            }
        }
    }

    /// A statement `expr;` leaves its value unused, which is allowed for `void` and for a call
    /// of a function declared `discardable` (unless the value is an error union); anything else
    /// takes `_ = expr;`, so that a result is not lost by accident.
    fn check_discarded(&self, expr: &Expr, ty: TypeId) -> Result<(), String> {
        let ty = self.resolve_type_var(ty);
        if matches!(self.compiler.program.types[ty.0 as usize], Type::Void | Type::Never) || self.is_terminated() {
            return Ok(());
        }
        // A linear one cannot be discarded at all, which the move checker says.
        if self.compiler.is_linear_type(ty) {
            return Ok(());
        }
        let shown = self.compiler.type_display_name(ty);
        if let Some(info) = self.compiler.results.get(&ty) {
            let shown = format!(
                "{}!{}",
                self.compiler.type_display_name(info.err_ty),
                self.compiler.type_display_name(info.ok_ty)
            );
            return Err(format!(
                "This discards an error union '{shown}', and with it any error; handle it with 'try' or 'catch', or discard it with '_ = ...'"
            ));
        }
        let call = matches!(expr, Expr::Call { .. } | Expr::MethodCall { .. });
        if call && self.last_call.is_some_and(|f| self.compiler.discardable_fns.contains(&f)) {
            return Ok(());
        }
        Err(format!(
            "This discards a value of type '{shown}'; use it, or discard it with '_ = ...' (a function whose result may go unused says so: '-> {shown} discardable')"
        ))
    }

    /// `let _ = expr;` and `_ = expr;`. A place of a variable (`x`, `x.f`, `*p`) is left as it
    /// is: not read, moved, or dropped. Any other value is dropped at once. A linear value cannot
    /// be discarded so.
    fn lower_discard(&mut self, ty: Option<&TypeExpr>, expr: &Expr) -> Result<(), String> {
        let place = !matches!(expr, Expr::Slice { .. })
            && Self::root_var_of_place_expr(expr)
                .is_some_and(|v| self.lookup_var(v).is_some() || self.lookup_capture(v).is_some());
        if place {
            return Ok(());
        }
        let expected = match ty {
            Some(t) => Some(self.compiler.resolve_type_expr(&self.mod_path, self.owner_ty, &self.comptime_env, t)?),
            None => None,
        };
        let (mut op, mut val_ty) = self.lower_expr(expr, expected)?;
        if let Some(t) = expected {
            op = self.coerce_operand(op, val_ty, t)?;
            val_ty = t;
        }
        if self.compiler.is_linear_type(val_ty) {
            return Err(format!(
                "'_' would discard a linear value of type '{}', which must be consumed; consume it, or bind it to a name",
                self.compiler.type_display_name(val_ty)
            ));
        }
        if !self.is_terminated()
            && !self.is_copy_type(val_ty)
            && let Operand::Move(place) = op
        {
            let next_bb = self.new_block();
            self.terminate(Terminator::Drop { place, target: next_bb });
            self.body.cur_block = next_bb;
        }
        Ok(())
    }

    /// Lowers `let` / `let mut`: the initializer, its declared or inferred type, and the binding.
    /// `let mut name: ty;`: storage only. The move checker sees no initialization, so it rejects
    /// reads until the variable, or each field read, is assigned.
    fn lower_let_deferred(&mut self, name: &str, ty: &TypeExpr) -> Result<(), String> {
        let var_ty = self.compiler.resolve_type_expr(
            &self.mod_path,
            self.owner_ty,
            &self.comptime_env,
            ty,
        )?;
        if self.compiler.traits.contains_key(&var_ty)
            || self.compiler.is_opaque_type(var_ty)
            || self.compiler.is_comptime_only_type(var_ty)
        {
            return Err(format!(
                "Type '{}' cannot be bound by value in 'let mut {name}'",
                self.compiler.type_display_name(var_ty)
            ));
        }
        let local = self.alloc_temp(var_ty);
        self.emit(Statement::StorageLive(local));
        self.comptime_env.remove(name);
        self.comptime_env
            .insert(format!("__var_ty:{name}"), ComptimeVal::Type(var_ty));
        self.scopes.last_mut().unwrap().push(ScopeVar {
            name: name.to_string(),
            local,
            ty: var_ty,
            opaque_bound: None,
            mutable: true,
        });
        Ok(())
    }

    fn lower_let_stmt(
        &mut self,
        mutable: &bool,
        name: &str,
        ty: &Option<TypeExpr>,
        init: &Expr,
    ) -> Result<(), String> {
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
            self.comptime_env.insert(name.to_string(), ct_val);
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
        // A type function keeps compile-time values it fills or changes at run time (`type`s,
        // records of them) in VM locals: `let specs: [FieldSpec; n] = uninit;`,
        // `let mut t: type = T;`.
        let runtime_uninit = self.type_fn.is_some() && matches!(init, Expr::Uninit(None));
        let runtime_ct = runtime_uninit
            || (self.type_fn.is_some()
                && *mutable
                && (matches!(init, Expr::TypeVal(_) | Expr::Path(_) | Expr::Call { .. })
                    || self.index_type_call(init).is_some()));
        // `let x: ?void = void;` binds the value, as any type but `type` would.
        let is_void_val = matches!(init, Expr::TypeVal(TypeExpr::Void))
            && expected_ty.is_some_and(|t| !self.compiler.is_comptime_only_type(t));
        if !runtime_ct
            && !is_void_val
            && (expected_ty.is_some_and(|t| {
                self.compiler.maps.contains_key(&t) || self.compiler.is_comptime_only_type(t)
            }) || self.is_comptime_only_expr(init))
        {
            let ct_val = if let Ok((_, _, cv)) = self.compiler.eval_const_expr_typed(
                &self.mod_path,
                self.owner_ty,
                &self.comptime_env,
                init,
                expected_ty,
            ) {
                cv
            } else {
                self.compiler.eval_comptime_val(
                    &self.mod_path,
                    self.owner_ty,
                    &self.comptime_env,
                    init,
                )?
            };
            self.comptime_env.insert(name.to_string(), ct_val);
            return Ok(());
        }
        if !*mutable
            && matches!(
                init,
                Expr::IntrinsicVariants(_)
                    | Expr::IntrinsicEntries(_)
                    | Expr::IntrinsicDeclarations(_)
                    | Expr::SliceLit { .. }
                    | Expr::StructLit { .. }
                    | Expr::TupleLit(_)
            )
            && let Ok(ct_val) = self.compiler.eval_comptime_val(
                &self.mod_path,
                self.owner_ty,
                &self.comptime_env,
                init,
            )
        {
            self.comptime_env.insert(name.to_string(), ct_val);
        } else {
            self.comptime_env.remove(name);
        }
        if matches!(init, Expr::Uninit(None))
            && let Some(var_ty) = expected_ty
            && (self.compiler.is_uninit_compatible_type(var_ty) || runtime_uninit)
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
                name: name.to_string(),
                local,
                ty: var_ty,
                opaque_bound: None,
                mutable: *mutable,
            });
            return Ok(());
        }
        // An unannotated literal binding gets a type variable, bound by its first typed use.
        let is_literal = |e: &Expr| matches!(e, Expr::Int(_) | Expr::Float(_));
        let expected_ty = match (expected_ty, init) {
            (None, e) if is_literal(e) => Some(self.new_type_var(matches!(e, Expr::Float(_)))),
            (
                None,
                Expr::Unary {
                    op: UnOp::Neg,
                    expr: inner,
                },
            ) if is_literal(inner) => {
                Some(self.new_type_var(matches!(inner.as_ref(), Expr::Float(_))))
            }
            (t, _) => t,
        };
        self.last_call_opaque_bound = None;
        let (init_op, inferred_ty) = self.lower_expr_open(init, expected_ty)?;
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
            name: name.to_string(),
            local,
            ty: var_ty,
            opaque_bound: call_opaque_bound,
            mutable: *mutable,
        });
        Ok(())
    }

    /// Lowers `target = value` and compound assignments (`target op= value`).
    fn lower_assign_stmt(
        &mut self,
        target: &Expr,
        op: &Option<BinOp>,
        value: &Expr,
    ) -> Result<(), String> {
        if let Expr::IntrinsicField { base, field } = target {
            let resolved = self.resolve_intrinsic_field_target(base, field)?;
            return self.lower_stmt(&Stmt::Assign {
                target: resolved,
                op: *op,
                value: value.clone(),
            });
        }
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
                self.check_binding_writable(&base_place, "assign to")?;
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
                self.check_binding_writable(&base_place, "assign to")?;
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
        self.check_binding_writable(&place, "assign to")?;
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
            if !self.operator_applies(*binop, target_ty) {
                return Err(format!(
                    "Operator '{}=' is not defined on '{}'",
                    crate::wide::op_symbol(*binop),
                    self.compiler.type_display_name(target_ty)
                ));
            }
            let (mut rhs_op, rhs_ty) = self.lower_expr(value, Some(target_ty))?;
            // As for binary operators, the right operand converts to the target's type (pointer
            // arithmetic aside, whose offset is an integer).
            if !matches!(
                self.compiler.program.types[target_ty.0 as usize],
                Type::Ptr { .. }
            ) && rhs_ty != target_ty
            {
                let base_ty = self.pattern_base(target_ty);
                rhs_op = match self.coerce_operand(rhs_op, rhs_ty, base_ty) {
                    Ok(op) => op,
                    Err(e) => {
                        let target_local = place.projections.is_empty().then_some(place.local);
                        self.learn_type_hint(target_local, rhs_ty);
                        return Err(format!("{e} (in '{}=')", crate::wide::op_symbol(*binop)));
                    }
                };
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
                self.check_linear_sink(inner_ty, "stores", " in 'uninit' storage")?;
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
            if place.projections.contains(&Projection::Deref) {
                self.check_linear_sink(target_ty, "writes", " through a raw pointer")?;
            }
            let (val_op, val_ty) = self.lower_expr(value, Some(target_ty))?;
            let coerced = self.coerce_operand(val_op, val_ty, target_ty)?;
            // Overwriting a local or a plain field path of a local drops the previous value
            // first; drop elaboration turns this into a no-op when the path was moved out
            // and rejects it when a still-live linear value would be discarded. A place reached
            // through a safe reference always holds a value to drop; one reached through a raw
            // pointer may not (`Vec::push` writes into uninitialized storage).
            let holds_value = self.is_local_field_path(&place) || self.place_traverses_safe_ref(&place);
            if holds_value && !self.is_copy_type(target_ty) {
                let next_bb = self.new_block();
                self.terminate(Terminator::Drop {
                    place: place.clone(),
                    target: next_bb,
                });
                self.body.cur_block = next_bb;
            }
            self.emit(Statement::Assign(place, Rvalue::Use(coerced)));
        }
        Ok(())
    }

    pub(super) fn is_copy_type(&self, ty_id: TypeId) -> bool {
        self.compiler.is_copy_type(ty_id)
    }

    pub(super) fn resolve_intrinsic_field_target(
        &mut self,
        base: &Expr,
        field: &Expr,
    ) -> Result<Expr, String> {
        let fval = self.compiler.eval_comptime_val(
            &self.mod_path,
            self.owner_ty,
            &self.comptime_env,
            field,
        )?;
        self.compiler.field_access_expr(base, &fval)
    }

    pub(super) fn has_comptime_root(&self, expr: &Expr) -> bool {
        match expr {
            Expr::TypeVal(_)
            | Expr::IntrinsicTypeName(_)
            | Expr::IntrinsicSatisfies { .. }
            | Expr::IntrinsicHasField { .. }
            | Expr::IntrinsicHasMethod { .. }
            | Expr::IntrinsicFields(_)
            | Expr::IntrinsicLeaves(_)
            | Expr::IntrinsicVariants(_)
            | Expr::IntrinsicEntries(_)
            | Expr::IntrinsicFnInfo(_)
            | Expr::IntrinsicDeclarations(_)
            | Expr::IntrinsicMap { .. }
            | Expr::MapLit(_)
            | Expr::IntrinsicInvert(_) => true,
            Expr::Path(p) => {
                if p.len() == 1
                    && (self.lookup_var(&p[0]).is_some() || self.lookup_capture(&p[0]).is_some())
                {
                    return false;
                }
                if p.len() == 1 && self.comptime_env.contains_key(&p[0]) {
                    return true;
                }
                let expanded = self.compiler.expand_module_path(&self.comptime_env, p);
                matches!(
                    self.compiler.resolve_path(&self.mod_path, &expanded),
                    Ok(ResolvedItem::Const(..)
                        | ResolvedItem::Type(..)
                        | ResolvedItem::Module(..))
                )
            }
            Expr::Field { base, .. }
            | Expr::TupleIndex { base, .. }
            | Expr::Index { base, .. }
            | Expr::IntrinsicField { base, .. } => self.has_comptime_root(base),
            _ => false,
        }
    }

    pub(super) fn expr_has_comptime_subexpr(&self, expr: &Expr) -> bool {
        if self.has_comptime_root(expr) {
            return true;
        }
        match expr {
            Expr::Unary { expr: inner, .. } => self.expr_has_comptime_subexpr(inner),
            Expr::Binary { lhs, rhs, .. }
            | Expr::LogicalAnd(lhs, rhs)
            | Expr::LogicalOr(lhs, rhs) => {
                self.expr_has_comptime_subexpr(lhs) || self.expr_has_comptime_subexpr(rhs)
            }
            Expr::Cast { expr: inner, .. } => self.expr_has_comptime_subexpr(inner),
            _ => false,
        }
    }

    pub(super) fn try_eval_comptime_branch_cond(&mut self, cond: &Expr) -> Option<bool> {
        match cond {
            Expr::LogicalAnd(a, b) => {
                let l = self.try_eval_comptime_branch_cond(a);
                if l == Some(false) {
                    return Some(false);
                }
                let r = self.try_eval_comptime_branch_cond(b);
                if r == Some(false) {
                    return Some(false);
                }
                if l == Some(true) && r == Some(true) {
                    return Some(true);
                }
                None
            }
            Expr::LogicalOr(a, b) => {
                let l = self.try_eval_comptime_branch_cond(a);
                if l == Some(true) {
                    return Some(true);
                }
                let r = self.try_eval_comptime_branch_cond(b);
                if r == Some(true) {
                    return Some(true);
                }
                if l == Some(false) && r == Some(false) {
                    return Some(false);
                }
                None
            }
            Expr::Unary {
                op: UnOp::Not,
                expr: inner,
            } => self.try_eval_comptime_branch_cond(inner).map(|b| !b),
            _ => {
                if !self.expr_has_comptime_subexpr(cond) {
                    return None;
                }
                let bool_ty = self.compiler.intern_type(Type::Bool);
                let outer = std::mem::replace(&mut self.compiler.implicit_folding, true);
                let folded = if let Ok((ConstValue::Bool(b), _, _)) = self.compiler.eval_const_expr_typed(
                    &self.mod_path,
                    self.owner_ty,
                    &self.comptime_env,
                    cond,
                    Some(bool_ty),
                ) {
                    Some(b)
                } else if let Ok(ComptimeVal::Bool(b)) = self.compiler.eval_comptime_val(
                    &self.mod_path,
                    self.owner_ty,
                    &self.comptime_env,
                    cond,
                ) {
                    Some(b)
                } else {
                    None
                };
                self.compiler.implicit_folding = outer;
                folded
            }
        }
    }

    pub(super) fn is_comptime_only_expr(&mut self, expr: &Expr) -> bool {
        match expr {
            Expr::TypeVal(TypeExpr::TypeCall { path, args })
                if self.generic_fn_value(path, args.len()).is_some() =>
            {
                false
            }
            Expr::Index { base, .. }
                if matches!(base.as_ref(), Expr::Path(p) if self.generic_fn_value(p, 1).is_some()) =>
            {
                false
            }
            Expr::TypeVal(_)
            | Expr::IntrinsicFields(_)
            | Expr::IntrinsicLeaves(_)
            | Expr::IntrinsicFnInfo(_)
            | Expr::IntrinsicMap { .. }
            | Expr::MapLit(_)
            | Expr::IntrinsicInvert(_) => true,
            Expr::IntrinsicVariants(te) => self
                .compiler
                .resolve_type_expr(&self.mod_path, self.owner_ty, &self.comptime_env, te)
                .is_ok_and(|t| {
                    self.compiler.unions.contains_key(&t) || self.compiler.errors.contains_key(&t)
                }),
            Expr::IntrinsicEntries(me) => self
                .compiler
                .resolve_map_expr(&self.mod_path, self.owner_ty, &self.comptime_env, me)
                .ok()
                .flatten()
                .is_some_and(|map_id| {
                    let inst = &self.compiler.map_instances[map_id as usize];
                    let minfo = self.compiler.maps[&inst.map_ty];
                    self.compiler.is_comptime_only_type(minfo.key_ty)
                        || self.compiler.is_comptime_only_type(minfo.val_ty)
                }),
            Expr::Path(p) => {
                p.len() == 1
                    && self.lookup_var(&p[0]).is_none()
                    && self.lookup_capture(&p[0]).is_none()
                    && matches!(
                        self.comptime_env.get(&p[0]),
                        Some(
                            ComptimeVal::Type(_)
                                | ComptimeVal::Module(_)
                                | ComptimeVal::Map(_)
                                | ComptimeVal::List(..)
                                | ComptimeVal::Record(..)
                                | ComptimeVal::Tuple(..)
                        )
                    )
            }
            // Integer reflection (`T::MAX`, `T::bits`) yields a plain value of a runtime type.
            Expr::Field { field, .. }
                if matches!(
                    field.as_str(),
                    "MIN" | "MAX" | "bits" | "BITS" | "signed" | "SIGNED"
                ) =>
            {
                false
            }
            Expr::Field { base, .. }
            | Expr::TupleIndex { base, .. }
            | Expr::Index { base, .. }
            | Expr::IntrinsicField { base, .. } => self.is_comptime_only_expr(base),
            Expr::SliceLit { elems, .. } | Expr::TupleLit(elems) => {
                elems.iter().any(|e| self.is_comptime_only_expr(e))
            }
            Expr::StructLit { ty, fields } => {
                self.compiler
                    .resolve_type_expr(&self.mod_path, self.owner_ty, &self.comptime_env, ty)
                    .is_ok_and(|t| self.compiler.is_comptime_only_type(t))
                    || fields.iter().any(|(_, e)| self.is_comptime_only_expr(e))
            }
            _ => false,
        }
    }

    pub(super) fn check_field_access(
        &self,
        comp_ty: TypeId,
        field_name: &str,
    ) -> Result<(u32, TypeId), String> {
        let Some(comp) = self.compiler.composites.get(&comp_ty) else {
            return Err(format!(
                "Type '{}' has no named fields",
                self.compiler.type_display_name(comp_ty)
            ));
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
        if comp.is_opaque && *f_vis == Visibility::Private && !self.has_private_access(comp_ty) {
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
    ) -> Result<Option<ConstOrStatic>, String> {
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
                    if comp.is_opaque
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
                if let Some((cval, cty, _)) = self.compiler.impl_assoc_const(comp_ty, member)? {
                    return Ok(Some(Ok((cval, cty))));
                }
                if let Some(comp) = self.compiler.composites.get(&comp_ty)
                    && comp.statics.contains_key(member)
                {
                    let (gl_id, sty, is_mut, svis) =
                        self.compiler.resolve_associated_static(comp_ty, member)?;
                    let comp = &self.compiler.composites[&comp_ty];
                    if comp.is_opaque
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
        if let Some((at, place, ty)) = self.lowered_base.take() {
            if std::ptr::eq(at, expr) {
                return Ok((place, ty));
            }
            self.lowered_base = Some((at, place, ty));
        }
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
                    return Err(format!(
                        "Cannot dereference non-pointer type '{}'",
                        self.compiler.type_display_name(ty)
                    ));
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
                    _ => return Err(format!(
                        "Cannot tuple-index non-tuple type '{}'",
                        self.compiler.type_display_name(base_ty)
                    )),
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
                                "Cannot index non-array/slice/simd type '{}'",
                                self.compiler.type_display_name(base_ty)
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
                self.check_index_type(idx_ty, "Index")?;
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
            Expr::IntrinsicField { base, field } => {
                let resolved = self.resolve_intrinsic_field_target(base, field)?;
                self.lower_place(&resolved, for_write_or_move)
            }
            Expr::IntrinsicVariant { base, variant } => {
                let vval = self.compiler.eval_comptime_val(
                    &self.mod_path,
                    self.owner_ty,
                    &self.comptime_env,
                    variant,
                )?;
                let ComptimeVal::Str(vname) = vval else {
                    return Err(format!(
                        "'@variant' second argument must evaluate at comptime to a variant name ('&str'), found {}",
                        self.compiler.comptime_val_label(&vval)
                    ));
                };
                let (mut place, mut base_ty) = self.lower_place(base, for_write_or_move)?;
                if let Type::Ptr { pointee, .. } = self.compiler.program.types[base_ty.0 as usize] {
                    if self.compiler.raw_ptrs.contains_key(&base_ty) && self.unsafe_depth == 0 {
                        return Err(format!(
                            "Dereferencing raw pointer of type '{}' for '@variant' access '{}' is unsafe and requires an 'unsafe {{ ... }}' block",
                            self.compiler.type_display_name(base_ty),
                            vname
                        ));
                    }
                    place.projections.push(Projection::Deref);
                    base_ty = pointee;
                }
                let Some(uinfo) = self.compiler.unions.get(&base_ty).cloned() else {
                    return Err(format!(
                        "'@variant' requires a 'union' value or reference, found '{}'",
                        self.compiler.type_display_name(base_ty)
                    ));
                };
                let Some((v_idx, (_, payload_ty))) = uinfo
                    .variants
                    .iter()
                    .enumerate()
                    .find(|(_, (vn, _))| vn == &vname)
                else {
                    return Err(format!(
                        "Union '{}' has no variant '{}'",
                        uinfo.name, vname
                    ));
                };
                let payload_ty = *payload_ty;
                let Type::Union { tag, .. } =
                    self.compiler.program.types[base_ty.0 as usize].clone()
                else {
                    return Err(format!(
                        "'@variant' requires a 'union' value or reference, found '{}'",
                        self.compiler.type_display_name(base_ty)
                    ));
                };
                let discr_local = self.alloc_temp(tag);
                self.emit(Statement::Assign(
                    Place::new(discr_local),
                    Rvalue::Discriminant(place.clone()),
                ));
                let ok_bb = self.new_block();
                let trap_bb = self.new_block();
                self.terminate(Terminator::SwitchInt {
                    discr: Operand::Copy(Place::new(discr_local)),
                    targets: vec![(v_idx as i128, ok_bb)],
                    otherwise: trap_bb,
                });
                self.body.cur_block = trap_bb;
                self.terminate(Terminator::Unreachable);
                self.body.cur_block = ok_bb;
                place.projections.push(Projection::Variant(v_idx as u32));
                Ok((place, payload_ty))
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
                // In the scope, so that an early exit from the statement drops it too.
                if !self.is_copy_type(ty)
                    && let Some(scope) = self.scopes.last_mut()
                {
                    scope.push(ScopeVar {
                        name: format!("{STATEMENT_TEMP}{}", tmp.0),
                        local: tmp,
                        ty,
                        opaque_bound: None,
                        mutable: true,
                    });
                }
                Ok((Place::new(tmp), ty))
            }
        }
    }

    /// Drops the temporaries of the statement just lowered. A temporary lives until then, unless
    /// `let x = &value;` keeps it for as long as `x`.
    pub(super) fn drop_statement_temps(&mut self, keep: bool) {
        let Some(scope) = self.scopes.last_mut() else {
            return;
        };
        if keep {
            for var in scope.iter_mut().filter(|v| v.name.starts_with(STATEMENT_TEMP)) {
                var.name = format!("__kept{}", var.local.0);
            }
            return;
        }
        let mut temps = Vec::new();
        scope.retain(|var| {
            let temp = var.name.starts_with(STATEMENT_TEMP);
            if temp {
                temps.push(var.local);
            }
            !temp
        });
        if !self.is_terminated() {
            for local in temps.into_iter().rev() {
                self.emit_drop_and_dead(local);
            }
        }
    }

    pub(super) fn place_type(&self, place: &Place) -> TypeId {
        let mut ty = self.body.locals[place.local.0 as usize];
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

    /// Rejects an index or slice bound whose type is not `usize` or a `usize` pattern type;
    /// integers convert explicitly (`i as usize`).
    pub(super) fn check_index_type(&mut self, ty: TypeId, what: &str) -> Result<(), String> {
        let usize_ty = self.compiler.intern_type(Type::Int {
            signed: false,
            bits: 64,
        });
        self.bind_type_var(ty, usize_ty)?;
        let ty = self.resolve_type_var(ty);
        let usize_like = |t: TypeId| {
            matches!(
                self.compiler.program.types[t.0 as usize],
                Type::Int {
                    signed: false,
                    bits: 64
                }
            )
        };
        let ok = match self.compiler.program.types[ty.0 as usize] {
            Type::Pattern { base, .. } => usize_like(base),
            _ => usize_like(ty),
        };
        if ok {
            Ok(())
        } else {
            Err(format!(
                "{what} must be 'usize', found '{}'; convert with 'as usize'",
                self.compiler.type_display_name(ty)
            ))
        }
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
                    && ranges
                        .iter()
                        .all(|(lo, hi)| !lo.is_negative() && *hi < Wide::from_i128(i128::from(len)))
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
        self.body.cur_block = trap_bb;
        self.terminate(Terminator::Unreachable);
        self.body.cur_block = ok_bb;
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
                    && ranges
                        .iter()
                        .all(|(lo, hi)| !lo.is_negative() && *hi <= Wide::from_i128(i128::from(len)))
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
        self.body.cur_block = trap_bb;
        self.terminate(Terminator::Unreachable);
        self.body.cur_block = ok_bb;
        Ok(())
    }

    /// Whether `place` dereferences a raw pointer (`*const T` / `*mut T`) anywhere along its path.
    pub(super) fn place_traverses_raw_ptr(&self, place: &Place) -> bool {
        let mut ty = self.body.locals[place.local.0 as usize];
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
    /// Whether `place` is a local or a path of fields and array elements inside one. An array
    /// element always holds a value, as none can be moved out alone.
    pub(super) fn is_local_field_path(&self, place: &Place) -> bool {
        let mut ty = self.body.locals[place.local.0 as usize];
        for proj in &place.projections {
            ty = match (proj, &self.compiler.program.types[ty.0 as usize]) {
                (Projection::Field(idx), Type::Struct(fields)) => fields[*idx as usize],
                (Projection::Index(_), Type::Array { elem, .. }) => *elem,
                _ => return false,
            };
        }
        true
    }

    /// Rejects handing a linear value to storage the move checker cannot follow (a raw-pointer
    /// write, `uninit(v)`, or `@forget`, described by `verb` and `place`) inside a method of a
    /// non-linear type. Such a
    /// type would be dropped at scope exit with the value still inside it, so it must declare
    /// `opaque(owns T)` (making it linear for a linear `T`). Free functions are not checked: there
    /// the `unsafe` block itself asserts the value is accounted for (`core::mem::replace`).
    pub(super) fn check_linear_sink(
        &self,
        val_ty: TypeId,
        verb: &str,
        place: &str,
    ) -> Result<(), String> {
        let Some(owner) = self.owner_ty else {
            return Ok(());
        };
        if !self.compiler.is_linear_type(val_ty) || self.compiler.is_linear_type(owner) {
            return Ok(());
        }
        let owner_name = self.compiler.type_display_name(owner);
        Err(format!(
            "A method of '{owner_name}' {verb} a linear '{}'{place}, where the move checker cannot follow it, but '{owner_name}' is not linear, so the value could be discarded unconsumed; hold the values it stores in '*own T' or 'uninit T' fields, which make a type linear when 'T' is",
            self.compiler.type_display_name(val_ty)
        ))
    }

    pub(super) fn place_traverses_safe_ref(&self, place: &Place) -> bool {
        let mut ty = self.body.locals[place.local.0 as usize];
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

    /// Rejects writing to `place` (`what`: "assign to", "borrow mutably", ...) when it is memory
    /// of a binding not declared `mut`. A write through a dereference is governed by the
    /// pointer's mutability instead (see `place_traverses_immutable_ptr`).
    pub(super) fn check_binding_writable(&self, place: &Place, what: &str) -> Result<(), String> {
        if place.projections.contains(&Projection::Deref) {
            return Ok(());
        }
        match self.scopes.iter().flatten().rev().find(|v| v.local == place.local) {
            Some(v) if !v.mutable && !v.name.starts_with("__") => Err(format!(
                "Cannot {what} '{}': it is not declared 'mut' (use 'let mut {0}', or 'mut {0}' for a parameter)",
                v.name
            )),
            _ => Ok(()),
        }
    }

    /// Whether every shared reference `place` dereferences leads into state that may change
    /// behind one: a `cell` field, or an `opaque` that declares `unsafe sync` (and so synchronizes
    /// its own state). Raw `*const` pointers never qualify.
    pub(super) fn shared_derefs_reach_cells(&self, place: &Place) -> bool {
        let types = &self.compiler.program.types;
        let mut ty = self.body.locals[place.local.0 as usize];
        let mut pending_shared = false;
        for proj in &place.projections {
            if pending_shared {
                let reaches_cell = match (proj, self.compiler.composites.get(&ty)) {
                    (_, Some(c)) if c.is_opaque && c.threads.unsafe_sync => true,
                    (Projection::Field(i), Some(c)) => c.cell_fields.contains(&(*i as usize)),
                    _ => false,
                };
                if !reaches_cell {
                    return false;
                }
                pending_shared = false;
            }
            ty = match (proj, &types[ty.0 as usize]) {
                (Projection::Deref, &Type::Ptr { mutable, pointee }) => {
                    if !mutable {
                        if self.compiler.raw_ptrs.contains_key(&ty) {
                            return false;
                        }
                        pending_shared = true;
                    }
                    pointee
                }
                (Projection::Field(i), Type::Struct(fields) | Type::Overlay(fields)) => {
                    fields[*i as usize]
                }
                (Projection::Variant(i), Type::Union { variants, .. }) => variants[*i as usize],
                (Projection::Index(_), Type::Array { elem, .. } | Type::Simd { elem, .. }) => *elem,
                _ => return false,
            };
        }
        // `&raw mut *shared` itself: the whole pointee must permit change.
        !pending_shared || self.compiler.permits_interior_mutation(ty)
    }

    /// If `place` traverses a `cell` field on an `opaque`, returns `"TypeName.field"`.
    pub(super) fn place_traverses_cell(&self, place: &Place) -> Option<String> {
        let types = &self.compiler.program.types;
        let mut ty = self.body.locals[place.local.0 as usize];
        for proj in &place.projections {
            if let Projection::Field(i) = proj
                && let Some(c) = self.compiler.composites.get(&ty)
                && c.cell_fields.contains(&(*i as usize))
            {
                let fname = &c.fields[*i as usize].0;
                return Some(format!("{}.{fname}", c.name));
            }
            ty = match (proj, &types[ty.0 as usize]) {
                (Projection::Deref, &Type::Ptr { pointee, .. }) => pointee,
                (Projection::Field(i), Type::Struct(fields) | Type::Overlay(fields)) => {
                    fields[*i as usize]
                }
                (Projection::Variant(i), Type::Union { variants, .. }) => variants[*i as usize],
                (Projection::Index(_), Type::Array { elem, .. } | Type::Simd { elem, .. }) => *elem,
                _ => return None,
            };
        }
        None
    }

    pub(super) fn place_traverses_immutable_ptr(&self, place: &Place) -> bool {
        let mut ty = self.body.locals[place.local.0 as usize];
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
                        self.compiler.type_display_name(expected_elem_ty),
                        self.compiler.type_display_name(rhs_ty)
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
                            struct_name, field_name, self.compiler.type_display_name(arr_ty)
                        ));
                    };
                    if elem != expected_elem {
                        return Err(format!(
                            "Element type mismatch in '&rel' slice '{}.{}': expected {}, found {}",
                            struct_name,
                            field_name,
                            self.compiler.type_display_name(expected_elem),
                            self.compiler.type_display_name(elem)
                        ));
                    }
                    let (start_op, start_ty) = self.lower_expr(start, Some(usize_ty))?;
                    self.check_index_type(start_ty, "Slice start")?;
                    let start_local = self.alloc_temp(usize_ty);
                    self.emit(Statement::Assign(
                        Place::new(start_local),
                        Rvalue::Use(start_op),
                    ));
                    let (end_op, end_ty) = self.lower_expr(end, Some(usize_ty))?;
                    self.check_index_type(end_ty, "Slice end")?;
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
                            struct_name, field_name, self.compiler.type_display_name(arr_ty)
                        ));
                    };
                    if elem != expected_elem {
                        return Err(format!(
                            "Element type mismatch in '&rel' slice '{}.{}': expected {}, found {}",
                            struct_name,
                            field_name,
                            self.compiler.type_display_name(expected_elem),
                            self.compiler.type_display_name(elem)
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
        if want_mut {
            self.check_binding_writable(&base_place, "borrow mutably")?;
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

/// An implicit conversion, chosen by `FuncLowerer::classify_coercion`.
enum Coercion {
    /// The value is used as is (same type, `never`, or a fn pointer with a compatible contract).
    Identity,
    /// Reborrow a named `&mut T` as `&T` / `&mut T`.
    ReborrowRef { mutable: bool },
    /// Reborrow a named `&mut [T]` as the target slice.
    ReborrowSlice(SliceInfo),
    /// Reborrow a named `&mut Trait` as the target trait object.
    ReborrowTraitObj(TraitObjInfo),
    /// `&mut Trait` -> `&Trait`.
    TraitObjToTraitObj(TraitObjInfo),
    /// `&T` / `&mut T` -> `&Trait` / `&mut Trait`, building `T`'s vtable.
    RefToTraitObj { target: TraitObjInfo, concrete: TypeId },
    /// Pointer-to-pointer cast; the result is moved when it is a `&mut T`.
    PtrCast { move_result: bool },
    /// String literal -> `&str`.
    StrToSlice { slice: SliceInfo, len: i128 },
    /// `&[T; N]` -> `&[T]`.
    ArrayRefToSlice { slice: SliceInfo, len: i128 },
    /// `&mut [T]` -> `&[T]`.
    SliceToSlice(SliceInfo),
    /// `error` subset widening.
    WidenError,
    /// `E'!T` -> `E!T`.
    ResultToResult { src: ResultTypeInfo, dst: ResultTypeInfo },
    /// `E'` -> `E!T`.
    ErrorToResult(ResultTypeInfo),
    /// `T'` -> `E!T`, coercing the value to `T`.
    OkToResult(ResultTypeInfo),
    /// `*T` -> `?*T`, mapping a null pointer to `null`.
    RawPtrToOptional,
    /// `T` -> `?T`.
    WrapOptional,
    /// A pointer -> `?*T`, coercing it to the raw pointer `*T` first.
    PtrToOptionalPtr(TypeId),
    /// Pattern type <-> base type (a constant narrowing was verified).
    ValueCast,
}
