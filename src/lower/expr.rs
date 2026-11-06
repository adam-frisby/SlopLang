use super::*;
use crate::fasthash::FastSet as HashSet;

/// Rejects a struct literal naming a field `fields` (of type `type_name`) does not have, or
/// naming one twice.
pub(super) fn check_literal_fields<D>(
    type_name: &str,
    fields: &[(String, TypeId, Visibility, D)],
    given: &[(String, Expr)],
) -> Result<(), String> {
    for (i, (name, _)) in given.iter().enumerate() {
        if !fields.iter().any(|(f, _, _, _)| f == name) {
            return Err(format!("Struct '{type_name}' has no field '{name}'"));
        }
        if given[..i].iter().any(|(n, _)| n == name) {
            return Err(format!("Field '{name}' of '{type_name}' is given twice"));
        }
    }
    Ok(())
}

/// What a `match` scrutinee is, which decides how arm patterns map to switch values.
enum MatchKind {
    /// An `enum`: its name and `(variant, value)` list.
    Enum(String, Vec<(String, i128)>),
    /// A tagged `union`, switched on its tag.
    Union(UnionTypeInfo),
    /// An `error` / `errorcode`, switched on its tag; arms name leaves or embedded errors.
    Error(ErrorTypeInfo),
    /// A plain integer: only literal and wildcard arms.
    Int,
}

impl MatchKind {
    fn variant_count(&self) -> usize {
        match self {
            MatchKind::Enum(_, vs) => vs.len(),
            MatchKind::Union(info) => info.variants.len(),
            MatchKind::Error(info) => info.leaves.len(),
            MatchKind::Int => 0,
        }
    }

    /// The error for a `match` without a wildcard that leaves variants uncovered.
    fn non_exhaustive_error(&self, covered: &[bool]) -> Option<String> {
        let missing = |names: Vec<String>| -> Vec<String> {
            names
                .into_iter()
                .zip(covered)
                .filter(|(_, c)| !**c)
                .map(|(n, _)| n)
                .collect()
        };
        let (what, missing) = match self {
            MatchKind::Int => {
                return Some(
                    "Non-exhaustive `match` on integer requires a wildcard `_` arm".to_string(),
                );
            }
            MatchKind::Enum(name, vs) => (
                format!("enum '{name}'"),
                missing(vs.iter().map(|(vn, _)| format!("{name}::{vn}")).collect()),
            ),
            MatchKind::Union(info) => (
                format!("union '{}'", info.name),
                missing(
                    info.variants
                        .iter()
                        .map(|(vn, _)| format!("{}::{vn}", info.name))
                        .collect(),
                ),
            ),
            MatchKind::Error(info) => (
                format!("error type '{}'", info.name),
                missing(
                    info.leaves
                        .iter()
                        .map(|l| format!("{}::{}", l.key.error_name, l.key.variant_name))
                        .collect(),
                ),
            ),
        };
        (!missing.is_empty()).then(|| {
            format!(
                "Non-exhaustive `match` on {what}: missing variants: {}",
                missing.join(", ")
            )
        })
    }
}

/// The arms of a `match` as they are collected: switch targets and variant coverage.
struct MatchArms {
    covered: Vec<bool>,
    has_wildcard: bool,
    targets: Vec<(i128, BlockId)>,
    wildcard_bb: Option<BlockId>,
}

impl MatchArms {
    /// A wildcard arm at `arm_bb`: covers every variant; the first one is the fallback.
    fn wildcard(&mut self, arm_bb: BlockId) {
        self.has_wildcard = true;
        self.covered.fill(true);
        if self.wildcard_bb.is_none() {
            self.wildcard_bb = Some(arm_bb);
        }
    }
}

/// An action deferred until all pattern tests of a branch in `lower_general_match` succeed.
enum GenBindAction {
    InitHolder {
        holder_local: LocalId,
        src_place: Place,
        ty: TypeId,
    },
    RetireUnionCopyPayload {
        variant_place: Place,
        payload_ty: TypeId,
    },
    RetireLocal(LocalId),
    BindPlace {
        name: String,
        mode: BindMode,
        place: Place,
        ty: TypeId,
    },
    BindPackedField {
        name: String,
        mode: BindMode,
        place: Place,
        struct_ty: TypeId,
        field_idx: usize,
        field_ty: TypeId,
    },
    BindVal {
        name: String,
        local: LocalId,
        ty: TypeId,
    },
}

impl GenBindAction {
    fn rebase_prefix(&mut self, prefix: &Place, new_local: LocalId) {
        let rebase = |p: &mut Place| {
            if p.local == prefix.local && p.projections.starts_with(&prefix.projections) {
                let tail = p.projections[prefix.projections.len()..].to_vec();
                p.local = new_local;
                p.projections = tail;
            }
        };
        match self {
            GenBindAction::InitHolder { src_place, .. } => rebase(src_place),
            GenBindAction::RetireUnionCopyPayload { variant_place, .. } => rebase(variant_place),
            GenBindAction::BindPlace { place, .. } => rebase(place),
            GenBindAction::BindPackedField { place, .. } => rebase(place),
            GenBindAction::RetireLocal(_) | GenBindAction::BindVal { .. } => {}
        }
    }
}

/// One receive or send arm of `@select`, prepared for the five-stage lowering.
struct SelectBranchLower {
    is_send: bool,
    bind: Option<String>,
    ch_ref_local: LocalId,
    elem_ty: TypeId,
    /// Raw pointer to the value slot: the receive slot, or the value to send.
    slot_ptr_local: LocalId,
    send_val_local: Option<LocalId>,
    unsent: Option<(String, Expr)>,
    fast_fn: FuncId,
    reg_fn: FuncId,
    unreg_fn: FuncId,
    body: Expr,
}

/// A `@select` send arm's value: `(arm index, value local, element type, else |unsent| handler)`.
type UnsentSendValue = (usize, LocalId, TypeId, Option<(String, Expr)>);

impl<'a> FuncLowerer<'a> {
    /// Lowers `expr`, returning its operand and type. A value of an open type variable (see
    /// `infer.rs`) passes through only when the caller allowed it (`lower_expr_open`) or expects
    /// an integer or float, whose coercion binds it; anywhere else it takes its default type.
    /// [`Compiler::index_as_type_call`], unless `F` is a local.
    pub(super) fn index_type_call(&self, expr: &Expr) -> Option<Expr> {
        if let Expr::Index { base, .. } = expr
            && let Expr::Path(p) = base.as_ref()
            && p.len() == 1
            && (self.lookup_var(&p[0]).is_some() || self.lookup_capture(&p[0]).is_some())
        {
            return None;
        }
        self.compiler
            .index_as_type_call(&self.mod_path, &self.comptime_env, expr)
    }

    /// `f[A, B]` with no call: the function pointer to `f`'s instance for those comptime
    /// arguments (defaults fill the rest), when `f` is a function that takes run-time
    /// arguments, so the brackets cannot mean a call made at compile time.
    fn try_lower_generic_fn_value(
        &mut self,
        path: &[String],
        ct: &[Expr],
    ) -> Result<Option<(Operand, TypeId)>, String> {
        let Some((fmod, fname, candidates)) = self.generic_fn_value(path, ct.len()) else {
            return Ok(None);
        };
        let given = self.eval_ct_args(ct)?;
        let mut last_err = None;
        for decl in &candidates {
            let fn_id = self
                .compiler
                .complete_comptime_args(&fmod, &fname, decl, &given, &HashMap::default())
                .and_then(|ct_args| self.compiler.get_or_instantiate_func(&fmod, &fname, &ct_args));
            match fn_id {
                Ok(fn_id) => {
                    let fn_ptr_ty = self.compiler.named_fn_ptr_type(fn_id);
                    return Ok(Some((Operand::Const(ConstValue::Func(fn_id)), fn_ptr_ty)));
                }
                Err(e) => last_err = Some(e),
            }
        }
        Err(last_err.unwrap())
    }

    /// A generic function named where a function pointer is expected (`let f: fn(i32) -> i32 =
    /// dbl;`): its comptime arguments inferred from that type's parameters and result.
    fn try_generic_fn_from_expected(
        &mut self,
        fmod: &str,
        fname: &str,
        expected_ty: Option<TypeId>,
    ) -> Result<Option<(Operand, TypeId)>, String> {
        let Some(want) = expected_ty else {
            return Ok(None);
        };
        let Type::FnPtr { args: want_args, ret: want_ret } =
            self.compiler.program.types[want.0 as usize].clone()
        else {
            return Ok(None);
        };
        let overloads = self.compiler.find_funcs_in_module(&self.mod_path, fmod, fname)?;
        let mut last_err = None;
        let mut tried = false;
        for (_, _, decl) in &overloads {
            let ct_params: Vec<(String, TypeExpr)> = decl
                .params
                .iter()
                .filter(|p| p.is_comptime)
                .map(|p| (p.name.clone(), p.ty.clone()))
                .collect();
            let rt: Vec<&crate::ast::Param> = decl.params.iter().filter(|p| !p.is_comptime).collect();
            if ct_params.is_empty() || rt.len() != want_args.len() {
                continue;
            }
            tried = true;
            let mut inferred = HashMap::default();
            let mut ok = true;
            for (p, &a) in rt.iter().zip(&want_args) {
                if self.compiler.unify_type_pattern(fmod, &ct_params, &p.ty, a, &mut inferred)?.is_none() {
                    ok = false;
                    break;
                }
            }
            if ok {
                let _ = self.compiler.unify_type_pattern(fmod, &ct_params, &decl.ret_ty, want_ret, &mut inferred)?;
            }
            if !ok {
                continue;
            }
            let fn_id = self
                .compiler
                .complete_comptime_args(fmod, fname, decl, &[], &inferred)
                .and_then(|ct| self.compiler.get_or_instantiate_func(fmod, fname, &ct));
            match fn_id {
                Ok(fn_id) => {
                    let fn_ptr_ty = self.compiler.named_fn_ptr_type(fn_id);
                    return Ok(Some((Operand::Const(ConstValue::Func(fn_id)), fn_ptr_ty)));
                }
                Err(e) => last_err = Some(e),
            }
        }
        match last_err {
            Some(e) => Err(e),
            None if tried => Err(format!(
                "No instance of generic '{fname}' has type '{}'; its parameters or bounds do not fit",
                self.compiler.type_display_name(want)
            )),
            None => Ok(None),
        }
    }

    /// Whether `path[...]`, with `n` bracketed arguments and no call, names a function that takes
    /// run-time arguments: its module, name, and the overloads that fit.
    pub(super) fn generic_fn_value(
        &self,
        path: &[String],
        n: usize,
    ) -> Option<(String, String, Vec<FuncDecl>)> {
        if path.len() == 1
            && (self.lookup_var(&path[0]).is_some() || self.lookup_capture(&path[0]).is_some())
        {
            return None;
        }
        let Ok(ResolvedItem::Func(fmod, fname)) = self.compiler.resolve_path(&self.mod_path, path)
        else {
            return None;
        };
        let overloads = self.compiler.find_funcs_in_module(&self.mod_path, &fmod, &fname).ok()?;
        let candidates: Vec<FuncDecl> = overloads
            .into_iter()
            .map(|(_, _, d)| d)
            .filter(|d| {
                d.params.iter().any(|p| !p.is_comptime)
                    && d.params.iter().filter(|p| p.is_comptime).count() >= n
            })
            .collect();
        (!candidates.is_empty()).then_some((fmod, fname, candidates))
    }

    pub(super) fn lower_expr(
        &mut self,
        expr: &Expr,
        expected_ty: Option<TypeId>,
    ) -> Result<(Operand, TypeId), String> {
        if let Some(tc) = self.index_type_call(expr) {
            return self.lower_expr(&tc, expected_ty);
        }
        let allow = std::mem::replace(&mut self.allow_type_var, false);
        if self.is_deferred_type_expr(expr) {
            return self.lower_deferred_type_expr(expr);
        }
        let expected_ty = expected_ty.map(|t| self.resolve_type_var(t));
        let (op, ty) = self.lower_expr_kind(expr, expected_ty)?;
        let ty = self.resolve_type_var(ty);
        if self.is_open_type_var(ty) {
            let numeric_context = expected_ty.is_some_and(|t| {
                let t = self.resolve_type_var(t);
                self.is_open_type_var(t)
                    || matches!(
                        self.compiler.program.types[t.0 as usize],
                        Type::Int { .. } | Type::F32 | Type::F64 | Type::Pattern { .. }
                    )
            });
            if !allow && !numeric_context {
                self.default_type_var(ty, true)?;
                return Ok((op, self.resolve_type_var(ty)));
            }
        }
        Ok((op, ty))
    }

    /// `lower_expr` for a consumer that accepts an open type variable (arithmetic, `let`,
    /// assignment, casts).
    pub(super) fn lower_expr_open(
        &mut self,
        expr: &Expr,
        expected_ty: Option<TypeId>,
    ) -> Result<(Operand, TypeId), String> {
        self.allow_type_var = true;
        self.lower_expr(expr, expected_ty)
    }

    fn lower_expr_kind(
        &mut self,
        expr: &Expr,
        expected_ty: Option<TypeId>,
    ) -> Result<(Operand, TypeId), String> {
        match expr {
            Expr::DotVariant { name, payload } => {
                self.lower_dot_variant(name, payload.as_deref(), expected_ty)
            }
            Expr::TypeMember { ty, name } => {
                let path = [self.name_type_for_paths(ty)?, name.clone()];
                self.lower_path_expr(&path, expected_ty)
            }
            Expr::RecordLit(fields) => self.lower_record_lit(fields, expected_ty),
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
                let n_wide = Wide::from_i128(*n);
                if let Some(t) = unwrapped_expected {
                    self.note_type_var_literal(t, *n);
                }
                let ty = match unwrapped_expected {
                    Some(t) => self.compiler.check_int_literal(&n_wide, t)?,
                    None => None,
                };
                let ty = match ty {
                    Some(t) => self.pattern_base(t),
                    None => {
                        let i64_ty = self.compiler.intern_type(Type::Int {
                            signed: true,
                            bits: 64,
                        });
                        self.compiler.check_int_literal(&n_wide, i64_ty)?.unwrap()
                    }
                };
                Ok((Operand::Const(ConstValue::I64(*n)), ty))
            }
            Expr::WideInt(w) => {
                // Literals beyond `i128` need an explicit wide integer type (`u128`..`u512`).
                let target = expected_ty.map(|t| {
                    if let Some(&res_info) = self.compiler.results.get(&t) {
                        return res_info.ok_ty;
                    }
                    match &self.compiler.program.types[t.0 as usize] {
                        Type::Union { variants, .. }
                            if variants.len() == 2
                                && !self.compiler.unions.contains_key(&t)
                                && !self.compiler.errors.contains_key(&t) =>
                        {
                            variants[1]
                        }
                        _ => t,
                    }
                });
                let Some(mut t) = target else {
                    return Err(format!(
                        "Integer literal {w} does not fit in the default 'i64'; give it a wide integer type (e.g. 'let x: u256 = ...')"
                    ));
                };
                let Some(checked) = self.compiler.check_int_literal(w, t)? else {
                    return Err(format!(
                        "Integer literal {w} cannot initialize '{}'",
                        self.compiler.type_display_name(t)
                    ));
                };
                t = self.pattern_base(checked);
                Ok((Operand::Const(ConstValue::Wide(w.clone())), t))
            }
            Expr::Float(bits) => {
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
                let literal = Operand::Const(ConstValue::Str(s.clone()));
                // Its type is `&str`, unless something asks for the bytes.
                let str_ty = self.compiler.intern_str_type();
                if expected_ty.is_none_or(|t| t == str_ty) {
                    return Ok((self.coerce_operand(literal, ptr_ty, str_ty)?, str_ty));
                }
                Ok((literal, ptr_ty))
            }
            Expr::Null => {
                let exp = expected_ty
                    .ok_or_else(|| "`null` requires a known optional `?T` type context".to_string())?;
                let opt_ty = if self.compiler.as_optional_type(exp).is_some() {
                    exp
                } else if let Some(&res) = self.compiler.results.get(&exp)
                    && self.compiler.as_optional_type(res.ok_ty).is_some()
                {
                    res.ok_ty
                } else {
                    exp
                };
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
            Expr::Uninit(opt_inner) => match opt_inner {
                None => {
                    let uninit_ty = expected_ty.ok_or_else(|| {
                        "`uninit` requires a known `uninit T` or `[uninit T; N]` type context"
                            .to_string()
                    })?;
                    if !self.compiler.is_uninit_compatible_type(uninit_ty) {
                        return Err(format!(
                            "`uninit` can only initialize `uninit T` or `[uninit T; N]`, found '{}'",
                            self.compiler.type_display_name(uninit_ty)
                        ));
                    }
                    if matches!(
                        self.compiler.program.types[uninit_ty.0 as usize],
                        Type::Array { .. }
                    ) {
                        return Ok((Operand::Const(ConstValue::Void), uninit_ty));
                    }
                    let tmp = self.alloc_temp(uninit_ty);
                    let mut init_place = Place::new(tmp);
                    if matches!(
                        self.compiler.program.types[uninit_ty.0 as usize],
                        Type::Overlay(_)
                    ) {
                        init_place.projections.push(Projection::Field(0));
                    }
                    self.emit(Statement::Assign(
                        init_place,
                        Rvalue::Use(Operand::Const(ConstValue::Void)),
                    ));
                    let op = if self.is_copy_type(uninit_ty) {
                        Operand::Copy(Place::new(tmp))
                    } else {
                        Operand::Move(Place::new(tmp))
                    };
                    Ok((op, uninit_ty))
                }
                Some(inner_expr) => {
                    let expected_inner =
                        expected_ty.and_then(|t| self.compiler.uninit_types.get(&t).copied());
                    let (val_op, val_ty) = self.lower_expr(inner_expr, expected_inner)?;
                    let inner_ty = expected_inner.unwrap_or(val_ty);
                    self.check_linear_sink(inner_ty, "stores", " in 'uninit' storage")?;
                    let coerced = self.coerce_operand(val_op, val_ty, inner_ty)?;
                    let uninit_ty = self.compiler.intern_uninit_type(inner_ty)?;
                    let tmp = self.alloc_temp(uninit_ty);
                    let mut init_place = Place::new(tmp);
                    init_place.projections.push(Projection::Field(1));
                    self.emit(Statement::Assign(init_place, Rvalue::Use(coerced)));
                    let op = if self.is_copy_type(uninit_ty) {
                        Operand::Copy(Place::new(tmp))
                    } else {
                        Operand::Move(Place::new(tmp))
                    };
                    Ok((op, uninit_ty))
                }
            },
            Expr::TypeVal(te) => {
                if let TypeExpr::TypeCall { path, args } = te
                    && let Some(res) = self.try_lower_generic_fn_value(path, args)?
                {
                    return Ok(res);
                }
                // `void` where a value is expected is the value, converted as any `void` is (to
                // `?void` or `E!void`, say), rather than the type; so is a bare `void` outside a
                // type function (`mk(void)` for an inferred `T`), as a type is no use at run time.
                let void_ty = self.compiler.intern_type(Type::Void);
                let as_value = match expected_ty {
                    Some(t) => !self.compiler.is_comptime_only_type(t),
                    None => self.type_fn.is_none(),
                };
                if matches!(te, TypeExpr::Void) && as_value {
                    return Ok((Operand::Const(ConstValue::Void), void_ty));
                }
                let meta_ty = self.compiler.intern_type(Type::MetaType);
                let t_id = self.compiler.resolve_type_expr(
                    &self.mod_path,
                    self.owner_ty,
                    &self.comptime_env,
                    te,
                )?;
                Ok((Operand::Const(ConstValue::Type(t_id)), meta_ty))
            }
            Expr::Path(p) => self.lower_path_expr(p, expected_ty),
            Expr::ZeroInit => {
                let Some(ty) = expected_ty else {
                    return Err("'zeroinit' needs a known type: write 'let x: T = zeroinit;'".to_string());
                };
                if !self.compiler.is_zeroinit(ty) {
                    return Err(format!(
                        "'zeroinit' makes a value of all zero bytes, which '{}' has none of (it is not 'zeroinit')",
                        self.compiler.type_display_name(ty)
                    ));
                }
                let dst = self.alloc_temp(ty);
                self.emit(Statement::Assign(Place::new(dst), Rvalue::Use(Operand::Const(ConstValue::Zeroed))));
                Ok((self.local_operand(dst, ty), ty))
            }
            Expr::IntrinsicAssert { cond, message, pos } => {
                // Unless `cond`, `std::io::assert_failed("assertion failed: ...")`: the message is
                // written to stderr before the trap, and the VM reports it as its error.
                let bool_ty = self.compiler.intern_type(Type::Bool);
                let (holds, cond_ty) = self.lower_expr(cond, Some(bool_ty))?;
                if cond_ty != bool_ty {
                    return Err(format!(
                        "'@assert' takes a 'bool', found '{}'",
                        self.compiler.type_display_name(cond_ty)
                    ));
                }
                let text = assertion_message(message.as_deref(), *pos, &self.mod_path);
                let fail = if self.compiler.modules.contains_key("std::io") {
                    Expr::Call {
                        callee: Box::new(Expr::Path(vec![
                            "std".to_string(),
                            "io".to_string(),
                            "assert_failed".to_string(),
                        ])),
                        ct_args: None,
                        args: vec![Expr::Str(text)],
                        at: crate::ast::At::default(),
                    }
                } else {
                    Expr::IntrinsicTrap
                };
                let (ok_bb, fail_bb) = (self.new_block(), self.new_block());
                self.terminate(Terminator::SwitchInt {
                    discr: holds,
                    targets: vec![(1, ok_bb)],
                    otherwise: fail_bb,
                });
                self.body.cur_block = fail_bb;
                self.lower_expr(&fail, None)?;
                if !self.is_terminated() {
                    self.terminate(Terminator::Unreachable);
                }
                self.body.cur_block = ok_bb;
                let void_ty = self.compiler.intern_type(Type::Void);
                Ok((Operand::Const(ConstValue::Void), void_ty))
            }
            Expr::Move(_)
            | Expr::Field { .. }
            | Expr::TupleIndex { .. }
            | Expr::Index { .. }
            | Expr::Deref(_)
            | Expr::IntrinsicVariant { .. }
            | Expr::RelRef(_)
            | Expr::Ref { .. }
            | Expr::RawPtr { .. }
            | Expr::Slice { .. } => self.lower_place_or_ref_expr(expr, expected_ty),
            Expr::Unary { .. }
            | Expr::Binary { .. }
            | Expr::IntrinsicArithUnchecked { .. }
            | Expr::IntrinsicBswap(_)
            | Expr::Cast { .. } => self.lower_arith_or_cast_expr(expr, expected_ty),
            Expr::LogicalAnd(lhs, rhs) => {
                let bool_ty = self.compiler.intern_type(Type::Bool);
                match self.try_eval_comptime_branch_cond(lhs) {
                    Some(false) => return Ok((Operand::Const(ConstValue::Bool(false)), bool_ty)),
                    Some(true) => return self.lower_expr(rhs, Some(bool_ty)),
                    None => {}
                }
                if self.try_eval_comptime_branch_cond(rhs) == Some(true) {
                    return self.lower_expr(lhs, Some(bool_ty));
                }
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

                self.body.cur_block = short_bb;
                self.emit(Statement::Assign(
                    Place::new(res_local),
                    Rvalue::Use(Operand::Const(ConstValue::Bool(false))),
                ));
                self.terminate(Terminator::Goto { target: join_bb });

                self.body.cur_block = rhs_bb;
                let (r_op, _) = self.lower_expr(rhs, Some(bool_ty))?;
                self.emit(Statement::Assign(Place::new(res_local), Rvalue::Use(r_op)));
                self.terminate(Terminator::Goto { target: join_bb });

                self.body.cur_block = join_bb;
                Ok((Operand::Copy(Place::new(res_local)), bool_ty))
            }
            Expr::LogicalOr(lhs, rhs) => {
                let bool_ty = self.compiler.intern_type(Type::Bool);
                match self.try_eval_comptime_branch_cond(lhs) {
                    Some(true) => return Ok((Operand::Const(ConstValue::Bool(true)), bool_ty)),
                    Some(false) => return self.lower_expr(rhs, Some(bool_ty)),
                    None => {}
                }
                if self.try_eval_comptime_branch_cond(rhs) == Some(false) {
                    return self.lower_expr(lhs, Some(bool_ty));
                }
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

                self.body.cur_block = short_bb;
                self.emit(Statement::Assign(
                    Place::new(res_local),
                    Rvalue::Use(Operand::Const(ConstValue::Bool(true))),
                ));
                self.terminate(Terminator::Goto { target: join_bb });

                self.body.cur_block = rhs_bb;
                let (r_op, _) = self.lower_expr(rhs, Some(bool_ty))?;
                self.emit(Statement::Assign(Place::new(res_local), Rvalue::Use(r_op)));
                self.terminate(Terminator::Goto { target: join_bb });

                self.body.cur_block = join_bb;
                Ok((Operand::Copy(Place::new(res_local)), bool_ty))
            }
            Expr::OrElse { .. }
            | Expr::Try(_)
            | Expr::Async { .. }
            | Expr::Catch { .. }
            | Expr::Match { .. }
            | Expr::Select { .. }
            | Expr::Block(_)
            | Expr::If { .. } => self.lower_control_flow_expr(expr, expected_ty),
            Expr::SliceLit { .. }
            | Expr::MapLit(_)
            | Expr::IntrinsicInvert(_)
            | Expr::IntrinsicMap { .. }
            | Expr::IntrinsicSatisfies { .. }
            | Expr::IntrinsicHasField { .. }
            | Expr::IntrinsicHasMethod { .. }
            | Expr::IntrinsicTypeName(_)
            | Expr::IntrinsicVariants(_)
            | Expr::IntrinsicEntries(_)
            | Expr::IntrinsicFields(_)
            | Expr::IntrinsicLeaves(_)
            | Expr::IntrinsicFnInfo(_)
            | Expr::IntrinsicField { .. }
            | Expr::IntrinsicMakeUnion { .. }
            | Expr::IntrinsicDeclarations(_)
            | Expr::TupleLit(_)
            | Expr::SimdLit { .. }
            | Expr::StructLit { .. } => self.lower_aggregate_or_meta_expr(expr, expected_ty),
            Expr::IntrinsicAlloc { .. }
            | Expr::IntrinsicRealloc { .. }
            | Expr::IntrinsicDealloc(_)
            | Expr::IntrinsicRawAlloc(_)
            | Expr::IntrinsicRawAllocZeroed(_)
            | Expr::IntrinsicAtomic { .. }
            | Expr::IntrinsicMemcpy { .. }
            | Expr::IntrinsicMemmove { .. }
            | Expr::IntrinsicTransmute { .. }
            | Expr::IntrinsicCAbi(_)
            | Expr::IntrinsicForget(_)
            | Expr::IntrinsicLayout { .. }
            | Expr::IntrinsicDefault(_)
            | Expr::IntrinsicClone(_)
            | Expr::IntrinsicDrop(_)
            | Expr::IntrinsicFormat { .. }
            | Expr::FormatStr(_)
            | Expr::IntrinsicTrap
            | Expr::IntrinsicCompileError(_)
            | Expr::Break(_)
            | Expr::Continue(_)
            | Expr::Return(_)
            | Expr::UnsafeBlock(_)
            | Expr::Lambda { .. } => self.lower_intrinsic_or_closure_expr(expr, expected_ty),
            // An error in a call says where the call is, unless one inside it said already.
            Expr::Call {
                callee,
                ct_args,
                args,
                at,
            } => self
                .at_call(at.0, |s| {
                    s.call_expected = expected_ty;
                    s.lower_call(callee, ct_args.as_deref(), args)
                })
                .map_err(|e| self.located(e, at.0.as_ref())),
            Expr::MethodCall {
                receiver,
                method,
                ct_args,
                args,
                at,
            } => self
                .at_call(at.0, |s| s.lower_method_call(receiver, method, ct_args.as_deref(), args))
                .map_err(|e| self.located(e, at.0.as_ref())),
        }
    }

    #[inline(never)]
    fn lower_path_expr(
        &mut self,
        p: &[String],
        expected_ty: Option<TypeId>,
    ) -> Result<(Operand, TypeId), String> {
        {
                if p.len() == 2
                    && let Ok(Some((cval, cty, _))) = self.compiler.eval_int_reflection_field(
                        &self.mod_path,
                        self.owner_ty,
                        &self.comptime_env,
                        &Expr::Path(vec![p[0].clone()]),
                        &p[1],
                    )
                {
                    let res_ty = if matches!(p[1].as_str(), "bits" | "BITS")
                        && let Some(t) = expected_ty
                        && matches!(self.compiler.program.types[t.0 as usize], Type::Int { .. })
                    {
                        t
                    } else {
                        cty
                    };
                    return Ok((Operand::Const(cval), res_ty));
                }
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
                        let ty = expected_ty
                            .or_else(|| {
                                match self.comptime_env.get(&format!("__var_ty:{}", p[0])) {
                                    Some(ComptimeVal::Type(t)) => Some(*t),
                                    _ => None,
                                }
                            })
                            .unwrap_or_else(|| {
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
                    if let Some(ComptimeVal::Str(s)) = self.comptime_env.get(&p[0]).cloned() {
                        let var_ty_opt =
                            match self.comptime_env.get(&format!("__var_ty:{}", p[0])) {
                                Some(ComptimeVal::Type(t)) => Some(*t),
                                _ => None,
                            };
                        let want_raw_ptr = expected_ty.or(var_ty_opt).is_some_and(|t| {
                            matches!(self.compiler.program.types[t.0 as usize], Type::Ptr { .. })
                        });
                        if want_raw_ptr {
                            let u8_ty = self.compiler.intern_type(Type::Int {
                                signed: false,
                                bits: 8,
                            });
                            let ptr_ty = self.compiler.intern_type(Type::Ptr {
                                mutable: false,
                                pointee: u8_ty,
                            });
                            return Ok((Operand::Const(ConstValue::Str(s)), ptr_ty));
                        }
                        let str_ty = self.compiler.intern_str_type();
                        let op = self.materialize_const_val(ConstValue::Str(s), str_ty);
                        return Ok((op, str_ty));
                    }
                    if let Some(ComptimeVal::Type(t_id)) = self.comptime_env.get(&p[0]).cloned() {
                        let meta_ty = self.compiler.intern_type(Type::MetaType);
                        return Ok((Operand::Const(ConstValue::Type(t_id)), meta_ty));
                    }
                    if let Some(ComptimeVal::Map(id)) = self.comptime_env.get(&p[0]).cloned() {
                        let inst = self.compiler.map_instances[id as usize].clone();
                        return Ok((Operand::Const(ConstValue::I64(id as i128)), inst.map_ty));
                    }
                    // A compile-time list (a field path from `@leaves`, a list of names) is a
                    // static slice at run time.
                    if let Some(list @ ComptimeVal::List(..)) = self.comptime_env.get(&p[0]).cloned() {
                        let (cval, ty, _) = self.compiler.comptime_val_to_const_result(&list, expected_ty)?;
                        let tmp = self.alloc_temp(ty);
                        self.emit(Statement::Assign(Place::new(tmp), Rvalue::Use(Operand::Const(cval))));
                        return Ok((Operand::Copy(Place::new(tmp)), ty));
                    }
                }
                let expanded = self.compiler.expand_module_path(&self.comptime_env, p);
                let p = &expanded;
                if p.len() >= 2 {
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
                        self.compiler
                            .resolve_type_path(
                                &self.mod_path,
                                self.owner_ty,
                                &self.comptime_env,
                                type_prefix,
                            )
                            .ok()
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
                // An `extern fn` named as a value is a C function pointer, `unsafe` to call
                // unless its declaration is `safe extern fn`.
                if let Ok(ResolvedItem::ExternFunc(emod, ename)) =
                    self.compiler.resolve_path(&self.mod_path, p)
                {
                    let fn_id = self.compiler.get_or_register_extern(&emod, &ename)?;
                    let (args, ret) = self.compiler.func_sigs[&fn_id].clone();
                    let is_unsafe = !self.compiler.safe_externs.contains(&(emod, ename));
                    let fn_ptr_ty = self.compiler.intern_c_fn_ptr_type(args, ret, is_unsafe);
                    return Ok((Operand::Const(ConstValue::Func(fn_id)), fn_ptr_ty));
                }
                if let Ok(ResolvedItem::Func(fmod, fname)) =
                    self.compiler.resolve_path(&self.mod_path, p)
                {
                    if let Some(res) = self.try_generic_fn_from_expected(&fmod, &fname, expected_ty)? {
                        return Ok(res);
                    }
                    let fn_id = self.compiler.get_or_instantiate_func(&fmod, &fname, &[])?;
                    let fn_ptr_ty = self.compiler.named_fn_ptr_type(fn_id);
                    return Ok((Operand::Const(ConstValue::Func(fn_id)), fn_ptr_ty));
                }
                Err(format!("Cannot resolve value path '{}'", p.join("::")))
        }
    }

    #[inline(never)]
    fn lower_place_or_ref_expr(
        &mut self,
        expr: &Expr,
        expected_ty: Option<TypeId>,
    ) -> Result<(Operand, TypeId), String> {
        match expr {
            Expr::Move(inner) => {
                let (place, ty) = self.lower_place(inner, true)?;
                if matches!(inner.as_ref(), Expr::Field { .. } | Expr::IntrinsicField { .. })
                    && matches!(place.projections.last(), Some(Projection::Field(_)))
                {
                    let mut parent_place = place.clone();
                    parent_place.projections.pop();
                    let parent_ty = self.place_type(&parent_place);
                    if let Some(comp) = self.compiler.composites.get(&parent_ty)
                        && comp.is_opaque
                    {
                        return Err(format!(
                            "Cannot partially move field out of opaque '{}'; only 'struct' and 'tuple' allow partial moves",
                            comp.name
                        ));
                    }
                }
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
            Expr::Field { .. }
            | Expr::TupleIndex { .. }
            | Expr::Index { .. }
            | Expr::Deref(_)
            | Expr::IntrinsicVariant { .. } => {
                if let Expr::Index { base, index } = expr
                    && let Expr::Path(p) = base.as_ref()
                    && let Some(res) =
                        self.try_lower_generic_fn_value(p, std::slice::from_ref(index))?
                {
                    return Ok(res);
                }
                if let Expr::Index { base, index } = expr
                    && let Some(map_id) = self.compiler.resolve_map_expr(
                        &self.mod_path,
                        self.owner_ty,
                        &self.comptime_env,
                        base,
                    )?
                {
                    return self.lower_map_index(map_id, index);
                }
                if let Expr::Field { base, field } = expr
                    && (matches!(base.as_ref(), Expr::TypeVal(_))
                        || matches!(base.as_ref(), Expr::Path(p) if p.len() == 1 && self.lookup_var(&p[0]).is_none() && self.lookup_capture(&p[0]).is_none())
                        || self.has_comptime_root(base))
                    && let Ok(Some((cval, cty, _))) = self.compiler.eval_int_reflection_field(
                        &self.mod_path,
                        self.owner_ty,
                        &self.comptime_env,
                        base,
                        field,
                    )
                {
                    let res_ty = if matches!(field.as_str(), "bits" | "BITS")
                        && let Some(t) = expected_ty
                        && matches!(self.compiler.program.types[t.0 as usize], Type::Int { .. })
                    {
                        t
                    } else {
                        cty
                    };
                    return Ok((Operand::Const(cval), res_ty));
                }
                if matches!(
                    expr,
                    Expr::Field { .. } | Expr::TupleIndex { .. } | Expr::Index { .. }
                ) && self.has_comptime_root(expr)
                {
                    match self.compiler.eval_const_expr_typed(
                        &self.mod_path,
                        self.owner_ty,
                        &self.comptime_env,
                        expr,
                        expected_ty,
                    ) {
                        Ok((cval, cty, _)) => {
                            let op = self.materialize_const_val(cval, cty);
                            return Ok((op, cty));
                        }
                        Err(e) => {
                            if self.is_comptime_only_expr(expr) {
                                return Err(e);
                            }
                        }
                    }
                }
                if let Expr::Field { base, field } = expr {
                    if field == "tag"
                        && let Some(res) = self.try_lower_union_tag(base)?
                    {
                        return Ok(res);
                    }
                    if let Some((op, ty)) =
                        self.try_lower_packed_or_reflect_field(base, field, expected_ty)?
                    {
                        return Ok((op, ty));
                    }
                }
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
                // `&0` where a `&i32` is expected is a reference to an `i32`.
                let literal_pointee = match (inner.as_ref(), expected_ty) {
                    (
                        Expr::Int(_) | Expr::Float(_) | Expr::Unary { op: UnOp::Neg, .. },
                        Some(want),
                    ) => match self.compiler.program.types[want.0 as usize] {
                        Type::Ptr { pointee, .. } => Some(pointee),
                        _ => None,
                    },
                    _ => None,
                };
                let (place, inner_ty) = match literal_pointee {
                    Some(pointee) => {
                        let (op, ty) = self.lower_expr(inner, Some(pointee))?;
                        let op = self.coerce_operand(op, ty, pointee)?;
                        let tmp = self.alloc_temp(pointee);
                        self.emit(Statement::Assign(Place::new(tmp), Rvalue::Use(op)));
                        (Place::new(tmp), pointee)
                    }
                    None => self.lower_place(inner, *mutable)?,
                };
                self.default_type_var(inner_ty, true)?;
                let inner_ty = self.resolve_type_var(inner_ty);
                if let Some((stat_name, true)) = self.static_locals.get(&place.local) {
                    return Err(format!(
                        "Taking a safe reference ('&' or '&mut') to mutable static '{}' is forbidden; use '&raw const' or '&raw mut' instead",
                        stat_name
                    ));
                }
                if let Some(cell_field) = self.place_traverses_cell(&place) {
                    return Err(format!(
                        "Cannot take a safe reference ('&' or '&mut') to 'cell' field '{cell_field}'; read or copy the field by value, or use '&raw const' / '&raw mut'"
                    ));
                }
                if *mutable {
                    self.check_binding_writable(&place, "borrow mutably")?;
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
                self.default_type_var(inner_ty, true)?;
                let inner_ty = self.resolve_type_var(inner_ty);
                if *mutable {
                    self.check_binding_writable(&place, "borrow mutably")?;
                }
                // A `cell` field reached through a shared reference: its address is taken as a
                // shared borrow (the borrow checker sees no `&mut` through `&`), then made `*mut`.
                let into_cell = *mutable
                    && self.place_traverses_immutable_ptr(&place)
                    && self.shared_derefs_reach_cells(&place);
                if *mutable && self.place_traverses_immutable_ptr(&place) && !into_cell {
                    if let Some((stat_name, false)) = self.static_locals.get(&place.local) {
                        return Err(format!(
                            "Cannot take mutable raw pointer '&raw mut' to immutable static variable '{}'",
                            stat_name
                        ));
                    }
                    return Err(format!(
                        "Cannot take mutable raw pointer '&raw mut' to '{}' through an immutable reference or pointer (only a 'cell' field may change behind a shared reference)",
                        place
                    ));
                }
                let raw_ptr_ty = self.compiler.intern_raw_ptr_type(*mutable, inner_ty);
                if into_cell {
                    let const_ty = self.compiler.intern_raw_ptr_type(false, inner_ty);
                    let addr = self.alloc_temp(const_ty);
                    self.emit(Statement::Assign(
                        Place::new(addr),
                        Rvalue::Ref {
                            mutable: false,
                            place,
                        },
                    ));
                    let tmp = self.alloc_temp(raw_ptr_ty);
                    self.emit(Statement::Assign(
                        Place::new(tmp),
                        Rvalue::Cast(Operand::Copy(Place::new(addr)), raw_ptr_ty),
                    ));
                    return Ok((Operand::Copy(Place::new(tmp)), raw_ptr_ty));
                }
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
            _ => unreachable!(),
        }
    }

    #[inline(never)]
    /// Whether binary `op` is defined on operands of type `ty` (after any implicit conversion):
    /// arithmetic on numbers, SIMD vectors, and pointers; bitwise operators on integers, `bool`,
    /// and SIMD vectors; ordering on numbers, `rune`, pointers, and enums; equality on those and
    /// on `bool`, function pointers, types, unions of unit variants, and packed types. A `struct`,
    /// an `opaque`, or a type parameter has none of them unless a trait gives it methods.
    /// Whether `ty` (under any pattern or `distinct`) is an unsigned integer, or a vector of them.
    fn is_unsigned_scalar_or_lanes(&self, ty: TypeId) -> bool {
        let mut ty = self.pattern_base(ty);
        while let Some(nt) = self.compiler.distinct_types.get(&ty) {
            ty = self.pattern_base(nt.underlying);
        }
        if let Type::Simd { elem, .. } = self.compiler.program.types[ty.0 as usize] {
            ty = elem;
        }
        !self.compiler.enums.contains_key(&ty)
            && matches!(self.compiler.program.types[ty.0 as usize], Type::Int { signed: false, .. })
    }

    pub(super) fn operator_applies(&self, op: BinOp, ty: TypeId) -> bool {
        let mut ty = self.pattern_base(ty);
        while let Some(nt) = self.compiler.distinct_types.get(&ty) {
            ty = self.pattern_base(nt.underlying);
        }
        // A packed value is one integer, so it compares bit for bit.
        if let Some(comp) = self.compiler.composites.get(&ty) {
            return comp.is_packed && matches!(op, BinOp::Eq | BinOp::Ne);
        }
        if self.compiler.named_opaques.contains(&ty) {
            return false;
        }
        let is_enum = self.compiler.enums.contains_key(&ty);
        let kind = self.compiler.program.types[ty.0 as usize].clone();
        let number = matches!(kind, Type::Int { .. } | Type::F32 | Type::F64) && !is_enum;
        let simd = matches!(kind, Type::Simd { .. });
        let pointer = matches!(kind, Type::Ptr { .. });
        match op {
            BinOp::Eq | BinOp::Ne => {
                number
                    || simd
                    || pointer
                    || is_enum
                    || matches!(kind, Type::Bool | Type::Rune | Type::FnPtr { .. } | Type::MetaType)
                    || matches!(&kind, Type::Union { variants, .. }
                        if variants.iter().all(|v| matches!(self.compiler.program.types[v.0 as usize], Type::Void)))
            }
            BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge => {
                number || pointer || is_enum || matches!(kind, Type::Rune)
            }
            BinOp::BitAnd | BinOp::BitOr | BinOp::BitXor => {
                (number && !matches!(kind, Type::F32 | Type::F64)) || simd || matches!(kind, Type::Bool)
            }
            BinOp::Shl | BinOp::Shr => (number && !matches!(kind, Type::F32 | Type::F64)) || simd,
            // Wrapping and saturating are about an integer's range.
            BinOp::AddWrap | BinOp::SubWrap | BinOp::MulWrap | BinOp::AddSat | BinOp::SubSat | BinOp::MulSat => {
                (number && !matches!(kind, Type::F32 | Type::F64)) || simd
            }
            _ => number || simd || pointer,
        }
    }

    fn lower_arith_or_cast_expr(
        &mut self,
        expr: &Expr,
        expected_ty: Option<TypeId>,
    ) -> Result<(Operand, TypeId), String> {
        match expr {
            Expr::Unary { op, expr: inner } => {
                // A negated literal is one literal (`-128` fits `i8` although `128` does not).
                if *op == UnOp::Neg
                    && let Expr::Int(n) = inner.as_ref()
                {
                    return self.lower_expr(&Expr::Int(-n), expected_ty);
                }
                let inner_expected = expected_ty.map(|t| self.pattern_base(t));
                let (inner_op, ty) = self.lower_expr_open(inner, inner_expected)?;
                let ty = self.pattern_base(ty);
                // `!` is bitwise (or logical) wherever `^` applies; `-` wherever `-` does, but
                // a pointer.
                let applies = match op {
                    UnOp::Not => self.operator_applies(BinOp::BitXor, ty),
                    UnOp::Neg => {
                        self.operator_applies(BinOp::Sub, ty)
                            && !matches!(self.compiler.program.types[ty.0 as usize], Type::Ptr { .. })
                            && !self.is_unsigned_scalar_or_lanes(ty)
                    }
                    UnOp::Bswap => true,
                };
                if *op == UnOp::Neg {
                    self.note_type_var_negated(ty);
                }
                if !applies && *op == UnOp::Neg && self.is_unsigned_scalar_or_lanes(ty) {
                    return Err(format!(
                        "Operator '-' is not defined on unsigned '{}'; write '0 -% x' to wrap, or convert to a signed type first",
                        self.compiler.type_display_name(ty)
                    ));
                }
                if !applies {
                    return Err(format!(
                        "Operator '{}' is not defined on '{}'",
                        if *op == UnOp::Not { "!" } else { "-" },
                        self.compiler.type_display_name(ty)
                    ));
                }
                let tmp = self.alloc_temp(ty);
                self.emit(Statement::Assign(
                    Place::new(tmp),
                    Rvalue::UnaryOp(*op, inner_op),
                ));
                Ok((Operand::Copy(Place::new(tmp)), ty))
            }
            // Whether an optional holds nothing is a question for its tag, whatever it holds.
            Expr::Binary { op: op @ (BinOp::Eq | BinOp::Ne), lhs, rhs }
                if matches!(**lhs, Expr::Null) != matches!(**rhs, Expr::Null) =>
            {
                let value = if matches!(**lhs, Expr::Null) { rhs } else { lhs };
                let (place, ty) = self.lower_place(value, false)?;
                let Type::Union { tag, .. } = self.compiler.program.types[ty.0 as usize].clone() else {
                    return Err(format!(
                        "Only an optional can be compared with 'null', found '{}'",
                        self.compiler.type_display_name(ty)
                    ));
                };
                if self.compiler.as_optional_type(ty).is_none() {
                    return Err(format!(
                        "Only an optional can be compared with 'null', found '{}'",
                        self.compiler.type_display_name(ty)
                    ));
                }
                let discriminant = self.alloc_temp(tag);
                self.emit(Statement::Assign(Place::new(discriminant), Rvalue::Discriminant(place)));
                let bool_ty = self.compiler.intern_type(Type::Bool);
                let result = self.alloc_temp(bool_ty);
                self.emit(Statement::Assign(
                    Place::new(result),
                    Rvalue::BinaryOp(
                        *op,
                        Operand::Copy(Place::new(discriminant)),
                        Operand::Const(ConstValue::I64(0)),
                    ),
                ));
                Ok((Operand::Copy(Place::new(result)), bool_ty))
            }
            Expr::Binary { op, lhs, rhs } => {
                if matches!(op, BinOp::Eq | BinOp::Ne)
                    && (self.has_comptime_root(lhs) || self.has_comptime_root(rhs))
                {
                    let outer = std::mem::replace(&mut self.compiler.implicit_folding, true);
                    let folded = self.compiler.eval_const_expr_typed(
                        &self.mod_path,
                        self.owner_ty,
                        &self.comptime_env,
                        expr,
                        expected_ty,
                    );
                    self.compiler.implicit_folding = outer;
                    if let Ok((cval, cty, _)) = folded {
                        return Ok((Operand::Const(cval), cty));
                    }
                }
                let is_checked_op = matches!(
                    op,
                    BinOp::AddChecked | BinOp::SubChecked | BinOp::MulChecked
                );
                let inner_expected_ty = if is_checked_op {
                    expected_ty
                        .and_then(|t| self.compiler.as_optional_type(t))
                        .or(expected_ty)
                } else {
                    expected_ty
                };
                // Arithmetic and comparisons operate on a pattern type's base integer type.
                let inner_expected_ty = inner_expected_ty.map(|t| self.pattern_base(t));
                let (l_op, l_ty, mut r_op, mut r_ty) = if inner_expected_ty.is_none()
                    && matches!(lhs.as_ref(), Expr::Int(_) | Expr::Float(_) | Expr::Str(_))
                    && !matches!(rhs.as_ref(), Expr::Int(_) | Expr::Float(_) | Expr::Str(_))
                {
                    let (r_op, r_ty) = self.lower_expr_open(rhs, None)?;
                    let r_ty = self.pattern_base(r_ty);
                    let (l_op, l_ty) = self.lower_expr_open(lhs, Some(r_ty))?;
                    (l_op, l_ty, r_op, r_ty)
                } else {
                    let (l_op, l_ty) = self.lower_expr_open(lhs, inner_expected_ty)?;
                    let l_ty = self.pattern_base(l_ty);
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
                    let (r_op, r_ty) = self.lower_expr_open(rhs, rhs_exp)?;
                    (l_op, l_ty, r_op, self.pattern_base(r_ty))
                };
                if let Type::Ptr { pointee, .. } = self.compiler.program.types[l_ty.0 as usize] {
                    if is_checked_op {
                        return Err(format!(
                            "Cannot perform checked arithmetic '{}' on pointer type '{}'",
                            op,
                            self.compiler.type_display_name(l_ty)
                        ));
                    }
                    if self.compiler.is_opaque_type(pointee)
                        && matches!(op, BinOp::Add | BinOp::AddWrap | BinOp::Sub | BinOp::SubWrap)
                    {
                        return Err(format!(
                            "Cannot perform element-scaled pointer arithmetic on '{}'; cast to '*const u8' or '*mut u8' for byte offsets",
                            self.compiler.type_display_name(l_ty)
                        ));
                    }
                } else {
                    if let Some(comp) = self.compiler.composites.get(&l_ty)
                        && comp.is_packed
                        && !matches!(op, BinOp::Eq | BinOp::Ne)
                    {
                        return Err(format!(
                            "Cannot perform arithmetic or bitwise operator '{}' directly on packed type '{}'; cast to its backing integer type first",
                            crate::wide::op_symbol(*op), comp.name
                        ));
                    }
                    // `rune` is a code point, not a number: only comparisons apply directly.
                    let is_rune = |t: TypeId| {
                        matches!(self.compiler.program.types[t.0 as usize], Type::Rune)
                    };
                    if (is_rune(l_ty) || is_rune(r_ty))
                        && !matches!(
                            op,
                            BinOp::Eq | BinOp::Ne | BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge
                        )
                    {
                        return Err(format!(
                            "Operator '{op}' is not defined on 'rune'; convert with 'as u32' first"
                        ));
                    }
                    // Operands share one type: the right operand converts implicitly (a string
                    // literal to `&str`) or the operation is a type error.
                    if r_ty != l_ty {
                        let l_local = Self::operand_local_id(&l_op);
                        r_op = match self.coerce_operand(r_op, r_ty, l_ty) {
                            Ok(op) => op,
                            Err(e) => {
                                self.learn_type_hint(l_local, r_ty);
                                return Err(format!("{e} (in '{}')", crate::wide::op_symbol(*op)));
                            }
                        };
                        r_ty = l_ty;
                    }
                    if r_ty != l_ty
                        && let (Some(l_nt), Some(r_nt)) = (
                            self.compiler.distinct_types.get(&l_ty),
                            self.compiler.distinct_types.get(&r_ty),
                        )
                    {
                        return Err(format!(
                            "Type mismatch in binary operation '{}': cannot mix distinct types '{}' and '{}'",
                            op, l_nt.name, r_nt.name
                        ));
                    }
                }
                // With two constant operands the backend would see no operand type (it would
                // use the result's, `bool` for a comparison): give the left operand a local.
                let l_op = if matches!((&l_op, &r_op), (Operand::Const(_), Operand::Const(_))) {
                    let tmp = self.alloc_temp(l_ty);
                    self.emit(Statement::Assign(Place::new(tmp), Rvalue::Use(l_op)));
                    Operand::Copy(Place::new(tmp))
                } else {
                    l_op
                };
                if is_checked_op {
                    if !matches!(
                        self.compiler.program.types[l_ty.0 as usize],
                        Type::Int { .. }
                    ) {
                        return Err(format!(
                            "Fallible arithmetic operator '{}' requires an integer type, found '{}'",
                            crate::wide::op_symbol(*op),
                            self.compiler.type_display_name(l_ty)
                        ));
                    }
                    let u8_ty = self.compiler.intern_type(Type::Int {
                        signed: false,
                        bits: 8,
                    });
                    let void_ty = self.compiler.intern_type(Type::Void);
                    let opt_ty = self.compiler.intern_type(Type::Union {
                        tag: u8_ty,
                        variants: vec![void_ty, l_ty],
                    });
                    self.compiler.ensure_union_destructor(opt_ty);
                    let tmp = self.alloc_temp(opt_ty);
                    self.emit(Statement::Assign(
                        Place::new(tmp),
                        Rvalue::BinaryOp(*op, l_op, r_op),
                    ));
                    return Ok((Operand::Move(Place::new(tmp)), opt_ty));
                }
                if matches!(op, BinOp::Eq | BinOp::Ne)
                    && (self
                        .compiler
                        .slices
                        .get(&l_ty)
                        .is_some_and(|s| s.is_str)
                        || self
                            .compiler
                            .slices
                            .get(&r_ty)
                            .is_some_and(|s| s.is_str))
                {
                    return self.lower_str_eq(l_op, l_ty, r_op, r_ty, *op == BinOp::Ne);
                }
                if !self.operator_applies(*op, l_ty) {
                    return Err(format!(
                        "Operator '{}' is not defined on '{}'",
                        crate::wide::op_symbol(*op),
                        self.compiler.type_display_name(l_ty)
                    ));
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
            Expr::IntrinsicArithUnchecked { op, lhs, rhs } => {
                let intr_name = match op {
                    BinOp::AddUnchecked => "@add_unchecked",
                    BinOp::SubUnchecked => "@sub_unchecked",
                    BinOp::MulUnchecked => "@mul_unchecked",
                    _ => "@arith_unchecked",
                };
                if self.unsafe_depth == 0 {
                    return Err(format!(
                        "'{intr_name}' is unsafe and requires an 'unsafe {{ ... }}' block"
                    ));
                }
                let (l_op, l_ty, r_op, r_ty) = if expected_ty.is_none()
                    && matches!(lhs.as_ref(), Expr::Int(_))
                    && !matches!(rhs.as_ref(), Expr::Int(_))
                {
                    let (r_op, r_ty) = self.lower_expr(rhs, None)?;
                    let (l_op, l_ty) = self.lower_expr(lhs, Some(r_ty))?;
                    (l_op, l_ty, r_op, r_ty)
                } else {
                    let (l_op, l_ty) = self.lower_expr(lhs, expected_ty)?;
                    let (r_op, r_ty) = self.lower_expr(rhs, Some(l_ty))?;
                    (l_op, l_ty, r_op, r_ty)
                };
                if !matches!(
                    self.compiler.program.types[l_ty.0 as usize],
                    Type::Int { .. }
                ) || self.compiler.composites.get(&l_ty).is_some_and(|c| c.is_packed)
                {
                    return Err(format!(
                        "'{intr_name}' requires an integer type, found '{}'",
                        self.compiler.type_display_name(l_ty)
                    ));
                }
                if r_ty != l_ty {
                    return Err(format!(
                        "Type mismatch in '{intr_name}': '{}' vs '{}'",
                        self.compiler.type_display_name(l_ty),
                        self.compiler.type_display_name(r_ty)
                    ));
                }
                let tmp = self.alloc_temp(l_ty);
                self.emit(Statement::Assign(
                    Place::new(tmp),
                    Rvalue::BinaryOp(*op, l_op, r_op),
                ));
                Ok((Operand::Copy(Place::new(tmp)), l_ty))
            }
            Expr::IntrinsicBswap(inner) => {
                let (inner_op, ty) = self.lower_expr(inner, expected_ty)?;
                let Some((bits, _)) = self.compiler.packed_field_bit_width(ty) else {
                    return Err(format!(
                        "'@bswap' requires a byte-multiple integer or packed type, found '{}'",
                        self.compiler.type_display_name(ty)
                    ));
                };
                if bits < 8 || bits % 8 != 0 {
                    return Err(format!(
                        "'@bswap' requires a byte-multiple bit width (multiple of 8 >= 8), found '{}' ({} bits)",
                        self.compiler.type_display_name(ty),
                        bits
                    ));
                }
                let tmp = self.alloc_temp(ty);
                self.emit(Statement::Assign(
                    Place::new(tmp),
                    Rvalue::UnaryOp(UnOp::Bswap, inner_op),
                ));
                Ok((Operand::Copy(Place::new(tmp)), ty))
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
                // Casting a string literal to a pointer asks for its bytes.
                let literal_as = matches!(**inner, Expr::Str(_)).then_some(target_ty);
                let (op, src_ty) = self.lower_expr_open(inner, literal_as)?;
                self.check_cast_kinds(src_ty, target_ty)?;
                if let Some(dest_inner) = self.compiler.as_optional_type(target_ty)
                    && matches!(
                        self.compiler.program.types[src_ty.0 as usize],
                        Type::Int { .. } | Type::Pattern { .. } | Type::Rune
                    )
                    && matches!(
                        self.compiler.program.types[dest_inner.0 as usize],
                        Type::Int { .. } | Type::Pattern { .. } | Type::Rune
                    )
                {
                    return self.lower_checked_cast(op, src_ty, dest_inner, target_ty);
                }
                // An enum holds only its variants' values: `7 as E` is checked like a pattern type.
                if src_ty != target_ty
                    && self.compiler.enums.contains_key(&target_ty)
                    && (self.compiler.enums.contains_key(&src_ty)
                        || matches!(
                            self.compiler.program.types[src_ty.0 as usize],
                            Type::Int { .. } | Type::Pattern { .. }
                        ))
                {
                    return self.lower_checked_enum_cast(op, src_ty, target_ty);
                }
                if let Operand::Const(c @ (ConstValue::I64(_) | ConstValue::Wide(_))) = &op {
                    self.verify_pattern_const(target_ty, &const_to_wide(c))?;
                } else if matches!(
                    self.compiler.program.types[target_ty.0 as usize],
                    Type::Pattern { .. } | Type::Rune
                ) {
                    return self.lower_trapping_pattern_or_rune_cast(op, src_ty, target_ty);
                }
                let src_place_op = if matches!(op, Operand::Const(_)) {
                    let src_tmp = self.alloc_temp(src_ty);
                    self.emit(Statement::Assign(Place::new(src_tmp), Rvalue::Use(op)));
                    self.local_operand(src_tmp, src_ty)
                } else {
                    op
                };
                let dst_tmp = self.alloc_temp(target_ty);
                self.emit(Statement::Assign(
                    Place::new(dst_tmp),
                    Rvalue::Cast(src_place_op, target_ty),
                ));
                Ok((self.local_operand(dst_tmp, target_ty), target_ty))
            }
            _ => unreachable!(),
        }
    }

    /// `as` converts scalars (integers, floats, `bool`, `rune`, enums, pattern types), pointers
    /// (and pointers to / from integers), and distinct types to / from their underlying type.
    /// Aggregates and sum types (`error`, unions, structs, arrays, slices, ...) have no value
    /// conversion, so casting one is an error unless the types are the same.
    fn check_cast_kinds(&self, src_ty: TypeId, target_ty: TypeId) -> Result<(), String> {
        let peel_distinct = |mut t: TypeId| {
            while let Some(nt) = self.compiler.distinct_types.get(&t) {
                t = nt.underlying;
            }
            t
        };
        let base_src = peel_distinct(src_ty);
        let base_dst = peel_distinct(target_ty);
        if base_src == base_dst {
            return Ok(());
        }
        // Writing through a shared reference is allowed only into state declared to change behind
        // one (`cell` fields, or a type that declares `unsafe sync`); other types are assumed
        // unchanged while shared, which is what makes them `sync`.
        if let (&Type::Ptr { mutable: false, pointee }, Some((true, _))) = (
            &self.compiler.program.types[base_src.0 as usize],
            self.compiler.raw_ptrs.get(&base_dst),
        ) && self.compiler.ptr_kind(base_src).is_none()
            && !self.compiler.slices.contains_key(&base_src)
            && !self.compiler.permits_interior_mutation(pointee)
        {
            return Err(format!(
                "Cannot cast shared reference '{}' to '{}': writing through it would change '{}' while it is shared; mark the fields that change 'cell' (or declare the type 'opaque(unsafe sync)' if it synchronizes them itself)",
                self.compiler.type_display_name(src_ty),
                self.compiler.type_display_name(target_ty),
                self.compiler.type_display_name(pointee)
            ));
        }
        // Making an owning pointer or a view asserts what it points to and how long that lives, so
        // it requires `unsafe`. The one exception is a reference becoming a view of the same type,
        // which carries the reference's borrow.
        if let Some(to @ (PtrKind::Own | PtrKind::View)) = self.compiler.ptr_kind(base_dst) {
            let (dst_mut, dst_pointee) = self.compiler.raw_ptrs[&base_dst];
            let from_ref = to == PtrKind::View
                && self.compiler.ptr_kind(base_src).is_none()
                && matches!(
                    self.compiler.program.types[base_src.0 as usize],
                    Type::Ptr { mutable, pointee } if pointee == dst_pointee && (mutable || !dst_mut)
                )
                && !self.compiler.slices.contains_key(&base_src);
            if !from_ref && self.unsafe_depth == 0 {
                return Err(format!(
                    "Converting '{}' to '{}' asserts what the pointer {} and requires an 'unsafe {{ ... }}' block",
                    self.compiler.type_display_name(src_ty),
                    self.compiler.type_display_name(target_ty),
                    if to == PtrKind::Own { "owns" } else { "borrows" }
                ));
            }
        }
        // `x as ?T` is a checked conversion to `T`.
        if let Some(inner) = self.compiler.as_optional_type(target_ty) {
            return self.check_cast_kinds(src_ty, inner);
        }
        let not_castable = |t: TypeId| {
            matches!(
                self.compiler.type_kind(t),
                Some(
                    TypeKind::Error
                        | TypeKind::Union
                        | TypeKind::Result
                        | TypeKind::Slice
                        | TypeKind::TraitObj
                        | TypeKind::Closure
                        | TypeKind::Map
                )
            ) || matches!(
                self.compiler.program.types[t.0 as usize],
                Type::Struct(_) | Type::Overlay(_) | Type::Union { .. } | Type::Array { .. }
            )
        };
        if not_castable(base_src) || not_castable(base_dst) {
            return Err(format!(
                "Cannot cast '{}' to '{}': 'as' converts scalars, pointers, and distinct types",
                self.compiler.type_display_name(src_ty),
                self.compiler.type_display_name(target_ty)
            ));
        }
        Ok(())
    }

    #[inline(never)]
    fn lower_control_flow_expr(
        &mut self,
        expr: &Expr,
        expected_ty: Option<TypeId>,
    ) -> Result<(Operand, TypeId), String> {
        match expr {
            // Falling back to nothing leaves the optional as it was.
            Expr::OrElse { opt, fallback } if matches!(**fallback, Expr::Null) => {
                self.lower_expr(opt, expected_ty)
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

                self.body.cur_block = some_bb;
                let mut payload_place = Place::new(opt_local);
                payload_place.projections.push(Projection::Variant(1));
                let p_op = if self.is_copy_type(payload_ty) {
                    Operand::Copy(payload_place)
                } else {
                    Operand::Move(payload_place)
                };
                self.emit(Statement::Assign(Place::new(res_local), Rvalue::Use(p_op)));
                self.terminate(Terminator::Goto { target: join_bb });

                self.body.cur_block = none_bb;
                let (fb_op, fb_ty) = self.lower_expr(fallback, Some(payload_ty))?;
                if !self.is_terminated() {
                    let coerced = self.coerce_operand(fb_op, fb_ty, payload_ty)?;
                    self.emit(Statement::Assign(Place::new(res_local), Rvalue::Use(coerced)));
                    self.terminate(Terminator::Goto { target: join_bb });
                }

                self.body.cur_block = join_bb;
                Ok((Operand::Move(Place::new(res_local)), payload_ty))
            }
            Expr::Async { call, bound, executor } => self.lower_async(call, *bound, executor.as_deref()),
            Expr::Try(inner) => {
                let (res_op, res_ty) = self.lower_expr(inner, None)?;
                if let Some(payload_ty) = self.compiler.as_optional_type(res_ty) {
                    let ret_ty = self.body.locals[0];
                    if self.compiler.as_optional_type(ret_ty).is_none() {
                        return Err(format!(
                            "`try` on an optional `?T` expression can only be used inside a function returning an optional `?U` (function '{}' returns {})",
                            self.decl.name,
                            self.compiler.type_display_name(ret_ty)
                        ));
                    }
                    let u8_ty = self.compiler.intern_type(Type::Int {
                        signed: false,
                        bits: 8,
                    });
                    let opt_local = self.alloc_temp(res_ty);
                    self.emit(Statement::Assign(Place::new(opt_local), Rvalue::Use(res_op)));
                    let discr_local = self.alloc_temp(u8_ty);
                    self.emit(Statement::Assign(
                        Place::new(discr_local),
                        Rvalue::Discriminant(Place::new(opt_local)),
                    ));

                    let some_bb = self.new_block();
                    let none_bb = self.new_block();
                    self.terminate(Terminator::SwitchInt {
                        discr: Operand::Copy(Place::new(discr_local)),
                        targets: vec![(1, some_bb)],
                        otherwise: none_bb,
                    });

                    self.body.cur_block = none_bb;
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

                    self.body.cur_block = some_bb;
                    if matches!(
                        self.compiler.program.types[payload_ty.0 as usize],
                        Type::Void
                    ) {
                        return Ok((Operand::Const(ConstValue::Void), payload_ty));
                    }
                    let mut p_place = Place::new(opt_local);
                    p_place.projections.push(Projection::Variant(1));
                    let p_op = if self.is_copy_type(payload_ty) {
                        Operand::Copy(p_place)
                    } else {
                        Operand::Move(p_place)
                    };
                    let p_local = self.alloc_temp(payload_ty);
                    self.emit(Statement::Assign(Place::new(p_local), Rvalue::Use(p_op)));
                    let out_op = if self.is_copy_type(payload_ty) {
                        Operand::Copy(Place::new(p_local))
                    } else {
                        Operand::Move(Place::new(p_local))
                    };
                    return Ok((out_op, payload_ty));
                }
                let Some(&src_res) = self.compiler.results.get(&res_ty) else {
                    return Err("`try` requires a fallible `E!T` or optional `?T` expression".to_string());
                };
                let ret_ty = self.body.locals[0];
                let Some(&fn_res) = self.compiler.results.get(&ret_ty) else {
                    return Err(format!(
                        "`try` can only be used inside a function returning a fallible `E!T` result (function '{}' returns {})",
                        self.decl.name,
                        self.compiler.type_display_name(ret_ty)
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

                self.body.cur_block = err_bb;
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

                self.body.cur_block = ok_bb;
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

                self.body.cur_block = ok_bb;
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

                self.body.cur_block = err_bb;
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
                        mutable: false,
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
                self.pop_scope();

                self.body.cur_block = join_bb;
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
            Expr::Select { arms } => self.lower_select(arms, expected_ty),
            Expr::Block(blk) => {
                let void_ty = self.compiler.intern_type(Type::Void);
                let never_ty = self.compiler.intern_type(Type::Never);
                let tail_expr_opt = if expected_ty != Some(void_ty) {
                    match blk.stmts.last() {
                        Some(Stmt::Expr(e)) => Some(e.clone()),
                        Some(Stmt::If {
                            cond,
                            then_block,
                            else_block: Some(else_blk),
                        }) => Some(Expr::If {
                            cond: Box::new(cond.clone()),
                            then_block: then_block.clone(),
                            else_block: Some(else_blk.clone()),
                        }),
                        Some(Stmt::Match { scrutinee, arms }) => Some(Expr::Match {
                            scrutinee: Box::new(scrutinee.clone()),
                            arms: arms.clone(),
                        }),
                        _ => None,
                    }
                } else {
                    None
                };
                if let Some(tail_expr) = tail_expr_opt {
                    self.scopes.push(Vec::new());
                    for s in &blk.stmts[..blk.stmts.len() - 1] {
                        if self.is_terminated() {
                            break;
                        }
                        self.lower_stmt(s)?;
                    }
                    if self.is_terminated() {
                        self.pop_scope();
                        return Ok((Operand::Const(ConstValue::Void), never_ty));
                    }
                    let (tail_op, tail_ty) = self.lower_expr(&tail_expr, expected_ty)?;
                    if self.is_terminated() {
                        self.pop_scope();
                        return Ok((Operand::Const(ConstValue::Void), never_ty));
                    }
                    if matches!(self.compiler.program.types[tail_ty.0 as usize], Type::Void) {
                        self.cleanup_top_scope();
                        self.pop_scope();
                        return Ok((Operand::Const(ConstValue::Void), void_ty));
                    }
                    let res_local = self.alloc_temp(tail_ty);
                    self.emit(Statement::Assign(Place::new(res_local), Rvalue::Use(tail_op)));
                    self.cleanup_top_scope();
                    self.pop_scope();
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
            Expr::If {
                cond,
                then_block,
                else_block,
            } => {
                let void_ty = self.compiler.intern_type(Type::Void);
                if let Some(const_b) = self.try_eval_comptime_branch_cond(cond) {
                    if const_b {
                        return self.lower_expr(&Expr::Block(then_block.clone()), expected_ty);
                    } else if let Some(eb) = else_block {
                        return self.lower_expr(&Expr::Block(eb.clone()), expected_ty);
                    } else {
                        return Ok((Operand::Const(ConstValue::Void), void_ty));
                    }
                }
                let bool_ty = self.compiler.intern_type(Type::Bool);
                let never_ty = self.compiler.intern_type(Type::Never);
                let (c_op, _) = self.lower_expr(cond, Some(bool_ty))?;
                let then_bb = self.new_block();
                let else_bb = self.new_block();
                let join_bb = self.new_block();
                self.terminate(Terminator::SwitchInt {
                    discr: c_op,
                    targets: vec![(1, then_bb)],
                    otherwise: else_bb,
                });

                // Each branch continues from wherever its block ended (calls and `orelse` inside
                // it open new blocks), so the result is stored there, not in `then_bb` / `else_bb`.
                self.body.cur_block = then_bb;
                let (t_op, t_ty) = self.lower_expr(&Expr::Block(then_block.clone()), expected_ty)?;
                let then_term = self.is_terminated();
                let then_end = self.body.cur_block;

                self.body.cur_block = else_bb;
                let exp_else = expected_ty.or(if t_ty != never_ty { Some(t_ty) } else { None });
                let (e_op, e_ty) = if let Some(eb) = else_block {
                    self.lower_expr(&Expr::Block(eb.clone()), exp_else)?
                } else {
                    (Operand::Const(ConstValue::Void), void_ty)
                };
                let else_term = self.is_terminated();
                let else_end = self.body.cur_block;

                let out_ty = expected_ty.unwrap_or(if t_ty != never_ty { t_ty } else { e_ty });
                if matches!(self.compiler.program.types[out_ty.0 as usize], Type::Void) {
                    if !then_term {
                        self.body.cur_block = then_end;
                        self.terminate(Terminator::Goto { target: join_bb });
                    }
                    if !else_term {
                        self.body.cur_block = else_end;
                        self.terminate(Terminator::Goto { target: join_bb });
                    }
                    if then_term && else_term {
                        return Ok((Operand::Const(ConstValue::Void), never_ty));
                    }
                    self.body.cur_block = join_bb;
                    return Ok((Operand::Const(ConstValue::Void), void_ty));
                }

                let res_local = self.alloc_temp(out_ty);
                if !then_term {
                    self.body.cur_block = then_end;
                    let coerced = self.coerce_operand(t_op, t_ty, out_ty)?;
                    self.emit(Statement::Assign(Place::new(res_local), Rvalue::Use(coerced)));
                    self.terminate(Terminator::Goto { target: join_bb });
                }
                if !else_term {
                    self.body.cur_block = else_end;
                    let coerced = self.coerce_operand(e_op, e_ty, out_ty)?;
                    self.emit(Statement::Assign(Place::new(res_local), Rvalue::Use(coerced)));
                    self.terminate(Terminator::Goto { target: join_bb });
                }
                if then_term && else_term {
                    return Ok((Operand::Const(ConstValue::Void), never_ty));
                }
                self.body.cur_block = join_bb;
                let out_op = if self.is_copy_type(out_ty) {
                    Operand::Copy(Place::new(res_local))
                } else {
                    Operand::Move(Place::new(res_local))
                };
                Ok((out_op, out_ty))
            }
            _ => unreachable!(),
        }
    }

    #[inline(never)]
    fn lower_aggregate_or_meta_expr(
        &mut self,
        expr: &Expr,
        expected_ty: Option<TypeId>,
    ) -> Result<(Operand, TypeId), String> {
        match expr {
            Expr::SliceLit { mutable, elems } => {
                self.lower_slice_lit(expected_ty, mutable, elems)
            }
            Expr::MapLit(_)
            | Expr::IntrinsicInvert(_)
            | Expr::IntrinsicMap { .. }
            | Expr::IntrinsicSatisfies { .. }
            | Expr::IntrinsicHasField { .. }
            | Expr::IntrinsicHasMethod { .. } => {
                let (cval, cty, _) = self.compiler.eval_const_expr_typed(
                    &self.mod_path,
                    self.owner_ty,
                    &self.comptime_env,
                    expr,
                    expected_ty,
                )?;
                Ok((Operand::Const(cval), cty))
            }
            Expr::IntrinsicTypeName(_)
            | Expr::IntrinsicVariants(_)
            | Expr::IntrinsicEntries(_) => {
                let (cval, cty, _) = self.compiler.eval_const_expr_typed(
                    &self.mod_path,
                    self.owner_ty,
                    &self.comptime_env,
                    expr,
                    expected_ty,
                )?;
                let op = self.materialize_const_val(cval, cty);
                Ok((op, cty))
            }
            Expr::IntrinsicFields(te) => {
                // Validate at comptime first so opaque/invalid type errors are reported immediately
                let _ = self.compiler.eval_fields_intrinsic(
                    &self.mod_path,
                    self.owner_ty,
                    &self.comptime_env,
                    te,
                )?;
                Err("'@fields(T)' contains compile-time 'type' metadata and can only be used in 'comptime for', 'comptime let', or indexed at compile time".to_string())
            }
            Expr::IntrinsicLeaves(_) => Err(
                "'@leaves(T)' is compile-time data and can only be used in 'comptime for', 'comptime let', or indexed at compile time".to_string(),
            ),
            Expr::IntrinsicFnInfo(fe) => {
                let _ = self.compiler.eval_fn_info_intrinsic(
                    &self.mod_path,
                    self.owner_ty,
                    &self.comptime_env,
                    fe,
                )?;
                Err("'@fn_info(f)' contains compile-time 'type' metadata and can only be used in 'comptime let' or accessed at compile time".to_string())
            }
            Expr::IntrinsicField { base, field } => {
                let resolved = self.resolve_intrinsic_field_target(base, field)?;
                self.lower_expr(&resolved, expected_ty)
            }
            Expr::IntrinsicMakeUnion {
                ty,
                variant,
                payload,
            } => {
                let u_ty = self.compiler.resolve_type_expr(
                    &self.mod_path,
                    self.owner_ty,
                    &self.comptime_env,
                    ty,
                )?;
                let vval = self.compiler.eval_comptime_val(
                    &self.mod_path,
                    self.owner_ty,
                    &self.comptime_env,
                    variant,
                )?;
                let ComptimeVal::Str(vname) = vval else {
                    return Err(format!(
                        "'@make_union' second argument must evaluate at comptime to a variant name ('&str'), found {}",
                        self.compiler.comptime_val_label(&vval)
                    ));
                };
                let (type_name, v_idx, payload_ty) =
                    if let Some(uinfo) = self.compiler.unions.get(&u_ty).cloned() {
                        let Some((idx, (_, pty))) = uinfo
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
                        (uinfo.name, idx as u32, *pty)
                    } else if let Some(einfo) = self.compiler.errors.get(&u_ty).cloned() {
                        let found = einfo
                            .leaves
                            .iter()
                            .enumerate()
                            .find(|(_, l)| {
                                l.key.error_name == einfo.name && l.key.variant_name == vname
                            })
                            .or_else(|| {
                                einfo
                                    .leaves
                                    .iter()
                                    .enumerate()
                                    .find(|(_, l)| l.key.variant_name == vname)
                            })
                            .or_else(|| {
                                einfo.leaves.iter().enumerate().find(|(_, l)| {
                                    format!("{}::{}", l.key.error_name, l.key.variant_name) == vname
                                })
                            });
                        let Some((idx, leaf)) = found else {
                            return Err(format!(
                                "Error '{}' has no variant '{}'",
                                einfo.name, vname
                            ));
                        };
                        (einfo.name, idx as u32, leaf.payload_ty)
                    } else {
                        return Err(format!(
                            "'@make_union' target type must be a 'union' or 'error' type, found '{}'",
                            self.compiler.type_display_name(u_ty)
                        ));
                    };
                let payload_op =
                    if matches!(self.compiler.program.types[payload_ty.0 as usize], Type::Void) {
                        if let Some(p_expr) = payload {
                            let (_, p_ty) = self.lower_expr(p_expr, Some(payload_ty))?;
                            if !matches!(self.compiler.program.types[p_ty.0 as usize], Type::Void) {
                                return Err(format!(
                                    "Unit variant '{}::{}' takes no payload, found '{}'",
                                    type_name,
                                    vname,
                                    self.compiler.type_display_name(p_ty)
                                ));
                            }
                        }
                        Operand::Const(ConstValue::Void)
                    } else {
                        let Some(p_expr) = payload else {
                            return Err(format!(
                                "Variant '{}::{}' requires a payload of type '{}'",
                                type_name,
                                vname,
                                self.compiler.type_display_name(payload_ty)
                            ));
                        };
                        let (p_op, p_ty) = self.lower_expr(p_expr, Some(payload_ty))?;
                        self.coerce_operand(p_op, p_ty, payload_ty)?
                    };
                let tmp = self.alloc_temp(u_ty);
                self.emit(Statement::Assign(
                    Place::new(tmp),
                    Rvalue::Union {
                        ty: u_ty,
                        variant: v_idx,
                        payload: payload_op,
                    },
                ));
                let res_op = if self.is_copy_type(u_ty) {
                    Operand::Copy(Place::new(tmp))
                } else {
                    Operand::Move(Place::new(tmp))
                };
                Ok((res_op, u_ty))
            }
            Expr::IntrinsicDeclarations(mod_expr) => {
                let (cval, cty, _) = self.compiler.eval_module_declarations(
                    &self.mod_path,
                    self.owner_ty,
                    &self.comptime_env,
                    mod_expr,
                )?;
                let op = self.materialize_const_val(cval, cty);
                Ok((op, cty))
            }
            Expr::TupleLit(elems) => {
                if elems.is_empty()
                    && let Some(exp) = expected_ty
                {
                    let mut candidates = vec![exp];
                    if let Some(inner) = self.compiler.as_optional_type(exp) {
                        candidates.push(inner);
                    }
                    if let Some(&res) = self.compiler.results.get(&exp) {
                        candidates.push(res.ok_ty);
                        if let Some(inner) = self.compiler.as_optional_type(res.ok_ty) {
                            candidates.push(inner);
                        }
                    }
                    if candidates.iter().any(|t| {
                        self.compiler.composites.contains_key(t)
                            || self.compiler.overlays.contains_key(t)
                    }) {
                        return self.lower_record_lit(&[], expected_ty);
                    }
                }
                if let Some(t) = expected_ty
                    && matches!(
                        self.compiler.program.types[t.0 as usize],
                        Type::Int {
                            signed: false,
                            bits: 256
                        }
                    )
                    && elems.len() == 4
                {
                    let u64_ty = self.compiler.intern_type(Type::Int {
                        signed: false,
                        bits: 64,
                    });
                    let mut ops = Vec::with_capacity(4);
                    for e in elems {
                        let (op, ety) = self.lower_expr(e, Some(u64_ty))?;
                        let coerced = self.coerce_operand(op, ety, u64_ty)?;
                        ops.push(coerced);
                    }
                    let tmp = self.alloc_temp(t);
                    self.emit(Statement::Assign(
                        Place::new(tmp),
                        Rvalue::Aggregate(t, ops),
                    ));
                    return Ok((Operand::Copy(Place::new(tmp)), t));
                }
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
                            "Expected SIMD or Array type in literal, got '{}'",
                            self.compiler.type_display_name(simd_ty)
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
                self.lower_struct_lit(ty, fields)
            }
            _ => unreachable!(),
        }
    }

    /// Lowers a slice literal `&[a, b, ...]` / `&mut [a, b, ...]` into a backing array and a slice.
    fn lower_slice_lit(
        &mut self,
        expected_ty: Option<TypeId>,
        mutable: &bool,
        elems: &[Expr],
    ) -> Result<(Operand, TypeId), String> {
        let mut elem_ty = None;
        let mut slice_ty = None;
        if let Some(exp) = expected_ty
            && let Some(&sinfo) = self.compiler.slices.get(&exp)
            && !sinfo.is_str
        {
            elem_ty = Some(sinfo.elem);
            slice_ty = Some(exp);
        }
        if !*mutable {
            let mut const_elems = Vec::with_capacity(elems.len());
            let mut cur_elem_ty = elem_ty;
            let mut all_const = true;
            for e in elems {
                match self.compiler.eval_const_expr_typed(
                    &self.mod_path,
                    self.owner_ty,
                    &self.comptime_env,
                    e,
                    cur_elem_ty,
                ) {
                    Ok((cv, ety, _)) => {
                        if cur_elem_ty.is_none() {
                            cur_elem_ty = Some(ety);
                        }
                        const_elems.push(cv);
                    }
                    Err(_) => {
                        all_const = false;
                        break;
                    }
                }
            }
            if all_const {
                let final_elem_ty = cur_elem_ty.unwrap_or_else(|| {
                    self.compiler.intern_type(Type::Int {
                        signed: true,
                        bits: 64,
                    })
                });
                let final_slice_ty = slice_ty.unwrap_or_else(|| {
                    self.compiler.intern_slice_type(false, final_elem_ty)
                });
                let arr_ty = self.compiler.intern_type(Type::Array {
                    elem: final_elem_ty,
                    len: const_elems.len() as u64,
                });
                let gl_id = GlobalId(self.compiler.program.globals.len() as u32);
                self.compiler.program.globals.push(Global {
                    id: gl_id,
                    mutable: false,
                    ty: arr_ty,
                    init: ConstValue::Aggregate(const_elems),
                });
                let sinfo = self.compiler.slices[&final_slice_ty];
                let ptr_arr_ty = self.compiler.intern_type(Type::Ptr {
                    mutable: false,
                    pointee: arr_ty,
                });
                let gl_ptr_tmp = self.alloc_temp(ptr_arr_ty);
                self.emit(Statement::Assign(
                    Place::new(gl_ptr_tmp),
                    Rvalue::Use(Operand::Const(ConstValue::Global(gl_id))),
                ));
                let ptr_tmp = self.alloc_temp(sinfo.ptr_ty);
                self.emit(Statement::Assign(
                    Place::new(ptr_tmp),
                    Rvalue::Cast(Operand::Copy(Place::new(gl_ptr_tmp)), sinfo.ptr_ty),
                ));
                let slice_local = self.alloc_temp(final_slice_ty);
                self.emit(Statement::Assign(
                    Place::new(slice_local),
                    Rvalue::Aggregate(
                        final_slice_ty,
                        vec![
                            Operand::Copy(Place::new(ptr_tmp)),
                            Operand::Const(ConstValue::I64(elems.len() as i128)),
                        ],
                    ),
                ));
                return Ok((Operand::Copy(Place::new(slice_local)), final_slice_ty));
            }
        }
        let mut ops = Vec::with_capacity(elems.len());
        for e in elems {
            let (op, ety) = self.lower_expr(e, elem_ty)?;
            let target_elem = match elem_ty {
                Some(te) => te,
                None => {
                    elem_ty = Some(ety);
                    ety
                }
            };
            let coerced = self.coerce_operand(op, ety, target_elem)?;
            ops.push(coerced);
        }
        let final_elem_ty = elem_ty.unwrap_or_else(|| {
            self.compiler.intern_type(Type::Int {
                signed: true,
                bits: 64,
            })
        });
        let final_slice_ty = slice_ty
            .unwrap_or_else(|| self.compiler.intern_slice_type(*mutable, final_elem_ty));
        let arr_ty = self.compiler.intern_type(Type::Array {
            elem: final_elem_ty,
            len: ops.len() as u64,
        });
        let arr_local = self.alloc_temp(arr_ty);
        self.emit(Statement::Assign(
            Place::new(arr_local),
            Rvalue::Aggregate(arr_ty, ops),
        ));
        let ref_arr_ty = self.compiler.intern_type(Type::Ptr {
            mutable: *mutable,
            pointee: arr_ty,
        });
        let ref_local = self.alloc_temp(ref_arr_ty);
        self.emit(Statement::Assign(
            Place::new(ref_local),
            Rvalue::Ref {
                mutable: *mutable,
                place: Place::new(arr_local),
            },
        ));
        let slice_op = self.coerce_operand(
            Operand::Copy(Place::new(ref_local)),
            ref_arr_ty,
            final_slice_ty,
        )?;
        Ok((slice_op, final_slice_ty))
    }

    /// Lowers a struct, opaque, or overlay literal `T { field: value, ... }`, applying field defaults.
    fn lower_struct_lit(
        &mut self,
        ty: &TypeExpr,
        fields: &[(String, Expr)],
    ) -> Result<(Operand, TypeId), String> {
        let mut wrap_union: Option<(TypeId, u32)> = None;
        let comp_ty = if let TypeExpr::Named(raw_path) = ty
            && raw_path.len() >= 2
            && {
                let expanded =
                    self.compiler.expand_module_path(&self.comptime_env, raw_path);
                self.compiler
                    .resolve_path(&self.mod_path, &expanded)
                    .is_err()
            }
        {
            let expanded = self.compiler.expand_module_path(&self.comptime_env, raw_path);
            let path = &expanded;
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
        self.lower_struct_lit_of(comp_ty, wrap_union, fields)
    }

    /// A struct, opaque, or overlay literal of type `comp_ty` (the payload of union / error
    /// variant `wrap_union` when set) with the given field values.
    fn lower_struct_lit_of(
        &mut self,
        comp_ty: TypeId,
        wrap_union: Option<(TypeId, u32)>,
        fields: &[(String, Expr)],
    ) -> Result<(Operand, TypeId), String> {
        if let Some(ov_info) = self.compiler.overlays.get(&comp_ty).cloned() {
            if fields.len() != 1 {
                return Err(format!(
                    "Overlay '{}' literal must initialize exactly 1 field, found {}",
                    ov_info.name,
                    fields.len()
                ));
            }
            let (f_name, val_expr) = &fields[0];
            let Some((f_idx, (_, f_ty))) = ov_info
                .fields
                .iter()
                .enumerate()
                .find(|(_, (n, _))| n == f_name)
            else {
                return Err(format!(
                    "Overlay '{}' has no field '{}'",
                    ov_info.name, f_name
                ));
            };
            let (op, val_ty) = self.lower_expr(val_expr, Some(*f_ty))?;
            let coerced = self.coerce_operand(op, val_ty, *f_ty)?;
            let tmp = self.alloc_temp(comp_ty);
            let mut field_place = Place::new(tmp);
            field_place.projections.push(Projection::Field(f_idx as u32));
            self.emit(Statement::Assign(field_place, Rvalue::Use(coerced)));
            let res_op = if self.is_copy_type(comp_ty) {
                Operand::Copy(Place::new(tmp))
            } else {
                Operand::Move(Place::new(tmp))
            };
            return Ok((res_op, comp_ty));
        }
        let Some(comp) = self.compiler.composites.get(&comp_ty).cloned() else {
            return Err(format!(
                "Cannot construct non-struct/opaque type '{}'",
                self.compiler.type_display_name(comp_ty)
            ));
        };
        check_literal_fields(&comp.name, &comp.fields, fields)?;
        // Enforce `opaque` private field encapsulation on literal construction!
        if comp.is_opaque && comp.fields.is_empty() && !self.has_private_access(comp_ty) {
            return Err(format!(
                "Cannot construct opaque type '{}' outside its 'opaque {{ ... }}' block",
                comp.name
            ));
        }
        for (f_name, _, f_vis, _) in &comp.fields {
            if comp.is_opaque
                && *f_vis == Visibility::Private
                && !self.has_private_access(comp_ty)
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
                mutable: true,
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
            self.pop_scope();
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
        let res_op = if comp.is_packed {
            let tmp = self.pack_composite_fields(comp_ty, field_ops)?;
            if self.is_copy_type(comp_ty) {
                Operand::Copy(Place::new(tmp))
            } else {
                Operand::Move(Place::new(tmp))
            }
        } else {
            let tmp = self.alloc_temp(comp_ty);
            self.emit(Statement::Assign(
                Place::new(tmp),
                Rvalue::Aggregate(comp_ty, field_ops),
            ));
            if self.is_copy_type(comp_ty) {
                Operand::Copy(Place::new(tmp))
            } else {
                Operand::Move(Place::new(tmp))
            }
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

    #[inline(never)]
    fn lower_intrinsic_or_closure_expr(
        &mut self,
        expr: &Expr,
        expected_ty: Option<TypeId>,
    ) -> Result<(Operand, TypeId), String> {
        match expr {
            Expr::IntrinsicAlloc { ty, len } => {
                self.lower_alloc(ty, len)
            }
            Expr::IntrinsicRealloc { ty, ptr, len } => {
                self.lower_realloc(ty, ptr, len)
            }
            Expr::IntrinsicRawAlloc(bytes) => self.lower_raw_alloc(bytes, false),
            Expr::IntrinsicRawAllocZeroed(bytes) => self.lower_raw_alloc(bytes, true),
            Expr::IntrinsicDealloc(ptr) => {
                if self.unsafe_depth == 0 {
                    return Err(
                        "'@dealloc' is unsafe and requires an 'unsafe { ... }' block".to_string(),
                    );
                }
                let (ptr_op, ptr_ty) = self.lower_expr(ptr, None)?;
                let Some(&(true, elem_ty)) = self.compiler.raw_ptrs.get(&ptr_ty) else {
                    return Err(format!(
                        "'@dealloc' expects a mutable raw pointer '*mut T', found '{}'",
                        self.compiler.type_display_name(ptr_ty)
                    ));
                };
                let (elem_size, _) = self.compiler.sized_type_layout(elem_ty, "'@dealloc'")?;
                let void_ty = self.compiler.intern_type(Type::Void);
                if elem_size == 0 {
                    // Deallocating a ZST pointer (`@align_of(T) as *mut T` in the null page) is a
                    // no-op; evaluate `ptr` for side effects and never pass it to `free`.
                    let ptr_sink = self.alloc_temp(ptr_ty);
                    self.emit(Statement::Assign(Place::new(ptr_sink), Rvalue::Use(ptr_op)));
                    return Ok((Operand::Const(ConstValue::Void), void_ty));
                }
                let u8_ty = self.compiler.intern_type(Type::Int {
                    signed: false,
                    bits: 8,
                });
                let raw_u8_ptr_ty = self.compiler.intern_raw_ptr_type(true, u8_ty);
                let ptr_u8 = self.alloc_temp(raw_u8_ptr_ty);
                self.emit(Statement::Assign(
                    Place::new(ptr_u8),
                    Rvalue::Cast(ptr_op, raw_u8_ptr_ty),
                ));
                let ptr_arg = (Operand::Copy(Place::new(ptr_u8)), raw_u8_ptr_ty);
                if self.allocator_call("dealloc", vec![ptr_arg])?.is_none() {
                    let free_fn = self.compiler.get_or_register_builtin_extern(
                        "free",
                        vec![raw_u8_ptr_ty],
                        void_ty,
                    );
                    let call_dst = self.alloc_temp(void_ty);
                    let next_bb = self.new_block();
                    self.terminate(Terminator::Call {
                        func: Operand::Const(ConstValue::Func(free_fn)),
                        args: vec![Operand::Copy(Place::new(ptr_u8))],
                        destination: Place::new(call_dst),
                        target: next_bb,
                    });
                    self.body.cur_block = next_bb;
                }
                Ok((Operand::Const(ConstValue::Void), void_ty))
            }
            Expr::IntrinsicAtomic { op, args } => self.lower_atomic(*op, args),
            Expr::IntrinsicMemcpy { dest, src, len }
            | Expr::IntrinsicMemmove { dest, src, len } => {
                let is_memmove = matches!(expr, Expr::IntrinsicMemmove { .. });
                let intr_name = if is_memmove { "@memmove" } else { "@memcpy" };
                if self.unsafe_depth == 0 {
                    return Err(format!(
                        "'{intr_name}' is unsafe and requires an 'unsafe {{ ... }}' block"
                    ));
                }
                let (dest_op, dest_ty) = self.lower_expr(dest, None)?;
                let Some(&(true, elem_ty)) = self.compiler.raw_ptrs.get(&dest_ty) else {
                    return Err(format!(
                        "'{intr_name}' destination must be a mutable raw pointer '*mut T', found '{}'",
                        self.compiler.type_display_name(dest_ty)
                    ));
                };
                self.compiler.sized_type_layout(elem_ty, intr_name)?;
                let const_elem_ptr_ty = self.compiler.intern_raw_ptr_type(false, elem_ty);
                let (src_op, src_ty) = self.lower_expr(src, Some(const_elem_ptr_ty))?;
                let Some(&(_, src_pointee)) = self.compiler.raw_ptrs.get(&src_ty) else {
                    return Err(format!(
                        "'{intr_name}' source must be a raw pointer '*const {}' or '*mut {}', found '{}'",
                        self.compiler.type_display_name(elem_ty),
                        self.compiler.type_display_name(elem_ty),
                        self.compiler.type_display_name(src_ty)
                    ));
                };
                if src_pointee != elem_ty {
                    return Err(format!(
                        "'{intr_name}' pointer type mismatch: destination points to '{}', but source points to '{}'",
                        self.compiler.type_display_name(elem_ty),
                        self.compiler.type_display_name(src_pointee)
                    ));
                }

                let usize_ty = self.compiler.intern_type(Type::Int {
                    signed: false,
                    bits: 64,
                });
                let (len_op, len_ty) = self.lower_expr(len, Some(usize_ty))?;
                let len_coerced = self.coerce_operand(len_op, len_ty, usize_ty)?;
                // `slir.memcopy.<copy|move>.<T>(dest, src, count)`: the element type travels with
                // the call, so the VM copies `T` slots; the LLVM backend emits `llvm.memcpy` /
                // `llvm.memmove` of `count * size_of(T)` bytes.
                let mut_ptr_ty = self.compiler.intern_raw_ptr_type(true, elem_ty);
                let dest_raw = self.alloc_temp(mut_ptr_ty);
                self.emit(Statement::Assign(
                    Place::new(dest_raw),
                    Rvalue::Cast(dest_op, mut_ptr_ty),
                ));
                let src_raw = self.alloc_temp(const_elem_ptr_ty);
                self.emit(Statement::Assign(
                    Place::new(src_raw),
                    Rvalue::Cast(src_op, const_elem_ptr_ty),
                ));
                let void_ty = self.compiler.intern_type(Type::Void);
                let op_name = if is_memmove { "move" } else { "copy" };
                let symbol = format!("{}{op_name}.{}", crate::ir::MEMCOPY_PREFIX, elem_ty.0);
                let copy_fn = self.compiler.get_or_register_builtin_extern(
                    &symbol,
                    vec![mut_ptr_ty, const_elem_ptr_ty, usize_ty],
                    void_ty,
                );
                let call_dst = self.alloc_temp(void_ty);
                let next_bb = self.new_block();
                self.terminate(Terminator::Call {
                    func: Operand::Const(ConstValue::Func(copy_fn)),
                    args: vec![
                        Operand::Copy(Place::new(dest_raw)),
                        Operand::Copy(Place::new(src_raw)),
                        len_coerced,
                    ],
                    destination: Place::new(call_dst),
                    target: next_bb,
                });
                self.body.cur_block = next_bb;
                Ok((Operand::Const(ConstValue::Void), void_ty))
            }
            Expr::IntrinsicTransmute { dst_ty, src } => {
                if self.unsafe_depth == 0 {
                    return Err(
                        "'@transmute' is unsafe and requires an 'unsafe { ... }' block".to_string(),
                    );
                }
                let target_ty = self.compiler.resolve_type_expr(
                    &self.mod_path,
                    self.owner_ty,
                    &self.comptime_env,
                    dst_ty,
                )?;
                let (src_op, src_ty) = self.lower_expr(src, None)?;
                let (src_size, _) = self.compiler.sized_type_layout(src_ty, "'@transmute'")?;
                let (dst_size, _) = self.compiler.sized_type_layout(target_ty, "'@transmute'")?;
                if src_size != dst_size {
                    return Err(format!(
                        "Cannot '@transmute' from '{}' ({} bytes) to '{}' ({} bytes): types must have identical size",
                        self.compiler.type_display_name(src_ty),
                        src_size,
                        self.compiler.type_display_name(target_ty),
                        dst_size
                    ));
                }
                let move_src_op = match src_op {
                    // A `copy` source stays usable; others are consumed without running `drop`.
                    Operand::Copy(p) if self.is_copy_type(src_ty) => Operand::Copy(p),
                    Operand::Copy(p) => {
                        if self.place_traverses_safe_ref(&p)
                            || self.static_locals.contains_key(&p.local)
                        {
                            Operand::Copy(p)
                        } else {
                            Operand::Move(p)
                        }
                    }
                    other => other,
                };
                let src_tmp = self.alloc_temp(src_ty);
                self.emit(Statement::Assign(
                    Place::new(src_tmp),
                    Rvalue::Use(move_src_op),
                ));
                let dst_tmp = self.alloc_temp(target_ty);
                self.emit(Statement::Assign(
                    Place::new(dst_tmp),
                    Rvalue::Transmute(Operand::Move(Place::new(src_tmp)), target_ty),
                ));
                let out_op = if self.is_copy_type(target_ty) {
                    Operand::Copy(Place::new(dst_tmp))
                } else {
                    Operand::Move(Place::new(dst_tmp))
                };
                Ok((out_op, target_ty))
            }
            Expr::IntrinsicCAbi(target) => {
                let Expr::Path(path) = target.as_ref() else {
                    return Err("'@c_abi' expects the name of an 'export fn'".to_string());
                };
                let Ok(ResolvedItem::Func(fmod, fname)) =
                    self.compiler.resolve_path(&self.mod_path, path)
                else {
                    return Err(format!(
                        "'@c_abi({})' does not name a function",
                        path.join("::")
                    ));
                };
                let fn_id = self.compiler.get_or_instantiate_func(&fmod, &fname, &[])?;
                let Some(wrapper) = self.compiler.c_abi_func_wrappers.get(&fn_id).cloned() else {
                    return Err(format!(
                        "'@c_abi({fname})' requires an 'export fn'; '{fname}' has no C ABI"
                    ));
                };
                // The C entry point of an `unsafe fn` keeps its preconditions.
                let is_unsafe = self.compiler.unsafe_fns.contains(&fn_id);
                let ptr_ty = self.compiler.intern_c_fn_ptr_type(
                    wrapper.c_abi_param_tys.clone(),
                    wrapper.c_abi_ret_ty,
                    is_unsafe,
                );
                Ok((Operand::Const(ConstValue::Func(wrapper.c_abi_fn_id)), ptr_ty))
            }
            Expr::IntrinsicForget(inner) => {
                if self.unsafe_depth == 0 {
                    return Err(
                        "'@forget' is unsafe and requires an 'unsafe { ... }' block".to_string(),
                    );
                }
                let (op, val_ty) = self.lower_expr(inner, None)?;
                self.check_linear_sink(val_ty, "forgets", "")?;
                let move_op = match op {
                    Operand::Copy(p) => {
                        if self.place_traverses_safe_ref(&p) {
                            return Err(format!(
                                "Cannot '@forget' through dereferenced safe reference '{}'",
                                p
                            ));
                        }
                        if let Some((stat_name, _)) = self.static_locals.get(&p.local) {
                            return Err(format!("Cannot '@forget' static variable '{}'", stat_name));
                        }
                        Operand::Move(p)
                    }
                    other => other,
                };
                let tmp = self.alloc_temp(val_ty);
                self.emit(Statement::Assign(Place::new(tmp), Rvalue::Use(move_op)));
                self.emit(Statement::StorageDead(tmp));
                let void_ty = self.compiler.intern_type(Type::Void);
                Ok((Operand::Const(ConstValue::Void), void_ty))
            }
            Expr::IntrinsicLayout { ty, align } => {
                let n = self.compiler.eval_layout_intrinsic(
                    &self.mod_path,
                    self.owner_ty,
                    &self.comptime_env,
                    ty,
                    *align,
                )?;
                let usize_ty = self.compiler.intern_type(Type::Int {
                    signed: false,
                    bits: 64,
                });
                Ok((Operand::Const(ConstValue::I64(n)), usize_ty))
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
                // `@clone(&e)` clones `e`, whatever its type (a `&T` element of a `Vec[&T]` is
                // cloned as a reference); `@clone(r)` of a reference `r` clones what it refers to.
                let (written_ref, (mut place, mut ty_id)) = match inner.as_ref() {
                    Expr::Ref { expr, .. } => (true, self.lower_place(expr, false)?),
                    _ => (false, self.lower_place(inner, false)?),
                };
                if !written_ref
                    && let Type::Ptr { pointee, .. } = self.compiler.program.types[ty_id.0 as usize]
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
                self.body.cur_block = next_bb;
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
            Expr::IntrinsicCompileError(_) => {
                self.compiler
                    .eval_comptime_val(&self.mod_path, self.owner_ty, &self.comptime_env, expr)?;
                unreachable!("'@compile_error' evaluates to an error")
            }
            Expr::IntrinsicTrap => {
                self.terminate(Terminator::Unreachable);
                let never_ty = self.compiler.intern_type(Type::Never);
                Ok((Operand::Const(ConstValue::Void), never_ty))
            }
            Expr::Break(label) | Expr::Continue(label) => {
                let is_break = matches!(expr, Expr::Break(_));
                let kw = if is_break { "break" } else { "continue" };
                let ctx = match label {
                    None => self.loops.last().cloned(),
                    Some(l) => {
                        let found = self.loops.iter().rev().find(|c| c.label.as_deref() == Some(l));
                        if found.is_none() {
                            return Err(format!("'{kw} {l}': no enclosing loop is labelled '{l}'"));
                        }
                        found.cloned()
                    }
                };
                let Some(ctx) = ctx else {
                    return Err(format!("'{kw}' outside of a loop"));
                };
                if !self.is_terminated() {
                    self.cleanup_scopes_from(ctx.scope_depth);
                    let target = if is_break { ctx.break_bb } else { ctx.continue_bb };
                    self.terminate(Terminator::Goto { target });
                }
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
                let ret_ty = self.body.locals[0];
                if let Some(expr) = opt_expr {
                    let (op, expr_ty) = self.lower_returned_expr(expr, ret_ty)?;
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
                        self.pop_scope();
                        Err(e)
                    } else if self.is_terminated() {
                        self.pop_scope();
                        Ok((Operand::Const(ConstValue::Void), never_ty))
                    } else {
                        match self.lower_expr(tail_expr, expected_ty) {
                            Err(e) => {
                                self.pop_scope();
                                Err(e)
                            }
                            Ok((tail_op, tail_ty)) => {
                                if self.is_terminated() {
                                    self.pop_scope();
                                    Ok((Operand::Const(ConstValue::Void), never_ty))
                                } else if matches!(
                                    self.compiler.program.types[tail_ty.0 as usize],
                                    Type::Void
                                ) {
                                    self.cleanup_top_scope();
                                    self.pop_scope();
                                    Ok((Operand::Const(ConstValue::Void), void_ty))
                                } else {
                                    let res_local = self.alloc_temp(tail_ty);
                                    self.emit(Statement::Assign(
                                        Place::new(res_local),
                                        Rvalue::Use(tail_op),
                                    ));
                                    self.cleanup_top_scope();
                                    self.pop_scope();
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
                self.lower_lambda(is_move, params, ret_ty, body)
            }
            _ => unreachable!(),
        }
    }

    /// Lowers `@alloc(T, len)`.
    fn lower_alloc(&mut self, ty: &TypeExpr, len: &Expr) -> Result<(Operand, TypeId), String> {
        let elem_ty = self.compiler.resolve_type_expr(
            &self.mod_path,
            self.owner_ty,
            &self.comptime_env,
            ty,
        )?;
        let (elem_size, elem_align) = self.compiler.sized_type_layout(elem_ty, "'@alloc'")?;
        let usize_ty = self.compiler.intern_type(Type::Int {
            signed: false,
            bits: 64,
        });
        let (len_op, len_ty) = self.lower_expr(len, Some(usize_ty))?;
        let len_coerced = self.coerce_operand(len_op, len_ty, usize_ty)?;
        let out_ptr_ty = self.compiler.intern_raw_ptr_type(true, elem_ty);

        if elem_size == 0 {
            // Zero-sized types (`void`, `struct {}`, `[T; 0]`, etc.) map to their alignment
            // (`1, 2, 4, 8, 16, ...`) in the OS null page with zero heap allocation.
            let len_sink = self.alloc_temp(usize_ty);
            self.emit(Statement::Assign(
                Place::new(len_sink),
                Rvalue::Use(len_coerced),
            ));
            let align_local = self.alloc_temp(usize_ty);
            self.emit(Statement::Assign(
                Place::new(align_local),
                Rvalue::Use(Operand::Const(ConstValue::I64(elem_align as i128))),
            ));
            let out_ptr = self.alloc_temp(out_ptr_ty);
            self.emit(Statement::Assign(
                Place::new(out_ptr),
                Rvalue::Cast(Operand::Copy(Place::new(align_local)), out_ptr_ty),
            ));
            return Ok((Operand::Copy(Place::new(out_ptr)), out_ptr_ty));
        }

        let bytes_local = self.alloc_temp(usize_ty);
        self.emit(Statement::Assign(
            Place::new(bytes_local),
            Rvalue::BinaryOp(
                BinOp::Mul,
                len_coerced,
                Operand::Const(ConstValue::I64(elem_size as i128)),
            ),
        ));

        let bool_ty = self.compiler.intern_type(Type::Bool);
        let is_zero = self.alloc_temp(bool_ty);
        self.emit(Statement::Assign(
            Place::new(is_zero),
            Rvalue::BinaryOp(
                BinOp::Eq,
                Operand::Copy(Place::new(bytes_local)),
                Operand::Const(ConstValue::I64(0)),
            ),
        ));
        let zero_bb = self.new_block();
        let call_bb = self.new_block();
        self.terminate(Terminator::SwitchInt {
            discr: Operand::Copy(Place::new(is_zero)),
            targets: vec![(1, zero_bb)],
            otherwise: call_bb,
        });
        self.body.cur_block = zero_bb;
        self.emit(Statement::Assign(
            Place::new(bytes_local),
            Rvalue::Use(Operand::Const(ConstValue::I64(1))),
        ));
        self.terminate(Terminator::Goto { target: call_bb });
        self.body.cur_block = call_bb;

        let u8_ty = self.compiler.intern_type(Type::Int {
            signed: false,
            bits: 8,
        });
        let raw_u8_ptr_ty = self.compiler.intern_raw_ptr_type(true, u8_ty);
        let bytes = Operand::Copy(Place::new(bytes_local));
        let raw_res = self.alloc_call(bytes, elem_align, usize_ty, raw_u8_ptr_ty)?;

        let addr_local = self.alloc_temp(usize_ty);
        self.emit(Statement::Assign(
            Place::new(addr_local),
            Rvalue::Cast(Operand::Copy(Place::new(raw_res)), usize_ty),
        ));
        let is_null = self.alloc_temp(bool_ty);
        self.emit(Statement::Assign(
            Place::new(is_null),
            Rvalue::BinaryOp(
                BinOp::Eq,
                Operand::Copy(Place::new(addr_local)),
                Operand::Const(ConstValue::I64(0)),
            ),
        ));
        let oom_bb = self.new_block();
        let ok_bb = self.new_block();
        self.terminate(Terminator::SwitchInt {
            discr: Operand::Copy(Place::new(is_null)),
            targets: vec![(1, oom_bb)],
            otherwise: ok_bb,
        });
        self.body.cur_block = oom_bb;
        self.terminate(Terminator::Unreachable);
        self.body.cur_block = ok_bb;

        let out_ptr = self.alloc_temp(out_ptr_ty);
        self.emit(Statement::Assign(
            Place::new(out_ptr),
            Rvalue::Cast(Operand::Copy(Place::new(raw_res)), out_ptr_ty),
        ));
        Ok((Operand::Copy(Place::new(out_ptr)), out_ptr_ty))
    }

    /// Calls the method `name` of the program's allocator, unless it is the default. An allocator
    /// cannot allocate through itself.
    fn allocator_call(
        &mut self,
        name: &str,
        args: Vec<(Operand, TypeId)>,
    ) -> Result<Option<Operand>, String> {
        let Some(allocator) = self.compiler.program_allocator()? else {
            return Ok(None);
        };
        if self.owner_ty == Some(allocator) {
            return Ok(None);
        }
        let outer = self.comptime_env.insert(ALLOCATOR_ENV.to_string(), ComptimeVal::Type(allocator));
        self.scopes.push(Vec::new());
        let mut arg_exprs = Vec::with_capacity(args.len());
        for (i, (op, ty)) in args.into_iter().enumerate() {
            let local = self.alloc_temp(ty);
            self.emit(Statement::Assign(Place::new(local), Rvalue::Use(op)));
            let name = format!("__allocator_arg{i}");
            arg_exprs.push(Expr::Path(vec![name.clone()]));
            self.scopes.last_mut().unwrap().push(ScopeVar {
                name,
                local,
                ty,
                opaque_bound: None,
                mutable: false,
            });
        }
        let call = Expr::Call {
            callee: Box::new(Expr::Path(vec![ALLOCATOR_ENV.to_string(), name.to_string()])),
            ct_args: None,
            args: arg_exprs,
            at: crate::ast::At::default(),
        };
        let result = self.lower_expr(&call, None);
        self.scopes.pop();
        match outer {
            Some(v) => {
                self.comptime_env.insert(ALLOCATOR_ENV.to_string(), v);
            }
            None => {
                self.comptime_env.remove(ALLOCATOR_ENV);
            }
        }
        Ok(Some(result?.0))
    }

    /// Allocates `bytes`, yielding a local holding the result.
    fn alloc_call(
        &mut self,
        bytes: Operand,
        align: u64,
        usize_ty: TypeId,
        raw_u8_ptr_ty: TypeId,
    ) -> Result<LocalId, String> {
        let raw_res = self.alloc_temp(raw_u8_ptr_ty);
        let custom = self.allocator_call(
            "alloc",
            vec![
                (bytes.clone(), usize_ty),
                (Operand::Const(ConstValue::I64(align as i128)), usize_ty),
            ],
        )?;
        if let Some(result) = custom {
            self.emit(Statement::Assign(Place::new(raw_res), Rvalue::Use(result)));
            return Ok(raw_res);
        }
        let malloc =
            self.compiler.get_or_register_builtin_extern("malloc", vec![usize_ty], raw_u8_ptr_ty);
        let next_bb = self.new_block();
        self.terminate(Terminator::Call {
            func: Operand::Const(ConstValue::Func(malloc)),
            args: vec![bytes],
            destination: Place::new(raw_res),
            target: next_bb,
        });
        self.body.cur_block = next_bb;
        Ok(raw_res)
    }

    /// Lowers `@raw_alloc(bytes)`, or with `zeroed` `@raw_alloc_zeroed(bytes)`, which may yield null.
    fn lower_raw_alloc(&mut self, bytes: &Expr, zeroed: bool) -> Result<(Operand, TypeId), String> {
        let usize_ty = self.compiler.intern_type(Type::Int {
            signed: false,
            bits: 64,
        });
        let u8_ty = self.compiler.intern_type(Type::Int {
            signed: false,
            bits: 8,
        });
        let raw_u8_ptr_ty = self.compiler.intern_raw_ptr_type(true, u8_ty);
        let (op, ty) = self.lower_expr(bytes, Some(usize_ty))?;
        let bytes = self.coerce_operand(op, ty, usize_ty)?;
        let dst = if zeroed {
            self.alloc_zeroed_call(bytes, 16, usize_ty, raw_u8_ptr_ty)?
        } else {
            self.alloc_call(bytes, 16, usize_ty, raw_u8_ptr_ty)?
        };
        Ok((Operand::Copy(Place::new(dst)), raw_u8_ptr_ty))
    }

    /// `alloc_call` for zeroed memory: the program allocator's `alloc_zeroed` (which, unless it
    /// writes its own, allocates and zeroes), or C's `calloc`, whose memory is often zero already.
    fn alloc_zeroed_call(
        &mut self,
        bytes: Operand,
        align: u64,
        usize_ty: TypeId,
        raw_u8_ptr_ty: TypeId,
    ) -> Result<LocalId, String> {
        let raw_res = self.alloc_temp(raw_u8_ptr_ty);
        let custom = self.allocator_call(
            "alloc_zeroed",
            vec![
                (bytes.clone(), usize_ty),
                (Operand::Const(ConstValue::I64(align as i128)), usize_ty),
            ],
        )?;
        if let Some(result) = custom {
            self.emit(Statement::Assign(Place::new(raw_res), Rvalue::Use(result)));
            return Ok(raw_res);
        }
        let calloc = self.compiler.get_or_register_builtin_extern(
            "calloc",
            vec![usize_ty, usize_ty],
            raw_u8_ptr_ty,
        );
        let next_bb = self.new_block();
        self.terminate(Terminator::Call {
            func: Operand::Const(ConstValue::Func(calloc)),
            args: vec![Operand::Const(ConstValue::I64(1)), bytes],
            destination: Place::new(raw_res),
            target: next_bb,
        });
        self.body.cur_block = next_bb;
        Ok(raw_res)
    }

    /// Lowers `@realloc(T, ptr, len)`.
    fn lower_realloc(
        &mut self,
        ty: &TypeExpr,
        ptr: &Expr,
        len: &Expr,
    ) -> Result<(Operand, TypeId), String> {
        let elem_ty = self.compiler.resolve_type_expr(
            &self.mod_path,
            self.owner_ty,
            &self.comptime_env,
            ty,
        )?;
        let (elem_size, elem_align) = self.compiler.sized_type_layout(elem_ty, "'@realloc'")?;
        let out_ptr_ty = self.compiler.intern_raw_ptr_type(true, elem_ty);
        let (ptr_op, ptr_ty) = self.lower_expr(ptr, Some(out_ptr_ty))?;
        if self.compiler.raw_ptrs.get(&ptr_ty) != Some(&(true, elem_ty)) {
            return Err(format!(
                "'@realloc' expects a mutable raw pointer '{}', found '{}'",
                self.compiler.type_display_name(out_ptr_ty),
                self.compiler.type_display_name(ptr_ty)
            ));
        }

        let usize_ty = self.compiler.intern_type(Type::Int {
            signed: false,
            bits: 64,
        });
        let (len_op, len_ty) = self.lower_expr(len, Some(usize_ty))?;
        let len_coerced = self.coerce_operand(len_op, len_ty, usize_ty)?;

        if elem_size == 0 {
            // Reallocating a ZST pointer evaluates `ptr` and `len` for side effects and returns
            // `@align_of(T) as *mut T` with zero heap traffic.
            let ptr_sink = self.alloc_temp(out_ptr_ty);
            self.emit(Statement::Assign(Place::new(ptr_sink), Rvalue::Use(ptr_op)));
            let len_sink = self.alloc_temp(usize_ty);
            self.emit(Statement::Assign(
                Place::new(len_sink),
                Rvalue::Use(len_coerced),
            ));
            let align_local = self.alloc_temp(usize_ty);
            self.emit(Statement::Assign(
                Place::new(align_local),
                Rvalue::Use(Operand::Const(ConstValue::I64(elem_align as i128))),
            ));
            let out_ptr = self.alloc_temp(out_ptr_ty);
            self.emit(Statement::Assign(
                Place::new(out_ptr),
                Rvalue::Cast(Operand::Copy(Place::new(align_local)), out_ptr_ty),
            ));
            return Ok((Operand::Copy(Place::new(out_ptr)), out_ptr_ty));
        }

        let bytes_local = self.alloc_temp(usize_ty);
        self.emit(Statement::Assign(
            Place::new(bytes_local),
            Rvalue::BinaryOp(
                BinOp::Mul,
                len_coerced,
                Operand::Const(ConstValue::I64(elem_size as i128)),
            ),
        ));

        let bool_ty = self.compiler.intern_type(Type::Bool);
        let is_zero = self.alloc_temp(bool_ty);
        self.emit(Statement::Assign(
            Place::new(is_zero),
            Rvalue::BinaryOp(
                BinOp::Eq,
                Operand::Copy(Place::new(bytes_local)),
                Operand::Const(ConstValue::I64(0)),
            ),
        ));
        let zero_bb = self.new_block();
        let call_bb = self.new_block();
        self.terminate(Terminator::SwitchInt {
            discr: Operand::Copy(Place::new(is_zero)),
            targets: vec![(1, zero_bb)],
            otherwise: call_bb,
        });
        self.body.cur_block = zero_bb;
        self.emit(Statement::Assign(
            Place::new(bytes_local),
            Rvalue::Use(Operand::Const(ConstValue::I64(1))),
        ));
        self.terminate(Terminator::Goto { target: call_bb });
        self.body.cur_block = call_bb;

        let u8_ty = self.compiler.intern_type(Type::Int {
            signed: false,
            bits: 8,
        });
        let raw_u8_ptr_ty = self.compiler.intern_raw_ptr_type(true, u8_ty);
        let ptr_u8 = self.alloc_temp(raw_u8_ptr_ty);
        self.emit(Statement::Assign(
            Place::new(ptr_u8),
            Rvalue::Cast(ptr_op, raw_u8_ptr_ty),
        ));

        let raw_res = self.alloc_temp(raw_u8_ptr_ty);
        let custom = self.allocator_call(
            "realloc",
            vec![
                (Operand::Copy(Place::new(ptr_u8)), raw_u8_ptr_ty),
                (Operand::Copy(Place::new(bytes_local)), usize_ty),
                (Operand::Const(ConstValue::I64(elem_align as i128)), usize_ty),
            ],
        )?;
        if let Some(result) = custom {
            self.emit(Statement::Assign(Place::new(raw_res), Rvalue::Use(result)));
        } else {
            let realloc_fn = self.compiler.get_or_register_builtin_extern(
                "realloc",
                vec![raw_u8_ptr_ty, usize_ty],
                raw_u8_ptr_ty,
            );
            let check_bb = self.new_block();
            self.terminate(Terminator::Call {
                func: Operand::Const(ConstValue::Func(realloc_fn)),
                args: vec![
                    Operand::Copy(Place::new(ptr_u8)),
                    Operand::Copy(Place::new(bytes_local)),
                ],
                destination: Place::new(raw_res),
                target: check_bb,
            });
            self.body.cur_block = check_bb;
        }

        let addr_local = self.alloc_temp(usize_ty);
        self.emit(Statement::Assign(
            Place::new(addr_local),
            Rvalue::Cast(Operand::Copy(Place::new(raw_res)), usize_ty),
        ));
        let is_null = self.alloc_temp(bool_ty);
        self.emit(Statement::Assign(
            Place::new(is_null),
            Rvalue::BinaryOp(
                BinOp::Eq,
                Operand::Copy(Place::new(addr_local)),
                Operand::Const(ConstValue::I64(0)),
            ),
        ));
        let oom_bb = self.new_block();
        let ok_bb = self.new_block();
        self.terminate(Terminator::SwitchInt {
            discr: Operand::Copy(Place::new(is_null)),
            targets: vec![(1, oom_bb)],
            otherwise: ok_bb,
        });
        self.body.cur_block = oom_bb;
        self.terminate(Terminator::Unreachable);
        self.body.cur_block = ok_bb;

        let out_ptr = self.alloc_temp(out_ptr_ty);
        self.emit(Statement::Assign(
            Place::new(out_ptr),
            Rvalue::Cast(Operand::Copy(Place::new(raw_res)), out_ptr_ty),
        ));
        Ok((Operand::Copy(Place::new(out_ptr)), out_ptr_ty))
    }

    /// Lowers `async f(x)`. The arguments are evaluated here, into locals, and a closure that
    /// moves them into the call goes to `start_task`. A receiver stays where it is, borrowed as
    /// the method needs, unless the method consumes it.
    fn lower_async(
        &mut self,
        call: &Expr,
        bound: bool,
        executor: Option<&Expr>,
    ) -> Result<(Operand, TypeId), String> {
        const RESULT: &str = "__AsyncResult";
        if !bound {
            let mut stmts = Vec::new();
            let mut bound_executor = None;
            if let Some(e) = executor {
                let name = "__async_executor".to_string();
                stmts.push(Stmt::Let { mutable: false, name: name.clone(), ty: None, init: e.clone() });
                bound_executor = Some(Box::new(Expr::Path(vec![name])));
            }
            let bind = |init: Expr, stmts: &mut Vec<Stmt>| {
                let name = format!("__async{}", stmts.len());
                stmts.push(Stmt::Let { mutable: false, name: name.clone(), ty: None, init });
                Expr::Path(vec![name])
            };
            let bind_args = |args: &[Expr], stmts: &mut Vec<Stmt>| -> Vec<Expr> {
                args.iter()
                    .map(|arg| match arg {
                        // Left in the call, a literal takes the type of its parameter.
                        Expr::Int(_) | Expr::Float(_) | Expr::Bool(_) | Expr::Rune(_)
                        | Expr::Str(_) | Expr::Null => arg.clone(),
                        _ => bind(arg.clone(), stmts),
                    })
                    .collect()
            };
            let call = match call {
                Expr::Call { callee, ct_args, args, at } => Expr::Call {
                    callee: callee.clone(),
                    ct_args: ct_args.clone(),
                    args: bind_args(args, &mut stmts),
                    at: *at,
                },
                Expr::MethodCall { receiver, method, args, .. } => {
                    let root = Self::root_var_of_place_expr(receiver);
                    let by_value = match receiver.as_ref() {
                        Expr::Path(p) if p.len() == 1 => self.method_consumes_self(&p[0], method)?,
                        _ => root.is_none(),
                    };
                    let mutable = root.is_some_and(|r| self.method_requires_mut_self(r, method));
                    let args = bind_args(args, &mut stmts);
                    let init = if by_value {
                        (**receiver).clone()
                    } else {
                        Expr::Ref { mutable, expr: receiver.clone() }
                    };
                    let bound_receiver = bind(init, &mut stmts);
                    let mut rebuilt = call.clone();
                    if let Expr::MethodCall { receiver: r, args: a, .. } = &mut rebuilt {
                        **r = bound_receiver;
                        *a = args;
                    }
                    rebuilt
                }
                _ => return Err("'async' takes a call".to_string()),
            };
            stmts.push(Stmt::Expr(Expr::Async { call: Box::new(call), bound: true, executor: bound_executor }));
            return self.lower_expr(&Expr::Block(Block { stmts, lines: Vec::new() }), None);
        }

        // The call is lowered once only for its type: its code belongs in the closure.
        let (saved, saved_scopes) = (self.body.clone(), self.scopes.clone());
        let result = self.lower_expr(call, None).map(|(_, ty)| ty);
        (self.body, self.scopes) = (saved, saved_scopes);
        let result = result?;
        let outer = self.comptime_env.insert(RESULT.to_string(), ComptimeVal::Type(result));
        let ret_ty = TypeExpr::Named(vec![RESULT.to_string()]);
        let returns_nothing =
            matches!(self.compiler.program.types[result.0 as usize], Type::Void);
        let body = if returns_nothing {
            vec![Stmt::Expr(call.clone())]
        } else {
            vec![Stmt::Return(Some(call.clone()))]
        };
        let task = Expr::Lambda {
            is_move: true,
            params: Vec::new(),
            ret_ty,
            body: Block { stmts: body, lines: Vec::new() },
        };
        let start = if executor.is_some() { "start_task_on" } else { "start_task" };
        let lowered = self.lower_expr(
            &Expr::Call {
                callee: Box::new(Expr::Path(["std", "thread", start].map(String::from).to_vec())),
                ct_args: None,
                args: std::iter::once(task).chain(executor.cloned()).collect(),
                at: crate::ast::At::default(),
            },
            None,
        );
        match outer {
            Some(v) => {
                self.comptime_env.insert(RESULT.to_string(), v);
            }
            None => {
                self.comptime_env.remove(RESULT);
            }
        }
        lowered
    }

    /// Lowers a closure literal: captures, its synthesized function, and the closure value.
    fn lower_lambda(
        &mut self,
        is_move: &bool,
        params: &[(bool, String, TypeExpr)],
        ret_ty: &TypeExpr,
        body: &Block,
    ) -> Result<(Operand, TypeId), String> {
        // Captured locals' types become part of the closure type: settle them first.
        self.default_all_type_vars(true)?;
        let mut param_tys = Vec::with_capacity(params.len());
        let mut ast_params = Vec::with_capacity(params.len());
        let mut initial_bound = crate::fasthash::FastSet::default();
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
                default: None,
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
        self.capture_binding_writes.borrow_mut().clear();
        self.capture_moves.borrow_mut().clear();
        self.collect_captures_in_block(body, &initial_bound, &mut captures);
        // A closure that writes a captured binding itself (not through a reference it holds)
        // needs the binding to be `mut`.
        let writes = std::mem::take(&mut *self.capture_binding_writes.borrow_mut());
        for (name, bare) in writes {
            let Some((local, ty)) = self.lookup_var(&name) else {
                continue;
            };
            let through_pointer =
                matches!(self.compiler.program.types[ty.0 as usize], Type::Ptr { .. })
                    || self.compiler.slices.contains_key(&ty)
                    || self.compiler.trait_objs.contains_key(&ty);
            if bare || !through_pointer {
                self.check_binding_writable(&Place::new(local), "assign to captured")?;
            }
        }

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
                is_unsafe: false,
                impl_of: None,
                is_unsafe_impl: false,
                discardable: false,
            };
            if !self.private_access {
                self.compiler.no_private_access_fns.insert(fn_id);
            }
            if self.unsafe_depth > 0 {
                self.compiler.unsafe_closures.insert(fn_id);
            }
            self.compiler.pending_funcs.push(PendingFunc {
                func_id: fn_id,
                module_path: self.mod_path.clone(),
                owner_ty: self.owner_ty,
                decl,
                comptime_env: self.comptime_env.clone(),
                closure_captures: Vec::new(),
            });
            let fn_ptr_ty = self.compiler.fn_value_ptr_type(param_tys, ret_ty_id, false);
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
            // Moving a capture out leaves the environment spent, so such a closure is single-use.
            let moves = std::mem::take(&mut *self.capture_moves.borrow_mut());
            let mut moves_out = false;
            for (name, method) in &moves {
                let ty = self
                    .lookup_var(name)
                    .map(|(_, t)| t)
                    .or_else(|| self.lookup_capture(name).map(|(_, t)| t));
                let by_value = match method {
                    Some(method) => self.method_consumes_self(name, method)?,
                    None => true,
                };
                moves_out |= by_value
                    && captures.iter().any(|(c, _)| c == name)
                    && ty.is_some_and(|t| !self.is_copy_type(t));
            }
            let env_by_val = *is_move && (moves_out || self.compiler.is_linear_type(closure_ty));
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
                    is_move: *is_move,
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
                is_unsafe: false,
                impl_of: None,
                is_unsafe_impl: false,
                discardable: false,
            };
            if !self.private_access {
                self.compiler.no_private_access_fns.insert(call_fn_id);
            }
            if self.unsafe_depth > 0 {
                self.compiler.unsafe_closures.insert(call_fn_id);
            }
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

    /// Lowers `@atomic_<op>(ptr, values...)` to a call of the builtin `slir.atomic.<op>.<type>`,
    /// which the LLVM backend emits as the atomic instruction itself and the VM evaluates directly.
    fn lower_atomic(&mut self, op: AtomicOp, args: &[Expr]) -> Result<(Operand, TypeId), String> {
        let name = op.name();
        if self.unsafe_depth == 0 {
            return Err(format!(
                "'@atomic_{name}' dereferences a raw pointer and requires an 'unsafe {{ ... }}' block"
            ));
        }
        if args.len() != 1 + op.value_args() {
            return Err(format!(
                "'@atomic_{name}' takes {} argument(s) (a pointer and {} value(s)), found {}",
                1 + op.value_args(),
                op.value_args(),
                args.len()
            ));
        }
        let (ptr_op, ptr_ty) = self.lower_expr(&args[0], None)?;
        let Some(&(mutable, elem_ty)) = self.compiler.raw_ptrs.get(&ptr_ty) else {
            return Err(format!(
                "'@atomic_{name}' expects a raw pointer, found '{}'",
                self.compiler.type_display_name(ptr_ty)
            ));
        };
        if !mutable && !matches!(op, AtomicOp::Load | AtomicOp::LoadRelaxed) {
            return Err(format!(
                "'@atomic_{name}' writes through its pointer and needs '*mut', found '{}'",
                self.compiler.type_display_name(ptr_ty)
            ));
        }
        if !matches!(
            self.compiler.program.types[elem_ty.0 as usize],
            Type::Int { bits: 8 | 16 | 32 | 64, .. }
        ) {
            return Err(format!(
                "'@atomic_{name}' operates on 8-, 16-, 32-, or 64-bit integers, found '{}'",
                self.compiler.type_display_name(elem_ty)
            ));
        }
        let mut_ptr_ty = self.compiler.intern_raw_ptr_type(true, elem_ty);
        let ptr_tmp = self.alloc_temp(mut_ptr_ty);
        self.emit(Statement::Assign(
            Place::new(ptr_tmp),
            Rvalue::Cast(ptr_op, mut_ptr_ty),
        ));
        let mut call_args = vec![Operand::Copy(Place::new(ptr_tmp))];
        for arg in &args[1..] {
            let (op, ty) = self.lower_expr(arg, Some(elem_ty))?;
            call_args.push(self.coerce_operand(op, ty, elem_ty)?);
        }
        let ret_ty = if op == AtomicOp::Store {
            self.compiler.intern_type(Type::Void)
        } else {
            elem_ty
        };
        let mut param_tys = vec![mut_ptr_ty];
        param_tys.extend(std::iter::repeat_n(elem_ty, op.value_args()));
        let symbol = format!("{}{name}.{}", crate::ir::ATOMIC_PREFIX, elem_ty.0);
        let fn_id = self
            .compiler
            .get_or_register_builtin_extern(&symbol, param_tys, ret_ty);
        let dst = self.emit_call_to(fn_id, call_args, ret_ty);
        Ok((Operand::Copy(Place::new(dst)), ret_ty))
    }

    pub(super) fn emit_call_to(
        &mut self,
        fn_id: FuncId,
        args: Vec<Operand>,
        ret_ty: TypeId,
    ) -> LocalId {
        let dst = self.alloc_temp(ret_ty);
        let next_bb = self.new_block();
        self.terminate(Terminator::Call {
            func: Operand::Const(ConstValue::Func(fn_id)),
            args,
            destination: Place::new(dst),
            target: next_bb,
        });
        self.body.cur_block = next_bb;
        dst
    }

    /// In the block of the winning `@select` arm (`winner`, or `None` for `default`), hands every
    /// losing send arm's still-owned value to its `else |unsent|` handler, or drops it. Dropping a
    /// linear value is rejected by Stage 3b, so linear sends must provide a handler.
    fn settle_unsent_select_values(
        &mut self,
        send_values: &[UnsentSendValue],
        winner: Option<usize>,
    ) -> Result<(), String> {
        for (idx, val_local, elem_ty, unsent) in send_values {
            if Some(*idx) == winner {
                continue;
            }
            if let Some((name, handler)) = unsent {
                self.scopes.push(vec![ScopeVar {
                    name: name.clone(),
                    local: *val_local,
                    ty: *elem_ty,
                    opaque_bound: None,
                    mutable: false,
                }]);
                let _ = self.lower_expr(handler, None)?;
                self.cleanup_top_scope();
                self.pop_scope();
            } else if !self.is_copy_type(*elem_ty) {
                let next = self.new_block();
                self.terminate(Terminator::Drop {
                    place: Place::new(*val_local),
                    target: next,
                });
                self.body.cur_block = next;
            }
        }
        Ok(())
    }

    pub(super) fn lower_select(
        &mut self,
        arms: &[SelectArm],
        expected_ty: Option<TypeId>,
    ) -> Result<(Operand, TypeId), String> {
        let mut wait_arms: Vec<&SelectArm> = Vec::new();
        let mut default_arm: Option<&Expr> = None;
        for arm in arms {
            if matches!(arm.op, SelectOp::Default) {
                if default_arm.is_some() {
                    return Err("Multiple 'default' arms in '@select'".to_string());
                }
                default_arm = Some(&arm.body);
            } else {
                wait_arms.push(arm);
            }
        }
        if wait_arms.is_empty() {
            if let Some(def_body) = default_arm {
                return self.lower_expr(def_body, expected_ty);
            }
            return Err("'@select' must have at least one branch".to_string());
        }

        let bool_ty = self.compiler.intern_type(Type::Bool);
        let i32_ty = self.compiler.intern_type(Type::Int {
            signed: true,
            bits: 32,
        });

        let mut branches: Vec<SelectBranchLower> = Vec::with_capacity(wait_arms.len());
        for arm in &wait_arms {
            branches.push(self.lower_select_branch(arm)?);
        }

        let winner_local = self.alloc_temp(i32_ty);
        self.emit(Statement::Assign(
            Place::new(winner_local),
            Rvalue::Use(Operand::Const(ConstValue::I64(-1))),
        ));

        // 5-stage Execution-Agnostic `@select` CFG:
        // FastPoll -> Register -> Park -> Unregister -> SwitchInt(winner)
        let bb_fast_0 = self.new_block();
        let bb_register = self.new_block();
        let bb_switch = self.new_block();
        let bb_default_opt = default_arm.map(|_| self.new_block());

        self.terminate(Terminator::Goto { target: bb_fast_0 });

        // Stage 1: FastPoll
        let mut cur_fast_bb = bb_fast_0;
        for (idx, binfo) in branches.iter().enumerate() {
            self.body.cur_block = cur_fast_bb;
            let fast_ok = self.emit_call_to(
                binfo.fast_fn,
                vec![
                    Operand::Copy(Place::new(binfo.ch_ref_local)),
                    Operand::Copy(Place::new(binfo.slot_ptr_local)),
                ],
                bool_ty,
            );
            let hit_bb = self.new_block();
            let next_fast_bb = if idx + 1 < branches.len() {
                self.new_block()
            } else if let Some(def_bb) = bb_default_opt {
                def_bb
            } else {
                bb_register
            };
            self.terminate(Terminator::SwitchInt {
                discr: Operand::Copy(Place::new(fast_ok)),
                targets: vec![(1, hit_bb)],
                otherwise: next_fast_bb,
            });
            self.body.cur_block = hit_bb;
            self.emit(Statement::Assign(
                Place::new(winner_local),
                Rvalue::Use(Operand::Const(ConstValue::I64(idx as i128))),
            ));
            self.terminate(Terminator::Goto { target: bb_switch });
            cur_fast_bb = next_fast_bb;
        }

        // Stages 2, 3, 4: Register -> Park -> Unregister (reachable when no `default` branch)
        if bb_default_opt.is_none() {
            self.body.cur_block = bb_register;
            self.emit_select_wait(&branches, winner_local)?;
            self.terminate(Terminator::Goto { target: bb_switch });
        }

        // Stage 5: SwitchInt(winner). Every arm first settles the values of the *losing* send arms.
        let send_values: Vec<UnsentSendValue> = branches
            .iter()
            .enumerate()
            .filter_map(|(i, b)| {
                b.send_val_local
                    .map(|l| (i, l, b.elem_ty, b.unsent.clone()))
            })
            .collect();
        let mut switch_targets: Vec<(i128, BlockId)> = Vec::with_capacity(branches.len());
        let mut arm_ends: Vec<(BlockId, Operand, TypeId)> = Vec::new();
        let mut inferred_res_ty: Option<TypeId> = expected_ty;

        for (idx, binfo) in branches.iter().enumerate() {
            let arm_bb = self.new_block();
            switch_targets.push((idx as i128, arm_bb));
            self.body.cur_block = arm_bb;
            self.scopes.push(Vec::new());
            self.settle_unsent_select_values(&send_values, Some(idx))?;
            self.take_select_value(binfo);
            self.lower_arm_body(&binfo.body, false, &mut inferred_res_ty, &mut arm_ends)?;
        }

        let otherwise_bb = if let Some(def_body) = default_arm {
            let def_bb = bb_default_opt.unwrap();
            self.body.cur_block = def_bb;
            self.scopes.push(Vec::new());
            self.settle_unsent_select_values(&send_values, None)?;
            self.lower_arm_body(def_body, false, &mut inferred_res_ty, &mut arm_ends)?;
            def_bb
        } else {
            let u_bb = self.new_block();
            self.body.blocks[u_bb.0 as usize].terminator = Terminator::Unreachable;
            self.body.terminated[u_bb.0 as usize] = true;
            u_bb
        };

        self.body.blocks[bb_switch.0 as usize].terminator = Terminator::SwitchInt {
            discr: Operand::Copy(Place::new(winner_local)),
            targets: switch_targets,
            otherwise: otherwise_bb,
        };
        self.body.terminated[bb_switch.0 as usize] = true;
        self.join_arms(arm_ends, inferred_res_ty, false)
    }

    /// Prepares one receive or send arm of `@select`: a reference to its channel, the
    /// channel's `@select` protocol methods, and the slot the value passes through (an
    /// uninitialized slot to receive into, or the value to send).
    fn lower_select_branch(&mut self, arm: &SelectArm) -> Result<SelectBranchLower, String> {
        let (channel, dir) = match &arm.op {
            SelectOp::Recv { source, .. } => (source, "recv"),
            SelectOp::Send { channel, .. } => (channel, "send"),
            SelectOp::Default => unreachable!(),
        };
        let (recv_place, recv_ty) = self.lower_place(channel, false)?;
        let comp_ty = if let Type::Ptr { pointee, .. } =
            self.compiler.program.types[recv_ty.0 as usize]
        {
            pointee
        } else {
            recv_ty
        };
        let target_place = if recv_ty == comp_ty {
            recv_place
        } else {
            let mut dp = recv_place;
            dp.projections.push(Projection::Deref);
            dp
        };
        let ch_ref_ty = self.compiler.intern_type(Type::Ptr {
            mutable: false,
            pointee: comp_ty,
        });
        let ch_ref_local = self.alloc_temp(ch_ref_ty);
        self.emit(Statement::Assign(
            Place::new(ch_ref_local),
            Rvalue::Ref {
                mutable: false,
                place: target_place,
            },
        ));

        let Some(comp) = self.compiler.composites.get(&comp_ty).cloned() else {
            return Err(format!(
                "Type '{}' in '@select' does not implement the '@select' {dir} protocol",
                self.compiler.type_display_name(comp_ty)
            ));
        };
        let method = |name: &str| {
            comp.method_fn_ids.get(name).copied().ok_or_else(|| {
                format!("Type '{}' has no '{name}' method for '@select'", comp.name)
            })
        };
        let fast_fn = method(&format!("select_fast_{dir}"))?;
        let reg_fn = method(&format!("select_register_{dir}"))?;
        let unreg_fn = method("select_unregister")?;
        let fast_sig = &self.compiler.func_sigs[&fast_fn].0;
        let Type::Ptr {
            pointee: elem_ty, ..
        } = self.compiler.program.types[fast_sig[1].0 as usize]
        else {
            return Err(format!(
                "Invalid 'select_fast_{dir}' signature on '{}'",
                comp.name
            ));
        };

        let mut branch = SelectBranchLower {
            is_send: false,
            bind: None,
            ch_ref_local,
            elem_ty,
            slot_ptr_local: ch_ref_local,
            send_val_local: None,
            unsent: None,
            fast_fn,
            reg_fn,
            unreg_fn,
            body: arm.body.clone(),
        };
        match &arm.op {
            SelectOp::Recv { bind, .. } => {
                let uninit_ty = self.compiler.intern_uninit_type(elem_ty)?;
                let slot_local = self.alloc_temp(uninit_ty);
                self.emit(Statement::Assign(
                    Place::new(slot_local),
                    Rvalue::Use(Operand::Const(ConstValue::Void)),
                ));
                branch.slot_ptr_local = self.raw_ptr_to_local(slot_local, uninit_ty, elem_ty);
                branch.bind = bind.clone();
            }
            SelectOp::Send { value, unsent, .. } => {
                let (val_op, val_ty) = self.lower_expr(value, Some(elem_ty))?;
                let coerced_val = self.coerce_operand(val_op, val_ty, elem_ty)?;
                let val_local = self.alloc_temp(elem_ty);
                self.emit(Statement::Assign(
                    Place::new(val_local),
                    Rvalue::Use(coerced_val),
                ));
                branch.slot_ptr_local = self.raw_ptr_to_local(val_local, elem_ty, elem_ty);
                branch.is_send = true;
                branch.send_val_local = Some(val_local);
                branch.unsent = unsent.as_ref().map(|(n, h)| (n.clone(), (**h).clone()));
            }
            SelectOp::Default => unreachable!(),
        }
        Ok(branch)
    }

    /// A raw `*mut elem_ty` to `local` (of type `local_ty`), through its address.
    fn raw_ptr_to_local(&mut self, local: LocalId, local_ty: TypeId, elem_ty: TypeId) -> LocalId {
        let usize_ty = self.compiler.intern_type(Type::Int {
            signed: false,
            bits: 64,
        });
        let ref_ty = self.compiler.intern_type(Type::Ptr {
            mutable: true,
            pointee: local_ty,
        });
        let ref_local = self.alloc_temp(ref_ty);
        self.emit(Statement::Assign(
            Place::new(ref_local),
            Rvalue::Ref {
                mutable: true,
                place: Place::new(local),
            },
        ));
        let addr_local = self.alloc_temp(usize_ty);
        self.emit(Statement::Assign(
            Place::new(addr_local),
            Rvalue::Cast(Operand::Copy(Place::new(ref_local)), usize_ty),
        ));
        let raw_ptr_ty = self.compiler.intern_raw_ptr_type(true, elem_ty);
        let ptr_local = self.alloc_temp(raw_ptr_ty);
        self.emit(Statement::Assign(
            Place::new(ptr_local),
            Rvalue::Cast(Operand::Copy(Place::new(addr_local)), raw_ptr_ty),
        ));
        ptr_local
    }

    /// A type of `std::sync` (or, failing that, visible from the current module).
    fn resolve_sync_type(&mut self, name: &str) -> Result<TypeId, String> {
        let te = TypeExpr::Named(vec![name.to_string()]);
        self.compiler
            .resolve_type_expr("std::sync", None, &HashMap::default(), &te)
            .or_else(|_| {
                self.compiler
                    .resolve_type_expr(&self.mod_path, None, &self.comptime_env, &te)
            })
    }

    /// Stages 2-4 of `@select` when no arm is ready and there is no `default`: registers a
    /// `WaitNode` with every channel, parks on a `Waiter` until one fires (storing its index in
    /// `winner_local`), and unregisters from every channel.
    fn emit_select_wait(
        &mut self,
        branches: &[SelectBranchLower],
        winner_local: LocalId,
    ) -> Result<(), String> {
        let waiter_ty = self.resolve_sync_type("Waiter")?;
        let wait_node_ty = self.resolve_sync_type("WaitNode")?;
        let waiter_new_fn = self.compiler.composites[&waiter_ty].method_fn_ids["new"];
        let waiter_park_fn = self.compiler.composites[&waiter_ty].method_fn_ids["park"];
        let node_new_fn = self.compiler.composites[&wait_node_ty].method_fn_ids["new"];
        let void_ty = self.compiler.intern_type(Type::Void);
        let bool_ty = self.compiler.intern_type(Type::Bool);
        let i32_ty = self.compiler.intern_type(Type::Int {
            signed: true,
            bits: 32,
        });
        let usize_ty = self.compiler.intern_type(Type::Int {
            signed: false,
            bits: 64,
        });

        // Stage 2: Register
        let waiter_local = self.emit_call_to(waiter_new_fn, Vec::new(), waiter_ty);
        let waiter_ref_ty = self.compiler.intern_type(Type::Ptr {
            mutable: false,
            pointee: waiter_ty,
        });
        let raw_waiter_ptr_ty = self.compiler.intern_raw_ptr_type(false, waiter_ty);
        let waiter_raw_tmp = self.alloc_temp(raw_waiter_ptr_ty);
        self.emit(Statement::Assign(
            Place::new(waiter_raw_tmp),
            Rvalue::Ref {
                mutable: false,
                place: Place::new(waiter_local),
            },
        ));
        let waiter_addr_tmp = self.alloc_temp(usize_ty);
        self.emit(Statement::Assign(
            Place::new(waiter_addr_tmp),
            Rvalue::Cast(Operand::Copy(Place::new(waiter_raw_tmp)), usize_ty),
        ));
        let waiter_ptr_local = self.alloc_temp(raw_waiter_ptr_ty);
        self.emit(Statement::Assign(
            Place::new(waiter_ptr_local),
            Rvalue::Cast(
                Operand::Copy(Place::new(waiter_addr_tmp)),
                raw_waiter_ptr_ty,
            ),
        ));

        let mut node_locals = Vec::with_capacity(branches.len());
        let mut node_ptr_locals = Vec::with_capacity(branches.len());
        for _ in 0..branches.len() {
            let n_loc = self.emit_call_to(node_new_fn, Vec::new(), wait_node_ty);
            node_ptr_locals.push(self.raw_ptr_to_local(n_loc, wait_node_ty, wait_node_ty));
            node_locals.push(n_loc);
        }

        for (idx, binfo) in branches.iter().enumerate() {
            let branch_i32_local = self.alloc_temp(i32_ty);
            self.emit(Statement::Assign(
                Place::new(branch_i32_local),
                Rvalue::Use(Operand::Const(ConstValue::I64(idx as i128))),
            ));
            let _claimed = self.emit_call_to(
                binfo.reg_fn,
                vec![
                    Operand::Copy(Place::new(binfo.ch_ref_local)),
                    Operand::Copy(Place::new(node_ptr_locals[idx])),
                    Operand::Copy(Place::new(waiter_ptr_local)),
                    Operand::Copy(Place::new(branch_i32_local)),
                    Operand::Copy(Place::new(binfo.slot_ptr_local)),
                ],
                bool_ty,
            );
        }

        // Stage 3: Park
        let park_ref_local = self.alloc_temp(waiter_ref_ty);
        self.emit(Statement::Assign(
            Place::new(park_ref_local),
            Rvalue::Ref {
                mutable: false,
                place: Place::new(waiter_local),
            },
        ));
        let parked_winner = self.emit_call_to(
            waiter_park_fn,
            vec![Operand::Copy(Place::new(park_ref_local))],
            i32_ty,
        );
        self.emit(Statement::Assign(
            Place::new(winner_local),
            Rvalue::Use(Operand::Copy(Place::new(parked_winner))),
        ));

        // Stage 4: Unregister
        for (idx, binfo) in branches.iter().enumerate() {
            let _unreg = self.emit_call_to(
                binfo.unreg_fn,
                vec![
                    Operand::Copy(Place::new(binfo.ch_ref_local)),
                    Operand::Copy(Place::new(node_ptr_locals[idx])),
                ],
                void_ty,
            );
        }
        let after_waiter_drop = self.new_block();
        self.terminate(Terminator::Drop {
            place: Place::new(waiter_local),
            target: after_waiter_drop,
        });
        self.body.cur_block = after_waiter_drop;
        self.emit(Statement::StorageDead(waiter_local));
        for n_loc in node_locals {
            self.emit(Statement::StorageDead(n_loc));
        }
        Ok(())
    }

    /// At the start of the winning arm: a send arm's value now belongs to the channel; a
    /// receive arm's value is moved out of its slot into its binding (or dropped).
    fn take_select_value(&mut self, binfo: &SelectBranchLower) {
        let ch_ref_ty = self.body.locals[binfo.ch_ref_local.0 as usize];
        if binfo.is_send {
            if let Some(val_local) = binfo.send_val_local {
                let void_ty = self.compiler.intern_type(Type::Void);
                let consume_fn =
                    self.get_or_create_select_consume_send(ch_ref_ty, binfo.elem_ty);
                let _ = self.emit_call_to(
                    consume_fn,
                    vec![
                        Operand::Copy(Place::new(binfo.ch_ref_local)),
                        Operand::Move(Place::new(val_local)),
                    ],
                    void_ty,
                );
            }
            return;
        }
        let slot_ptr_ty = self.body.locals[binfo.slot_ptr_local.0 as usize];
        let take_fn =
            self.get_or_create_select_take_recv(ch_ref_ty, slot_ptr_ty, binfo.elem_ty);
        let recv_val_local = self.emit_call_to(
            take_fn,
            vec![
                Operand::Copy(Place::new(binfo.ch_ref_local)),
                Operand::Copy(Place::new(binfo.slot_ptr_local)),
            ],
            binfo.elem_ty,
        );
        if let Some(b_name) = &binfo.bind {
            self.scopes.last_mut().unwrap().push(ScopeVar {
                name: b_name.clone(),
                local: recv_val_local,
                ty: binfo.elem_ty,
                opaque_bound: None,
                mutable: false,
            });
        } else if !self.is_copy_type(binfo.elem_ty) {
            let drop_next = self.new_block();
            self.terminate(Terminator::Drop {
                place: Place::new(recv_val_local),
                target: drop_next,
            });
            self.body.cur_block = drop_next;
            self.emit(Statement::StorageDead(recv_val_local));
        }
    }

    fn get_or_create_select_consume_send(&mut self, ch_ref_ty: TypeId, elem_ty: TypeId) -> FuncId {
        let name = format!("__select_consume_send_{}_{}", ch_ref_ty.0, elem_ty.0);
        if let Some(f) = self
            .compiler
            .program
            .functions
            .iter()
            .find(|f| f.debug_name.as_deref() == Some(name.as_str()))
        {
            return f.id;
        }
        let void_ty = self.compiler.intern_type(Type::Void);
        let fn_id = FuncId(
            (self.compiler.program.functions.len() + self.compiler.program.externs.len()) as u32,
        );
        self.compiler
            .func_sigs
            .insert(fn_id, (vec![ch_ref_ty, elem_ty], void_ty));
        let block = BasicBlock {
            statements: vec![
                Statement::Assign(
                    Place::new(LocalId(3)),
                    Rvalue::Use(Operand::Move(Place::new(LocalId(2)))),
                ),
                Statement::StorageDead(LocalId(3)),
                Statement::Assign(
                    Place::new(LocalId(0)),
                    Rvalue::Use(Operand::Const(ConstValue::Void)),
                ),
            ],
            terminator: Terminator::Return,
        };
        self.compiler.program.functions.push(Function {
            id: fn_id,
            debug_name: Some(name),
            param_names: vec!["ch".to_string(), "val".to_string()],
            local_names: Vec::new(),
            export: None,
            linear_self: None,
            linear_owner: false,
            ret_borrows: Some(Vec::new()),
            param_borrows: Some(vec![(LocalId(1), LocalId(2))]),
            arg_count: 2,
            locals: vec![void_ty, ch_ref_ty, elem_ty, elem_ty],
            blocks: vec![block],
        });
        fn_id
    }

    fn get_or_create_select_take_recv(
        &mut self,
        ch_ref_ty: TypeId,
        slot_ptr_ty: TypeId,
        elem_ty: TypeId,
    ) -> FuncId {
        let name = format!(
            "__select_take_recv_{}_{}_{}",
            ch_ref_ty.0, slot_ptr_ty.0, elem_ty.0
        );
        if let Some(f) = self
            .compiler
            .program
            .functions
            .iter()
            .find(|f| f.debug_name.as_deref() == Some(name.as_str()))
        {
            return f.id;
        }
        let fn_id = FuncId(
            (self.compiler.program.functions.len() + self.compiler.program.externs.len()) as u32,
        );
        self.compiler
            .func_sigs
            .insert(fn_id, (vec![ch_ref_ty, slot_ptr_ty], elem_ty));
        let deref_place = Place {
            local: LocalId(2),
            projections: vec![Projection::Deref],
        };
        let deref_op = if self.is_copy_type(elem_ty) {
            Operand::Copy(deref_place)
        } else {
            Operand::Move(deref_place)
        };
        let block = BasicBlock {
            statements: vec![Statement::Assign(
                Place::new(LocalId(0)),
                Rvalue::Use(deref_op),
            )],
            terminator: Terminator::Return,
        };
        self.compiler.program.functions.push(Function {
            id: fn_id,
            debug_name: Some(name),
            param_names: vec!["ch".to_string(), "slot".to_string()],
            local_names: Vec::new(),
            export: None,
            linear_self: None,
            linear_owner: false,
            ret_borrows: Some(vec![LocalId(1).contents()]),
            param_borrows: Some(Vec::new()),
            arg_count: 2,
            locals: vec![elem_ty, ch_ref_ty, slot_ptr_ty],
            blocks: vec![block],
        });
        fn_id
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

    /// Binds a `match` arm's variant payload at `payload_place`: by copy/move, or by reference for
    /// `ref` / `ref mut`. Returns the binding's local and type.
    fn bind_variant_payload(
        &mut self,
        mode: BindMode,
        payload_place: Place,
        payload_ty: TypeId,
    ) -> Result<(LocalId, TypeId), String> {
        self.check_pat_bind_place(mode, &payload_place, payload_ty)?;
        if let BindMode::Ref { mutable } = mode {
            let ref_ty = self.compiler.intern_type(Type::Ptr {
                mutable,
                pointee: payload_ty,
            });
            let var_local = self.alloc_temp(ref_ty);
            self.emit(Statement::StorageLive(var_local));
            self.emit(Statement::Assign(
                Place::new(var_local),
                Rvalue::Ref {
                    mutable,
                    place: payload_place,
                },
            ));
            return Ok((var_local, ref_ty));
        }
        let var_local = self.alloc_temp(payload_ty);
        self.emit(Statement::StorageLive(var_local));
        let op = if self.is_copy_type(payload_ty) {
            Operand::Copy(payload_place)
        } else {
            Operand::Move(payload_place)
        };
        self.emit(Statement::Assign(Place::new(var_local), Rvalue::Use(op)));
        Ok((var_local, payload_ty))
    }

    fn check_pat_bind_place(
        &self,
        mode: BindMode,
        place: &Place,
        ty: TypeId,
    ) -> Result<(), String> {
        if let BindMode::Ref { mutable } = mode {
            if let Some(cell_field) = self.place_traverses_cell(place) {
                return Err(format!(
                    "Cannot take a safe reference ('&' or '&mut') to 'cell' field '{cell_field}'; read or copy the field by value, or use '&raw const' / '&raw mut'"
                ));
            }
            if mutable && self.place_traverses_immutable_ptr(place) {
                return Err(format!(
                    "Cannot take mutable reference '&mut' to '{place}' through an immutable reference or pointer"
                ));
            }
        } else if !self.is_copy_type(ty) && self.place_traverses_safe_ref(place) {
            return Err(format!(
                "Cannot move out of dereferenced safe reference '{place}'"
            ));
        }
        Ok(())
    }

    pub(super) fn lower_match(
        &mut self,
        scrutinee: &Expr,
        arms: &[(MatchPat, Expr)],
        expected_ty: Option<TypeId>,
        is_stmt: bool,
    ) -> Result<(Operand, TypeId), String> {
        // `ref` / `ref mut` bindings borrow from the matched value, so match on a reference to it
        // instead of moving it into the match.
        let ref_mode = arms
            .iter()
            .fold(None, |acc: Option<bool>, (pat, _)| match (acc, pat.ref_bind_mode()) {
                (a, None) => a,
                (Some(m1), Some(m2)) => Some(m1 || m2),
                (None, Some(m)) => Some(m),
            });
        let is_place_scrutinee = matches!(
            scrutinee,
            Expr::Path(_)
                | Expr::Field { .. }
                | Expr::TupleIndex { .. }
                | Expr::Index { .. }
                | Expr::Deref(_)
        );
        let borrowed_scrutinee;
        let scrutinee = match (ref_mode, scrutinee) {
            (Some(_), Expr::Ref { .. }) => scrutinee,
            (Some(mutable), other) if is_place_scrutinee => {
                borrowed_scrutinee = Expr::Ref {
                    mutable,
                    expr: Box::new(other.clone()),
                };
                &borrowed_scrutinee
            }
            (None, Expr::Deref(_)) if self.unsafe_depth == 0 => {
                borrowed_scrutinee = Expr::Ref {
                    mutable: false,
                    expr: Box::new(scrutinee.clone()),
                };
                &borrowed_scrutinee
            }
            _ => scrutinee,
        };
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
        // A scrutinee moved into the match is a hidden variable of the enclosing scope, so a
        // payload that no arm moves out is dropped at scope exit (or, if linear, rejected).
        let scrut_owned = scrut_place.projections.is_empty() && !self.is_copy_type(scrut_ty);
        if scrut_owned && let Some(scope) = self.scopes.last_mut() {
            scope.push(ScopeVar {
                name: "match scrutinee".to_string(),
                local: raw_scrut_local,
                ty: scrut_ty,
                opaque_bound: None,
                mutable: false,
            });
        }

        let kind = if let Some(info) = self.compiler.errors.get(&scrut_ty).cloned() {
            MatchKind::Error(info)
        } else if let Some(info) = self.compiler.unions.get(&scrut_ty).cloned() {
            MatchKind::Union(info)
        } else if let Some((name, variants)) = self.compiler.enums.get(&scrut_ty).cloned() {
            MatchKind::Enum(name, variants)
        } else {
            MatchKind::Int
        };

        if !self.can_use_flat_switch(&kind, scrut_ty, arms) {
            return self.lower_general_match(
                &kind,
                raw_scrut_local,
                &scrut_place,
                scrut_ty,
                scrut_owned,
                arms,
                expected_ty,
                is_stmt,
            );
        }

        let discr = if matches!(kind, MatchKind::Error(_) | MatchKind::Union(_)) {
            let Type::Union { tag: tag_ty, .. } =
                self.compiler.program.types[scrut_ty.0 as usize]
            else {
                unreachable!()
            };
            let discr_local = self.alloc_temp(tag_ty);
            self.emit(Statement::Assign(
                Place::new(discr_local),
                Rvalue::Discriminant(scrut_place.clone()),
            ));
            Operand::Copy(Place::new(discr_local))
        } else {
            Operand::Copy(scrut_place.clone())
        };
        let entry_bb = self.body.cur_block;

        let mut st = MatchArms {
            covered: vec![false; kind.variant_count()],
            has_wildcard: false,
            targets: Vec::new(),
            wildcard_bb: None,
        };
        let mut arm_ends: Vec<(BlockId, Operand, TypeId)> = Vec::new();
        let mut inferred_res_ty: Option<TypeId> = expected_ty;
        for (raw_pat, arm_expr) in arms {
            let pat = self.normalize_match_pat(&kind, raw_pat)?;
            let arm_bb = self.new_block();
            let covered_before = st.covered.clone();
            let binding = match &pat {
                MatchPat::Wildcard => {
                    st.wildcard(arm_bb);
                    None
                }
                MatchPat::CatchAllBind { mode, name } => {
                    st.wildcard(arm_bb);
                    if name != "_" {
                        self.body.cur_block = arm_bb;
                        let (bind_local, bind_ty) =
                            self.bind_variant_payload(*mode, scrut_place.clone(), scrut_ty)?;
                        Some((name.clone(), bind_local, bind_ty))
                    } else {
                        None
                    }
                }
                MatchPat::Variant { path, payload } => {
                    let b_opt = Self::simple_payload_bind(payload);
                    self.match_variant_pattern(
                        &kind,
                        path,
                        &b_opt,
                        arm_bb,
                        &scrut_place,
                        scrut_ty,
                        &mut st,
                    )?
                }
                MatchPat::DotVariant { name, payload } => {
                    let b_opt = Self::simple_payload_bind(payload);
                    self.match_dot_variant(
                        &kind,
                        name,
                        &b_opt,
                        arm_bb,
                        &scrut_place,
                        scrut_ty,
                        &mut st,
                    )?
                }
                MatchPat::Int(val) => match &kind {
                    MatchKind::Enum(..) | MatchKind::Int => {
                        st.targets.push((*val, arm_bb));
                        None
                    }
                    MatchKind::Union(_) => {
                        return Err(
                            "Cannot match integer literal against `union` type".to_string()
                        );
                    }
                    MatchKind::Error(_) => {
                        return Err(
                            "Cannot match integer literal against `error` type".to_string()
                        );
                    }
                },
                _ => unreachable!("handled by lower_general_match"),
            };

            self.body.cur_block = arm_bb;
            // In an arm whose variants carry only `copy` payloads there is nothing left to drop,
            // but the move checker cannot see which variant the arm holds: retire the scrutinee.
            if scrut_owned {
                let payloads_copy = (0..covered_before.len())
                    .filter(|&i| st.covered[i] && !covered_before[i])
                    .all(|i| match &kind {
                        MatchKind::Union(info) => self.is_copy_type(info.variants[i].1),
                        MatchKind::Error(info) => self.is_copy_type(info.leaves[i].payload_ty),
                        MatchKind::Enum(..) | MatchKind::Int => true,
                    });
                if payloads_copy {
                    self.emit(Statement::StorageDead(raw_scrut_local));
                }
            }
            self.scopes.push(Vec::new());
            if let Some((b_name, b_local, b_ty)) = binding {
                self.scopes.last_mut().unwrap().push(ScopeVar {
                    name: b_name,
                    local: b_local,
                    ty: b_ty,
                    opaque_bound: None,
                    mutable: false,
                });
            }
            self.lower_arm_body(arm_expr, is_stmt, &mut inferred_res_ty, &mut arm_ends)?;
        }

        if !st.has_wildcard
            && let Some(err) = kind.non_exhaustive_error(&st.covered)
        {
            return Err(err);
        }

        let otherwise_bb = st.wildcard_bb.unwrap_or_else(|| {
            let u_bb = self.new_block();
            self.body.blocks[u_bb.0 as usize].terminator = Terminator::Unreachable;
            self.body.terminated[u_bb.0 as usize] = true;
            u_bb
        });
        let mut dedup_targets = Vec::with_capacity(st.targets.len());
        for (val, bb) in st.targets {
            if !dedup_targets.iter().any(|(v, _)| *v == val) {
                dedup_targets.push((val, bb));
            }
        }
        self.body.blocks[entry_bb.0 as usize].terminator = Terminator::SwitchInt {
            discr,
            targets: dedup_targets,
            otherwise: otherwise_bb,
        };
        self.body.terminated[entry_bb.0 as usize] = true;
        self.join_arms(arm_ends, inferred_res_ty, is_stmt)
    }

    fn simple_payload_bind(payload: &Option<Box<MatchPat>>) -> Option<(BindMode, String)> {
        match payload.as_deref() {
            None => None,
            Some(MatchPat::Wildcard) => Some((BindMode::Move, "_".to_string())),
            Some(MatchPat::CatchAllBind { mode, name }) => Some((*mode, name.clone())),
            _ => None,
        }
    }

    fn can_use_flat_switch(
        &mut self,
        kind: &MatchKind,
        scrut_ty: TypeId,
        arms: &[(MatchPat, Expr)],
    ) -> bool {
        match kind {
            MatchKind::Enum(..) | MatchKind::Union(..) | MatchKind::Error(..) => {}
            MatchKind::Int => {
                if self.compiler.distinct_types.contains_key(&scrut_ty) {
                    return false;
                }
                let Type::Int { signed, bits } =
                    self.compiler.program.types[scrut_ty.0 as usize]
                else {
                    return false;
                };
                if bits > 128 {
                    return false;
                }
                let has_catchall = arms.iter().any(|(p, _)| match p {
                    MatchPat::Wildcard => true,
                    MatchPat::CatchAllBind { name, .. } => !matches!(
                        self.compiler
                            .resolve_path(&self.mod_path, std::slice::from_ref(name)),
                        Ok(ResolvedItem::Const(..))
                    ),
                    _ => false,
                });
                if !has_catchall && bits <= 16 {
                    return false;
                }
                return arms.iter().all(|(p, _)| match p {
                    MatchPat::Wildcard => true,
                    MatchPat::CatchAllBind { name, .. } => !matches!(
                        self.compiler
                            .resolve_path(&self.mod_path, std::slice::from_ref(name)),
                        Ok(ResolvedItem::Const(..))
                    ),
                    MatchPat::Int(n) => crate::wide::Wide::from_i128(*n).fits(bits, signed),
                    _ => false,
                });
            }
        }
        arms.iter().all(|(raw_pat, _)| {
            let Ok(pat) = self.normalize_match_pat(kind, raw_pat) else {
                return true;
            };
            match pat {
                MatchPat::Wildcard | MatchPat::CatchAllBind { .. } | MatchPat::Int(_) => true,
                MatchPat::Variant { path, payload } => {
                    if path.len() >= 2 && payload.is_none() {
                        let is_known_variant = match kind {
                            MatchKind::Enum(_, vs) => {
                                let vname = path.last().unwrap();
                                vs.iter().any(|(vn, _)| vn == vname)
                            }
                            MatchKind::Union(u) => {
                                let vname = path.last().unwrap();
                                u.variants.iter().any(|(vn, _)| vn == vname)
                            }
                            MatchKind::Error(_) => true,
                            MatchKind::Int => false,
                        };
                        if !is_known_variant {
                            return false;
                        }
                    }
                    matches!(
                        payload.as_deref(),
                        None | Some(MatchPat::Wildcard | MatchPat::CatchAllBind { .. })
                    )
                }
                MatchPat::DotVariant { payload, .. } => matches!(
                    payload.as_deref(),
                    None | Some(MatchPat::Wildcard | MatchPat::CatchAllBind { .. })
                ),
                _ => false,
            }
        })
    }

    /// `{ x: 1, y: 2 }`: a literal of the expected struct, opaque, or overlay type (looking
    /// through `?T` and the ok side of `E!T`); with none expected, a value of the structural
    /// anonymous struct of its fields.
    fn lower_record_lit(
        &mut self,
        fields: &[(String, Expr)],
        expected_ty: Option<TypeId>,
    ) -> Result<(Operand, TypeId), String> {
        if let Some(exp) = expected_ty {
            let mut candidates = vec![exp];
            if let Some(inner) = self.compiler.as_optional_type(exp) {
                candidates.push(inner);
            }
            if let Some(&res) = self.compiler.results.get(&exp) {
                candidates.push(res.ok_ty);
                if let Some(inner) = self.compiler.as_optional_type(res.ok_ty) {
                    candidates.push(inner);
                }
            }
            if let Some(ty) = candidates.into_iter().find(|t| {
                self.compiler.composites.contains_key(t) || self.compiler.overlays.contains_key(t)
            }) {
                return self.lower_struct_lit_of(ty, None, fields);
            }
        }
        let mut ops = Vec::with_capacity(fields.len());
        let mut field_tys = Vec::with_capacity(fields.len());
        for (name, value) in fields {
            if field_tys.iter().any(|(n, _): &(String, TypeId)| n == name) {
                return Err(format!("Duplicate field '{name}' in struct literal"));
            }
            let (op, ty) = self.lower_expr(value, None)?;
            ops.push(op);
            field_tys.push((name.clone(), ty));
        }
        let ty = self
            .compiler
            .structural_struct(&self.mod_path, false, field_tys, "struct literal")?;
        let tmp = self.alloc_temp(ty);
        self.emit(Statement::Assign(Place::new(tmp), Rvalue::Aggregate(ty, ops)));
        Ok((self.local_operand(tmp, ty), ty))
    }

    /// `.Name` / `.Name(payload)`: the variant `Name` of the expected enum, union, or error
    /// type, looking through `?T` and both sides of `E!T`.
    fn lower_dot_variant(
        &mut self,
        name: &str,
        payload: Option<&Expr>,
        expected_ty: Option<TypeId>,
    ) -> Result<(Operand, TypeId), String> {
        let Some(exp) = expected_ty else {
            return Err(format!(
                "'.{name}' needs a known type; write 'Type::{name}' where none is expected"
            ));
        };
        let mut candidates = vec![exp];
        if let Some(inner) = self.compiler.as_optional_type(exp) {
            candidates.push(inner);
        }
        let ty_has_variant = |c: &Compiler, ty: TypeId| {
            c.enums
                .get(&ty)
                .is_some_and(|(_, vs)| vs.iter().any(|(vn, _)| vn == name))
                || c.unions
                    .get(&ty)
                    .is_some_and(|u| u.variants.iter().any(|(vn, _)| vn == name))
                || c.errors
                    .get(&ty)
                    .is_some_and(|e| e.leaves.iter().any(|l| l.key.variant_name == name))
        };
        if let Some(&res) = self.compiler.results.get(&exp) {
            let ok_cand = self
                .compiler
                .as_optional_type(res.ok_ty)
                .filter(|&inner| ty_has_variant(self.compiler, inner))
                .unwrap_or(res.ok_ty);
            if ty_has_variant(self.compiler, ok_cand) && ty_has_variant(self.compiler, res.err_ty) {
                return Err(format!(
                    "Variant '.{name}' is ambiguous in '{}': both '{}' and '{}' have a variant '{name}'; qualify with the type name",
                    self.compiler.type_display_name(exp),
                    self.compiler.type_display_name(ok_cand),
                    self.compiler.type_display_name(res.err_ty),
                ));
            }
            candidates.push(res.ok_ty);
            if let Some(inner) = self.compiler.as_optional_type(res.ok_ty) {
                candidates.push(inner);
            }
            candidates.push(res.err_ty);
        }
        let args: Vec<Expr> = payload.into_iter().cloned().collect();
        for ty in candidates {
            if let Some((_, variants)) = self.compiler.enums.get(&ty)
                && let Some(&(_, value)) = variants.iter().find(|(vn, _)| vn == name)
            {
                if payload.is_some() {
                    return Err(format!("Enum variant '.{name}' takes no payload"));
                }
                return Ok((Operand::Const(ConstValue::I64(value)), ty));
            }
            let has_variant = self
                .compiler
                .unions
                .get(&ty)
                .is_some_and(|u| u.variants.iter().any(|(vn, _)| vn == name))
                || self
                    .compiler
                    .errors
                    .get(&ty)
                    .is_some_and(|e| e.leaves.iter().any(|l| l.key.variant_name == name));
            if has_variant {
                return self.lower_static_type_call(ty, name, None, &args);
            }
        }
        Err(format!(
            "'.{name}' is not a variant of '{}'",
            self.compiler.type_display_name(exp)
        ))
    }

    /// Checks an arm pattern against the scrutinee kind. A bare name always binds, so one
    /// spelled like an enum or union variant (`Red`, `Ping(n)`) is an error asking for the
    /// variant form `.Red` / `.Ping(n)`; on an `error`, a bare type name (`IoError`) is the
    /// pattern for that embedded error.
    /// A comptime name for the type `te`, so that a path can start with it as with a type
    /// parameter: `Maybe[i32]::None` is lowered as `<name>::None`.
    pub(super) fn name_type_for_paths(&mut self, te: &TypeExpr) -> Result<String, String> {
        let ty = self.compiler.resolve_type_expr(&self.mod_path, self.owner_ty, &self.comptime_env, te)?;
        let name = format!("__type_{}", ty.0);
        self.comptime_env.insert(name.clone(), ComptimeVal::Type(ty));
        Ok(name)
    }

    /// `pat` with each `TypeQualified` pattern written as the path it stands for, through a name
    /// from `name_type_for_paths`.
    fn resolve_type_qualified(&mut self, pat: &MatchPat) -> Result<MatchPat, String> {
        let boxed = |c: &mut Self, p: &Option<Box<MatchPat>>| -> Result<Option<Box<MatchPat>>, String> {
            p.as_deref().map(|p| c.resolve_type_qualified(p).map(Box::new)).transpose()
        };
        Ok(match pat {
            MatchPat::TypeQualified { ty, pat } => {
                let name = self.name_type_for_paths(ty)?;
                match self.resolve_type_qualified(pat)? {
                    MatchPat::Variant { path, payload } => MatchPat::Variant {
                        path: std::iter::once(name).chain(path).collect(),
                        payload,
                    },
                    MatchPat::Struct { path, fields, rest } => MatchPat::Struct {
                        path: Some(
                            std::iter::once(name).chain(path.unwrap_or_default()).collect(),
                        ),
                        fields,
                        rest,
                    },
                    other => other,
                }
            }
            MatchPat::Variant { path, payload } => MatchPat::Variant {
                path: path.clone(),
                payload: boxed(self, payload)?,
            },
            MatchPat::DotVariant { name, payload } => MatchPat::DotVariant {
                name: name.clone(),
                payload: boxed(self, payload)?,
            },
            MatchPat::Struct { path, fields, rest } => MatchPat::Struct {
                path: path.clone(),
                fields: fields
                    .iter()
                    .map(|(n, p)| Ok((n.clone(), self.resolve_type_qualified(p)?)))
                    .collect::<Result<_, String>>()?,
                rest: *rest,
            },
            MatchPat::Seq { elems, rest, bracketed } => MatchPat::Seq {
                elems: elems
                    .iter()
                    .map(|p| self.resolve_type_qualified(p))
                    .collect::<Result<_, String>>()?,
                rest: *rest,
                bracketed: *bracketed,
            },
            MatchPat::Or(alts) => MatchPat::Or(
                alts.iter().map(|p| self.resolve_type_qualified(p)).collect::<Result<_, String>>()?,
            ),
            other => other.clone(),
        })
    }

    fn normalize_match_pat(
        &mut self,
        kind: &MatchKind,
        pat: &MatchPat,
    ) -> Result<MatchPat, String> {
        let resolved;
        let pat = if pat.has_type_qualified() {
            resolved = self.resolve_type_qualified(pat)?;
            &resolved
        } else {
            pat
        };
        // A variant named through a type is one of the matched value's own.
        if let MatchPat::Variant { path, .. } = pat
            && path.len() >= 2
            && let Some(named) = self.resolve_match_type_path(&path[..path.len() - 1])
        {
            let same = match kind {
                MatchKind::Union(info) => self.compiler.unions.get(&named) == Some(info),
                MatchKind::Enum(name, variants) => self
                    .compiler
                    .enums
                    .get(&named)
                    .is_some_and(|(n, vs)| n == name && vs == variants),
                _ => true,
            };
            if !same {
                return Err(format!(
                    "Pattern '{}' names a variant of '{}', which is not the type of the value matched",
                    path.join("::"),
                    self.compiler.type_display_name(named)
                ));
            }
        }
        let variant_names: Vec<String> = match kind {
            MatchKind::Enum(_, variants) => variants.iter().map(|(vn, _)| vn.clone()).collect(),
            MatchKind::Union(info) => info.variants.iter().map(|(vn, _)| vn.clone()).collect(),
            MatchKind::Error(info) => {
                let leaves: Vec<String> = info
                    .leaves
                    .iter()
                    .map(|l| l.key.variant_name.clone())
                    .collect();
                leaves
                    .into_iter()
                    .filter(|vn| {
                        !self
                            .resolve_match_type_path(std::slice::from_ref(vn))
                            .is_some_and(|t| self.compiler.errors.contains_key(&t))
                    })
                    .collect()
            }
            _ => Vec::new(),
        };
        match pat {
            MatchPat::CatchAllBind { name, .. } if variant_names.contains(name) => Err(format!(
                "Pattern '{name}' would bind the value, but '{name}' is a variant; write '.{name}' to match it"
            )),
            MatchPat::Variant {
                path,
                payload: Some(inner),
            } if path.len() == 1 && variant_names.contains(&path[0]) => {
                let b = match inner.as_ref() {
                    MatchPat::CatchAllBind { name, .. } => name.as_str(),
                    MatchPat::Wildcard => "_",
                    _ => "...",
                };
                Err(format!(
                    "Write '.{}({b})' to match variant '{}' of the scrutinee's type",
                    path[0], path[0]
                ))
            }
            MatchPat::CatchAllBind {
                mode: BindMode::Default,
                name,
            } if matches!(
                self.compiler
                    .resolve_path(&self.mod_path, std::slice::from_ref(name)),
                Ok(ResolvedItem::Const(..))
            ) =>
            {
                Ok(MatchPat::Variant {
                    path: vec![name.clone()],
                    payload: None,
                })
            }
            MatchPat::CatchAllBind { name, .. }
                if matches!(kind, MatchKind::Error(_))
                    && self
                        .resolve_match_type_path(std::slice::from_ref(name))
                        .is_some_and(|t| self.compiler.errors.contains_key(&t)) =>
            {
                Ok(MatchPat::Variant {
                    path: vec![name.clone()],
                    payload: None,
                })
            }
            MatchPat::Or(alts) => {
                let mut out = Vec::with_capacity(alts.len());
                for a in alts {
                    out.push(self.normalize_match_pat(kind, a)?);
                }
                Ok(MatchPat::Or(out))
            }
            other => Ok(other.clone()),
        }
    }

    /// The switch targets of a variant pattern (`E::V`, `U::V(x)`, `IoError::Timeout(t)`, an
    /// embedded error subtype `IoError(e)`) arm leading to `arm_bb`, and the binding it makes.
    #[allow(clippy::too_many_arguments)]
    fn match_variant_pattern(
        &mut self,
        kind: &MatchKind,
        path: &[String],
        binding: &Option<(BindMode, String)>,
        arm_bb: BlockId,
        scrut_place: &Place,
        scrut_ty: TypeId,
        st: &mut MatchArms,
    ) -> Result<Option<(String, LocalId, TypeId)>, String> {
        let vname = path.last().unwrap();
        match kind {
            MatchKind::Int => Err(format!(
                "Cannot match variant pattern '{}' against non-enum/union/error type {}",
                path.join("::"),
                self.compiler.type_display_name(scrut_ty)
            )),
            MatchKind::Enum(enum_name, variants) => {
                if binding.is_some() {
                    return Err("Enum variant cannot bind a payload in `match`".to_string());
                }
                let Some((v_idx, (_, v_val))) =
                    variants.iter().enumerate().find(|(_, (vn, _))| vn == vname)
                else {
                    return Err(format!("Enum '{}' has no variant '{}'", enum_name, vname));
                };
                st.covered[v_idx] = true;
                st.targets.push((*v_val, arm_bb));
                Ok(None)
            }
            MatchKind::Union(union_info) => {
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
                st.covered[v_idx] = true;
                st.targets.push((v_idx as i128, arm_bb));
                let Some((mode, b_name)) = binding else {
                    return Ok(None);
                };
                if b_name == "_" {
                    return Ok(None);
                }
                self.body.cur_block = arm_bb;
                let mut p_place = scrut_place.clone();
                p_place.projections.push(Projection::Variant(v_idx as u32));
                let (var_local, var_ty) =
                    self.bind_variant_payload(*mode, p_place, *payload_ty)?;
                Ok(Some((b_name.clone(), var_local, var_ty)))
            }
            MatchKind::Error(err_info) => {
                let mut binding_out = None;
                // An embedded error subtype (`IoError(io_err)`) covers all of its leaves.
                if let Some(sub_ty) = self.resolve_match_type_path(path)
                    && let Some(sub_err) = self.compiler.errors.get(&sub_ty).cloned()
                {
                    if matches!(binding, Some((BindMode::Ref { .. }, _))) {
                        return Err(format!(
                            "'ref' bindings are not supported for embedded error subtype patterns ('{}(...)'); match on a reference to the error instead",
                            path.join("::")
                        ));
                    }
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
                        if st.covered[scrut_idx] {
                            continue;
                        }
                        st.covered[scrut_idx] = true;
                        if let Some((_, sub_local)) = &bind_local_opt {
                            let tramp_bb = self.new_block();
                            st.targets.push((scrut_idx as i128, tramp_bb));
                            self.body.cur_block = tramp_bb;
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
                            st.targets.push((scrut_idx as i128, arm_bb));
                        }
                    }
                    if let Some((b_name, sub_local)) = bind_local_opt {
                        binding_out = Some((b_name, sub_local, sub_ty));
                    }
                } else {
                    // A leaf: `IoError::Timeout` or `ParseError::UnexpectedToken(tok)`.
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
                    let payload_ty = scrut_leaf.payload_ty;
                    binding_out = self.match_error_leaf(
                        scrut_idx,
                        payload_ty,
                        binding,
                        arm_bb,
                        scrut_place,
                        st,
                    )?;
                }
                Ok(binding_out)
            }
        }
    }

    /// A `.Name` / `.Name(x)` arm: the variant `Name` of the scrutinee's own type (for an
    /// `error`, the one leaf of that name).
    #[allow(clippy::too_many_arguments)]
    fn match_dot_variant(
        &mut self,
        kind: &MatchKind,
        name: &str,
        binding: &Option<(BindMode, String)>,
        arm_bb: BlockId,
        scrut_place: &Place,
        scrut_ty: TypeId,
        st: &mut MatchArms,
    ) -> Result<Option<(String, LocalId, TypeId)>, String> {
        let MatchKind::Error(err_info) = kind else {
            let path = [name.to_string()];
            return self.match_variant_pattern(
                kind,
                &path,
                binding,
                arm_bb,
                scrut_place,
                scrut_ty,
                st,
            );
        };
        let found: Vec<usize> = (0..err_info.leaves.len())
            .filter(|&i| err_info.leaves[i].key.variant_name == name)
            .collect();
        match found.as_slice() {
            [] => Err(format!("Error type '{}' has no variant '{name}'", err_info.name)),
            [idx] => {
                let payload_ty = err_info.leaves[*idx].payload_ty;
                self.match_error_leaf(*idx, payload_ty, binding, arm_bb, scrut_place, st)
            }
            several => {
                let qualified: Vec<String> = several
                    .iter()
                    .map(|&i| format!("'{}::{name}'", err_info.leaves[i].key.error_name))
                    .collect();
                Err(format!(
                    "'.{name}' is ambiguous in error type '{}'; write {}",
                    err_info.name,
                    qualified.join(" or ")
                ))
            }
        }
    }

    /// Arm `arm_bb` for leaf `idx` of an `error` scrutinee, binding its payload if asked.
    fn match_error_leaf(
        &mut self,
        idx: usize,
        payload_ty: TypeId,
        binding: &Option<(BindMode, String)>,
        arm_bb: BlockId,
        scrut_place: &Place,
        st: &mut MatchArms,
    ) -> Result<Option<(String, LocalId, TypeId)>, String> {
        st.covered[idx] = true;
        st.targets.push((idx as i128, arm_bb));
        let Some((mode, b_name)) = binding.as_ref().filter(|(_, n)| n != "_") else {
            return Ok(None);
        };
        self.body.cur_block = arm_bb;
        let mut p_place = scrut_place.clone();
        p_place.projections.push(Projection::Variant(idx as u32));
        let (var_local, var_ty) = self.bind_variant_payload(*mode, p_place, payload_ty)?;
        Ok(Some((b_name.clone(), var_local, var_ty)))
    }

    #[allow(clippy::too_many_arguments)]
    fn lower_general_match(
        &mut self,
        kind: &MatchKind,
        raw_scrut_local: LocalId,
        scrut_place: &Place,
        scrut_ty: TypeId,
        scrut_owned: bool,
        arms: &[(MatchPat, Expr)],
        expected_ty: Option<TypeId>,
        is_stmt: bool,
    ) -> Result<(Operand, TypeId), String> {
        let mut arm_ends: Vec<(BlockId, Operand, TypeId)> = Vec::new();
        let mut inferred_res_ty: Option<TypeId> = expected_ty;
        let mut normalized_pats: Vec<MatchPat> = Vec::with_capacity(arms.len());
        let mut cur_test_bb = self.body.cur_block;

        for (raw_pat, arm_expr) in arms {
            let norm_pat = self.normalize_match_pat(kind, raw_pat)?;
            let branches = Self::expand_or_pat(&norm_pat);
            if branches.len() > 1 {
                let mut first_names = HashSet::default();
                branches[0].collect_bound_names(&mut first_names);
                for b in &branches[1..] {
                    let mut names = HashSet::default();
                    b.collect_bound_names(&mut names);
                    if names != first_names {
                        return Err(
                            "All alternatives of an `|` pattern must bind the same variables"
                                .to_string(),
                        );
                    }
                }
            }

            let arm_bb = self.new_block();
            let mut shared_bindings: Vec<(String, LocalId, TypeId)> = Vec::new();
            let mut single_branch_holders: Vec<(LocalId, TypeId)> = Vec::new();

            for (b_idx, branch_pat) in branches.iter().enumerate() {
                let next_branch_bb = self.new_block();
                self.body.cur_block = cur_test_bb;
                let mut actions: Vec<GenBindAction> = Vec::new();
                self.lower_pat_test(
                    scrut_place,
                    scrut_ty,
                    scrut_owned,
                    branch_pat,
                    next_branch_bb,
                    &mut actions,
                )?;

                // `self.body.cur_block` is now the success edge for `branch_pat`.
                let mut seen_names: Vec<String> = Vec::new();
                let mut branch_holders: Vec<(LocalId, TypeId)> = Vec::new();
                let mut retired_scrut = false;
                for act in actions {
                    match act {
                        GenBindAction::InitHolder {
                            holder_local,
                            src_place,
                            ty,
                        } => {
                            self.emit(Statement::StorageLive(holder_local));
                            self.emit(Statement::Assign(
                                Place::new(holder_local),
                                Rvalue::Use(Operand::Move(src_place)),
                            ));
                            branch_holders.push((holder_local, ty));
                        }
                        GenBindAction::RetireUnionCopyPayload {
                            variant_place,
                            payload_ty,
                        } => {
                            if variant_place.local == raw_scrut_local
                                && variant_place.projections.len() == 1
                                && scrut_owned
                            {
                                if !retired_scrut {
                                    self.emit(Statement::StorageDead(raw_scrut_local));
                                    retired_scrut = true;
                                }
                            } else if !matches!(
                                self.compiler.program.types[payload_ty.0 as usize],
                                Type::Void
                            ) {
                                let tmp = self.alloc_temp(payload_ty);
                                self.emit(Statement::Assign(
                                    Place::new(tmp),
                                    Rvalue::Use(Operand::Move(variant_place)),
                                ));
                            }
                        }
                        GenBindAction::RetireLocal(local) => {
                            if local == raw_scrut_local {
                                if !retired_scrut {
                                    self.emit(Statement::StorageDead(local));
                                    retired_scrut = true;
                                }
                            } else {
                                self.emit(Statement::StorageDead(local));
                            }
                        }
                        GenBindAction::BindPlace {
                            name,
                            mode,
                            place,
                            ty,
                        } => {
                            if seen_names.contains(&name) {
                                return Err(format!(
                                    "Identifier '{name}' is bound more than once in the same pattern"
                                ));
                            }
                            seen_names.push(name.clone());
                            let (b_local, b_ty) = self.bind_variant_payload(mode, place, ty)?;
                            self.record_branch_binding(
                                b_idx,
                                &name,
                                b_local,
                                b_ty,
                                &mut shared_bindings,
                            )?;
                        }
                        GenBindAction::BindPackedField {
                            name,
                            mode,
                            place,
                            struct_ty,
                            field_idx,
                            field_ty,
                        } => {
                            if seen_names.contains(&name) {
                                return Err(format!(
                                    "Identifier '{name}' is bound more than once in the same pattern"
                                ));
                            }
                            seen_names.push(name.clone());
                            if matches!(mode, BindMode::Ref { .. }) {
                                return Err(format!(
                                    "Cannot take a reference ('ref' / 'ref mut') to packed struct field in pattern on '{}'",
                                    self.compiler.type_display_name(struct_ty)
                                ));
                            }
                            let val_op = self.extract_packed_field_from_place(
                                &place, struct_ty, field_idx, field_ty,
                            )?;
                            let b_local = self.alloc_temp(field_ty);
                            self.emit(Statement::StorageLive(b_local));
                            self.emit(Statement::Assign(
                                Place::new(b_local),
                                Rvalue::Use(val_op),
                            ));
                            self.record_branch_binding(
                                b_idx,
                                &name,
                                b_local,
                                field_ty,
                                &mut shared_bindings,
                            )?;
                        }
                        GenBindAction::BindVal { name, local, ty } => {
                            if seen_names.contains(&name) {
                                return Err(format!(
                                    "Identifier '{name}' is bound more than once in the same pattern"
                                ));
                            }
                            seen_names.push(name.clone());
                            self.record_branch_binding(
                                b_idx,
                                &name,
                                local,
                                ty,
                                &mut shared_bindings,
                            )?;
                        }
                    }
                }
                if branches.len() == 1 {
                    single_branch_holders = branch_holders;
                } else {
                    for (h_local, _) in branch_holders {
                        self.emit(Statement::StorageDead(h_local));
                    }
                }
                self.terminate(Terminator::Goto { target: arm_bb });
                cur_test_bb = next_branch_bb;
            }

            normalized_pats.extend(branches);

            self.body.cur_block = arm_bb;
            self.scopes.push(Vec::new());
            for (h_local, h_ty) in single_branch_holders {
                self.scopes.last_mut().unwrap().push(ScopeVar {
                    name: "match scrutinee".to_string(),
                    local: h_local,
                    ty: h_ty,
                    opaque_bound: None,
                    mutable: false,
                });
            }
            for (b_name, b_local, b_ty) in shared_bindings {
                self.scopes.last_mut().unwrap().push(ScopeVar {
                    name: b_name,
                    local: b_local,
                    ty: b_ty,
                    opaque_bound: None,
                    mutable: false,
                });
            }
            self.lower_arm_body(arm_expr, is_stmt, &mut inferred_res_ty, &mut arm_ends)?;
        }

        if let Some(err) = self.check_general_match_exhaustive(kind, scrut_ty, &normalized_pats) {
            return Err(err);
        }

        self.body.cur_block = cur_test_bb;
        self.terminate(Terminator::Unreachable);
        self.join_arms(arm_ends, inferred_res_ty, is_stmt)
    }

    fn record_branch_binding(
        &mut self,
        branch_idx: usize,
        name: &str,
        local: LocalId,
        ty: TypeId,
        shared_bindings: &mut Vec<(String, LocalId, TypeId)>,
    ) -> Result<(), String> {
        if branch_idx == 0 {
            shared_bindings.push((name.to_string(), local, ty));
            return Ok(());
        }
        let Some((_, shared_local, shared_ty)) =
            shared_bindings.iter().find(|(n, _, _)| n == name)
        else {
            return Err(format!(
                "All alternatives of an `|` pattern must bind the same variable '{name}'"
            ));
        };
        if *shared_ty != ty {
            return Err(format!(
                "Variable '{name}' is bound with inconsistent types across `|` pattern alternatives ('{}' vs '{}')",
                self.compiler.type_display_name(*shared_ty),
                self.compiler.type_display_name(ty)
            ));
        }
        let op = if self.is_copy_type(ty) {
            Operand::Copy(Place::new(local))
        } else {
            Operand::Move(Place::new(local))
        };
        self.emit(Statement::StorageLive(*shared_local));
        self.emit(Statement::Assign(Place::new(*shared_local), Rvalue::Use(op)));
        Ok(())
    }

    fn expand_or_pat(pat: &MatchPat) -> Vec<MatchPat> {
        match pat {
            MatchPat::Or(alts) => alts.iter().flat_map(Self::expand_or_pat).collect(),
            MatchPat::Variant {
                path,
                payload: Some(inner),
            } => Self::expand_or_pat(inner)
                .into_iter()
                .map(|p| MatchPat::Variant {
                    path: path.clone(),
                    payload: Some(Box::new(p)),
                })
                .collect(),
            MatchPat::DotVariant {
                name,
                payload: Some(inner),
            } => Self::expand_or_pat(inner)
                .into_iter()
                .map(|p| MatchPat::DotVariant {
                    name: name.clone(),
                    payload: Some(Box::new(p)),
                })
                .collect(),
            MatchPat::Struct { path, fields, rest } => {
                let mut combinations: Vec<Vec<(String, MatchPat)>> = vec![Vec::new()];
                for (fname, fpat) in fields {
                    let expanded = Self::expand_or_pat(fpat);
                    let mut next = Vec::with_capacity(combinations.len() * expanded.len());
                    for prefix in &combinations {
                        for ep in &expanded {
                            let mut v = prefix.clone();
                            v.push((fname.clone(), ep.clone()));
                            next.push(v);
                        }
                    }
                    combinations = next;
                }
                combinations
                    .into_iter()
                    .map(|fs| MatchPat::Struct {
                        path: path.clone(),
                        fields: fs,
                        rest: *rest,
                    })
                    .collect()
            }
            MatchPat::Seq {
                elems,
                rest,
                bracketed,
            } => {
                let mut combinations: Vec<Vec<MatchPat>> = vec![Vec::new()];
                for ep_raw in elems {
                    let expanded = Self::expand_or_pat(ep_raw);
                    let mut next = Vec::with_capacity(combinations.len() * expanded.len());
                    for prefix in &combinations {
                        for ep in &expanded {
                            let mut v = prefix.clone();
                            v.push(ep.clone());
                            next.push(v);
                        }
                    }
                    combinations = next;
                }
                combinations
                    .into_iter()
                    .map(|es| MatchPat::Seq {
                        elems: es,
                        rest: *rest,
                        bracketed: *bracketed,
                    })
                    .collect()
            }
            other => vec![other.clone()],
        }
    }

    fn extract_packed_field_from_place(
        &mut self,
        place: &Place,
        struct_ty: TypeId,
        field_idx: usize,
        field_ty: TypeId,
    ) -> Result<Operand, String> {
        let comp = self.compiler.composites[&struct_ty].clone();
        let (bit_offset, bit_width) = comp.packed_offsets[field_idx];
        let (_, f_signed) = self
            .compiler
            .packed_field_bit_width(field_ty)
            .unwrap_or((bit_width, false));
        let backing_ty = self.compiler.program.types[struct_ty.0 as usize].clone();
        let Type::Int {
            bits: total_bits, ..
        } = backing_ty
        else {
            return Err("Invalid packed struct backing type".to_string());
        };
        let unsigned_backing_ty = self.compiler.intern_type(Type::Int {
            signed: false,
            bits: total_bits,
        });
        let base_val = self.alloc_temp(unsigned_backing_ty);
        self.emit(Statement::Assign(
            Place::new(base_val),
            Rvalue::Cast(Operand::Copy(place.clone()), unsigned_backing_ty),
        ));
        let shifted = if f_signed {
            let signed_backing_ty = self.compiler.intern_type(Type::Int {
                signed: true,
                bits: total_bits,
            });
            let shl_amt = u32::from(total_bits - (bit_offset + bit_width));
            let shr_amt = u32::from(total_bits - bit_width);
            let shl_tmp = self.alloc_temp(unsigned_backing_ty);
            self.emit(Statement::Assign(
                Place::new(shl_tmp),
                Rvalue::BinaryOp(
                    BinOp::Shl,
                    Operand::Copy(Place::new(base_val)),
                    Operand::Const(ConstValue::I64(i128::from(shl_amt))),
                ),
            ));
            let s_tmp = self.alloc_temp(signed_backing_ty);
            self.emit(Statement::Assign(
                Place::new(s_tmp),
                Rvalue::Cast(Operand::Copy(Place::new(shl_tmp)), signed_backing_ty),
            ));
            let ashr_tmp = self.alloc_temp(signed_backing_ty);
            self.emit(Statement::Assign(
                Place::new(ashr_tmp),
                Rvalue::BinaryOp(
                    BinOp::Shr,
                    Operand::Copy(Place::new(s_tmp)),
                    Operand::Const(ConstValue::I64(i128::from(shr_amt))),
                ),
            ));
            Place::new(ashr_tmp)
        } else {
            let shr_tmp = if bit_offset > 0 {
                let t = self.alloc_temp(unsigned_backing_ty);
                self.emit(Statement::Assign(
                    Place::new(t),
                    Rvalue::BinaryOp(
                        BinOp::Shr,
                        Operand::Copy(Place::new(base_val)),
                        Operand::Const(ConstValue::I64(i128::from(bit_offset))),
                    ),
                ));
                t
            } else {
                base_val
            };
            if bit_width < total_bits {
                let mask = crate::wide::Wide::max_value(bit_width, false);
                let mask_const = super::comptime::int_const(mask);
                let masked = self.alloc_temp(unsigned_backing_ty);
                self.emit(Statement::Assign(
                    Place::new(masked),
                    Rvalue::BinaryOp(
                        BinOp::BitAnd,
                        Operand::Copy(Place::new(shr_tmp)),
                        Operand::Const(mask_const),
                    ),
                ));
                Place::new(masked)
            } else {
                Place::new(shr_tmp)
            }
        };
        let out_tmp = self.alloc_temp(field_ty);
        self.emit(Statement::Assign(
            Place::new(out_tmp),
            Rvalue::Cast(Operand::Copy(shifted), field_ty),
        ));
        Ok(Operand::Copy(Place::new(out_tmp)))
    }

    fn emit_cond_branch(&mut self, cond_op: Operand, fail_bb: BlockId) {
        let ok_bb = self.new_block();
        self.terminate(Terminator::SwitchInt {
            discr: cond_op,
            targets: vec![(1, ok_bb)],
            otherwise: fail_bb,
        });
        self.body.cur_block = ok_bb;
    }

    fn lower_pat_test(
        &mut self,
        place: &Place,
        ty: TypeId,
        place_owned: bool,
        pat: &MatchPat,
        fail_bb: BlockId,
        actions: &mut Vec<GenBindAction>,
    ) -> Result<(), String> {
        let local_kind = if let Some(info) = self.compiler.errors.get(&ty).cloned() {
            MatchKind::Error(info)
        } else if let Some(info) = self.compiler.unions.get(&ty).cloned() {
            MatchKind::Union(info)
        } else if let Some((name, variants)) = self.compiler.enums.get(&ty).cloned() {
            MatchKind::Enum(name, variants)
        } else {
            MatchKind::Int
        };
        let pat = self.normalize_match_pat(&local_kind, pat)?;

        match &pat {
            MatchPat::Wildcard => {
                if place_owned && matches!(local_kind, MatchKind::Union(_) | MatchKind::Error(_)) {
                    // For a top-level owned union/error matched by `_`, the enclosing scope
                    // cleans up `raw_scrut_local` at scope exit; nothing to bind.
                }
                return Ok(());
            }
            MatchPat::CatchAllBind { mode, name } => {
                if name != "_" {
                    actions.push(GenBindAction::BindPlace {
                        name: name.clone(),
                        mode: *mode,
                        place: place.clone(),
                        ty,
                    });
                }
                return Ok(());
            }
            _ => {}
        }

        // Handle optional `?T`:
        if let Some(inner_ty) = self.compiler.as_optional_type(ty) {
            return self.lower_optional_pat_test(
                place,
                ty,
                inner_ty,
                place_owned,
                &pat,
                fail_bb,
                actions,
            );
        }

        // Handle result `E!T`:
        if let Some(&res_info) = self.compiler.results.get(&ty) {
            return self.lower_result_pat_test(
                place,
                ty,
                res_info,
                place_owned,
                &pat,
                fail_bb,
                actions,
            );
        }

        // Handle `enum`, `union`, `error`:
        match &local_kind {
            MatchKind::Enum(enum_name, variants) => {
                return self.lower_enum_pat_test(
                    place, ty, enum_name, variants, &pat, fail_bb, actions,
                );
            }
            MatchKind::Union(union_info) => {
                return self.lower_union_pat_test(
                    place,
                    ty,
                    place_owned,
                    union_info,
                    &pat,
                    fail_bb,
                    actions,
                );
            }
            MatchKind::Error(err_info) => {
                return self.lower_error_pat_test(
                    place,
                    ty,
                    place_owned,
                    err_info,
                    &pat,
                    fail_bb,
                    actions,
                );
            }
            MatchKind::Int => {}
        }

        // Handle `&str`:
        if self.compiler.slices.get(&ty).is_some_and(|s| s.is_str) {
            return self.lower_str_pat_test(place, ty, &pat, fail_bb);
        }

        // Handle `&[T]` / `&mut [T]` slice:
        if let Some(&slice_info) = self.compiler.slices.get(&ty) {
            return self.lower_slice_pat_test(
                place,
                ty,
                slice_info.elem,
                slice_info.mutable,
                &pat,
                fail_bb,
                actions,
            );
        }

        // Handle `[T; N]` array:
        if let Type::Array { elem, len } = self.compiler.program.types[ty.0 as usize] {
            return self.lower_array_pat_test(
                place,
                ty,
                elem,
                len as usize,
                place_owned,
                &pat,
                fail_bb,
                actions,
            );
        }

        // Handle composite `struct` (including `packed struct`):
        if let Some(comp) = self.compiler.composites.get(&ty).cloned() {
            return self.lower_struct_pat_test(
                place,
                ty,
                &comp,
                place_owned,
                &pat,
                fail_bb,
                actions,
            );
        }

        // Handle structural tuple (`Type::Struct` not in `composites`, `slices`, `closures`, `trait_objs`):
        if self.compiler.type_satisfies_constraint(ty, TypeConstraint::Tuple)
            && let Type::Struct(elem_tys) = self.compiler.program.types[ty.0 as usize].clone()
        {
            return self.lower_tuple_pat_test(
                place,
                ty,
                &elem_tys,
                place_owned,
                &pat,
                fail_bb,
                actions,
            );
        }

        // Handle `bool`:
        if matches!(self.compiler.program.types[ty.0 as usize], Type::Bool)
            && !self.compiler.distinct_types.contains_key(&ty)
        {
            return self.lower_bool_pat_test(place, ty, &pat, fail_bb);
        }

        // Handle `rune`:
        if matches!(self.compiler.program.types[ty.0 as usize], Type::Rune)
            && !self.compiler.distinct_types.contains_key(&ty)
        {
            return self.lower_rune_pat_test(place, ty, &pat, fail_bb);
        }

        // Handle `f32` / `f64`:
        if matches!(
            self.compiler.program.types[ty.0 as usize],
            Type::F32 | Type::F64
        ) && !self.compiler.distinct_types.contains_key(&ty)
        {
            return self.lower_float_pat_test(place, ty, &pat, fail_bb);
        }

        // Handle integers and `Type::Pattern`:
        let base_ty = self.pattern_base(ty);
        if matches!(
            self.compiler.program.types[base_ty.0 as usize],
            Type::Int { .. }
        ) && !self.compiler.distinct_types.contains_key(&ty)
            && !self.compiler.named_opaques.contains(&ty)
        {
            return self.lower_int_pat_test(place, ty, base_ty, &pat, fail_bb);
        }

        Err(format!(
            "Cannot match pattern against type '{}'",
            self.compiler.type_display_name(ty)
        ))
    }

    fn lower_optional_pat_test(
        &mut self,
        place: &Place,
        opt_ty: TypeId,
        inner_ty: TypeId,
        place_owned: bool,
        pat: &MatchPat,
        fail_bb: BlockId,
        actions: &mut Vec<GenBindAction>,
    ) -> Result<(), String> {
        let u8_ty = self.compiler.intern_type(Type::Int {
            signed: false,
            bits: 8,
        });
        let discr_local = self.alloc_temp(u8_ty);
        self.emit(Statement::Assign(
            Place::new(discr_local),
            Rvalue::Discriminant(place.clone()),
        ));

        let is_none_pat = match pat {
            MatchPat::Null => true,
            MatchPat::DotVariant { name, payload } if name == "None" => {
                if payload.is_some() {
                    return Err("Optional variant '.None' takes no payload".to_string());
                }
                true
            }
            MatchPat::Variant { path, payload }
                if path.len() == 1 && path[0] == "None" && payload.is_none() =>
            {
                return Err(
                    "Pattern 'None' would bind the value, but 'None' is a variant; write '.None' or 'null' to match it"
                        .to_string(),
                );
            }
            _ => false,
        };
        if is_none_pat {
            let ok_bb = self.new_block();
            self.terminate(Terminator::SwitchInt {
                discr: Operand::Copy(Place::new(discr_local)),
                targets: vec![(0, ok_bb)],
                otherwise: fail_bb,
            });
            self.body.cur_block = ok_bb;
            if place_owned && !self.is_copy_type(opt_ty) {
                let mut v_place = place.clone();
                v_place.projections.push(Projection::Variant(0));
                let void_ty = self.compiler.intern_type(Type::Void);
                actions.push(GenBindAction::RetireUnionCopyPayload {
                    variant_place: v_place,
                    payload_ty: void_ty,
                });
            }
            return Ok(());
        }

        // Check for `.Some(inner)` or direct inner pattern `inner`
        let inner_pat: &MatchPat = match pat {
            MatchPat::DotVariant { name, payload } => {
                if name != "Some" {
                    return Err(format!(
                        "Optional type '{}' has no variant '.{name}' (expected '.Some(x)', '.None', or 'null')",
                        self.compiler.type_display_name(opt_ty)
                    ));
                }
                let Some(sub) = payload.as_deref() else {
                    return Err("Optional variant '.Some' requires a payload pattern".to_string());
                };
                sub
            }
            MatchPat::Variant {
                path,
                payload: Some(_),
            } if path.len() == 1 && path[0] == "Some" => {
                return Err("Write '.Some(...)' to match optional payload".to_string());
            }
            other => other,
        };

        let ok_bb = self.new_block();
        self.terminate(Terminator::SwitchInt {
            discr: Operand::Copy(Place::new(discr_local)),
            targets: vec![(1, ok_bb)],
            otherwise: fail_bb,
        });
        self.body.cur_block = ok_bb;

        let mut payload_place = place.clone();
        payload_place.projections.push(Projection::Variant(1));
        self.lower_union_payload_subpat(
            payload_place,
            inner_ty,
            place_owned && !self.is_copy_type(opt_ty),
            inner_pat,
            fail_bb,
            actions,
        )
    }

    fn lower_result_pat_test(
        &mut self,
        place: &Place,
        res_ty: TypeId,
        res_info: ResultTypeInfo,
        place_owned: bool,
        pat: &MatchPat,
        fail_bb: BlockId,
        actions: &mut Vec<GenBindAction>,
    ) -> Result<(), String> {
        let MatchPat::DotVariant { name, payload } = pat else {
            if let MatchPat::Variant { path, .. } = pat
                && path.len() == 1
                && (path[0] == "Ok" || path[0] == "Err")
            {
                return Err(format!(
                    "Write '.{}(...)' to match result variant '{}'",
                    path[0], path[0]
                ));
            }
            return Err(format!(
                "Cannot match pattern against result type '{}' (expected '.Ok(...)' or '.Err(...)')",
                self.compiler.type_display_name(res_ty)
            ));
        };
        let (v_idx, payload_ty) = match name.as_str() {
            "Ok" => (0u32, res_info.ok_ty),
            "Err" => (1u32, res_info.err_ty),
            _ => {
                return Err(format!(
                    "Result type '{}' has no variant '.{name}' (expected '.Ok' or '.Err')",
                    self.compiler.type_display_name(res_ty)
                ));
            }
        };
        let is_void_payload = matches!(
            self.compiler.program.types[payload_ty.0 as usize],
            Type::Void
        );
        let sub_pat = match payload.as_deref() {
            Some(p) => p,
            None if is_void_payload => &MatchPat::Wildcard,
            None => {
                return Err(format!(
                    "Result variant '.{name}' requires a payload pattern"
                ));
            }
        };

        let u8_ty = self.compiler.intern_type(Type::Int {
            signed: false,
            bits: 8,
        });
        let discr_local = self.alloc_temp(u8_ty);
        self.emit(Statement::Assign(
            Place::new(discr_local),
            Rvalue::Discriminant(place.clone()),
        ));
        let ok_bb = self.new_block();
        self.terminate(Terminator::SwitchInt {
            discr: Operand::Copy(Place::new(discr_local)),
            targets: vec![(i128::from(v_idx), ok_bb)],
            otherwise: fail_bb,
        });
        self.body.cur_block = ok_bb;

        let mut payload_place = place.clone();
        payload_place.projections.push(Projection::Variant(v_idx));
        self.lower_union_payload_subpat(
            payload_place,
            payload_ty,
            place_owned && !self.is_copy_type(res_ty),
            sub_pat,
            fail_bb,
            actions,
        )
    }

    fn lower_union_payload_subpat(
        &mut self,
        payload_place: Place,
        payload_ty: TypeId,
        union_owned_noncopy: bool,
        sub_pat: &MatchPat,
        fail_bb: BlockId,
        actions: &mut Vec<GenBindAction>,
    ) -> Result<(), String> {
        let payload_copy = self.is_copy_type(payload_ty);
        match sub_pat {
            MatchPat::Wildcard => {
                if union_owned_noncopy && payload_copy {
                    actions.push(GenBindAction::RetireUnionCopyPayload {
                        variant_place: payload_place,
                        payload_ty,
                    });
                }
                Ok(())
            }
            MatchPat::CatchAllBind { mode, name } => {
                if name == "_" {
                    if union_owned_noncopy && payload_copy {
                        actions.push(GenBindAction::RetireUnionCopyPayload {
                            variant_place: payload_place,
                            payload_ty,
                        });
                    }
                } else {
                    actions.push(GenBindAction::BindPlace {
                        name: name.clone(),
                        mode: *mode,
                        place: payload_place,
                        ty: payload_ty,
                    });
                }
                Ok(())
            }
            _ => {
                let mut sub_actions = Vec::new();
                self.lower_pat_test(
                    &payload_place,
                    payload_ty,
                    union_owned_noncopy && !payload_copy,
                    sub_pat,
                    fail_bb,
                    &mut sub_actions,
                )?;
                if union_owned_noncopy && payload_copy {
                    actions.push(GenBindAction::RetireUnionCopyPayload {
                        variant_place: payload_place,
                        payload_ty,
                    });
                    actions.extend(sub_actions);
                } else if union_owned_noncopy
                    && !payload_copy
                    && sub_pat.ref_bind_mode().is_none()
                {
                    let holder_local = self.alloc_temp(payload_ty);
                    actions.push(GenBindAction::InitHolder {
                        holder_local,
                        src_place: payload_place.clone(),
                        ty: payload_ty,
                    });
                    for mut act in sub_actions {
                        act.rebase_prefix(&payload_place, holder_local);
                        actions.push(act);
                    }
                } else {
                    actions.extend(sub_actions);
                }
                Ok(())
            }
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn lower_enum_pat_test(
        &mut self,
        place: &Place,
        ty: TypeId,
        enum_name: &str,
        variants: &[(String, i128)],
        pat: &MatchPat,
        fail_bb: BlockId,
        _actions: &mut Vec<GenBindAction>,
    ) -> Result<(), String> {
        let v_val = match pat {
            MatchPat::Int(n) => *n,
            MatchPat::DotVariant { name, payload } => {
                if payload.is_some() {
                    return Err("Enum variant cannot bind a payload in `match`".to_string());
                }
                let Some((_, val)) = variants.iter().find(|(vn, _)| vn == name) else {
                    return Err(format!("Enum '{enum_name}' has no variant '{name}'"));
                };
                *val
            }
            MatchPat::Variant { path, payload } => {
                if payload.is_some() {
                    return Err("Enum variant cannot bind a payload in `match`".to_string());
                }
                let vname = path.last().unwrap();
                if let Some((_, val)) = variants.iter().find(|(vn, _)| vn == vname) {
                    *val
                } else if path.len() >= 2
                    && let Ok((ConstValue::I64(n), cty, _)) = self.compiler.eval_const_path(
                        &self.mod_path,
                        self.owner_ty,
                        &self.comptime_env,
                        Some(ty),
                        path,
                    )
                    && cty == ty
                {
                    n
                } else {
                    return Err(format!("Enum '{enum_name}' has no variant '{vname}'"));
                }
            }
            _ => {
                return Err(format!(
                    "Cannot match pattern against enum type '{enum_name}'"
                ));
            }
        };
        let ok_bb = self.new_block();
        self.terminate(Terminator::SwitchInt {
            discr: Operand::Copy(place.clone()),
            targets: vec![(v_val, ok_bb)],
            otherwise: fail_bb,
        });
        self.body.cur_block = ok_bb;
        Ok(())
    }

    #[allow(clippy::too_many_arguments)]
    fn lower_union_pat_test(
        &mut self,
        place: &Place,
        ty: TypeId,
        place_owned: bool,
        union_info: &UnionTypeInfo,
        pat: &MatchPat,
        fail_bb: BlockId,
        actions: &mut Vec<GenBindAction>,
    ) -> Result<(), String> {
        let (vname, payload_pat) = match pat {
            MatchPat::Int(_) => {
                return Err("Cannot match integer literal against `union` type".to_string());
            }
            MatchPat::DotVariant { name, payload } => (name.as_str(), payload.as_deref()),
            MatchPat::Variant { path, payload } => (path.last().unwrap().as_str(), payload.as_deref()),
            _ => {
                return Err(format!(
                    "Cannot match pattern against union type '{}'",
                    union_info.name
                ));
            }
        };
        let Some((v_idx, (_, payload_ty))) = union_info
            .variants
            .iter()
            .enumerate()
            .find(|(_, (vn, _))| vn == vname)
        else {
            return Err(format!(
                "Union '{}' has no variant '{vname}'",
                union_info.name
            ));
        };
        let Type::Union { tag: tag_ty, .. } = self.compiler.program.types[ty.0 as usize] else {
            unreachable!()
        };
        let discr_local = self.alloc_temp(tag_ty);
        self.emit(Statement::Assign(
            Place::new(discr_local),
            Rvalue::Discriminant(place.clone()),
        ));
        let ok_bb = self.new_block();
        self.terminate(Terminator::SwitchInt {
            discr: Operand::Copy(Place::new(discr_local)),
            targets: vec![(v_idx as i128, ok_bb)],
            otherwise: fail_bb,
        });
        self.body.cur_block = ok_bb;

        let mut p_place = place.clone();
        p_place.projections.push(Projection::Variant(v_idx as u32));
        let sub_pat = payload_pat.unwrap_or(&MatchPat::Wildcard);
        self.lower_union_payload_subpat(
            p_place,
            *payload_ty,
            place_owned && !self.is_copy_type(ty),
            sub_pat,
            fail_bb,
            actions,
        )
    }

    #[allow(clippy::too_many_arguments)]
    fn lower_error_pat_test(
        &mut self,
        place: &Place,
        ty: TypeId,
        place_owned: bool,
        err_info: &ErrorTypeInfo,
        pat: &MatchPat,
        fail_bb: BlockId,
        actions: &mut Vec<GenBindAction>,
    ) -> Result<(), String> {
        let Type::Union { tag: tag_ty, .. } = self.compiler.program.types[ty.0 as usize] else {
            unreachable!()
        };
        let discr_local = self.alloc_temp(tag_ty);
        self.emit(Statement::Assign(
            Place::new(discr_local),
            Rvalue::Discriminant(place.clone()),
        ));

        match pat {
            MatchPat::Int(_) => {
                Err("Cannot match integer literal against `error` type".to_string())
            }
            MatchPat::DotVariant { name, payload } => {
                let found: Vec<usize> = (0..err_info.leaves.len())
                    .filter(|&i| err_info.leaves[i].key.variant_name == *name)
                    .collect();
                match found.as_slice() {
                    [] => Err(format!(
                        "Error type '{}' has no variant '{name}'",
                        err_info.name
                    )),
                    [idx] => {
                        let payload_ty = err_info.leaves[*idx].payload_ty;
                        let ok_bb = self.new_block();
                        self.terminate(Terminator::SwitchInt {
                            discr: Operand::Copy(Place::new(discr_local)),
                            targets: vec![(*idx as i128, ok_bb)],
                            otherwise: fail_bb,
                        });
                        self.body.cur_block = ok_bb;
                        let mut p_place = place.clone();
                        p_place.projections.push(Projection::Variant(*idx as u32));
                        let sub_pat = payload.as_deref().unwrap_or(&MatchPat::Wildcard);
                        self.lower_union_payload_subpat(
                            p_place,
                            payload_ty,
                            place_owned && !self.is_copy_type(ty),
                            sub_pat,
                            fail_bb,
                            actions,
                        )
                    }
                    several => {
                        let qualified: Vec<String> = several
                            .iter()
                            .map(|&i| format!("'{}::{name}'", err_info.leaves[i].key.error_name))
                            .collect();
                        Err(format!(
                            "'.{name}' is ambiguous in error type '{}'; write {}",
                            err_info.name,
                            qualified.join(" or ")
                        ))
                    }
                }
            }
            MatchPat::Variant { path, payload } => {
                if let Some(sub_ty) = self.resolve_match_type_path(path)
                    && let Some(sub_err) = self.compiler.errors.get(&sub_ty).cloned()
                {
                    if payload
                        .as_deref()
                        .is_some_and(|p| p.ref_bind_mode().is_some())
                    {
                        return Err(format!(
                            "'ref' bindings are not supported for embedded error subtype patterns ('{}(...)'); match on a reference to the error instead",
                            path.join("::")
                        ));
                    }
                    let need_sub_val = payload
                        .as_deref()
                        .is_some_and(|p| !matches!(p, MatchPat::Wildcard));
                    let sub_local = need_sub_val.then(|| self.alloc_temp(sub_ty));
                    let join_ok_bb = self.new_block();
                    let mut targets = Vec::with_capacity(sub_err.leaves.len());
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
                        if let Some(s_loc) = sub_local {
                            let tramp_bb = self.new_block();
                            targets.push((scrut_idx as i128, tramp_bb));
                            self.body.cur_block = tramp_bb;
                            self.emit(Statement::StorageLive(s_loc));
                            let p_ty = scrut_leaf.payload_ty;
                            let p_op = if matches!(
                                self.compiler.program.types[p_ty.0 as usize],
                                Type::Void
                            ) {
                                Operand::Const(ConstValue::Void)
                            } else {
                                let mut p_place = place.clone();
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
                                Place::new(s_loc),
                                Rvalue::Union {
                                    ty: sub_ty,
                                    variant: sub_idx as u32,
                                    payload: p_op,
                                },
                            ));
                            self.terminate(Terminator::Goto { target: join_ok_bb });
                        } else {
                            targets.push((scrut_idx as i128, join_ok_bb));
                        }
                    }
                    self.body.blocks[self.body.cur_block.0 as usize].terminator =
                        Terminator::SwitchInt {
                            discr: Operand::Copy(Place::new(discr_local)),
                            targets,
                            otherwise: fail_bb,
                        };
                    self.body.terminated[self.body.cur_block.0 as usize] = true;
                    self.body.cur_block = join_ok_bb;
                    if let (Some(s_loc), Some(sub_pat)) = (sub_local, payload.as_deref()) {
                        match sub_pat {
                            MatchPat::CatchAllBind { name, .. } if name != "_" => {
                                actions.push(GenBindAction::BindVal {
                                    name: name.clone(),
                                    local: s_loc,
                                    ty: sub_ty,
                                });
                            }
                            MatchPat::CatchAllBind { .. } | MatchPat::Wildcard => {}
                            other => {
                                self.lower_pat_test(
                                    &Place::new(s_loc),
                                    sub_ty,
                                    !self.is_copy_type(sub_ty),
                                    other,
                                    fail_bb,
                                    actions,
                                )?;
                            }
                        }
                    }
                    Ok(())
                } else {
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
                    let Some(pat_err) = self.compiler.errors.get(&pat_err_ty).cloned() else {
                        return Err(format!(
                            "'{}' in match pattern is not an `error` type",
                            prefix.join("::")
                        ));
                    };
                    let Some(pat_leaf) = pat_err
                        .leaves
                        .iter()
                        .find(|l| l.key.error_name == pat_err.name && l.key.variant_name == *vname)
                        .or_else(|| pat_err.leaves.iter().find(|l| l.key.variant_name == *vname))
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
                            pat_leaf.key.error_name, pat_leaf.key.variant_name, err_info.name
                        ));
                    };
                    let payload_ty = scrut_leaf.payload_ty;
                    let ok_bb = self.new_block();
                    self.terminate(Terminator::SwitchInt {
                        discr: Operand::Copy(Place::new(discr_local)),
                        targets: vec![(scrut_idx as i128, ok_bb)],
                        otherwise: fail_bb,
                    });
                    self.body.cur_block = ok_bb;
                    let mut p_place = place.clone();
                    p_place
                        .projections
                        .push(Projection::Variant(scrut_idx as u32));
                    let sub_pat = payload.as_deref().unwrap_or(&MatchPat::Wildcard);
                    self.lower_union_payload_subpat(
                        p_place,
                        payload_ty,
                        place_owned && !self.is_copy_type(ty),
                        sub_pat,
                        fail_bb,
                        actions,
                    )
                }
            }
            _ => Err(format!(
                "Cannot match pattern against error type '{}'",
                err_info.name
            )),
        }
    }

    fn lower_str_pat_test(
        &mut self,
        place: &Place,
        ty: TypeId,
        pat: &MatchPat,
        fail_bb: BlockId,
    ) -> Result<(), String> {
        let s_const = match pat {
            MatchPat::Str(s) => {
                let str_ty = self.compiler.intern_str_type();
                (
                    Operand::Const(ConstValue::Aggregate(vec![
                        ConstValue::Str(s.clone()),
                        ConstValue::I64(s.len() as i128),
                    ])),
                    str_ty,
                )
            }
            MatchPat::Variant {
                path,
                payload: None,
            } => {
                let (cval, cty, _) = self.compiler.eval_const_path(
                    &self.mod_path,
                    self.owner_ty,
                    &self.comptime_env,
                    Some(ty),
                    path,
                )?;
                if !self.compiler.slices.get(&cty).is_some_and(|s| s.is_str) {
                    return Err(format!(
                        "Constant '{}' has type '{}', expected '&str'",
                        path.join("::"),
                        self.compiler.type_display_name(cty)
                    ));
                }
                (Operand::Const(cval), cty)
            }
            _ => {
                return Err("Expected string literal or `&str` constant in pattern".to_string());
            }
        };
        let (eq_op, _) =
            self.lower_str_eq(Operand::Copy(place.clone()), ty, s_const.0, s_const.1, false)?;
        self.emit_cond_branch(eq_op, fail_bb);
        Ok(())
    }

    fn lower_bool_pat_test(
        &mut self,
        place: &Place,
        ty: TypeId,
        pat: &MatchPat,
        fail_bb: BlockId,
    ) -> Result<(), String> {
        let b = match pat {
            MatchPat::Bool(b) => *b,
            MatchPat::Variant {
                path,
                payload: None,
            } => {
                let (cval, cty, _) = self.compiler.eval_const_path(
                    &self.mod_path,
                    self.owner_ty,
                    &self.comptime_env,
                    Some(ty),
                    path,
                )?;
                let ConstValue::Bool(b) = cval else {
                    return Err(format!(
                        "Constant '{}' has type '{}', expected 'bool'",
                        path.join("::"),
                        self.compiler.type_display_name(cty)
                    ));
                };
                b
            }
            _ => return Err("Expected `true` or `false` in `bool` pattern".to_string()),
        };
        let ok_bb = self.new_block();
        self.terminate(Terminator::SwitchInt {
            discr: Operand::Copy(place.clone()),
            targets: vec![(i128::from(b), ok_bb)],
            otherwise: fail_bb,
        });
        self.body.cur_block = ok_bb;
        Ok(())
    }

    fn eval_rune_bound(&mut self, pat: &MatchPat) -> Result<char, String> {
        match pat {
            MatchPat::Rune(ch) => Ok(*ch),
            MatchPat::Variant {
                path,
                payload: None,
            } => {
                let rune_ty = self.compiler.intern_type(Type::Rune);
                let (cval, cty, _) = self.compiler.eval_const_path(
                    &self.mod_path,
                    self.owner_ty,
                    &self.comptime_env,
                    Some(rune_ty),
                    path,
                )?;
                if cty != rune_ty {
                    return Err(format!(
                        "Constant '{}' has type '{}', expected 'rune'",
                        path.join("::"),
                        self.compiler.type_display_name(cty)
                    ));
                }
                let ConstValue::I64(n) = cval else {
                    return Err("Invalid rune constant".to_string());
                };
                char::from_u32(n as u32).ok_or_else(|| "Invalid rune scalar value".to_string())
            }
            _ => Err("Expected `rune` literal in pattern".to_string()),
        }
    }

    fn lower_rune_pat_test(
        &mut self,
        place: &Place,
        _ty: TypeId,
        pat: &MatchPat,
        fail_bb: BlockId,
    ) -> Result<(), String> {
        let bool_ty = self.compiler.intern_type(Type::Bool);
        match pat {
            MatchPat::Range { lo, hi } => {
                let lo_ch = self.eval_rune_bound(lo)?;
                let hi_ch = self.eval_rune_bound(hi)?;
                if lo_ch > hi_ch {
                    return Err(format!(
                        "Empty rune range '{lo_ch}'..='{hi_ch}' in match pattern: lower bound exceeds upper bound"
                    ));
                }
                let ge_tmp = self.alloc_temp(bool_ty);
                self.emit(Statement::Assign(
                    Place::new(ge_tmp),
                    Rvalue::BinaryOp(
                        BinOp::Ge,
                        Operand::Copy(place.clone()),
                        Operand::Const(ConstValue::I64(i128::from(u32::from(lo_ch)))),
                    ),
                ));
                self.emit_cond_branch(Operand::Copy(Place::new(ge_tmp)), fail_bb);
                let le_tmp = self.alloc_temp(bool_ty);
                self.emit(Statement::Assign(
                    Place::new(le_tmp),
                    Rvalue::BinaryOp(
                        BinOp::Le,
                        Operand::Copy(place.clone()),
                        Operand::Const(ConstValue::I64(i128::from(u32::from(hi_ch)))),
                    ),
                ));
                self.emit_cond_branch(Operand::Copy(Place::new(le_tmp)), fail_bb);
                Ok(())
            }
            other => {
                let ch = self.eval_rune_bound(other)?;
                let ok_bb = self.new_block();
                self.terminate(Terminator::SwitchInt {
                    discr: Operand::Copy(place.clone()),
                    targets: vec![(i128::from(u32::from(ch)), ok_bb)],
                    otherwise: fail_bb,
                });
                self.body.cur_block = ok_bb;
                Ok(())
            }
        }
    }

    fn lower_float_pat_test(
        &mut self,
        place: &Place,
        ty: TypeId,
        pat: &MatchPat,
        fail_bb: BlockId,
    ) -> Result<(), String> {
        let bits = match pat {
            MatchPat::Float(b) => *b,
            MatchPat::Int(n) => (*n as f64).to_bits(),
            MatchPat::Variant {
                path,
                payload: None,
            } => {
                let (cval, cty, _) = self.compiler.eval_const_path(
                    &self.mod_path,
                    self.owner_ty,
                    &self.comptime_env,
                    Some(ty),
                    path,
                )?;
                let ConstValue::F64(b) = cval else {
                    return Err(format!(
                        "Constant '{}' has type '{}', expected '{}'",
                        path.join("::"),
                        self.compiler.type_display_name(cty),
                        self.compiler.type_display_name(ty)
                    ));
                };
                b
            }
            _ => {
                return Err(format!(
                    "Expected float literal in pattern for '{}'",
                    self.compiler.type_display_name(ty)
                ));
            }
        };
        let bool_ty = self.compiler.intern_type(Type::Bool);
        let eq_tmp = self.alloc_temp(bool_ty);
        self.emit(Statement::Assign(
            Place::new(eq_tmp),
            Rvalue::BinaryOp(
                BinOp::Eq,
                Operand::Copy(place.clone()),
                Operand::Const(ConstValue::F64(bits)),
            ),
        ));
        self.emit_cond_branch(Operand::Copy(Place::new(eq_tmp)), fail_bb);
        Ok(())
    }

    fn eval_int_pat_bound(
        &mut self,
        pat: &MatchPat,
        scrut_ty: TypeId,
        base_ty: TypeId,
        in_range_bound: bool,
    ) -> Result<crate::wide::Wide, String> {
        let Type::Int { signed, bits } = self.compiler.program.types[base_ty.0 as usize] else {
            unreachable!()
        };
        let w = match pat {
            MatchPat::Int(n) => crate::wide::Wide::from_i128(*n),
            MatchPat::WideInt(w) => **w,
            MatchPat::CatchAllBind { name, .. } if in_range_bound => {
                let path = vec![name.clone()];
                let (cval, _, _) = self.compiler.eval_const_path(
                    &self.mod_path,
                    self.owner_ty,
                    &self.comptime_env,
                    Some(base_ty),
                    &path,
                )?;
                super::comptime::const_to_wide(&cval)
            }
            MatchPat::Variant {
                path,
                payload: None,
            } if in_range_bound || path.len() >= 2 => {
                let (cval, _, _) = self.compiler.eval_const_path(
                    &self.mod_path,
                    self.owner_ty,
                    &self.comptime_env,
                    Some(base_ty),
                    path,
                )?;
                if !matches!(cval, ConstValue::I64(_) | ConstValue::Wide(_)) {
                    return Err(format!(
                        "Constant '{}' is not an integer constant",
                        path.join("::")
                    ));
                }
                super::comptime::const_to_wide(&cval)
            }
            _ => {
                return Err(format!(
                    "Expected integer pattern for type '{}'",
                    self.compiler.type_display_name(scrut_ty)
                ));
            }
        };
        if !w.fits(bits, signed) {
            return Err(format!(
                "Integer pattern {w} does not fit in '{}'",
                self.compiler.type_display_name(scrut_ty)
            ));
        }
        if let Type::Pattern { ranges, .. } = &self.compiler.program.types[scrut_ty.0 as usize]
            && !ranges.iter().any(|(lo, hi)| w >= *lo && w <= *hi)
        {
            return Err(format!(
                "Integer pattern {w} is outside pattern type '{}'",
                self.compiler.type_display_name(scrut_ty)
            ));
        }
        Ok(w)
    }

    fn lower_int_pat_test(
        &mut self,
        place: &Place,
        scrut_ty: TypeId,
        base_ty: TypeId,
        pat: &MatchPat,
        fail_bb: BlockId,
    ) -> Result<(), String> {
        let bool_ty = self.compiler.intern_type(Type::Bool);
        let val_op = if scrut_ty != base_ty {
            let tmp = self.alloc_temp(base_ty);
            self.emit(Statement::Assign(
                Place::new(tmp),
                Rvalue::Cast(Operand::Copy(place.clone()), base_ty),
            ));
            Operand::Copy(Place::new(tmp))
        } else {
            Operand::Copy(place.clone())
        };
        match pat {
            MatchPat::Range { lo, hi } => {
                let lo_w = self.eval_int_pat_bound(lo, scrut_ty, base_ty, true)?;
                let hi_w = self.eval_int_pat_bound(hi, scrut_ty, base_ty, true)?;
                if lo_w > hi_w {
                    return Err(format!(
                        "Empty integer range {lo_w}..={hi_w} in match pattern: lower bound exceeds upper bound"
                    ));
                }
                let ge_tmp = self.alloc_temp(bool_ty);
                self.emit(Statement::Assign(
                    Place::new(ge_tmp),
                    Rvalue::BinaryOp(
                        BinOp::Ge,
                        val_op.clone(),
                        Operand::Const(super::comptime::int_const(lo_w)),
                    ),
                ));
                self.emit_cond_branch(Operand::Copy(Place::new(ge_tmp)), fail_bb);
                let le_tmp = self.alloc_temp(bool_ty);
                self.emit(Statement::Assign(
                    Place::new(le_tmp),
                    Rvalue::BinaryOp(
                        BinOp::Le,
                        val_op,
                        Operand::Const(super::comptime::int_const(hi_w)),
                    ),
                ));
                self.emit_cond_branch(Operand::Copy(Place::new(le_tmp)), fail_bb);
                Ok(())
            }
            other => {
                let w = self.eval_int_pat_bound(other, scrut_ty, base_ty, false)?;
                let eq_tmp = self.alloc_temp(bool_ty);
                self.emit(Statement::Assign(
                    Place::new(eq_tmp),
                    Rvalue::BinaryOp(
                        BinOp::Eq,
                        val_op,
                        Operand::Const(super::comptime::int_const(w)),
                    ),
                ));
                self.emit_cond_branch(Operand::Copy(Place::new(eq_tmp)), fail_bb);
                Ok(())
            }
        }
    }

    pub(super) fn seq_to_shorthand_struct_pat(
        pat: &MatchPat,
    ) -> Option<(Vec<(String, MatchPat)>, bool)> {
        let MatchPat::Seq {
            elems,
            rest,
            bracketed: false,
        } = pat
        else {
            return None;
        };
        if let Some(split) = rest
            && *split != elems.len()
        {
            return None;
        }
        let mut fields = Vec::with_capacity(elems.len());
        for ep in elems {
            let MatchPat::CatchAllBind { mode, name } = ep else {
                return None;
            };
            if name == "_" {
                return None;
            }
            fields.push((
                name.clone(),
                MatchPat::CatchAllBind {
                    mode: *mode,
                    name: name.clone(),
                },
            ));
        }
        Some((fields, rest.is_some()))
    }

    #[allow(clippy::too_many_arguments)]
    fn lower_struct_pat_test(
        &mut self,
        place: &Place,
        struct_ty: TypeId,
        comp: &CompositeInfo,
        place_owned: bool,
        pat: &MatchPat,
        fail_bb: BlockId,
        actions: &mut Vec<GenBindAction>,
    ) -> Result<(), String> {
        let shorthand_storage;
        let (path, fields, rest) = match pat {
            MatchPat::Struct { path, fields, rest } => (path.as_ref(), fields.as_slice(), *rest),
            other => {
                if let Some((sh_fields, sh_rest)) = Self::seq_to_shorthand_struct_pat(other) {
                    shorthand_storage = sh_fields;
                    (None, shorthand_storage.as_slice(), sh_rest)
                } else {
                    return Err(format!(
                        "Cannot match non-struct pattern against struct type '{}'",
                        comp.name
                    ));
                }
            }
        };
        if let Some(p) = path {
            let pat_ty = if p.len() == 1 && p[0] == "Self" && let Some(st) = self.owner_ty {
                Some(st)
            } else {
                self.resolve_match_type_path(p)
            };
            let Some(pat_ty) = pat_ty else {
                return Err(format!(
                    "Unknown struct type '{}' in match pattern",
                    p.join("::")
                ));
            };
            if pat_ty != struct_ty {
                return Err(format!(
                    "Pattern struct type '{}' does not match scrutinee type '{}'",
                    self.compiler.type_display_name(pat_ty),
                    comp.name
                ));
            }
        }
        if comp.is_opaque && comp.fields.is_empty() && self.owner_ty != Some(struct_ty) {
            return Err(format!(
                "Cannot destructure opaque type '{}' outside its 'opaque {{ ... }}' block",
                comp.name
            ));
        }

        for (i, (fname, _)) in fields.iter().enumerate() {
            if !comp.fields.iter().any(|(n, _, _, _)| n == fname) {
                return Err(format!("Struct '{}' has no field '{fname}'", comp.name));
            }
            if fields[..i].iter().any(|(n, _)| n == fname) {
                return Err(format!(
                    "Field '{fname}' of '{}' is matched more than once in pattern",
                    comp.name
                ));
            }
            self.check_field_access(struct_ty, fname)?;
        }

        if !rest {
            for (fname, _, _, _) in &comp.fields {
                if !fields.iter().any(|(n, _)| n == fname) {
                    self.check_field_access(struct_ty, fname)?;
                    return Err(format!(
                        "Pattern for struct '{}' is missing field '{fname}' (list all fields or add '..')",
                        comp.name
                    ));
                }
            }
        }

        for (fname, fpat) in fields {
            let (f_idx, (_, f_ty, _, _)) = comp
                .fields
                .iter()
                .enumerate()
                .find(|(_, (n, _, _, _))| n == fname)
                .unwrap();
            if comp.is_packed {
                match fpat {
                    MatchPat::Wildcard => {}
                    MatchPat::CatchAllBind { mode, name } => {
                        if name != "_" {
                            actions.push(GenBindAction::BindPackedField {
                                name: name.clone(),
                                mode: *mode,
                                place: place.clone(),
                                struct_ty,
                                field_idx: f_idx,
                                field_ty: *f_ty,
                            });
                        }
                    }
                    other => {
                        let val_op = self.extract_packed_field_from_place(
                            place, struct_ty, f_idx, *f_ty,
                        )?;
                        let tmp = self.alloc_temp(*f_ty);
                        self.emit(Statement::Assign(Place::new(tmp), Rvalue::Use(val_op)));
                        self.lower_pat_test(
                            &Place::new(tmp),
                            *f_ty,
                            false,
                            other,
                            fail_bb,
                            actions,
                        )?;
                    }
                }
            } else {
                let mut f_place = place.clone();
                f_place.projections.push(Projection::Field(f_idx as u32));
                self.lower_pat_test(
                    &f_place,
                    *f_ty,
                    place_owned && !self.is_copy_type(*f_ty),
                    fpat,
                    fail_bb,
                    actions,
                )?;
            }
        }
        Ok(())
    }

    #[allow(clippy::too_many_arguments)]
    fn lower_tuple_pat_test(
        &mut self,
        place: &Place,
        tuple_ty: TypeId,
        elem_tys: &[TypeId],
        place_owned: bool,
        pat: &MatchPat,
        fail_bb: BlockId,
        actions: &mut Vec<GenBindAction>,
    ) -> Result<(), String> {
        let (elems, rest) = match pat {
            MatchPat::Seq {
                elems,
                rest,
                bracketed: false,
            } => (elems.as_slice(), *rest),
            MatchPat::Struct {
                path: None,
                fields,
                rest: true,
            } if fields.is_empty() => (&[][..], Some(0)),
            _ => {
                return Err(format!(
                    "Cannot match pattern against tuple type '{}'",
                    self.compiler.type_display_name(tuple_ty)
                ));
            }
        };
        let n = elem_tys.len();
        match rest {
            None => {
                if elems.len() != n {
                    return Err(format!(
                        "Tuple pattern has {} element(s), but tuple '{}' has {}",
                        elems.len(),
                        self.compiler.type_display_name(tuple_ty),
                        n
                    ));
                }
                for (i, ep) in elems.iter().enumerate() {
                    let mut e_place = place.clone();
                    e_place.projections.push(Projection::Field(i as u32));
                    let ety = elem_tys[i];
                    self.lower_pat_test(
                        &e_place,
                        ety,
                        place_owned && !self.is_copy_type(ety),
                        ep,
                        fail_bb,
                        actions,
                    )?;
                }
            }
            Some(split) => {
                if elems.len() > n {
                    return Err(format!(
                        "Tuple pattern requires at least {} element(s), but tuple '{}' has {}",
                        elems.len(),
                        self.compiler.type_display_name(tuple_ty),
                        n
                    ));
                }
                let suffix_count = elems.len() - split;
                for (i, ep) in elems[..split].iter().enumerate() {
                    let mut e_place = place.clone();
                    e_place.projections.push(Projection::Field(i as u32));
                    let ety = elem_tys[i];
                    self.lower_pat_test(
                        &e_place,
                        ety,
                        place_owned && !self.is_copy_type(ety),
                        ep,
                        fail_bb,
                        actions,
                    )?;
                }
                for (k, ep) in elems[split..].iter().enumerate() {
                    let idx = n - suffix_count + k;
                    let mut e_place = place.clone();
                    e_place.projections.push(Projection::Field(idx as u32));
                    let ety = elem_tys[idx];
                    self.lower_pat_test(
                        &e_place,
                        ety,
                        place_owned && !self.is_copy_type(ety),
                        ep,
                        fail_bb,
                        actions,
                    )?;
                }
            }
        }
        Ok(())
    }

    #[allow(clippy::too_many_arguments)]
    fn lower_array_pat_test(
        &mut self,
        place: &Place,
        arr_ty: TypeId,
        elem_ty: TypeId,
        arr_len: usize,
        place_owned: bool,
        pat: &MatchPat,
        fail_bb: BlockId,
        actions: &mut Vec<GenBindAction>,
    ) -> Result<(), String> {
        let (elems, rest) = match pat {
            MatchPat::Seq { elems, rest, .. } => (elems.as_slice(), *rest),
            MatchPat::Struct {
                path: None,
                fields,
                rest: true,
            } if fields.is_empty() => (&[][..], Some(0)),
            _ => {
                return Err(format!(
                    "Cannot match pattern against array type '{}'",
                    self.compiler.type_display_name(arr_ty)
                ));
            }
        };
        match rest {
            None => {
                if elems.len() != arr_len {
                    return Err(format!(
                        "Array pattern has {} element(s), but '{}' has length {arr_len}",
                        elems.len(),
                        self.compiler.type_display_name(arr_ty)
                    ));
                }
            }
            Some(_) => {
                if elems.len() > arr_len {
                    return Err(format!(
                        "Array pattern requires at least {} element(s), but '{}' has length {arr_len}",
                        elems.len(),
                        self.compiler.type_display_name(arr_ty)
                    ));
                }
            }
        }

        let elem_copy = self.is_copy_type(elem_ty);
        if !elem_copy {
            let moves_any = elems.iter().any(|ep| {
                let mut names = HashSet::default();
                ep.collect_bound_names(&mut names);
                !names.is_empty() && ep.ref_bind_mode().is_none()
            });
            if moves_any {
                let binds_all = rest.is_none()
                    && elems.len() == arr_len
                    && elems.iter().all(|ep| {
                        matches!(ep, MatchPat::CatchAllBind { mode: BindMode::Move, name } if name != "_")
                    });
                if !binds_all || !place.projections.is_empty() || !place_owned {
                    return Err(format!(
                        "Cannot partially move elements out of non-copy array '{}'; bind all {} elements by value or use 'ref' bindings",
                        self.compiler.type_display_name(arr_ty),
                        arr_len
                    ));
                }
            }
        }

        let usize_ty = self.compiler.intern_type(Type::Int {
            signed: false,
            bits: 64,
        });
        let split = rest.unwrap_or(elems.len());
        let suffix_count = elems.len() - split;
        for (i, ep) in elems[..split].iter().enumerate() {
            let idx_local = self.alloc_temp(usize_ty);
            self.emit(Statement::Assign(
                Place::new(idx_local),
                Rvalue::Use(Operand::Const(ConstValue::I64(i as i128))),
            ));
            let mut e_place = place.clone();
            e_place.projections.push(Projection::Index(idx_local));
            self.lower_pat_test(&e_place, elem_ty, false, ep, fail_bb, actions)?;
        }
        for (k, ep) in elems[split..].iter().enumerate() {
            let idx = arr_len - suffix_count + k;
            let idx_local = self.alloc_temp(usize_ty);
            self.emit(Statement::Assign(
                Place::new(idx_local),
                Rvalue::Use(Operand::Const(ConstValue::I64(idx as i128))),
            ));
            let mut e_place = place.clone();
            e_place.projections.push(Projection::Index(idx_local));
            self.lower_pat_test(&e_place, elem_ty, false, ep, fail_bb, actions)?;
        }
        if !elem_copy && place_owned && place.projections.is_empty() {
            let binds_all = rest.is_none()
                && elems.len() == arr_len
                && elems.iter().all(|ep| {
                    matches!(ep, MatchPat::CatchAllBind { mode: BindMode::Move, name } if name != "_")
                });
            if binds_all {
                actions.push(GenBindAction::RetireLocal(place.local));
            }
        }
        Ok(())
    }

    #[allow(clippy::too_many_arguments)]
    fn lower_slice_pat_test(
        &mut self,
        place: &Place,
        slice_ty: TypeId,
        elem_ty: TypeId,
        _slice_mut: bool,
        pat: &MatchPat,
        fail_bb: BlockId,
        actions: &mut Vec<GenBindAction>,
    ) -> Result<(), String> {
        let (elems, rest) = match pat {
            MatchPat::Seq { elems, rest, .. } => (elems.as_slice(), *rest),
            MatchPat::Struct {
                path: None,
                fields,
                rest: true,
            } if fields.is_empty() => (&[][..], Some(0)),
            _ => {
                return Err(format!(
                    "Cannot match pattern against slice type '{}'",
                    self.compiler.type_display_name(slice_ty)
                ));
            }
        };
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
        let cmp_op = if rest.is_some() { BinOp::Ge } else { BinOp::Eq };
        let len_ok = self.alloc_temp(bool_ty);
        self.emit(Statement::Assign(
            Place::new(len_ok),
            Rvalue::BinaryOp(
                cmp_op,
                Operand::Copy(Place::new(len_local)),
                Operand::Const(ConstValue::I64(elems.len() as i128)),
            ),
        ));
        self.emit_cond_branch(Operand::Copy(Place::new(len_ok)), fail_bb);

        let split = rest.unwrap_or(elems.len());
        let suffix_count = elems.len() - split;
        for (i, ep) in elems[..split].iter().enumerate() {
            let idx_local = self.alloc_temp(usize_ty);
            self.emit(Statement::Assign(
                Place::new(idx_local),
                Rvalue::Use(Operand::Const(ConstValue::I64(i as i128))),
            ));
            let mut e_place = place.clone();
            e_place.projections.push(Projection::Field(0));
            e_place.projections.push(Projection::Deref);
            e_place.projections.push(Projection::Index(idx_local));
            self.lower_pat_test(&e_place, elem_ty, false, ep, fail_bb, actions)?;
        }
        for (k, ep) in elems[split..].iter().enumerate() {
            let offset = suffix_count - k;
            let idx_local = self.alloc_temp(usize_ty);
            self.emit(Statement::Assign(
                Place::new(idx_local),
                Rvalue::BinaryOp(
                    BinOp::Sub,
                    Operand::Copy(Place::new(len_local)),
                    Operand::Const(ConstValue::I64(offset as i128)),
                ),
            ));
            let mut e_place = place.clone();
            e_place.projections.push(Projection::Field(0));
            e_place.projections.push(Projection::Deref);
            e_place.projections.push(Projection::Index(idx_local));
            self.lower_pat_test(&e_place, elem_ty, false, ep, fail_bb, actions)?;
        }
        Ok(())
    }

    fn is_irrefutable_pat(&mut self, ty: TypeId, pat: &MatchPat) -> bool {
        let local_kind = if let Some(info) = self.compiler.errors.get(&ty).cloned() {
            MatchKind::Error(info)
        } else if let Some(info) = self.compiler.unions.get(&ty).cloned() {
            MatchKind::Union(info)
        } else if let Some((name, variants)) = self.compiler.enums.get(&ty).cloned() {
            MatchKind::Enum(name, variants)
        } else {
            MatchKind::Int
        };
        let Ok(pat) = self.normalize_match_pat(&local_kind, pat) else {
            return false;
        };
        match &pat {
            MatchPat::Wildcard | MatchPat::CatchAllBind { .. } => true,
            MatchPat::Or(alts) => alts.iter().any(|a| self.is_irrefutable_pat(ty, a)),
            MatchPat::Struct { fields, .. } => {
                if let Some(comp) = self.compiler.composites.get(&ty).cloned() {
                    fields.iter().all(|(fname, fpat)| {
                        comp.fields
                            .iter()
                            .find(|(n, _, _, _)| n == fname)
                            .is_some_and(|(_, fty, _, _)| self.is_irrefutable_pat(*fty, fpat))
                    })
                } else {
                    self.compiler
                        .type_satisfies_constraint(ty, TypeConstraint::Tuple)
                        && fields.is_empty()
                }
            }
            MatchPat::Seq { elems, rest, .. } => {
                if let Some(comp) = self.compiler.composites.get(&ty).cloned() {
                    if let Some((sh_fields, _)) = Self::seq_to_shorthand_struct_pat(&pat) {
                        sh_fields.iter().all(|(fname, fpat)| {
                            comp.fields
                                .iter()
                                .find(|(n, _, _, _)| n == fname)
                                .is_some_and(|(_, fty, _, _)| self.is_irrefutable_pat(*fty, fpat))
                        })
                    } else {
                        false
                    }
                } else if self.compiler.type_satisfies_constraint(ty, TypeConstraint::Tuple)
                    && let Type::Struct(elem_tys) =
                        self.compiler.program.types[ty.0 as usize].clone()
                {
                    let n = elem_tys.len();
                    let split = rest.unwrap_or(elems.len());
                    let suffix_count = elems.len() - split;
                    elems[..split]
                        .iter()
                        .enumerate()
                        .all(|(i, ep)| self.is_irrefutable_pat(elem_tys[i], ep))
                        && elems[split..].iter().enumerate().all(|(k, ep)| {
                            self.is_irrefutable_pat(elem_tys[n - suffix_count + k], ep)
                        })
                } else if let Type::Array { elem, .. } = self.compiler.program.types[ty.0 as usize]
                {
                    elems.iter().all(|ep| self.is_irrefutable_pat(elem, ep))
                } else if let Some(&sinfo) = self.compiler.slices.get(&ty) {
                    !sinfo.is_str && rest.is_some() && elems.is_empty()
                } else {
                    false
                }
            }
            _ => false,
        }
    }

    fn check_general_match_exhaustive(
        &mut self,
        kind: &MatchKind,
        scrut_ty: TypeId,
        pats: &[MatchPat],
    ) -> Option<String> {
        if pats.iter().any(|p| self.is_irrefutable_pat(scrut_ty, p)) {
            return None;
        }
        match kind {
            MatchKind::Enum(name, vs) => {
                let mut covered = vec![false; vs.len()];
                for p in pats {
                    match p {
                        MatchPat::DotVariant { name: vn, .. } => {
                            if let Some((i, _)) = vs.iter().enumerate().find(|(_, (n, _))| n == vn)
                            {
                                covered[i] = true;
                            }
                        }
                        MatchPat::Variant { path, .. } => {
                            let vn = path.last().unwrap();
                            if let Some((i, _)) = vs.iter().enumerate().find(|(_, (n, _))| n == vn)
                            {
                                covered[i] = true;
                            } else if path.len() >= 2
                                && let Ok((ConstValue::I64(val), cty, _)) =
                                    self.compiler.eval_const_path(
                                        &self.mod_path,
                                        self.owner_ty,
                                        &self.comptime_env,
                                        Some(scrut_ty),
                                        path,
                                    )
                                && cty == scrut_ty
                                && let Some((i, _)) =
                                    vs.iter().enumerate().find(|(_, (_, v))| *v == val)
                            {
                                covered[i] = true;
                            }
                        }
                        MatchPat::Int(val) => {
                            if let Some((i, _)) =
                                vs.iter().enumerate().find(|(_, (_, v))| v == val)
                            {
                                covered[i] = true;
                            }
                        }
                        _ => {}
                    }
                }
                let _ = name;
                return kind.non_exhaustive_error(&covered);
            }
            MatchKind::Union(info) => {
                let mut covered = vec![false; info.variants.len()];
                let mut sub_pats: Vec<Vec<MatchPat>> = vec![Vec::new(); info.variants.len()];
                for p in pats {
                    let (vname, payload) = match p {
                        MatchPat::DotVariant { name, payload } => (name.as_str(), payload.as_deref()),
                        MatchPat::Variant { path, payload } => {
                            (path.last().unwrap().as_str(), payload.as_deref())
                        }
                        _ => continue,
                    };
                    if let Some((i, (_, pty))) = info
                        .variants
                        .iter()
                        .enumerate()
                        .find(|(_, (vn, _))| vn == vname)
                    {
                        let sp = payload.cloned().unwrap_or(MatchPat::Wildcard);
                        if self.is_irrefutable_pat(*pty, &sp) {
                            covered[i] = true;
                        } else {
                            sub_pats[i].push(sp);
                        }
                    }
                }
                for (i, (_, pty)) in info.variants.iter().enumerate() {
                    if !covered[i] && !sub_pats[i].is_empty() {
                        let sub_k = self.match_kind_for(*pty);
                        if self
                            .check_general_match_exhaustive(&sub_k, *pty, &sub_pats[i])
                            .is_none()
                        {
                            covered[i] = true;
                        }
                    }
                }
                return kind.non_exhaustive_error(&covered);
            }
            MatchKind::Error(info) => {
                let mut covered = vec![false; info.leaves.len()];
                let mut sub_pats: Vec<Vec<MatchPat>> = vec![Vec::new(); info.leaves.len()];
                for p in pats {
                    match p {
                        MatchPat::DotVariant { name, payload } => {
                            if let Some((i, leaf)) = info
                                .leaves
                                .iter()
                                .enumerate()
                                .find(|(_, l)| l.key.variant_name == *name)
                            {
                                let sp = payload.as_deref().cloned().unwrap_or(MatchPat::Wildcard);
                                if self.is_irrefutable_pat(leaf.payload_ty, &sp) {
                                    covered[i] = true;
                                } else {
                                    sub_pats[i].push(sp);
                                }
                            }
                        }
                        MatchPat::Variant { path, payload } => {
                            if let Some(sub_ty) = self.resolve_match_type_path(path)
                                && let Some(sub_err) = self.compiler.errors.get(&sub_ty).cloned()
                            {
                                let sp = payload.as_deref().cloned().unwrap_or(MatchPat::Wildcard);
                                if self.is_irrefutable_pat(sub_ty, &sp) {
                                    for sub_leaf in &sub_err.leaves {
                                        if let Some((i, _)) = info
                                            .leaves
                                            .iter()
                                            .enumerate()
                                            .find(|(_, sl)| sl.key == sub_leaf.key)
                                        {
                                            covered[i] = true;
                                        }
                                    }
                                }
                            } else if path.len() >= 2 {
                                let prefix = &path[..path.len() - 1];
                                let vname = path.last().unwrap();
                                if let Some(pat_err_ty) = self.resolve_match_type_path(prefix)
                                    && let Some(pat_err) =
                                        self.compiler.errors.get(&pat_err_ty).cloned()
                                    && let Some(pat_leaf) = pat_err
                                        .leaves
                                        .iter()
                                        .find(|l| {
                                            l.key.error_name == pat_err.name
                                                && l.key.variant_name == *vname
                                        })
                                        .or_else(|| {
                                            pat_err
                                                .leaves
                                                .iter()
                                                .find(|l| l.key.variant_name == *vname)
                                        })
                                    && let Some((i, scrut_leaf)) = info
                                        .leaves
                                        .iter()
                                        .enumerate()
                                        .find(|(_, sl)| sl.key == pat_leaf.key)
                                {
                                    let sp =
                                        payload.as_deref().cloned().unwrap_or(MatchPat::Wildcard);
                                    if self.is_irrefutable_pat(scrut_leaf.payload_ty, &sp) {
                                        covered[i] = true;
                                    } else {
                                        sub_pats[i].push(sp);
                                    }
                                }
                            }
                        }
                        _ => {}
                    }
                }
                for (i, leaf) in info.leaves.iter().enumerate() {
                    if !covered[i] && !sub_pats[i].is_empty() {
                        let sub_k = self.match_kind_for(leaf.payload_ty);
                        if self
                            .check_general_match_exhaustive(&sub_k, leaf.payload_ty, &sub_pats[i])
                            .is_none()
                        {
                            covered[i] = true;
                        }
                    }
                }
                return kind.non_exhaustive_error(&covered);
            }
            MatchKind::Int => {}
        }

        // Optional `?T`
        if let Some(inner_ty) = self.compiler.as_optional_type(scrut_ty) {
            let mut none_covered = false;
            let mut some_pats = Vec::new();
            for p in pats {
                match p {
                    MatchPat::Null => none_covered = true,
                    MatchPat::DotVariant { name, .. } if name == "None" => none_covered = true,
                    MatchPat::DotVariant {
                        name,
                        payload: Some(sub),
                    } if name == "Some" => some_pats.push((**sub).clone()),
                    other => some_pats.push(other.clone()),
                }
            }
            let inner_k = self.match_kind_for(inner_ty);
            let some_covered = !some_pats.is_empty()
                && self
                    .check_general_match_exhaustive(&inner_k, inner_ty, &some_pats)
                    .is_none();
            if none_covered && some_covered {
                return None;
            }
            return Some(format!(
                "Non-exhaustive `match` on optional type '{}'",
                self.compiler.type_display_name(scrut_ty)
            ));
        }

        // Result `E!T`
        if let Some(&res_info) = self.compiler.results.get(&scrut_ty) {
            let mut ok_pats = Vec::new();
            let mut err_pats = Vec::new();
            for p in pats {
                if let MatchPat::DotVariant { name, payload } = p {
                    let sp = payload.as_deref().cloned().unwrap_or(MatchPat::Wildcard);
                    if name == "Ok" {
                        ok_pats.push(sp);
                    } else if name == "Err" {
                        err_pats.push(sp);
                    }
                }
            }
            let ok_k = self.match_kind_for(res_info.ok_ty);
            let err_k = self.match_kind_for(res_info.err_ty);
            let ok_cov = !ok_pats.is_empty()
                && self
                    .check_general_match_exhaustive(&ok_k, res_info.ok_ty, &ok_pats)
                    .is_none();
            let err_cov = !err_pats.is_empty()
                && self
                    .check_general_match_exhaustive(&err_k, res_info.err_ty, &err_pats)
                    .is_none();
            if ok_cov && err_cov {
                return None;
            }
            return Some(format!(
                "Non-exhaustive `match` on result type '{}'",
                self.compiler.type_display_name(scrut_ty)
            ));
        }

        // `bool`
        if matches!(self.compiler.program.types[scrut_ty.0 as usize], Type::Bool) {
            let mut has_true = false;
            let mut has_false = false;
            for p in pats {
                match p {
                    MatchPat::Bool(true) => has_true = true,
                    MatchPat::Bool(false) => has_false = true,
                    MatchPat::Variant {
                        path,
                        payload: None,
                    } if path.len() >= 2 => {
                        if let Ok((ConstValue::Bool(b), _, _)) = self.compiler.eval_const_path(
                            &self.mod_path,
                            self.owner_ty,
                            &self.comptime_env,
                            Some(scrut_ty),
                            path,
                        ) {
                            if b {
                                has_true = true;
                            } else {
                                has_false = true;
                            }
                        }
                    }
                    _ => {}
                }
            }
            if has_true && has_false {
                return None;
            }
            return Some(
                "Non-exhaustive `match` on `bool`: missing `true` or `false`".to_string(),
            );
        }

        // `rune`
        if matches!(self.compiler.program.types[scrut_ty.0 as usize], Type::Rune) {
            let mut intervals = Vec::new();
            for p in pats {
                match p {
                    MatchPat::Range { lo, hi } => {
                        if let (Ok(l), Ok(h)) =
                            (self.eval_rune_bound(lo), self.eval_rune_bound(hi))
                        {
                            intervals.push((
                                crate::wide::Wide::from_i128(i128::from(u32::from(l))),
                                crate::wide::Wide::from_i128(i128::from(u32::from(h))),
                            ));
                        }
                    }
                    other => {
                        if let Ok(ch) = self.eval_rune_bound(other) {
                            let w = crate::wide::Wide::from_i128(i128::from(u32::from(ch)));
                            intervals.push((w, w));
                        }
                    }
                }
            }
            let required = [
                (
                    crate::wide::Wide::from_i128(0),
                    crate::wide::Wide::from_i128(0xD7FF),
                ),
                (
                    crate::wide::Wide::from_i128(0xE000),
                    crate::wide::Wide::from_i128(0x10FFFF),
                ),
            ];
            if Self::intervals_cover_domain(&intervals, &required) {
                return None;
            }
            return Some("Non-exhaustive `match` on `rune` requires a wildcard `_` arm".to_string());
        }

        // Integers and `Type::Pattern`
        let base_ty = self.pattern_base(scrut_ty);
        if let Type::Int { signed, bits } = self.compiler.program.types[base_ty.0 as usize] {
            let mut intervals = Vec::new();
            for p in pats {
                match p {
                    MatchPat::Range { lo, hi } => {
                        if let (Ok(l), Ok(h)) = (
                            self.eval_int_pat_bound(lo, scrut_ty, base_ty, true),
                            self.eval_int_pat_bound(hi, scrut_ty, base_ty, true),
                        ) {
                            intervals.push((l, h));
                        }
                    }
                    other => {
                        if let Ok(w) = self.eval_int_pat_bound(other, scrut_ty, base_ty, false) {
                            intervals.push((w, w));
                        }
                    }
                }
            }
            let required: Vec<(crate::wide::Wide, crate::wide::Wide)> =
                if let Type::Pattern { ranges, .. } =
                    &self.compiler.program.types[scrut_ty.0 as usize]
                {
                    ranges.clone()
                } else {
                    vec![(
                        crate::wide::Wide::min_value(bits, signed),
                        crate::wide::Wide::max_value(bits, signed),
                    )]
                };
            if Self::intervals_cover_domain(&intervals, &required) {
                return None;
            }
            return Some(
                "Non-exhaustive `match` on integer requires a wildcard `_` arm".to_string(),
            );
        }

        // Slice `&[T]` / `&mut [T]`
        if let Some(&sinfo) = self.compiler.slices.get(&scrut_ty) {
            if sinfo.is_str {
                return Some(
                    "Non-exhaustive `match` on `&str` requires a wildcard `_` arm".to_string(),
                );
            }
            let mut exact_lens: HashMap<usize, Vec<Vec<MatchPat>>> = HashMap::default();
            let mut min_irrefutable_rest: Option<usize> = None;
            for p in pats {
                if let MatchPat::Seq { elems, rest, .. } = p {
                    let all_irrefutable = elems
                        .iter()
                        .all(|ep| self.is_irrefutable_pat(sinfo.elem, ep));
                    match rest {
                        None => {
                            exact_lens
                                .entry(elems.len())
                                .or_default()
                                .push(elems.clone());
                        }
                        Some(_) if all_irrefutable => {
                            min_irrefutable_rest = Some(
                                min_irrefutable_rest
                                    .map_or(elems.len(), |cur| cur.min(elems.len())),
                            );
                        }
                        Some(_) => {}
                    }
                }
            }
            if let Some(k) = min_irrefutable_rest {
                let all_shorter_covered = (0..k).all(|len| {
                    let Some(rows) = exact_lens.get(&len) else {
                        return false;
                    };
                    let col_tys = vec![sinfo.elem; len];
                    self.product_rows_exhaustive(&col_tys, rows)
                });
                if all_shorter_covered {
                    return None;
                }
            }
            return Some(format!(
                "Non-exhaustive `match` on slice '{}' requires a wildcard `_` or rest `..` arm",
                self.compiler.type_display_name(scrut_ty)
            ));
        }

        // Product types: `struct`, `tuple`, `[T; N]`
        if let Some(comp) = self.compiler.composites.get(&scrut_ty).cloned() {
            let col_tys: Vec<TypeId> = comp.fields.iter().map(|(_, t, _, _)| *t).collect();
            let mut rows = Vec::new();
            for p in pats {
                let sh_storage;
                let fields_opt = match p {
                    MatchPat::Struct { fields, .. } => Some(fields.as_slice()),
                    other => {
                        if let Some((sh_fields, _)) = Self::seq_to_shorthand_struct_pat(other) {
                            sh_storage = sh_fields;
                            Some(sh_storage.as_slice())
                        } else {
                            None
                        }
                    }
                };
                if let Some(fields) = fields_opt {
                    let row: Vec<MatchPat> = comp
                        .fields
                        .iter()
                        .map(|(fname, _, _, _)| {
                            fields
                                .iter()
                                .find(|(n, _)| n == fname)
                                .map(|(_, fp)| fp.clone())
                                .unwrap_or(MatchPat::Wildcard)
                        })
                        .collect();
                    rows.push(row);
                }
            }
            if self.product_rows_exhaustive(&col_tys, &rows) {
                return None;
            }
            return Some(format!(
                "Non-exhaustive `match` on struct '{}' requires a wildcard `_` arm",
                comp.name
            ));
        }

        if self
            .compiler
            .type_satisfies_constraint(scrut_ty, TypeConstraint::Tuple)
            && let Type::Struct(col_tys) = self.compiler.program.types[scrut_ty.0 as usize].clone()
        {
            let n = col_tys.len();
            let mut rows = Vec::new();
            for p in pats {
                if let MatchPat::Seq { elems, rest, .. } = p {
                    let row = Self::expand_seq_row(elems, *rest, n);
                    rows.push(row);
                }
            }
            if self.product_rows_exhaustive(&col_tys, &rows) {
                return None;
            }
            return Some(format!(
                "Non-exhaustive `match` on tuple '{}' requires a wildcard `_` arm",
                self.compiler.type_display_name(scrut_ty)
            ));
        }

        if let Type::Array { elem, len } = self.compiler.program.types[scrut_ty.0 as usize] {
            let n = len as usize;
            let col_tys = vec![elem; n];
            let mut rows = Vec::new();
            for p in pats {
                if let MatchPat::Seq { elems, rest, .. } = p {
                    let row = Self::expand_seq_row(elems, *rest, n);
                    rows.push(row);
                }
            }
            if self.product_rows_exhaustive(&col_tys, &rows) {
                return None;
            }
            return Some(format!(
                "Non-exhaustive `match` on array '{}' requires a wildcard `_` arm",
                self.compiler.type_display_name(scrut_ty)
            ));
        }

        Some(format!(
            "Non-exhaustive `match` on '{}' requires a wildcard `_` arm",
            self.compiler.type_display_name(scrut_ty)
        ))
    }

    fn expand_seq_row(elems: &[MatchPat], rest: Option<usize>, len: usize) -> Vec<MatchPat> {
        let Some(split) = rest else {
            return elems.to_vec();
        };
        let suffix_count = elems.len() - split;
        let mid_wildcards = len.saturating_sub(elems.len());
        let mut row = Vec::with_capacity(len);
        row.extend_from_slice(&elems[..split]);
        row.extend(std::iter::repeat_n(MatchPat::Wildcard, mid_wildcards));
        row.extend_from_slice(&elems[split..split + suffix_count]);
        row
    }

    fn product_rows_exhaustive(&mut self, col_tys: &[TypeId], rows: &[Vec<MatchPat>]) -> bool {
        if rows.is_empty() {
            return false;
        }
        if col_tys.is_empty() {
            return true;
        }
        if rows.iter().any(|r| {
            r.iter()
                .zip(col_tys.iter())
                .all(|(p, &t)| self.is_irrefutable_pat(t, p))
        }) {
            return true;
        }
        let first_ty = col_tys[0];
        let rest_tys = &col_tys[1..];
        let wildcard_rows: Vec<Vec<MatchPat>> = rows
            .iter()
            .filter(|r| self.is_irrefutable_pat(first_ty, &r[0]))
            .map(|r| r[1..].to_vec())
            .collect();
        if self.product_rows_exhaustive(rest_tys, &wildcard_rows) {
            return true;
        }
        // Check if first column's patterns cover `first_ty` when restricted to rows whose remaining
        // columns are irrefutable, or by splitting on `first_ty`'s constructors/values.
        let mut head_pats_with_irrefutable_tail = Vec::new();
        let mut specific_heads: Vec<MatchPat> = Vec::new();
        for r in rows {
            if r[1..]
                .iter()
                .zip(rest_tys.iter())
                .all(|(p, &t)| self.is_irrefutable_pat(t, p))
            {
                head_pats_with_irrefutable_tail.push(r[0].clone());
            }
            if !self.is_irrefutable_pat(first_ty, &r[0])
                && !specific_heads.iter().any(|h| h == &r[0])
            {
                specific_heads.push(r[0].clone());
            }
        }
        let first_k = self.match_kind_for(first_ty);
        if !head_pats_with_irrefutable_tail.is_empty()
            && self
                .check_general_match_exhaustive(
                    &first_k,
                    first_ty,
                    &head_pats_with_irrefutable_tail,
                )
                .is_none()
        {
            return true;
        }
        if specific_heads.is_empty() {
            return false;
        }
        // For each distinct specific pattern in column 0, check if rows matching that pattern (or wildcard in col 0)
        // exhaust `rest_tys`; if so, treat that head pattern as fully covering `rest_tys`.
        let mut fully_covered_heads = head_pats_with_irrefutable_tail;
        for head in &specific_heads {
            let specialized: Vec<Vec<MatchPat>> = rows
                .iter()
                .filter(|r| &r[0] == head || self.is_irrefutable_pat(first_ty, &r[0]))
                .map(|r| r[1..].to_vec())
                .collect();
            if self.product_rows_exhaustive(rest_tys, &specialized) {
                fully_covered_heads.push(head.clone());
            }
        }
        !fully_covered_heads.is_empty()
            && self
                .check_general_match_exhaustive(&first_k, first_ty, &fully_covered_heads)
                .is_none()
    }

    fn match_kind_for(&self, ty: TypeId) -> MatchKind {
        if let Some(info) = self.compiler.errors.get(&ty).cloned() {
            MatchKind::Error(info)
        } else if let Some(info) = self.compiler.unions.get(&ty).cloned() {
            MatchKind::Union(info)
        } else if let Some((name, variants)) = self.compiler.enums.get(&ty).cloned() {
            MatchKind::Enum(name, variants)
        } else {
            MatchKind::Int
        }
    }

    fn intervals_cover_domain(
        given: &[(crate::wide::Wide, crate::wide::Wide)],
        required: &[(crate::wide::Wide, crate::wide::Wide)],
    ) -> bool {
        if given.is_empty() {
            return false;
        }
        let mut sorted: Vec<(crate::wide::Wide, crate::wide::Wide)> = given
            .iter()
            .copied()
            .filter(|(lo, hi)| lo <= hi)
            .collect();
        sorted.sort();
        let one = crate::wide::Wide::from_i128(1);
        let mut merged: Vec<(crate::wide::Wide, crate::wide::Wide)> = Vec::new();
        for (lo, hi) in sorted {
            match merged.last_mut() {
                Some(last) if lo <= last.1 || lo == last.1.add(&one) => {
                    if hi > last.1 {
                        last.1 = hi;
                    }
                }
                _ => merged.push((lo, hi)),
            }
        }
        required
            .iter()
            .all(|(req_lo, req_hi)| merged.iter().any(|(lo, hi)| lo <= req_lo && hi >= req_hi))
    }

    /// Lowers the body of a `match` or `@select` arm in its own (already pushed) scope; when
    /// it falls through, records its end block and saved value in `arm_ends` and refines
    /// `inferred_res_ty`. A statement `match` (`is_stmt`) discards arm values.
    fn lower_arm_body(
        &mut self,
        body: &Expr,
        is_stmt: bool,
        inferred_res_ty: &mut Option<TypeId>,
        arm_ends: &mut Vec<(BlockId, Operand, TypeId)>,
    ) -> Result<(), String> {
        let void_ty = self.compiler.intern_type(Type::Void);
        let never_ty = self.compiler.intern_type(Type::Never);
        let is_lit = |e: &Expr| matches!(e, Expr::Int(_) | Expr::Float(_));
        if !is_stmt && inferred_res_ty.is_none() {
            match body {
                e if is_lit(e) => {
                    *inferred_res_ty = Some(self.new_type_var(matches!(e, Expr::Float(_))));
                }
                Expr::Unary {
                    op: UnOp::Neg,
                    expr: inner,
                } if is_lit(inner) => {
                    *inferred_res_ty =
                        Some(self.new_type_var(matches!(inner.as_ref(), Expr::Float(_))));
                }
                _ => {}
            }
        }
        let arm_exp = if is_stmt {
            Some(void_ty)
        } else {
            inferred_res_ty.map(|t| self.resolve_type_var(t))
        };
        let (arm_op, arm_ty) = self.lower_expr_open(body, arm_exp)?;
        if !self.is_terminated() {
            if !is_stmt && arm_ty != never_ty {
                match *inferred_res_ty {
                    None => *inferred_res_ty = Some(arm_ty),
                    Some(prev) if self.is_open_type_var(prev) && !self.is_open_type_var(arm_ty) => {
                        self.bind_type_var(prev, arm_ty)?;
                        *inferred_res_ty = Some(self.resolve_type_var(prev));
                    }
                    _ => {}
                }
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
            arm_ends.push((self.body.cur_block, saved_op, arm_ty));
        }
        self.pop_scope();
        Ok(())
    }

    /// Joins the arms that fell through (`arm_ends`) into one value of the arms' common type
    /// (`never` when none fell through, `void` for a statement).
    fn join_arms(
        &mut self,
        arm_ends: Vec<(BlockId, Operand, TypeId)>,
        inferred_res_ty: Option<TypeId>,
        is_stmt: bool,
    ) -> Result<(Operand, TypeId), String> {
        let void_ty = self.compiler.intern_type(Type::Void);
        let never_ty = self.compiler.intern_type(Type::Never);
        let final_ty = if is_stmt {
            void_ty
        } else {
            self.resolve_type_var(inferred_res_ty.unwrap_or(never_ty))
        };
        if arm_ends.is_empty() {
            let unreach_after = self.new_block();
            self.body.cur_block = unreach_after;
            self.terminate(Terminator::Unreachable);
            return Ok((Operand::Const(ConstValue::Void), never_ty));
        }
        let join_bb = self.new_block();
        let res_local = self.alloc_temp(final_ty);
        for (end_bb, saved_op, arm_ty) in arm_ends {
            let arm_ty = self.resolve_type_var(arm_ty);
            self.body.cur_block = end_bb;
            if !is_stmt && final_ty != void_ty && final_ty != never_ty {
                let coerced = self.coerce_operand(saved_op, arm_ty, final_ty)?;
                self.emit(Statement::Assign(
                    Place::new(res_local),
                    Rvalue::Use(coerced),
                ));
            }
            self.terminate(Terminator::Goto { target: join_bb });
        }
        self.body.cur_block = join_bb;
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
        if let Some(cell_field) = self.place_traverses_cell(&base_place) {
            return Err(format!(
                "Cannot take a safe slice reference to 'cell' field '{cell_field}'; read or copy the field by value, or use '&raw const' / '&raw mut'"
            ));
        }
        if want_mut {
            self.check_binding_writable(&base_place, "borrow mutably")?;
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
        let (elem_ty, bound) = if let Some(&slice_info) = self.compiler.slices.get(&base_ty) {
            if want_mut && !slice_info.mutable {
                return Err("Cannot take mutable subslice of an immutable slice".to_string());
            }
            let mut len_place = base_place.clone();
            len_place.projections.push(Projection::Field(1));
            base_place.projections.push(Projection::Field(0));
            base_place.projections.push(Projection::Deref);
            (slice_info.elem, IndexBound::Dynamic(len_place))
        } else if let Type::Array { elem, len } = self.compiler.program.types[base_ty.0 as usize] {
            if len == 0 && (self.unsafe_depth > 0 || self.place_traverses_raw_ptr(&base_place)) {
                (elem, IndexBound::Unchecked)
            } else {
                (elem, IndexBound::Static(len))
            }
        } else {
            return Err(format!(
                "Cannot slice non-array/slice type '{}'",
                self.compiler.type_display_name(base_ty)
            ));
        };

        let usize_ty = self.compiler.intern_type(Type::Int {
            signed: false,
            bits: 64,
        });
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
        // `end <= len` here; `start <= end` is enforced by the checked `end - start` below.
        self.emit_range_end_check(end_local, end_ty, const_end, bound)?;
        let end_op = Operand::Copy(Place::new(end_local));

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
        // An aggregate whose default is all zero bytes is one store, not one a field or element.
        if matches!(
            self.compiler.program.types[ty_id.0 as usize],
            Type::Array { .. } | Type::Simd { .. } | Type::Struct(_)
        ) && self.compiler.default_is_zero(ty_id)
        {
            let dst = self.alloc_temp(ty_id);
            self.emit(Statement::Assign(Place::new(dst), Rvalue::Use(Operand::Const(ConstValue::Zeroed))));
            return Ok((Operand::Move(Place::new(dst)), ty_id));
        }
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
                self.body.cur_block = next_bb;
                return Ok((Operand::Move(Place::new(dst)), ty_id));
            } else if comp.is_opaque {
                return Err(format!(
                    "Opaque type '{}' does not implement a `default()` hook",
                    comp.name
                ));
            } else {
                // Struct auto-synthesizes default from field defaults or field `@default`
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
                let dst = if comp.is_packed {
                    self.pack_composite_fields(ty_id, f_ops)?
                } else {
                    let dst = self.alloc_temp(ty_id);
                    self.emit(Statement::Assign(
                        Place::new(dst),
                        Rvalue::Aggregate(ty_id, f_ops),
                    ));
                    dst
                };
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
            _ => Err(format!(
                "Type '{}' does not support `@default`",
                self.compiler.type_display_name(ty_id)
            )),
        }
    }

    pub(super) fn lower_clone_for_place(
        &mut self,
        place: Place,
        ty_id: TypeId,
    ) -> Result<(Operand, TypeId), String> {
        if let Some(nt) = self.compiler.distinct_types.get(&ty_id).cloned()
            && !self.is_copy_type(ty_id)
        {
            let (inner_op, _) = self.lower_clone_for_place(place, nt.underlying)?;
            let dst = self.alloc_temp(ty_id);
            self.emit(Statement::Assign(
                Place::new(dst),
                Rvalue::Cast(inner_op, ty_id),
            ));
            return Ok((Operand::Move(Place::new(dst)), ty_id));
        }
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
                self.body.cur_block = next_bb;
                return Ok((Operand::Move(Place::new(dst)), ty_id));
            } else if comp.is_opaque {
                if comp.ownership != OpaqueOwnership::Copy {
                    return Err(format!("Opaque type '{}' does not implement `clone`", comp.name));
                }
            } else if !comp.is_packed {
                // Struct structural clone
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
            Err(format!("Type '{}' is not clonable", self.compiler.type_display_name(ty_id)))
        }
    }

    /// `v.tag` on a `union` value: its active variant as a `T::Tag` enum value. Only place-like
    /// receivers are considered (so the union is read, not moved, and nothing is evaluated twice).
    fn try_lower_union_tag(&mut self, base: &Expr) -> Result<Option<(Operand, TypeId)>, String> {
        if !is_pure_place(base) {
            return Ok(None);
        }
        let Ok((mut place, mut ty)) = self.lower_place(base, false) else {
            return Ok(None);
        };
        if let Type::Ptr { pointee, .. } = self.compiler.program.types[ty.0 as usize]
            && !self.compiler.raw_ptrs.contains_key(&ty)
        {
            place.projections.push(Projection::Deref);
            ty = pointee;
        }
        if !self.compiler.unions.contains_key(&ty) && !self.compiler.errors.contains_key(&ty) {
            return Ok(None);
        }
        let Type::Union { tag, .. } = self.compiler.program.types[ty.0 as usize].clone() else {
            return Ok(None);
        };
        let tag_enum = self.compiler.union_tag_enum(ty);
        let idx_local = self.alloc_temp(tag);
        self.emit(Statement::Assign(
            Place::new(idx_local),
            Rvalue::Discriminant(place),
        ));
        let out = self.alloc_temp(tag_enum);
        let custom_values = self
            .compiler
            .export_error_values
            .get(&ty)
            .cloned()
            .or_else(|| self.compiler.program.union_tag_values(ty).map(<[i128]>::to_vec));
        match custom_values {
            Some(values) => {
                let join = self.new_block();
                let mut targets = Vec::with_capacity(values.len());
                for (i, v) in values.iter().enumerate() {
                    let bb = self.new_block();
                    targets.push((i as i128, bb));
                    let saved = self.body.cur_block;
                    self.body.cur_block = bb;
                    self.emit(Statement::Assign(
                        Place::new(out),
                        Rvalue::Use(Operand::Const(ConstValue::I64(*v))),
                    ));
                    self.terminate(Terminator::Goto { target: join });
                    self.body.cur_block = saved;
                }
                let unreachable_bb = self.new_block();
                self.terminate(Terminator::SwitchInt {
                    discr: Operand::Copy(Place::new(idx_local)),
                    targets,
                    otherwise: unreachable_bb,
                });
                self.body.cur_block = unreachable_bb;
                self.terminate(Terminator::Unreachable);
                self.body.cur_block = join;
            }
            // Synthesized `T::Tag`: its values are the variant indices.
            None => {
                self.emit(Statement::Assign(
                    Place::new(out),
                    Rvalue::Cast(Operand::Copy(Place::new(idx_local)), tag_enum),
                ));
            }
        }
        Ok(Some((Operand::Copy(Place::new(out)), tag_enum)))
    }

    pub(super) fn try_lower_packed_or_reflect_field(
        &mut self,
        base: &Expr,
        field: &str,
        expected_ty: Option<TypeId>,
    ) -> Result<Option<(Operand, TypeId)>, String> {
        let res = self.lower_packed_or_reflect_field(base, field, expected_ty);
        // Only a field that is neither leaves the base for `lower_place`.
        if !matches!(res, Ok(None)) {
            self.lowered_base = None;
        }
        res
    }

    fn lower_packed_or_reflect_field(
        &mut self,
        base: &Expr,
        field: &str,
        expected_ty: Option<TypeId>,
    ) -> Result<Option<(Operand, TypeId)>, String> {
        // A base that is not a place (a call) is evaluated here, once: if the field turns out not
        // to be packed, `lower_place` takes its place from `lowered_base`.
        let lowered = if is_pure_place(base) {
            self.lower_expr(base, None)
        } else {
            self.lower_place(base, false).map(|(place, ty)| {
                self.lowered_base = Some((base as *const Expr, place.clone(), ty));
                (Operand::Copy(place), ty)
            })
        };
        let Ok((base_op, mut base_ty)) = lowered else {
            return Ok(None);
        };
        if (field == "bits" || field == "signed")
            && let Some((signed, bits, _, _)) = self.compiler.int_type_reflection(base_ty)
        {
            if field == "bits" {
                let cty = expected_ty
                    .filter(|t| matches!(self.compiler.program.types[t.0 as usize], Type::Int { .. }))
                    .unwrap_or_else(|| {
                        self.compiler.intern_type(Type::Int {
                            signed: false,
                            bits: 32,
                        })
                    });
                return Ok(Some((Operand::Const(ConstValue::I64(bits as i128)), cty)));
            } else {
                let bool_ty = self.compiler.intern_type(Type::Bool);
                return Ok(Some((Operand::Const(ConstValue::Bool(signed)), bool_ty)));
            }
        }
        if field == "bits"
            && let Some(comp) = self.compiler.composites.get(&base_ty)
            && comp.is_packed
        {
            let b = comp.total_bits as i128;
            let cty = expected_ty
                .filter(|t| matches!(self.compiler.program.types[t.0 as usize], Type::Int { .. }))
                .unwrap_or_else(|| {
                    self.compiler.intern_type(Type::Int {
                        signed: false,
                        bits: 32,
                    })
                });
            return Ok(Some((Operand::Const(ConstValue::I64(b)), cty)));
        }
        let mut cur_op = base_op;
        if let Type::Ptr { pointee, .. } = self.compiler.program.types[base_ty.0 as usize]
            && self
                .compiler
                .composites
                .get(&pointee)
                .is_some_and(|c| c.is_packed)
        {
            if self.compiler.raw_ptrs.contains_key(&base_ty) && self.unsafe_depth == 0 {
                return Err(format!(
                    "Dereferencing raw pointer of type '{}' is unsafe and requires an 'unsafe {{ ... }}' block",
                    self.compiler.type_display_name(base_ty)
                ));
            }
            let ptr_place = match cur_op {
                Operand::Copy(p) | Operand::Move(p) => p,
                other => {
                    let tmp = self.alloc_temp(base_ty);
                    self.emit(Statement::Assign(Place::new(tmp), Rvalue::Use(other)));
                    Place::new(tmp)
                }
            };
            let mut deref_p = ptr_place;
            deref_p.projections.push(Projection::Deref);
            cur_op = Operand::Copy(deref_p);
            base_ty = pointee;
        }
        if let Some(comp) = self.compiler.composites.get(&base_ty).cloned()
            && comp.is_packed
        {
            let (f_idx, f_ty) = self.check_field_access(base_ty, field)?;
            let f_loc = self.extract_packed_field(cur_op, base_ty, f_idx as usize)?;
            let out_op = if self.is_copy_type(f_ty) {
                Operand::Copy(Place::new(f_loc))
            } else {
                Operand::Move(Place::new(f_loc))
            };
            return Ok(Some((out_op, f_ty)));
        }
        Ok(None)
    }

    pub(super) fn try_assign_packed_field(
        &mut self,
        target: &Expr,
        op: Option<BinOp>,
        value: &Expr,
    ) -> Result<bool, String> {
        let mut field_chain: Vec<&str> = Vec::new();
        let mut cur = target;
        while let Expr::Field { base, field } = cur {
            field_chain.push(field.as_str());
            cur = base;
        }
        if field_chain.is_empty() {
            return Ok(false);
        }
        field_chain.reverse();

        let (mut root_place, mut root_ty) = match self.lower_place(cur, true) {
            Ok(res) => res,
            Err(_) => return Ok(false),
        };
        if let Type::Ptr { pointee, .. } = self.compiler.program.types[root_ty.0 as usize] {
            if self.compiler.raw_ptrs.contains_key(&root_ty) && self.unsafe_depth == 0 {
                return Err(format!(
                    "Dereferencing raw pointer of type '{}' is unsafe and requires an 'unsafe {{ ... }}' block",
                    self.compiler.type_display_name(root_ty)
                ));
            }
            root_place.projections.push(Projection::Deref);
            root_ty = pointee;
        }

        // Advance `root_place` through any non-packed composite prefixes until we hit a `packed` composite
        let mut packed_start = None;
        for (i, &fname) in field_chain.iter().enumerate() {
            if let Some(comp) = self.compiler.composites.get(&root_ty).cloned() {
                if comp.is_packed {
                    packed_start = Some(i);
                    break;
                }
                if comp.rel_fields.is_empty()
                    && let Ok((f_idx, f_ty)) = self.check_field_access(root_ty, fname)
                {
                    root_place.projections.push(Projection::Field(f_idx));
                    root_ty = f_ty;
                    if let Type::Ptr { pointee, .. } =
                        self.compiler.program.types[root_ty.0 as usize]
                    {
                        root_place.projections.push(Projection::Deref);
                        root_ty = pointee;
                    }
                    continue;
                }
            }
            return Ok(false);
        }

        let Some(start_idx) = packed_start else {
            return Ok(false);
        };
        self.check_binding_writable(&root_place, "assign to")?;
        if self.place_traverses_immutable_ptr(&root_place) {
            if let Some((stat_name, false)) = self.static_locals.get(&root_place.local) {
                return Err(format!(
                    "Cannot mutate immutable static variable '{}'",
                    stat_name
                ));
            }
            return Err(format!(
                "Cannot assign to '{}' through an immutable reference or pointer",
                root_place
            ));
        }

        let packed_chain = &field_chain[start_idx..];
        let mut steps: Vec<(Place, TypeId, usize, TypeId)> = Vec::with_capacity(packed_chain.len());
        let mut cur_place = root_place;
        let mut cur_ty = root_ty;
        for (depth, &fname) in packed_chain.iter().enumerate() {
            let (f_idx, f_ty) = self.check_field_access(cur_ty, fname)?;
            steps.push((cur_place.clone(), cur_ty, f_idx as usize, f_ty));
            if depth + 1 < packed_chain.len() {
                let sub_loc = self.extract_packed_field(
                    Operand::Copy(cur_place),
                    cur_ty,
                    f_idx as usize,
                )?;
                cur_place = Place::new(sub_loc);
                cur_ty = f_ty;
            }
        }

        let &(ref leaf_base_place, leaf_comp_ty, leaf_f_idx, leaf_f_ty) = steps.last().unwrap();
        let final_leaf_op = if let Some(binop) = op {
            let cur_f_loc = self.extract_packed_field(
                Operand::Copy(leaf_base_place.clone()),
                leaf_comp_ty,
                leaf_f_idx,
            )?;
            let (rhs_op, rhs_ty) = self.lower_expr(value, Some(leaf_f_ty))?;
            let coerced_rhs = self.coerce_operand(rhs_op, rhs_ty, leaf_f_ty)?;
            let res_loc = self.alloc_temp(leaf_f_ty);
            self.emit(Statement::Assign(
                Place::new(res_loc),
                Rvalue::BinaryOp(binop, Operand::Copy(Place::new(cur_f_loc)), coerced_rhs),
            ));
            Operand::Copy(Place::new(res_loc))
        } else {
            let (val_op, val_ty) = self.lower_expr(value, Some(leaf_f_ty))?;
            self.coerce_operand(val_op, val_ty, leaf_f_ty)?
        };

        let mut pending_val = final_leaf_op;
        for (step_place, step_comp_ty, step_f_idx, _) in steps.into_iter().rev() {
            self.insert_packed_field(
                step_place.clone(),
                step_comp_ty,
                step_f_idx,
                pending_val,
            )?;
            pending_val = Operand::Copy(step_place);
        }
        Ok(true)
    }

    pub(super) fn extract_packed_field(
        &mut self,
        base_op: Operand,
        comp_ty: TypeId,
        field_idx: usize,
    ) -> Result<LocalId, String> {
        let comp = self.compiler.composites[&comp_ty].clone();
        let (_, f_ty, _, _) = comp.fields[field_idx];
        let (bit_offset, bit_width) = comp.packed_offsets[field_idx];
        let (_, f_signed) = self
            .compiler
            .packed_field_bit_width(f_ty)
            .ok_or_else(|| "Invalid packed field type".to_string())?;
        let backing_ty = self.compiler.intern_type(Type::Int {
            signed: false,
            bits: comp.total_bits,
        });
        let base_place_op = match base_op {
            Operand::Const(_) => {
                let tmp = self.alloc_temp(comp_ty);
                self.emit(Statement::Assign(Place::new(tmp), Rvalue::Use(base_op)));
                Operand::Copy(Place::new(tmp))
            }
            other => other,
        };
        let mut cur_u = self.alloc_temp(backing_ty);
        self.emit(Statement::Assign(
            Place::new(cur_u),
            Rvalue::Cast(base_place_op, backing_ty),
        ));
        if bit_offset > 0 {
            let shifted = self.alloc_temp(backing_ty);
            self.emit(Statement::Assign(
                Place::new(shifted),
                Rvalue::BinaryOp(
                    BinOp::Shr,
                    Operand::Copy(Place::new(cur_u)),
                    Operand::Const(ConstValue::I64(bit_offset as i128)),
                ),
            ));
            cur_u = shifted;
        }
        let raw_f_ty = self.compiler.intern_type(Type::Int {
            signed: f_signed,
            bits: bit_width,
        });
        let raw_f_loc = self.alloc_temp(raw_f_ty);
        self.emit(Statement::Assign(
            Place::new(raw_f_loc),
            Rvalue::Cast(Operand::Copy(Place::new(cur_u)), raw_f_ty),
        ));
        if raw_f_ty == f_ty {
            return Ok(raw_f_loc);
        }
        let dst_loc = self.alloc_temp(f_ty);
        self.emit(Statement::Assign(
            Place::new(dst_loc),
            Rvalue::Cast(Operand::Copy(Place::new(raw_f_loc)), f_ty),
        ));
        Ok(dst_loc)
    }

    pub(super) fn insert_packed_field(
        &mut self,
        base_place: Place,
        comp_ty: TypeId,
        field_idx: usize,
        val_op: Operand,
    ) -> Result<(), String> {
        let comp = self.compiler.composites[&comp_ty].clone();
        let (_, f_ty, _, _) = comp.fields[field_idx];
        let (bit_offset, bit_width) = comp.packed_offsets[field_idx];
        let backing_ty = self.compiler.intern_type(Type::Int {
            signed: false,
            bits: comp.total_bits,
        });
        let u_field_ty = self.compiler.intern_type(Type::Int {
            signed: false,
            bits: bit_width,
        });
        let val_place_op = match val_op {
            Operand::Const(_) => {
                let tmp = self.alloc_temp(f_ty);
                self.emit(Statement::Assign(Place::new(tmp), Rvalue::Use(val_op)));
                Operand::Copy(Place::new(tmp))
            }
            other => other,
        };
        let u_field_loc = self.alloc_temp(u_field_ty);
        self.emit(Statement::Assign(
            Place::new(u_field_loc),
            Rvalue::Cast(val_place_op, u_field_ty),
        ));
        let mut ext_loc = self.alloc_temp(backing_ty);
        self.emit(Statement::Assign(
            Place::new(ext_loc),
            Rvalue::Cast(Operand::Copy(Place::new(u_field_loc)), backing_ty),
        ));
        if bit_width < comp.total_bits && bit_width < 128 {
            let f_mask = (1i128 << bit_width) - 1;
            let masked = self.alloc_temp(backing_ty);
            self.emit(Statement::Assign(
                Place::new(masked),
                Rvalue::BinaryOp(
                    BinOp::BitAnd,
                    Operand::Copy(Place::new(ext_loc)),
                    Operand::Const(ConstValue::I64(f_mask)),
                ),
            ));
            ext_loc = masked;
        }
        if bit_offset > 0 {
            let shifted = self.alloc_temp(backing_ty);
            self.emit(Statement::Assign(
                Place::new(shifted),
                Rvalue::BinaryOp(
                    BinOp::Shl,
                    Operand::Copy(Place::new(ext_loc)),
                    Operand::Const(ConstValue::I64(bit_offset as i128)),
                ),
            ));
            ext_loc = shifted;
        }
        let old_u_loc = self.alloc_temp(backing_ty);
        self.emit(Statement::Assign(
            Place::new(old_u_loc),
            Rvalue::Cast(Operand::Copy(base_place.clone()), backing_ty),
        ));
        let new_u_loc = if bit_width >= comp.total_bits {
            ext_loc
        } else {
            let one_mask = if bit_width >= 128 {
                let ones_small = self.alloc_temp(u_field_ty);
                self.emit(Statement::Assign(
                    Place::new(ones_small),
                    Rvalue::UnaryOp(UnOp::Not, Operand::Const(ConstValue::I64(0))),
                ));
                let ones_ext = self.alloc_temp(backing_ty);
                self.emit(Statement::Assign(
                    Place::new(ones_ext),
                    Rvalue::Cast(Operand::Copy(Place::new(ones_small)), backing_ty),
                ));
                Operand::Copy(Place::new(ones_ext))
            } else {
                Operand::Const(ConstValue::I64((1i128 << bit_width) - 1))
            };
            let shifted_mask = if bit_offset > 0 {
                let sm = self.alloc_temp(backing_ty);
                self.emit(Statement::Assign(
                    Place::new(sm),
                    Rvalue::BinaryOp(
                        BinOp::Shl,
                        one_mask,
                        Operand::Const(ConstValue::I64(bit_offset as i128)),
                    ),
                ));
                Operand::Copy(Place::new(sm))
            } else {
                one_mask
            };
            let inv_mask = self.alloc_temp(backing_ty);
            self.emit(Statement::Assign(
                Place::new(inv_mask),
                Rvalue::UnaryOp(UnOp::Not, shifted_mask),
            ));
            let cleared = self.alloc_temp(backing_ty);
            self.emit(Statement::Assign(
                Place::new(cleared),
                Rvalue::BinaryOp(
                    BinOp::BitAnd,
                    Operand::Copy(Place::new(old_u_loc)),
                    Operand::Copy(Place::new(inv_mask)),
                ),
            ));
            let combined = self.alloc_temp(backing_ty);
            self.emit(Statement::Assign(
                Place::new(combined),
                Rvalue::BinaryOp(
                    BinOp::BitOr,
                    Operand::Copy(Place::new(cleared)),
                    Operand::Copy(Place::new(ext_loc)),
                ),
            ));
            combined
        };
        self.emit(Statement::Assign(
            base_place,
            Rvalue::Cast(Operand::Copy(Place::new(new_u_loc)), comp_ty),
        ));
        Ok(())
    }

    pub(super) fn pack_composite_fields(
        &mut self,
        comp_ty: TypeId,
        field_ops: Vec<Operand>,
    ) -> Result<LocalId, String> {
        let dst = self.alloc_temp(comp_ty);
        self.emit(Statement::Assign(
            Place::new(dst),
            Rvalue::Use(Operand::Const(ConstValue::I64(0))),
        ));
        for (idx, f_op) in field_ops.into_iter().enumerate() {
            self.insert_packed_field(Place::new(dst), comp_ty, idx, f_op)?;
        }
        Ok(dst)
    }

    /// The base integer type of a pattern type; any other type unchanged.
    pub(super) fn pattern_base(&self, ty: TypeId) -> TypeId {
        match self.compiler.program.types[ty.0 as usize] {
            Type::Pattern { base, .. } => base,
            _ => ty,
        }
    }

    fn int_type_bounds(&self, ty_id: TypeId) -> Option<(Wide, Wide, u16, bool)> {
        if matches!(self.compiler.program.types[ty_id.0 as usize], Type::Rune) {
            return Some((Wide::ZERO, Wide::from_i128(0x10FFFF), 32, false));
        }
        let (signed, bits, min_val, max_val) = self.compiler.int_type_reflection(ty_id)?;
        Some((min_val, max_val, bits, signed))
    }

    fn emit_in_range_bool(
        &mut self,
        src_local: LocalId,
        src_ty: TypeId,
        dest_ty: TypeId,
    ) -> Result<LocalId, String> {
        let bool_ty = self.compiler.intern_type(Type::Bool);
        let (_, _, src_bits, src_signed) = self
            .int_type_bounds(src_ty)
            .ok_or_else(|| "Expected integer source type for range check".to_string())?;
        let base_src_ty = self.compiler.intern_type(Type::Int {
            signed: src_signed,
            bits: src_bits,
        });
        let val_loc = if base_src_ty == src_ty {
            src_local
        } else {
            let tmp = self.alloc_temp(base_src_ty);
            self.emit(Statement::Assign(
                Place::new(tmp),
                Rvalue::Cast(Operand::Copy(Place::new(src_local)), base_src_ty),
            ));
            tmp
        };

        let intervals: Vec<(Wide, Wide)> =
            match &self.compiler.program.types[dest_ty.0 as usize] {
                Type::Pattern { ranges, .. } => ranges.clone(),
                Type::Rune => vec![
                    (Wide::ZERO, Wide::from_i128(0xD7FF)),
                    (Wide::from_i128(0xE000), Wide::from_i128(0x10FFFF)),
                ],
                Type::Int { .. } => {
                    let Some((d_min, d_max, _, _)) = self.int_type_bounds(dest_ty) else {
                        let out = self.alloc_temp(bool_ty);
                        self.emit(Statement::Assign(
                            Place::new(out),
                            Rvalue::Use(Operand::Const(ConstValue::Bool(true))),
                        ));
                        return Ok(out);
                    };
                    vec![(d_min, d_max)]
                }
                _ => {
                    return Err(format!(
                        "Unsupported target type '{}' in checked cast",
                        self.compiler.type_display_name(dest_ty)
                    ));
                }
            };

        let (s_min, s_max, _, _) = self
            .int_type_bounds(base_src_ty)
            .unwrap_or((
                Wide::min_value(src_bits, src_signed),
                Wide::max_value(src_bits, src_signed),
                src_bits,
                src_signed,
            ));

        let mut any_match_loc: Option<LocalId> = None;
        for (lo, hi) in intervals {
            let eff_lo = lo.max(s_min);
            let eff_hi = hi.min(s_max);
            let range_ok_loc = if eff_lo > eff_hi {
                let f_loc = self.alloc_temp(bool_ty);
                self.emit(Statement::Assign(
                    Place::new(f_loc),
                    Rvalue::Use(Operand::Const(ConstValue::Bool(false))),
                ));
                f_loc
            } else {
                let mut cond_loc: Option<LocalId> = None;
                if eff_lo > s_min {
                    let ge_loc = self.alloc_temp(bool_ty);
                    self.emit(Statement::Assign(
                        Place::new(ge_loc),
                        Rvalue::BinaryOp(
                            BinOp::Ge,
                            Operand::Copy(Place::new(val_loc)),
                            Operand::Const(int_const(eff_lo)),
                        ),
                    ));
                    cond_loc = Some(ge_loc);
                }
                if eff_hi < s_max {
                    let le_loc = self.alloc_temp(bool_ty);
                    self.emit(Statement::Assign(
                        Place::new(le_loc),
                        Rvalue::BinaryOp(
                            BinOp::Le,
                            Operand::Copy(Place::new(val_loc)),
                            Operand::Const(int_const(eff_hi)),
                        ),
                    ));
                    cond_loc = Some(match cond_loc {
                        Some(prev) => {
                            let both = self.alloc_temp(bool_ty);
                            self.emit(Statement::Assign(
                                Place::new(both),
                                Rvalue::BinaryOp(
                                    BinOp::BitAnd,
                                    Operand::Copy(Place::new(prev)),
                                    Operand::Copy(Place::new(le_loc)),
                                ),
                            ));
                            both
                        }
                        None => le_loc,
                    });
                }
                match cond_loc {
                    Some(c) => c,
                    None => {
                        let t_loc = self.alloc_temp(bool_ty);
                        self.emit(Statement::Assign(
                            Place::new(t_loc),
                            Rvalue::Use(Operand::Const(ConstValue::Bool(true))),
                        ));
                        t_loc
                    }
                }
            };
            any_match_loc = Some(match any_match_loc {
                Some(prev) => {
                    let either = self.alloc_temp(bool_ty);
                    self.emit(Statement::Assign(
                        Place::new(either),
                        Rvalue::BinaryOp(
                            BinOp::BitOr,
                            Operand::Copy(Place::new(prev)),
                            Operand::Copy(Place::new(range_ok_loc)),
                        ),
                    ));
                    either
                }
                None => range_ok_loc,
            });
        }
        Ok(any_match_loc.unwrap())
    }

    pub(super) fn lower_checked_cast(
        &mut self,
        op: Operand,
        src_ty: TypeId,
        dest_inner: TypeId,
        opt_ty: TypeId,
    ) -> Result<(Operand, TypeId), String> {
        let src_local = self.alloc_temp(src_ty);
        self.emit(Statement::Assign(Place::new(src_local), Rvalue::Use(op)));
        let in_range_loc = self.emit_in_range_bool(src_local, src_ty, dest_inner)?;
        let res_local = self.alloc_temp(opt_ty);
        let ok_bb = self.new_block();
        let fail_bb = self.new_block();
        let join_bb = self.new_block();
        self.terminate(Terminator::SwitchInt {
            discr: Operand::Copy(Place::new(in_range_loc)),
            targets: vec![(1, ok_bb)],
            otherwise: fail_bb,
        });

        self.body.cur_block = ok_bb;
        let cast_tmp = self.alloc_temp(dest_inner);
        self.emit(Statement::Assign(
            Place::new(cast_tmp),
            Rvalue::Cast(Operand::Copy(Place::new(src_local)), dest_inner),
        ));
        self.emit(Statement::Assign(
            Place::new(res_local),
            Rvalue::Union {
                ty: opt_ty,
                variant: 1,
                payload: Operand::Copy(Place::new(cast_tmp)),
            },
        ));
        self.terminate(Terminator::Goto { target: join_bb });

        self.body.cur_block = fail_bb;
        self.emit(Statement::Assign(
            Place::new(res_local),
            Rvalue::Union {
                ty: opt_ty,
                variant: 0,
                payload: Operand::Const(ConstValue::Void),
            },
        ));
        self.terminate(Terminator::Goto { target: join_bb });

        self.body.cur_block = join_bb;
        Ok((Operand::Move(Place::new(res_local)), opt_ty))
    }

    pub(super) fn lower_trapping_pattern_or_rune_cast(
        &mut self,
        op: Operand,
        src_ty: TypeId,
        target_ty: TypeId,
    ) -> Result<(Operand, TypeId), String> {
        let src_local = self.alloc_temp(src_ty);
        self.emit(Statement::Assign(Place::new(src_local), Rvalue::Use(op)));
        let in_range_loc = self.emit_in_range_bool(src_local, src_ty, target_ty)?;
        let ok_bb = self.new_block();
        let trap_bb = self.new_block();
        self.terminate(Terminator::SwitchInt {
            discr: Operand::Copy(Place::new(in_range_loc)),
            targets: vec![(1, ok_bb)],
            otherwise: trap_bb,
        });

        self.body.cur_block = trap_bb;
        self.terminate(Terminator::Unreachable);

        self.body.cur_block = ok_bb;
        let dst_tmp = self.alloc_temp(target_ty);
        self.emit(Statement::Assign(
            Place::new(dst_tmp),
            Rvalue::Cast(Operand::Copy(Place::new(src_local)), target_ty),
        ));
        Ok((Operand::Copy(Place::new(dst_tmp)), target_ty))
    }

    /// `x as E` for an enum `E`: a constant that is no variant's value is an error, and a
    /// run-time value traps unless it is one.
    fn lower_checked_enum_cast(
        &mut self,
        op: Operand,
        src_ty: TypeId,
        target_ty: TypeId,
    ) -> Result<(Operand, TypeId), String> {
        let (name, variants) = self.compiler.enums[&target_ty].clone();
        let values: Vec<i128> = variants.iter().map(|(_, v)| *v).collect();
        if let Operand::Const(c @ (ConstValue::I64(_) | ConstValue::Wide(_))) = &op {
            let w = const_to_wide(c);
            if !values.iter().any(|&v| crate::wide::Wide::from_i128(v) == w) {
                let listed: Vec<String> = values.iter().map(|v| v.to_string()).collect();
                return Err(format!(
                    "{w} is not a value of enum '{name}', whose values are {}",
                    listed.join(", ")
                ));
            }
        }
        let src_local = self.alloc_temp(src_ty);
        self.emit(Statement::Assign(Place::new(src_local), Rvalue::Use(op)));
        let ok_bb = self.new_block();
        let trap_bb = self.new_block();
        self.terminate(Terminator::SwitchInt {
            discr: Operand::Copy(Place::new(src_local)),
            targets: values.iter().map(|&v| (v, ok_bb)).collect(),
            otherwise: trap_bb,
        });
        self.body.cur_block = trap_bb;
        self.terminate(Terminator::Unreachable);
        self.body.cur_block = ok_bb;
        let dst_tmp = self.alloc_temp(target_ty);
        self.emit(Statement::Assign(
            Place::new(dst_tmp),
            Rvalue::Cast(Operand::Copy(Place::new(src_local)), target_ty),
        ));
        Ok((Operand::Copy(Place::new(dst_tmp)), target_ty))
    }

    pub(super) fn materialize_const_val(&mut self, cval: ConstValue, ty: TypeId) -> Operand {
        match &cval {
            ConstValue::Global(gl_id) => {
                let gl_ty = self.compiler.program.globals[gl_id.0 as usize].ty;
                let gl_ptr_ty = self.compiler.intern_type(Type::Ptr {
                    mutable: false,
                    pointee: gl_ty,
                });
                if ty == gl_ptr_ty {
                    return Operand::Const(cval);
                }
                let gl_tmp = self.alloc_temp(gl_ptr_ty);
                self.emit(Statement::Assign(
                    Place::new(gl_tmp),
                    Rvalue::Use(Operand::Const(cval)),
                ));
                let cast_tmp = self.alloc_temp(ty);
                self.emit(Statement::Assign(
                    Place::new(cast_tmp),
                    Rvalue::Cast(Operand::Copy(Place::new(gl_tmp)), ty),
                ));
                Operand::Copy(Place::new(cast_tmp))
            }
            ConstValue::Str(s) => {
                let u8_ty = self.compiler.intern_type(Type::Int {
                    signed: false,
                    bits: 8,
                });
                let ptr_u8_ty = self.compiler.intern_type(Type::Ptr {
                    mutable: false,
                    pointee: u8_ty,
                });
                if ty == ptr_u8_ty {
                    return Operand::Const(cval);
                }
                if matches!(self.compiler.program.types[ty.0 as usize], Type::Ptr { .. }) {
                    let s_tmp = self.alloc_temp(ptr_u8_ty);
                    self.emit(Statement::Assign(
                        Place::new(s_tmp),
                        Rvalue::Use(Operand::Const(cval)),
                    ));
                    let tmp = self.alloc_temp(ty);
                    self.emit(Statement::Assign(
                        Place::new(tmp),
                        Rvalue::Cast(Operand::Copy(Place::new(s_tmp)), ty),
                    ));
                    return Operand::Copy(Place::new(tmp));
                }
                let sinfo_ptr_ty = self
                    .compiler
                    .slices
                    .get(&ty)
                    .map(|si| si.ptr_ty)
                    .unwrap_or(ptr_u8_ty);
                let ptr_op = if sinfo_ptr_ty == ptr_u8_ty {
                    Operand::Const(ConstValue::Str(s.clone()))
                } else {
                    let s_tmp = self.alloc_temp(ptr_u8_ty);
                    self.emit(Statement::Assign(
                        Place::new(s_tmp),
                        Rvalue::Use(Operand::Const(ConstValue::Str(s.clone()))),
                    ));
                    let p_tmp = self.alloc_temp(sinfo_ptr_ty);
                    self.emit(Statement::Assign(
                        Place::new(p_tmp),
                        Rvalue::Cast(Operand::Copy(Place::new(s_tmp)), sinfo_ptr_ty),
                    ));
                    Operand::Copy(Place::new(p_tmp))
                };
                let tmp = self.alloc_temp(ty);
                self.emit(Statement::Assign(
                    Place::new(tmp),
                    Rvalue::Aggregate(
                        ty,
                        vec![ptr_op, Operand::Const(ConstValue::I64(s.len() as i128))],
                    ),
                ));
                Operand::Copy(Place::new(tmp))
            }
            ConstValue::Aggregate(items) => {
                let items = items.clone();
                let tmp = self.alloc_temp(ty);
                match self.compiler.program.types[ty.0 as usize].clone() {
                    Type::Struct(ftys) if items.len() == ftys.len() => {
                        let mut ops = Vec::with_capacity(items.len());
                        for (item, fty) in items.into_iter().zip(ftys.into_iter()) {
                            ops.push(self.materialize_const_val(item, fty));
                        }
                        self.emit(Statement::Assign(
                            Place::new(tmp),
                            Rvalue::Aggregate(ty, ops),
                        ));
                    }
                    Type::Array { elem, .. } => {
                        let mut ops = Vec::with_capacity(items.len());
                        for item in items {
                            ops.push(self.materialize_const_val(item, elem));
                        }
                        self.emit(Statement::Assign(
                            Place::new(tmp),
                            Rvalue::Aggregate(ty, ops),
                        ));
                    }
                    _ => {
                        self.emit(Statement::Assign(
                            Place::new(tmp),
                            Rvalue::Use(Operand::Const(cval)),
                        ));
                    }
                }
                if self.is_copy_type(ty) {
                    Operand::Copy(Place::new(tmp))
                } else {
                    Operand::Move(Place::new(tmp))
                }
            }
            _ => Operand::Const(cval),
        }
    }

    pub(super) fn get_or_build_dense_map_global(
        &mut self,
        map_id: u32,
        min_k: i128,
        len: usize,
        default_val: ConstValue,
    ) -> GlobalId {
        if let Some(&(gl_id, _, _)) = self.compiler.dense_map_globals.get(&map_id) {
            return gl_id;
        }
        let inst = self.compiler.map_instances[map_id as usize].clone();
        let minfo = self.compiler.maps[&inst.map_ty];
        let mut elems = vec![default_val; len];
        for entry in &inst.entries {
            if let MapKey::Int(k) = entry.key {
                let idx = (k - min_k) as usize;
                if idx < len {
                    elems[idx] = entry.val_const.clone();
                }
            }
        }
        let arr_ty = self.compiler.intern_type(Type::Array {
            elem: minfo.val_ty,
            len: len as u64,
        });
        let gl_id = GlobalId(self.compiler.program.globals.len() as u32);
        self.compiler.program.globals.push(crate::ir::Global {
            id: gl_id,
            ty: arr_ty,
            init: ConstValue::Aggregate(elems),
            mutable: false,
        });
        self.compiler
            .dense_map_globals
            .insert(map_id, (gl_id, min_k, min_k + (len as i128) - 1));
        gl_id
    }

    pub(super) fn lower_map_index(
        &mut self,
        map_id: u32,
        index: &Expr,
    ) -> Result<(Operand, TypeId), String> {
        let inst = self.compiler.map_instances[map_id as usize].clone();
        let minfo = self.compiler.maps[&inst.map_ty];
        if let Ok((key, _, _)) = self.compiler.eval_map_key(
            &self.mod_path,
            self.owner_ty,
            &self.comptime_env,
            index,
            Some(minfo.key_ty),
        ) {
            if let Some(entry) = inst.entries.iter().find(|e| e.key == key) {
                let op = self.materialize_const_val(entry.val_const.clone(), minfo.val_ty);
                return Ok((op, minfo.val_ty));
            }
            return Err(format!("Comptime key {key:?} not found in map"));
        }

        // Runtime indexing `MAP[k]` is only allowed when `K` is an `enum` and `MAP` exhaustively covers all variants of `K`.
        let Some((enum_name, variants)) = self.compiler.enums.get(&minfo.key_ty).cloned() else {
            return Err(format!(
                "Direct map indexing 'MAP[k]' with a runtime key is only permitted when the key type is an exhaustively covered 'enum' (key type is '{}'); use 'MAP.get(k)' instead",
                self.compiler.type_display_name(minfo.key_ty)
            ));
        };
        for (vname, vval) in &variants {
            if !inst
                .entries
                .iter()
                .any(|e| matches!(e.key, MapKey::Int(k) if k == *vval))
            {
                return Err(format!(
                    "Direct map indexing 'MAP[k]' requires exhaustive coverage of enum '{}', but variant '{}::{}' is missing from map; use 'MAP.get(k)' instead",
                    enum_name, enum_name, vname
                ));
            }
        }
        if matches!(
            self.compiler.program.types[minfo.val_ty.0 as usize],
            Type::MetaType
        ) {
            return Err(
                "Map with 'type' values can only be indexed with a 'comptime' key".to_string(),
            );
        }

        let (k_op, k_ty) = self.lower_expr(index, Some(minfo.key_ty))?;
        let k_coerced = self.coerce_operand(k_op, k_ty, minfo.key_ty)?;
        let min_v = variants.iter().map(|(_, v)| *v).min().unwrap_or(0);
        let max_v = variants.iter().map(|(_, v)| *v).max().unwrap_or(0);
        let span = (max_v - min_v + 1) as usize;

        // Dense enum keys -> read-only Global array `[V; N]` with direct O(1) indexing!
        if !variants.is_empty() && span <= variants.len().saturating_mul(2).max(16) && span <= 4096
        {
            let default_val = inst.entries[0].val_const.clone();
            let gl_id = self.get_or_build_dense_map_global(map_id, min_v, span, default_val);
            let arr_ty = self.compiler.intern_type(Type::Array {
                elem: minfo.val_ty,
                len: span as u64,
            });
            let ptr_arr_ty = self.compiler.intern_type(Type::Ptr {
                mutable: false,
                pointee: arr_ty,
            });
            let gl_ptr = self.alloc_temp(ptr_arr_ty);
            self.emit(Statement::Assign(
                Place::new(gl_ptr),
                Rvalue::Use(Operand::Const(ConstValue::Global(gl_id))),
            ));
            let usize_ty = self.compiler.intern_type(Type::Int {
                signed: false,
                bits: 64,
            });
            let idx_local = self.alloc_temp(usize_ty);
            if min_v == 0 {
                self.emit(Statement::Assign(
                    Place::new(idx_local),
                    Rvalue::Cast(k_coerced, usize_ty),
                ));
            } else {
                let i64_ty = self.compiler.intern_type(Type::Int {
                    signed: true,
                    bits: 64,
                });
                let k_i64 = self.alloc_temp(i64_ty);
                self.emit(Statement::Assign(
                    Place::new(k_i64),
                    Rvalue::Cast(k_coerced, i64_ty),
                ));
                let diff = self.alloc_temp(i64_ty);
                self.emit(Statement::Assign(
                    Place::new(diff),
                    Rvalue::BinaryOp(
                        BinOp::SubWrap,
                        Operand::Copy(Place::new(k_i64)),
                        Operand::Const(ConstValue::I64(min_v)),
                    ),
                ));
                self.emit(Statement::Assign(
                    Place::new(idx_local),
                    Rvalue::Cast(Operand::Copy(Place::new(diff)), usize_ty),
                ));
            }
            let mut elem_place = Place::new(gl_ptr);
            elem_place.projections.push(Projection::Deref);
            elem_place.projections.push(Projection::Index(idx_local));
            let out_local = self.alloc_temp(minfo.val_ty);
            self.emit(Statement::Assign(
                Place::new(out_local),
                Rvalue::Use(Operand::Copy(elem_place)),
            ));
            return Ok((Operand::Copy(Place::new(out_local)), minfo.val_ty));
        }

        // Sparse enum keys -> `Terminator::SwitchInt` jump table
        let res_local = self.alloc_temp(minfo.val_ty);
        let join_bb = self.new_block();
        let unreach_bb = self.new_block();
        let mut targets = Vec::with_capacity(inst.entries.len());
        let mut arm_bbs = Vec::with_capacity(inst.entries.len());
        for entry in &inst.entries {
            if let MapKey::Int(k) = entry.key {
                let bb = self.new_block();
                targets.push((k, bb));
                arm_bbs.push((bb, entry.val_const.clone()));
            }
        }
        self.terminate(Terminator::SwitchInt {
            discr: k_coerced,
            targets,
            otherwise: unreach_bb,
        });
        self.body.cur_block = unreach_bb;
        self.terminate(Terminator::Unreachable);
        for (bb, val_c) in arm_bbs {
            self.body.cur_block = bb;
            let op = self.materialize_const_val(val_c, minfo.val_ty);
            self.emit(Statement::Assign(Place::new(res_local), Rvalue::Use(op)));
            self.terminate(Terminator::Goto { target: join_bb });
        }
        self.body.cur_block = join_bb;
        Ok((Operand::Copy(Place::new(res_local)), minfo.val_ty))
    }

    pub(super) fn lower_map_get(
        &mut self,
        map_id: u32,
        key_expr: &Expr,
    ) -> Result<(Operand, TypeId), String> {
        let inst = self.compiler.map_instances[map_id as usize].clone();
        let minfo = self.compiler.maps[&inst.map_ty];
        if matches!(
            self.compiler.program.types[minfo.val_ty.0 as usize],
            Type::MetaType
        ) {
            return Err(
                "Cannot call '.get(k)' on a map with 'type' values; use 'MAP[K]' with a comptime key"
                    .to_string(),
            );
        }
        let u8_ty = self.compiler.intern_type(Type::Int {
            signed: false,
            bits: 8,
        });
        let void_ty = self.compiler.intern_type(Type::Void);
        let opt_ty = self.compiler.intern_type(Type::Union {
            tag: u8_ty,
            variants: vec![void_ty, minfo.val_ty],
        });
        self.compiler.ensure_union_destructor(opt_ty);

        // 1. Constant-fold if the key is a comptime constant
        if let Ok((key, _, _)) = self.compiler.eval_map_key(
            &self.mod_path,
            self.owner_ty,
            &self.comptime_env,
            key_expr,
            Some(minfo.key_ty),
        ) {
            let res_local = self.alloc_temp(opt_ty);
            if let Some(entry) = inst.entries.iter().find(|e| e.key == key) {
                let op = self.materialize_const_val(entry.val_const.clone(), minfo.val_ty);
                self.emit(Statement::Assign(
                    Place::new(res_local),
                    Rvalue::Union {
                        ty: opt_ty,
                        variant: 1,
                        payload: op,
                    },
                ));
            } else {
                self.emit(Statement::Assign(
                    Place::new(res_local),
                    Rvalue::Union {
                        ty: opt_ty,
                        variant: 0,
                        payload: Operand::Const(ConstValue::Void),
                    },
                ));
            }
            return Ok((Operand::Move(Place::new(res_local)), opt_ty));
        }

        let (k_op, k_ty) = self.lower_expr(key_expr, Some(minfo.key_ty))?;
        let k_coerced = self.coerce_operand(k_op, k_ty, minfo.key_ty)?;

        // 2. String (`&str`) keys -> Compiler-Synthesized Perfect Hash Table (PHF) in a read-only `Global`
        if self
            .compiler
            .slices
            .get(&minfo.key_ty)
            .is_some_and(|s| s.is_str)
        {
            return self.lower_phf_str_map_get(map_id, k_coerced, opt_ty);
        }

        // 3. Integer / enum / bool keys -> Dense Global Lookup Array or `Terminator::SwitchInt`
        let mut int_keys = Vec::with_capacity(inst.entries.len());
        for e in &inst.entries {
            match e.key {
                MapKey::Int(n) => int_keys.push(n),
                MapKey::Bool(b) => int_keys.push(i128::from(b)),
                _ => {
                    return Err("Unsupported runtime map key kind".to_string());
                }
            }
        }
        if int_keys.is_empty() {
            let res_local = self.alloc_temp(opt_ty);
            self.emit(Statement::Assign(
                Place::new(res_local),
                Rvalue::Union {
                    ty: opt_ty,
                    variant: 0,
                    payload: Operand::Const(ConstValue::Void),
                },
            ));
            return Ok((Operand::Move(Place::new(res_local)), opt_ty));
        }
        let min_k = *int_keys.iter().min().unwrap();
        let max_k = *int_keys.iter().max().unwrap();
        let span = (max_k - min_k + 1) as usize;
        let is_contiguous = span == inst.entries.len() && inst.entries.len() >= 4 && span <= 4096;

        if is_contiguous {
            let default_val = inst.entries[0].val_const.clone();
            let gl_id = self.get_or_build_dense_map_global(map_id, min_k, span, default_val);
            let arr_ty = self.compiler.intern_type(Type::Array {
                elem: minfo.val_ty,
                len: span as u64,
            });
            let ptr_arr_ty = self.compiler.intern_type(Type::Ptr {
                mutable: false,
                pointee: arr_ty,
            });
            let k_local = self.alloc_temp(minfo.key_ty);
            self.emit(Statement::Assign(
                Place::new(k_local),
                Rvalue::Use(k_coerced),
            ));
            let bool_ty = self.compiler.intern_type(Type::Bool);
            let ge_min = self.alloc_temp(bool_ty);
            self.emit(Statement::Assign(
                Place::new(ge_min),
                Rvalue::BinaryOp(
                    BinOp::Ge,
                    Operand::Copy(Place::new(k_local)),
                    Operand::Const(ConstValue::I64(min_k)),
                ),
            ));
            let le_max = self.alloc_temp(bool_ty);
            self.emit(Statement::Assign(
                Place::new(le_max),
                Rvalue::BinaryOp(
                    BinOp::Le,
                    Operand::Copy(Place::new(k_local)),
                    Operand::Const(ConstValue::I64(max_k)),
                ),
            ));
            let in_range = self.alloc_temp(bool_ty);
            self.emit(Statement::Assign(
                Place::new(in_range),
                Rvalue::BinaryOp(
                    BinOp::BitAnd,
                    Operand::Copy(Place::new(ge_min)),
                    Operand::Copy(Place::new(le_max)),
                ),
            ));
            let res_local = self.alloc_temp(opt_ty);
            let hit_bb = self.new_block();
            let miss_bb = self.new_block();
            let join_bb = self.new_block();
            self.terminate(Terminator::SwitchInt {
                discr: Operand::Copy(Place::new(in_range)),
                targets: vec![(1, hit_bb)],
                otherwise: miss_bb,
            });

            self.body.cur_block = hit_bb;
            let gl_ptr = self.alloc_temp(ptr_arr_ty);
            self.emit(Statement::Assign(
                Place::new(gl_ptr),
                Rvalue::Use(Operand::Const(ConstValue::Global(gl_id))),
            ));
            let usize_ty = self.compiler.intern_type(Type::Int {
                signed: false,
                bits: 64,
            });
            let idx_local = self.alloc_temp(usize_ty);
            if min_k == 0 {
                self.emit(Statement::Assign(
                    Place::new(idx_local),
                    Rvalue::Cast(Operand::Copy(Place::new(k_local)), usize_ty),
                ));
            } else {
                let i64_ty = self.compiler.intern_type(Type::Int {
                    signed: true,
                    bits: 64,
                });
                let k_i64 = self.alloc_temp(i64_ty);
                self.emit(Statement::Assign(
                    Place::new(k_i64),
                    Rvalue::Cast(Operand::Copy(Place::new(k_local)), i64_ty),
                ));
                let diff = self.alloc_temp(i64_ty);
                self.emit(Statement::Assign(
                    Place::new(diff),
                    Rvalue::BinaryOp(
                        BinOp::SubWrap,
                        Operand::Copy(Place::new(k_i64)),
                        Operand::Const(ConstValue::I64(min_k)),
                    ),
                ));
                self.emit(Statement::Assign(
                    Place::new(idx_local),
                    Rvalue::Cast(Operand::Copy(Place::new(diff)), usize_ty),
                ));
            }
            let mut elem_place = Place::new(gl_ptr);
            elem_place.projections.push(Projection::Deref);
            elem_place.projections.push(Projection::Index(idx_local));
            let val_local = self.alloc_temp(minfo.val_ty);
            self.emit(Statement::Assign(
                Place::new(val_local),
                Rvalue::Use(Operand::Copy(elem_place)),
            ));
            self.emit(Statement::Assign(
                Place::new(res_local),
                Rvalue::Union {
                    ty: opt_ty,
                    variant: 1,
                    payload: Operand::Copy(Place::new(val_local)),
                },
            ));
            self.terminate(Terminator::Goto { target: join_bb });

            self.body.cur_block = miss_bb;
            self.emit(Statement::Assign(
                Place::new(res_local),
                Rvalue::Union {
                    ty: opt_ty,
                    variant: 0,
                    payload: Operand::Const(ConstValue::Void),
                },
            ));
            self.terminate(Terminator::Goto { target: join_bb });

            self.body.cur_block = join_bb;
            return Ok((Operand::Move(Place::new(res_local)), opt_ty));
        }

        // Sparse integer / enum / bool keys -> `Terminator::SwitchInt`
        let res_local = self.alloc_temp(opt_ty);
        let miss_bb = self.new_block();
        let join_bb = self.new_block();
        let mut targets = Vec::with_capacity(inst.entries.len());
        let mut arm_bbs = Vec::with_capacity(inst.entries.len());
        for entry in &inst.entries {
            let k_val = match entry.key {
                MapKey::Int(n) => n,
                MapKey::Bool(b) => i128::from(b),
                _ => unreachable!(),
            };
            let bb = self.new_block();
            targets.push((k_val, bb));
            arm_bbs.push((bb, entry.val_const.clone()));
        }
        self.terminate(Terminator::SwitchInt {
            discr: k_coerced,
            targets,
            otherwise: miss_bb,
        });
        for (bb, val_c) in arm_bbs {
            self.body.cur_block = bb;
            let op = self.materialize_const_val(val_c, minfo.val_ty);
            self.emit(Statement::Assign(
                Place::new(res_local),
                Rvalue::Union {
                    ty: opt_ty,
                    variant: 1,
                    payload: op,
                },
            ));
            self.terminate(Terminator::Goto { target: join_bb });
        }
        self.body.cur_block = miss_bb;
        self.emit(Statement::Assign(
            Place::new(res_local),
            Rvalue::Union {
                ty: opt_ty,
                variant: 0,
                payload: Operand::Const(ConstValue::Void),
            },
        ));
        self.terminate(Terminator::Goto { target: join_bb });
        self.body.cur_block = join_bb;
        Ok((Operand::Move(Place::new(res_local)), opt_ty))
    }

    fn fnv1a_str_with_seed(s: &str, seed: u64) -> u64 {
        let mut h = seed;
        for &b in s.as_bytes() {
            h = (h ^ (b as u64)).wrapping_mul(0x100000001b3);
        }
        h
    }

    pub(super) fn get_or_build_phf_str_table(&mut self, map_id: u32) -> PhfTableInfo {
        if let Some(info) = self.compiler.phf_map_globals.get(&map_id).cloned() {
            return info;
        }
        let inst = self.compiler.map_instances[map_id as usize].clone();
        let minfo = self.compiler.maps[&inst.map_ty];
        let n = inst.entries.len();
        let mut table_len = n.next_power_of_two().max(1);
        let chosen_seed: u64;
        let slot_map: Vec<Option<usize>>;

        'search: loop {
            for attempt in 0..10_000u64 {
                let seed = 0xcbf29ce484222325u64.wrapping_add(attempt.wrapping_mul(0x9e3779b97f4a7c15));
                let mut slots = vec![None; table_len];
                let mut ok = true;
                for (idx, e) in inst.entries.iter().enumerate() {
                    let MapKey::Str(ref s) = e.key else {
                        unreachable!()
                    };
                    let h = Self::fnv1a_str_with_seed(s, seed);
                    let bucket = (h as usize) & (table_len - 1);
                    if slots[bucket].is_some() {
                        ok = false;
                        break;
                    }
                    slots[bucket] = Some(idx);
                }
                if ok {
                    chosen_seed = seed;
                    slot_map = slots;
                    break 'search;
                }
            }
            table_len *= 2;
        }

        let str_ty = self.compiler.intern_str_type();
        let entry_ty = self
            .compiler
            .intern_type(Type::Struct(vec![str_ty, minfo.val_ty]));
        let default_val = inst
            .entries
            .first()
            .map(|e| e.val_const.clone())
            .unwrap_or(ConstValue::I64(0));
        let empty_str_cv = ConstValue::Aggregate(vec![
            ConstValue::Str(String::new()),
            ConstValue::I64(0),
        ]);
        let mut table_elems = Vec::with_capacity(table_len);
        for slot in slot_map {
            if let Some(e_idx) = slot {
                let e = &inst.entries[e_idx];
                let MapKey::Str(ref s) = e.key else {
                    unreachable!()
                };
                let key_cv = ConstValue::Aggregate(vec![
                    ConstValue::Str(s.clone()),
                    ConstValue::I64(s.len() as i128),
                ]);
                table_elems.push(ConstValue::Aggregate(vec![key_cv, e.val_const.clone()]));
            } else {
                table_elems.push(ConstValue::Aggregate(vec![
                    empty_str_cv.clone(),
                    default_val.clone(),
                ]));
            }
        }
        let arr_ty = self.compiler.intern_type(Type::Array {
            elem: entry_ty,
            len: table_len as u64,
        });
        let gl_id = GlobalId(self.compiler.program.globals.len() as u32);
        self.compiler.program.globals.push(crate::ir::Global {
            id: gl_id,
            ty: arr_ty,
            init: ConstValue::Aggregate(table_elems),
            mutable: false,
        });
        let info = PhfTableInfo {
            global_id: gl_id,
            seed: chosen_seed,
            table_len,
            entry_ty,
        };
        self.compiler.phf_map_globals.insert(map_id, info);
        info
    }

    fn lower_phf_str_map_get(
        &mut self,
        map_id: u32,
        k_op: Operand,
        opt_ty: TypeId,
    ) -> Result<(Operand, TypeId), String> {
        let inst = self.compiler.map_instances[map_id as usize].clone();
        let minfo = self.compiler.maps[&inst.map_ty];
        let res_local = self.alloc_temp(opt_ty);
        if inst.entries.is_empty() {
            self.emit(Statement::Assign(
                Place::new(res_local),
                Rvalue::Union {
                    ty: opt_ty,
                    variant: 0,
                    payload: Operand::Const(ConstValue::Void),
                },
            ));
            return Ok((Operand::Move(Place::new(res_local)), opt_ty));
        }

        let phf = self.get_or_build_phf_str_table(map_id);
        let str_ty = self.compiler.intern_str_type();
        let usize_ty = self.compiler.intern_type(Type::Int {
            signed: false,
            bits: 64,
        });
        let u8_ty = self.compiler.intern_type(Type::Int {
            signed: false,
            bits: 8,
        });
        let bool_ty = self.compiler.intern_type(Type::Bool);

        let key_local = self.alloc_temp(str_ty);
        self.emit(Statement::Assign(Place::new(key_local), Rvalue::Use(k_op)));

        let mut key_len_place = Place::new(key_local);
        key_len_place.projections.push(Projection::Field(1));
        let key_len = self.alloc_temp(usize_ty);
        self.emit(Statement::Assign(
            Place::new(key_len),
            Rvalue::Use(Operand::Copy(key_len_place)),
        ));

        // Compute FNV-1a hash over `key_local` bytes
        let hash_local = self.alloc_temp(usize_ty);
        self.emit(Statement::Assign(
            Place::new(hash_local),
            Rvalue::Use(Operand::Const(ConstValue::I64(phf.seed as i128))),
        ));
        let i_local = self.alloc_temp(usize_ty);
        self.emit(Statement::Assign(
            Place::new(i_local),
            Rvalue::Use(Operand::Const(ConstValue::I64(0))),
        ));

        let hash_cond_bb = self.new_block();
        let hash_body_bb = self.new_block();
        let hash_done_bb = self.new_block();
        self.terminate(Terminator::Goto {
            target: hash_cond_bb,
        });

        self.body.cur_block = hash_cond_bb;
        let cmp_i = self.alloc_temp(bool_ty);
        self.emit(Statement::Assign(
            Place::new(cmp_i),
            Rvalue::BinaryOp(
                BinOp::Lt,
                Operand::Copy(Place::new(i_local)),
                Operand::Copy(Place::new(key_len)),
            ),
        ));
        self.terminate(Terminator::SwitchInt {
            discr: Operand::Copy(Place::new(cmp_i)),
            targets: vec![(1, hash_body_bb)],
            otherwise: hash_done_bb,
        });

        self.body.cur_block = hash_body_bb;
        let mut kb_place = Place::new(key_local);
        kb_place.projections.push(Projection::Field(0));
        kb_place.projections.push(Projection::Deref);
        kb_place.projections.push(Projection::Index(i_local));
        let b_val = self.alloc_temp(u8_ty);
        self.emit(Statement::Assign(
            Place::new(b_val),
            Rvalue::Use(Operand::Copy(kb_place)),
        ));
        let b_u64 = self.alloc_temp(usize_ty);
        self.emit(Statement::Assign(
            Place::new(b_u64),
            Rvalue::Cast(Operand::Copy(Place::new(b_val)), usize_ty),
        ));
        let xored = self.alloc_temp(usize_ty);
        self.emit(Statement::Assign(
            Place::new(xored),
            Rvalue::BinaryOp(
                BinOp::BitXor,
                Operand::Copy(Place::new(hash_local)),
                Operand::Copy(Place::new(b_u64)),
            ),
        ));
        self.emit(Statement::Assign(
            Place::new(hash_local),
            Rvalue::BinaryOp(
                BinOp::MulWrap,
                Operand::Copy(Place::new(xored)),
                Operand::Const(ConstValue::I64(0x100000001b3)),
            ),
        ));
        self.emit(Statement::Assign(
            Place::new(i_local),
            Rvalue::BinaryOp(
                BinOp::AddWrap,
                Operand::Copy(Place::new(i_local)),
                Operand::Const(ConstValue::I64(1)),
            ),
        ));
        self.terminate(Terminator::Goto {
            target: hash_cond_bb,
        });

        // Index into PHF table at `bucket = hash & (table_len - 1)`
        self.body.cur_block = hash_done_bb;
        let bucket_local = self.alloc_temp(usize_ty);
        self.emit(Statement::Assign(
            Place::new(bucket_local),
            Rvalue::BinaryOp(
                BinOp::BitAnd,
                Operand::Copy(Place::new(hash_local)),
                Operand::Const(ConstValue::I64((phf.table_len - 1) as i128)),
            ),
        ));

        let arr_ty = self.compiler.intern_type(Type::Array {
            elem: phf.entry_ty,
            len: phf.table_len as u64,
        });
        let ptr_arr_ty = self.compiler.intern_type(Type::Ptr {
            mutable: false,
            pointee: arr_ty,
        });
        let gl_ptr = self.alloc_temp(ptr_arr_ty);
        self.emit(Statement::Assign(
            Place::new(gl_ptr),
            Rvalue::Use(Operand::Const(ConstValue::Global(phf.global_id))),
        ));

        let mut slot_place = Place::new(gl_ptr);
        slot_place.projections.push(Projection::Deref);
        slot_place
            .projections
            .push(Projection::Index(bucket_local));
        let slot_local = self.alloc_temp(phf.entry_ty);
        self.emit(Statement::Assign(
            Place::new(slot_local),
            Rvalue::Use(Operand::Copy(slot_place)),
        ));

        let mut cand_key_place = Place::new(slot_local);
        cand_key_place.projections.push(Projection::Field(0));
        let cand_key = self.alloc_temp(str_ty);
        self.emit(Statement::Assign(
            Place::new(cand_key),
            Rvalue::Use(Operand::Copy(cand_key_place)),
        ));

        let mut cand_len_place = Place::new(cand_key);
        cand_len_place.projections.push(Projection::Field(1));
        let cand_len = self.alloc_temp(usize_ty);
        self.emit(Statement::Assign(
            Place::new(cand_len),
            Rvalue::Use(Operand::Copy(cand_len_place)),
        ));

        // Verify `cand_len == key_len` and all bytes match
        let len_eq = self.alloc_temp(bool_ty);
        self.emit(Statement::Assign(
            Place::new(len_eq),
            Rvalue::BinaryOp(
                BinOp::Eq,
                Operand::Copy(Place::new(cand_len)),
                Operand::Copy(Place::new(key_len)),
            ),
        ));
        let eq_loop_init_bb = self.new_block();
        let eq_cond_bb = self.new_block();
        let eq_body_bb = self.new_block();
        let hit_bb = self.new_block();
        let miss_bb = self.new_block();
        let join_bb = self.new_block();

        self.terminate(Terminator::SwitchInt {
            discr: Operand::Copy(Place::new(len_eq)),
            targets: vec![(1, eq_loop_init_bb)],
            otherwise: miss_bb,
        });

        self.body.cur_block = eq_loop_init_bb;
        let j_local = self.alloc_temp(usize_ty);
        self.emit(Statement::Assign(
            Place::new(j_local),
            Rvalue::Use(Operand::Const(ConstValue::I64(0))),
        ));
        self.terminate(Terminator::Goto { target: eq_cond_bb });

        self.body.cur_block = eq_cond_bb;
        let cmp_j = self.alloc_temp(bool_ty);
        self.emit(Statement::Assign(
            Place::new(cmp_j),
            Rvalue::BinaryOp(
                BinOp::Lt,
                Operand::Copy(Place::new(j_local)),
                Operand::Copy(Place::new(key_len)),
            ),
        ));
        self.terminate(Terminator::SwitchInt {
            discr: Operand::Copy(Place::new(cmp_j)),
            targets: vec![(1, eq_body_bb)],
            otherwise: hit_bb,
        });

        self.body.cur_block = eq_body_bb;
        let mut kb2_place = Place::new(key_local);
        kb2_place.projections.push(Projection::Field(0));
        kb2_place.projections.push(Projection::Deref);
        kb2_place.projections.push(Projection::Index(j_local));
        let kb2 = self.alloc_temp(u8_ty);
        self.emit(Statement::Assign(
            Place::new(kb2),
            Rvalue::Use(Operand::Copy(kb2_place)),
        ));
        let mut cb2_place = Place::new(cand_key);
        cb2_place.projections.push(Projection::Field(0));
        cb2_place.projections.push(Projection::Deref);
        cb2_place.projections.push(Projection::Index(j_local));
        let cb2 = self.alloc_temp(u8_ty);
        self.emit(Statement::Assign(
            Place::new(cb2),
            Rvalue::Use(Operand::Copy(cb2_place)),
        ));
        let byte_eq = self.alloc_temp(bool_ty);
        self.emit(Statement::Assign(
            Place::new(byte_eq),
            Rvalue::BinaryOp(
                BinOp::Eq,
                Operand::Copy(Place::new(kb2)),
                Operand::Copy(Place::new(cb2)),
            ),
        ));
        let next_j_bb = self.new_block();
        self.terminate(Terminator::SwitchInt {
            discr: Operand::Copy(Place::new(byte_eq)),
            targets: vec![(1, next_j_bb)],
            otherwise: miss_bb,
        });

        self.body.cur_block = next_j_bb;
        self.emit(Statement::Assign(
            Place::new(j_local),
            Rvalue::BinaryOp(
                BinOp::AddWrap,
                Operand::Copy(Place::new(j_local)),
                Operand::Const(ConstValue::I64(1)),
            ),
        ));
        self.terminate(Terminator::Goto { target: eq_cond_bb });

        self.body.cur_block = hit_bb;
        let mut val_place = Place::new(slot_local);
        val_place.projections.push(Projection::Field(1));
        let hit_val = self.alloc_temp(minfo.val_ty);
        self.emit(Statement::Assign(
            Place::new(hit_val),
            Rvalue::Use(Operand::Copy(val_place)),
        ));
        self.emit(Statement::Assign(
            Place::new(res_local),
            Rvalue::Union {
                ty: opt_ty,
                variant: 1,
                payload: Operand::Copy(Place::new(hit_val)),
            },
        ));
        self.terminate(Terminator::Goto { target: join_bb });

        self.body.cur_block = miss_bb;
        self.emit(Statement::Assign(
            Place::new(res_local),
            Rvalue::Union {
                ty: opt_ty,
                variant: 0,
                payload: Operand::Const(ConstValue::Void),
            },
        ));
        self.terminate(Terminator::Goto { target: join_bb });

        self.body.cur_block = join_bb;
        Ok((Operand::Move(Place::new(res_local)), opt_ty))
    }

    pub(super) fn lower_str_eq(
        &mut self,
        l_op: Operand,
        l_ty: TypeId,
        r_op: Operand,
        r_ty: TypeId,
        is_ne: bool,
    ) -> Result<(Operand, TypeId), String> {
        let str_ty = self.compiler.intern_str_type();
        let bool_ty = self.compiler.intern_type(Type::Bool);
        let usize_ty = self.compiler.intern_type(Type::Int {
            signed: false,
            bits: 64,
        });
        let u8_ty = self.compiler.intern_type(Type::Int {
            signed: false,
            bits: 8,
        });

        let a_coerced = self.coerce_operand(l_op, l_ty, str_ty)?;
        let b_coerced = self.coerce_operand(r_op, r_ty, str_ty)?;
        let a_local = self.alloc_temp(str_ty);
        self.emit(Statement::Assign(Place::new(a_local), Rvalue::Use(a_coerced)));
        let b_local = self.alloc_temp(str_ty);
        self.emit(Statement::Assign(Place::new(b_local), Rvalue::Use(b_coerced)));

        let mut a_len_p = Place::new(a_local);
        a_len_p.projections.push(Projection::Field(1));
        let a_len = self.alloc_temp(usize_ty);
        self.emit(Statement::Assign(
            Place::new(a_len),
            Rvalue::Use(Operand::Copy(a_len_p)),
        ));
        let mut b_len_p = Place::new(b_local);
        b_len_p.projections.push(Projection::Field(1));
        let b_len = self.alloc_temp(usize_ty);
        self.emit(Statement::Assign(
            Place::new(b_len),
            Rvalue::Use(Operand::Copy(b_len_p)),
        ));

        let len_eq = self.alloc_temp(bool_ty);
        self.emit(Statement::Assign(
            Place::new(len_eq),
            Rvalue::BinaryOp(
                BinOp::Eq,
                Operand::Copy(Place::new(a_len)),
                Operand::Copy(Place::new(b_len)),
            ),
        ));

        let res_local = self.alloc_temp(bool_ty);
        let loop_init_bb = self.new_block();
        let cond_bb = self.new_block();
        let body_bb = self.new_block();
        let next_bb = self.new_block();
        let hit_bb = self.new_block();
        let miss_bb = self.new_block();
        let join_bb = self.new_block();

        self.terminate(Terminator::SwitchInt {
            discr: Operand::Copy(Place::new(len_eq)),
            targets: vec![(1, loop_init_bb)],
            otherwise: miss_bb,
        });

        self.body.cur_block = loop_init_bb;
        let i_local = self.alloc_temp(usize_ty);
        self.emit(Statement::Assign(
            Place::new(i_local),
            Rvalue::Use(Operand::Const(ConstValue::I64(0))),
        ));
        self.terminate(Terminator::Goto { target: cond_bb });

        self.body.cur_block = cond_bb;
        let cmp_i = self.alloc_temp(bool_ty);
        self.emit(Statement::Assign(
            Place::new(cmp_i),
            Rvalue::BinaryOp(
                BinOp::Lt,
                Operand::Copy(Place::new(i_local)),
                Operand::Copy(Place::new(a_len)),
            ),
        ));
        self.terminate(Terminator::SwitchInt {
            discr: Operand::Copy(Place::new(cmp_i)),
            targets: vec![(1, body_bb)],
            otherwise: hit_bb,
        });

        self.body.cur_block = body_bb;
        let mut ab_p = Place::new(a_local);
        ab_p.projections.push(Projection::Field(0));
        ab_p.projections.push(Projection::Deref);
        ab_p.projections.push(Projection::Index(i_local));
        let ab = self.alloc_temp(u8_ty);
        self.emit(Statement::Assign(Place::new(ab), Rvalue::Use(Operand::Copy(ab_p))));

        let mut bb_p = Place::new(b_local);
        bb_p.projections.push(Projection::Field(0));
        bb_p.projections.push(Projection::Deref);
        bb_p.projections.push(Projection::Index(i_local));
        let bb = self.alloc_temp(u8_ty);
        self.emit(Statement::Assign(Place::new(bb), Rvalue::Use(Operand::Copy(bb_p))));

        let byte_eq = self.alloc_temp(bool_ty);
        self.emit(Statement::Assign(
            Place::new(byte_eq),
            Rvalue::BinaryOp(
                BinOp::Eq,
                Operand::Copy(Place::new(ab)),
                Operand::Copy(Place::new(bb)),
            ),
        ));
        self.terminate(Terminator::SwitchInt {
            discr: Operand::Copy(Place::new(byte_eq)),
            targets: vec![(1, next_bb)],
            otherwise: miss_bb,
        });

        self.body.cur_block = next_bb;
        self.emit(Statement::Assign(
            Place::new(i_local),
            Rvalue::BinaryOp(
                BinOp::AddWrap,
                Operand::Copy(Place::new(i_local)),
                Operand::Const(ConstValue::I64(1)),
            ),
        ));
        self.terminate(Terminator::Goto { target: cond_bb });

        self.body.cur_block = hit_bb;
        self.emit(Statement::Assign(
            Place::new(res_local),
            Rvalue::Use(Operand::Const(ConstValue::Bool(!is_ne))),
        ));
        self.terminate(Terminator::Goto { target: join_bb });

        self.body.cur_block = miss_bb;
        self.emit(Statement::Assign(
            Place::new(res_local),
            Rvalue::Use(Operand::Const(ConstValue::Bool(is_ne))),
        ));
        self.terminate(Terminator::Goto { target: join_bb });

        self.body.cur_block = join_bb;
        Ok((Operand::Copy(Place::new(res_local)), bool_ty))
    }
}

/// A place expression whose lowering has no effects: a variable, or fields and dereferences of one.
fn is_pure_place(e: &Expr) -> bool {
    match e {
        Expr::Path(_) => true,
        Expr::Field { base, .. } | Expr::TupleIndex { base, .. } => is_pure_place(base),
        Expr::Deref(inner) => is_pure_place(inner),
        _ => false,
    }
}

/// What a failed `@assert` says: its message, or that it failed, and where it is written.
pub(super) fn assertion_message(message: Option<&str>, pos: crate::ir::Pos, mod_path: &str) -> String {
    let module = if mod_path == "root" { String::new() } else { format!(" of module '{mod_path}'") };
    match message {
        Some(m) => format!("assertion failed: {m} ({pos}{module})"),
        None => format!("assertion failed ({pos}{module})"),
    }
}
