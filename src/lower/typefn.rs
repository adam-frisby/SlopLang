//! Type functions (`fn F[T] -> type`) run on the compile-time VM.
//!
//! A call `F(args)` instantiates `F` for its arguments and lowers it like any other function, so
//! its statements, loops, locals, and recursion execute on the VM with its step limit. Building
//! a type, though, is the compiler's job: each expression that yields a type (`[T; N]`,
//! `opaque { ... }`, `@Struct(&specs)`, a call of another type function) is lowered to a call of
//! a host function (see `vm::HOST_PREFIX`). The VM suspends there, the compiler evaluates the
//! expression (`HostThunk`) in the function's compile-time environment plus the current values
//! of the locals it names, and the VM resumes with the type. Types are therefore built only on
//! the path the function actually takes, as `if N == 0 { return void; } return List(N - 1);`
//! requires.

use super::comptime::{comptime_to_vm_value, vm_value_to_comptime};
use super::*;
use crate::vm::{HOST_PREFIX, Value, Vm, VmExit};

/// A type-building step of a type function, evaluated by the compiler when the VM reaches it.
#[derive(Debug, Clone)]
pub(super) struct HostThunk {
    mod_path: String,
    /// The compile-time environment where the expression appears (parameters, `comptime let`
    /// bindings, unrolled `comptime for` variables).
    env: HashMap<String, ComptimeVal>,
    /// Names and types of the runtime locals passed as the host call's arguments.
    captured: Vec<(String, TypeId)>,
    kind: ThunkKind,
}

#[derive(Debug, Clone)]
enum ThunkKind {
    /// An expression of type `type`.
    Eval(Expr),
    /// The type literal a type function returns: a nominal type is named after the function
    /// and memoized under its arguments.
    Returned {
        te: TypeExpr,
        fname: String,
        args: Vec<ComptimeVal>,
    },
}

impl<'a> FuncLowerer<'a> {
    /// In a type function: whether `expr` builds a type, and so runs on the compiler when the
    /// VM reaches it rather than when the function is lowered.
    pub(super) fn is_deferred_type_expr(&self, expr: &Expr) -> bool {
        if self.type_fn.is_none() {
            return false;
        }
        match expr {
            Expr::IntrinsicCompileError(_) => true,
            Expr::TypeVal(te) => !matches!(
                te,
                TypeExpr::Void
                    | TypeExpr::Never
                    | TypeExpr::Bool
                    | TypeExpr::Rune
                    | TypeExpr::F32
                    | TypeExpr::F64
                    | TypeExpr::Isize
                    | TypeExpr::Usize
                    | TypeExpr::Int { .. }
                    | TypeExpr::CInt(_)
                    | TypeExpr::StrRef
                    | TypeExpr::MetaType
            ),
            Expr::Index { .. } => self.index_type_call(expr).is_some(),
            Expr::Call { callee, .. } => {
                let Expr::Path(p) = callee.as_ref() else {
                    return false;
                };
                if p.len() == 1 && self.lookup_var(&p[0]).is_some() {
                    return false;
                }
                let expanded = self.compiler.expand_module_path(&self.comptime_env, p);
                let Ok(ResolvedItem::Func(fmod, fname)) =
                    self.compiler.resolve_path(&self.mod_path, &expanded)
                else {
                    return false;
                };
                matches!(
                    self.compiler.find_item_in_module(&self.mod_path, &fmod, &fname),
                    Ok(Some((_, _, Item::Func(decl), _))) if decl.ret_ty == TypeExpr::MetaType
                )
            }
            _ => false,
        }
    }

    /// Lowers a type-building expression of a type function to a host call.
    pub(super) fn lower_deferred_type_expr(
        &mut self,
        expr: &Expr,
    ) -> Result<(Operand, TypeId), String> {
        self.lower_host_thunk(ThunkKind::Eval(expr.clone()))
    }

    /// The value of `return expr` in a function returning `ret_ty`: in a type function, a
    /// returned type literal becomes the function's own (named, memoized) type.
    pub(super) fn lower_returned_expr(
        &mut self,
        expr: &Expr,
        ret_ty: TypeId,
    ) -> Result<(Operand, TypeId), String> {
        // `&T` of a compile-time type is that reference type, not a reference to a value.
        let reference;
        let expr = match expr {
            Expr::Ref { mutable, expr: inner }
                if self.type_fn.is_some()
                    && matches!(&**inner, Expr::Path(p) if p.len() == 1
                        && matches!(self.comptime_env.get(&p[0]), Some(ComptimeVal::Type(_)))) =>
            {
                let Expr::Path(path) = &**inner else { unreachable!() };
                reference = Expr::TypeVal(TypeExpr::Ref {
                    mutable: *mutable,
                    inner: Box::new(TypeExpr::Named(path.clone())),
                });
                &reference
            }
            _ => expr,
        };
        if let Some((fname, args)) = self.type_fn.clone()
            && let Expr::TypeVal(te) = expr
        {
            return self.lower_host_thunk(ThunkKind::Returned {
                te: te.clone(),
                fname,
                args,
            });
        }
        self.lower_expr(expr, Some(ret_ty))
    }

    /// A call of a new host function evaluating `kind`, passed the runtime locals it names.
    fn lower_host_thunk(&mut self, kind: ThunkKind) -> Result<(Operand, TypeId), String> {
        let meta_ty = self.compiler.intern_type(Type::MetaType);
        // The locals the expression names: its `Debug` form quotes every identifier, so this
        // may over-approximate (a field spelled like a local), never miss one.
        let text = format!("{kind:?}");
        let mut captured: Vec<(String, LocalId, TypeId)> = Vec::new();
        for v in self.scopes.iter().flatten() {
            captured.retain(|(n, _, _)| *n != v.name);
            if text.contains(&format!("\"{}\"", v.name)) {
                captured.push((v.name.clone(), v.local, v.ty));
            }
        }
        for c in &mut captured {
            if self.is_open_type_var(c.2) {
                self.default_type_var(c.2, true)?;
            }
            c.2 = self.resolve_type_var(c.2);
        }
        let idx = self.compiler.host_thunks.len();
        self.compiler.host_thunks.push(HostThunk {
            mod_path: self.mod_path.clone(),
            env: self.comptime_env.clone(),
            captured: captured.iter().map(|(n, _, t)| (n.clone(), *t)).collect(),
            kind,
        });
        let arg_tys = captured.iter().map(|c| c.2).collect();
        let fn_id = self.compiler.get_or_register_builtin_extern(
            &format!("{HOST_PREFIX}{idx}"),
            arg_tys,
            meta_ty,
        );
        let args = captured
            .iter()
            .map(|c| Operand::Copy(Place::new(c.1)))
            .collect();
        let dst = self.emit_call_to(fn_id, args, meta_ty);
        Ok((Operand::Copy(Place::new(dst)), meta_ty))
    }
}

impl Compiler {
    /// Runs the type function `def_mod::fname` (declared by `decl`) for `args` on the VM.
    pub(super) fn eval_type_fn_on_vm(
        &mut self,
        def_mod: &str,
        fname: &str,
        decl: &FuncDecl,
        args: &[ComptimeVal],
    ) -> Result<ComptimeVal, String> {
        if decl.params.len() != args.len() {
            return Err(format!(
                "Comptime function '{fname}' expects {} args, got {}",
                decl.params.len(),
                args.len()
            ));
        }
        let mut ct_args = Vec::new();
        let mut rt_args = Vec::new();
        for (p, a) in decl.params.iter().zip(args) {
            if p.is_comptime {
                ct_args.push(a.clone());
            } else {
                rt_args.push(comptime_to_vm_value(a).ok_or_else(|| {
                    format!(
                        "Argument for parameter '{}' of '{fname}' cannot be passed to a compile-time call",
                        p.name
                    )
                })?);
            }
        }
        let fn_id = self.get_or_instantiate_func(def_mod, fname, &ct_args)?;
        self.type_fn_instances
            .insert(fn_id, (fname.to_string(), args.to_vec()));
        self.lower_for_comptime(fn_id)?;

        let failed = |e: String| format!("Compile-time evaluation of '{fname}' failed: {e}");
        let mut vm = Vm::new(&mut self.program);
        let mut exit = vm.start_call(fn_id, rt_args).map_err(failed)?;
        let mut state = vm.into_state();
        loop {
            match exit {
                VmExit::Return(v) => {
                    return vm_value_to_comptime(&v).ok_or_else(|| {
                        format!("Comptime function '{fname}' did not return a type: {v:?}")
                    });
                }
                VmExit::Host { symbol, args } => {
                    let result = self.answer_host_call(&symbol, args)?;
                    let mut vm = Vm::from_state(&mut self.program, state);
                    exit = vm.resume(result).map_err(failed)?;
                    state = vm.into_state();
                }
            }
        }
    }

    /// Evaluates the host thunk named by `symbol` with the VM's `args` (see `HostThunk`).
    fn answer_host_call(&mut self, symbol: &str, args: Vec<Value>) -> Result<Value, String> {
        let idx: usize = symbol[HOST_PREFIX.len()..]
            .parse()
            .map_err(|_| format!("Unknown host function '{symbol}'"))?;
        let thunk = self.host_thunks[idx].clone();
        let mut env = thunk.env;
        for ((name, ty), v) in thunk.captured.iter().zip(&args) {
            // A local not yet holding a compile-time value (unassigned, or a runtime-only
            // value) is left out; naming it in the expression reports it as unknown.
            if let Some(cv) = self.vm_value_to_comptime_typed(v, *ty) {
                env.insert(name.clone(), cv);
            }
        }
        let ty = match &thunk.kind {
            ThunkKind::Returned { te, fname, args } => {
                self.instantiate_returned_type(&thunk.mod_path, fname, args, te, &env)?
            }
            ThunkKind::Eval(expr) => {
                match self.eval_comptime_val(&thunk.mod_path, None, &env, expr)? {
                    ComptimeVal::Type(t) => t,
                    other => {
                        return Err(format!(
                            "Expected a type, found {}",
                            self.comptime_val_label(&other)
                        ));
                    }
                }
            }
        };
        Ok(Value::Type(ty))
    }

    /// The type a type function `fname(args)` returns for the literal `te`: nominal types are
    /// named `fname` and memoized under `(module, fname, args)`.
    fn instantiate_returned_type(
        &mut self,
        mod_path: &str,
        fname: &str,
        args: &[ComptimeVal],
        te: &TypeExpr,
        env: &HashMap<String, ComptimeVal>,
    ) -> Result<TypeId, String> {
        if !Self::is_reservable(te) {
            return self.instantiate_returned_literal(mod_path, fname, args, te, env);
        }
        let key = (mod_path.to_string(), fname.to_string(), args.to_vec());
        let id = match self.reserved_calls.remove(&key) {
            Some(id) => id,
            None => self.alloc_distinct_type(Type::Void),
        };
        self.memoized_type_calls.insert(key.clone(), id);
        let built = self.with_reserved_type(id, |c| {
            c.instantiate_returned_literal(mod_path, fname, args, te, env)
        });
        if built.is_err() {
            self.memoized_type_calls.remove(&key);
        }
        built
    }

    fn instantiate_returned_literal(
        &mut self,
        mod_path: &str,
        fname: &str,
        args: &[ComptimeVal],
        te: &TypeExpr,
        env: &HashMap<String, ComptimeVal>,
    ) -> Result<TypeId, String> {
        let memo_key = Some((mod_path.to_string(), fname.to_string(), args.to_vec()));
        match te {
            TypeExpr::BareOpaque => {
                self.instantiate_named_opaque(mod_path, fname, env, memo_key, &[])
            }
            TypeExpr::OpaqueDef { methods } => {
                self.instantiate_named_opaque(mod_path, fname, env, memo_key, methods)
            }
            TypeExpr::Distinct {
                underlying,
                methods,
            } => self.instantiate_distinct_type(
                mod_path, fname, env, memo_key, underlying, methods,
            ),
            TypeExpr::Trait(methods) => {
                self.instantiate_trait(mod_path, fname, env, memo_key, methods)
            }
            TypeExpr::Enum { backing, variants } => {
                let ty_id = self.instantiate_enum(
                    mod_path,
                    None,
                    env,
                    fname,
                    backing.as_deref(),
                    variants,
                )?;
                if let Some(key) = memo_key {
                    self.memoized_type_calls.insert(key, ty_id);
                }
                Ok(ty_id)
            }
            TypeExpr::Union { backing, variants } => self.instantiate_union(
                mod_path,
                fname,
                env,
                memo_key,
                backing.as_deref(),
                variants,
            ),
            TypeExpr::Overlay(fields) => {
                self.instantiate_overlay(mod_path, fname, env, memo_key, fields)
            }
            TypeExpr::Error {
                backing,
                ok_flag,
                variants,
            } => self.instantiate_error(
                mod_path,
                fname,
                env,
                memo_key,
                backing.as_deref(),
                ok_flag.as_ref(),
                variants,
            ),
            TypeExpr::Struct {
                is_packed,
                fields,
                methods,
            } => self.instantiate_composite(
                mod_path,
                fname,
                false,
                *is_packed,
                OpaqueOwnership::Copy,
                ThreadDecl::default(),
                env,
                memo_key,
                fields,
                &[],
                &[],
                methods,
                None,
                &[],
                &[],
                None,
                DeclaredContents::default(),
            ),
            TypeExpr::Opaque(body) => {
                self.instantiate_opaque_body(mod_path, fname, env, memo_key, body)
            }
            other => self.resolve_type_expr(mod_path, None, env, other),
        }
    }

    /// A VM value of IR type `ty` as a compile-time value: records for named structs, lists for
    /// arrays, strings for `&str` (`None` for values with no compile-time form).
    fn vm_value_to_comptime_typed(&self, v: &Value, ty: TypeId) -> Option<ComptimeVal> {
        if let Some(cv) = vm_value_to_comptime(v) {
            return Some(cv);
        }
        match (v, &self.program.types[ty.0 as usize]) {
            (Value::Array(items), Type::Array { elem, .. }) => {
                let elem = *elem;
                let items = items
                    .iter()
                    .map(|i| self.vm_value_to_comptime_typed(i, elem))
                    .collect::<Option<Vec<_>>>()?;
                Some(ComptimeVal::List(items, Some(elem)))
            }
            (Value::Struct { fields, .. }, Type::Struct(field_tys)) => {
                if self.slices.get(&ty).is_some_and(|s| s.is_str) {
                    let (Value::Str(s), Value::Int(len)) = (&fields[0], &fields[1]) else {
                        return None;
                    };
                    return Some(ComptimeVal::Str(s.get(..*len as usize)?.to_string()));
                }
                let vals = fields
                    .iter()
                    .zip(field_tys)
                    .map(|(f, &fty)| self.vm_value_to_comptime_typed(f, fty))
                    .collect::<Option<Vec<_>>>()?;
                match self.composites.get(&ty) {
                    Some(comp) => Some(ComptimeVal::Record(
                        comp.fields
                            .iter()
                            .map(|(n, _, _, _)| n.clone())
                            .zip(vals)
                            .collect(),
                    )),
                    None => Some(ComptimeVal::Tuple(vals)),
                }
            }
            _ => None,
        }
    }
}
