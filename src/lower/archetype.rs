//! Checking a generic body against its bounds, before and apart from any use of it.
//!
//! A type parameter promises its bounds and nothing more, so a generic is checked by instantiating
//! it with an *archetype* for each type parameter: a type made here that has exactly what the bounds
//! say (the methods of a bound trait, `copy` if bound by `copy`, ...) and nothing else. A body that
//! uses more fails, whether or not anything calls it. Duck typing is opt-in: a parameter declared
//! `[T: unchecked]` may be used as anything, and is checked only where it is used.

use super::*;

/// What a generic parameter stands for while its generic is checked.
enum Stand {
    /// An archetype or a representative, shown as the string in errors.
    Arg(ComptimeVal),
    /// `unchecked`, or a bound an archetype cannot model: the generic is checked where it is used.
    Skip,
}

impl Compiler {
    /// Checks every generic function, and every generic type declared with brackets, in the
    /// program's modules (or, with `std_too`, in std's) against its bounds.
    pub(super) fn check_generic_bodies(&mut self, std_too: bool) -> Result<(), String> {
        let mut mod_names: Vec<String> = self
            .modules
            .keys()
            .filter(|m| std_too || !crate::stdlib::is_stdlib_module(m))
            .cloned()
            .collect();
        mod_names.sort();
        for mod_path in mod_names {
            let decls: Vec<FuncDecl> = self.modules[&mod_path]
                .items
                .iter()
                .filter_map(|item| match item {
                    Item::Func(f) if f.params.iter().any(|p| p.is_comptime) => Some(f.clone()),
                    _ => None,
                })
                .collect();
            for decl in decls {
                let is_type = decl.ret_ty == TypeExpr::MetaType;
                // Of the functions that make types, only a declared generic type is checked: one
                // that computes a type is code to run, not a template.
                if is_type
                    && !matches!(decl.body.stmts.as_slice(), [Stmt::Return(Some(Expr::TypeVal(te)))] if Self::is_reservable(te))
                {
                    continue;
                }
                let mut sandbox = self.clone();
                let Some(args) = sandbox.archetype_args(&mod_path, &decl)? else {
                    continue;
                };
                let checked = sandbox.program.functions.len();
                let instantiated = if is_type {
                    sandbox.eval_comptime_type_func(&mod_path, &decl.name, &args).map(|_| ())
                } else {
                    // This declaration, not whichever overload its name resolves to for `args`.
                    sandbox.instantiate_specific_func_decl(&mod_path, &decl, &args).map(|_| ())
                };
                let res = instantiated
                    .and_then(|_| sandbox.lower_pending_funcs())
                    .and_then(|_| elaborate_drops_from(&mut sandbox.program, checked))
                    .and_then(|_| check_borrows(&sandbox.program));
                if let Err(e) = res {
                    let first = e.lines().next().unwrap_or_default();
                    let params: Vec<&str> = decl
                        .params
                        .iter()
                        .filter(|p| p.is_comptime)
                        .map(|p| p.name.as_str())
                        .collect();
                    return Err(format!(
                        "Generic '{mod_path}::{}' uses its type parameters beyond what their bounds promise: {first}. State what it needs as a bound (a trait, or a constraint such as 'integer' or 'copy'), or declare a parameter 'unchecked' (as in '[{}: unchecked]') to check it only where it is used",
                        decl.name,
                        params.first().copied().unwrap_or("T")
                    ));
                }
            }
        }
        Ok(())
    }

    /// An argument for each comptime parameter of `decl`, or `None` when the generic is to be
    /// checked only where it is used.
    fn archetype_args(
        &mut self,
        mod_path: &str,
        decl: &FuncDecl,
    ) -> Result<Option<Vec<ComptimeVal>>, String> {
        let mut args = Vec::new();
        for p in decl.params.iter().filter(|p| p.is_comptime) {
            let mut bounds = match &p.ty {
                TypeExpr::MetaType => Vec::new(),
                TypeExpr::TraitBounds(parts) => parts.clone(),
                other => vec![other.clone()],
            };
            for w in &decl.where_clauses {
                if w.type_param == p.name && !w.negated {
                    bounds.push(TypeExpr::Constraint(w.constraint));
                }
            }
            match self.stand_in(mod_path, &p.name, &bounds)? {
                Stand::Arg(v) => args.push(v),
                Stand::Skip => return Ok(None),
            }
        }
        Ok(Some(args))
    }

    /// What stands for a parameter `name` bounded by `bounds` while its generic is checked.
    fn stand_in(&mut self, mod_path: &str, name: &str, bounds: &[TypeExpr]) -> Result<Stand, String> {
        let int = |c: &mut Self, signed: bool, bits: u16| c.intern_type(Type::Int { signed, bits });
        let mut copy = false;
        let mut linear = false;
        let (mut clone, mut default, mut format, mut send, mut sync) = (false, false, false, false, false);
        let mut number: Option<TypeId> = None;
        let mut traits = Vec::new();
        for bound in bounds {
            match bound {
                TypeExpr::Constraint(c) => match c {
                    TypeConstraint::AnyType | TypeConstraint::Affine => {}
                    TypeConstraint::Unchecked => return Ok(Stand::Skip),
                    TypeConstraint::Copy => copy = true,
                    TypeConstraint::Linear => linear = true,
                    TypeConstraint::Clone => clone = true,
                    TypeConstraint::Default => default = true,
                    TypeConstraint::Format => format = true,
                    TypeConstraint::Send => send = true,
                    TypeConstraint::Sync => sync = true,
                    // Numbers are about their operators, which a real number type has.
                    TypeConstraint::Scalar
                    | TypeConstraint::Number
                    | TypeConstraint::Integer
                    | TypeConstraint::Signed => number = Some(int(self, true, 32)),
                    TypeConstraint::Unsigned => number = Some(int(self, false, 32)),
                    TypeConstraint::Float => number = Some(self.intern_type(Type::F64)),
                    // Kinds of type (`struct`, `enum`, `callable`, ...) are not modelled.
                    _ => return Ok(Stand::Skip),
                },
                // `opaque` is a kind of type, like `struct`.
                TypeExpr::BareOpaque => return Ok(Stand::Skip),
                other => {
                    let env = HashMap::new();
                    let Ok(t) = self.resolve_type_expr(mod_path, None, &env, other) else {
                        return Ok(Stand::Skip);
                    };
                    if self.traits.contains_key(&t) {
                        traits.push(t);
                    } else if matches!(self.program.types[t.0 as usize], Type::Int { .. })
                        && !self.named_opaques.contains(&t)
                        && !self.composites.contains_key(&t)
                        && bounds.len() == 1
                    {
                        // A value parameter (`[n: usize]`).
                        return Ok(Stand::Arg(ComptimeVal::Int(1)));
                    } else {
                        return Ok(Stand::Skip);
                    }
                }
            }
        }
        if let Some(n) = number {
            // A number bounded by traits as well needs a type that has both; there is none here.
            return Ok(if traits.is_empty() { Stand::Arg(ComptimeVal::Type(n)) } else { Stand::Skip });
        }
        let trap = || Block {
            stmts: vec![Stmt::Expr(Expr::IntrinsicTrap)],
            lines: Vec::new(),
        };
        let mut env = HashMap::new();
        let mut methods = Vec::new();
        for (i, &t) in traits.iter().enumerate() {
            let key = format!("__bound_{i}");
            env.insert(key.clone(), ComptimeVal::Type(t));
            let info = self.traits[&t].clone();
            for (k, v) in &info.comptime_env {
                env.entry(k.clone()).or_insert_with(|| v.clone());
            }
            for m in &info.methods {
                methods.push(FuncDecl {
                    vis: Visibility::Pub,
                    name: m.name.clone(),
                    params: m.params.clone(),
                    ret_ty: m.ret_ty.clone(),
                    borrows: m.borrows.clone(),
                    where_clauses: Vec::new(),
                    body: trap(),
                    is_unsafe: m.is_unsafe,
                    impl_of: Some(TypeExpr::Named(vec![key.clone()])),
                    is_unsafe_impl: info.is_unsafe,
                });
            }
        }
        let ownership = if linear {
            OpaqueOwnership::Linear
        } else if copy {
            OpaqueOwnership::Copy
        } else {
            OpaqueOwnership::Affine
        };
        let threads = ThreadDecl {
            unsafe_send: send,
            unsafe_sync: sync,
            not_send: !send,
            not_sync: !sync,
        };
        let clone_hooks = if clone && !copy && !linear {
            vec![CloneHookDecl {
                self_name: "self".to_string(),
                where_clauses: Vec::new(),
                body: Block {
                    stmts: vec![Stmt::Return(Some(Expr::IntrinsicTrap))],
                    lines: Vec::new(),
                },
            }]
        } else {
            Vec::new()
        };
        let default_hook = default.then(|| {
            (
                Vec::new(),
                Block {
                    stmts: vec![Stmt::Return(Some(Expr::IntrinsicTrap))],
                    lines: Vec::new(),
                },
            )
        });
        let format_hook =
            format.then(|| ("self".to_string(), "f".to_string(), None, Block { stmts: Vec::new(), lines: Vec::new() }));
        let ty = self.instantiate_composite(
            mod_path,
            name,
            true,
            false,
            ownership,
            threads,
            &env,
            None,
            &[],
            &[],
            &[],
            &methods,
            default_hook,
            &clone_hooks,
            &[],
            format_hook,
            DeclaredContents::default(),
        )?;
        Ok(Stand::Arg(ComptimeVal::Type(ty)))
    }
}
