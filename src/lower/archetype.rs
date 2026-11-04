//! Checking a generic body against its bounds, before and apart from any use of it.
//!
//! A type parameter promises its bounds and nothing more, so a generic is checked by instantiating
//! it with an *archetype* for each type parameter: a type made here that has exactly what the bounds
//! say (the methods of a bound trait, `copy` if bound by `copy`, ...) and nothing else. A body that
//! uses more fails, whether or not anything calls it. Duck typing is opt-in: a parameter declared
//! `[T: unchecked]` may be used as anything, and is checked only where it is used.

use super::*;
use crate::ast::{ImplDecl, Param};

/// What a generic parameter stands for while its generic is checked.
enum Stand {
    /// An archetype or a representative, shown as the string in errors.
    Arg(ComptimeVal),
    /// `unchecked`, or a bound an archetype cannot model: the generic is checked where it is used.
    Skip,
}

impl Compiler {
    /// Checks every generic in the program's modules (or, with `std_too`, in std's) against its
    /// bounds: generic functions, generic types declared with brackets and all their methods
    /// (generic ones, and those a `where` clause gates), and `impl` blocks, generic or not, whose
    /// methods would otherwise be checked only when called. One scratch compiler serves a module.
    pub(super) fn check_generic_bodies(&mut self, std_too: bool) -> Result<(), String> {
        let mut mod_names: Vec<String> = self
            .modules
            .keys()
            .filter(|m| std_too || !crate::stdlib::is_stdlib_module(m))
            .cloned()
            .collect();
        mod_names.sort();
        for mod_path in mod_names {
            let items = self.modules[&mod_path].items.clone();
            let mut sandbox = self.clone();
            for item in &items {
                match item {
                    Item::Func(decl) if decl.ret_ty == TypeExpr::MetaType => {
                        // Of the functions that make types, only a declared generic type is
                        // checked: one that computes a type is code to run, not a template.
                        if matches!(decl.body.stmts.as_slice(), [Stmt::Return(Some(Expr::TypeVal(te)))] if Self::is_reservable(te))
                        {
                            sandbox.check_generic_type(&mod_path, decl)?;
                        }
                    }
                    Item::Func(decl) if decl.params.iter().any(|p| p.is_comptime) => {
                        let Some(args) =
                            sandbox.archetype_args(&mod_path, &decl.params, &decl.where_clauses)?
                        else {
                            continue;
                        };
                        let label = format!("Generic '{mod_path}::{}'", decl.name);
                        sandbox.check_step(&label, true, |c| {
                            // This declaration, not whichever overload its name resolves to.
                            c.instantiate_specific_func_decl(&mod_path, decl, &args).map(|_| ())
                        })?;
                    }
                    Item::Impl(d) => sandbox.check_module_impl(&mod_path, d)?,
                    Item::TypeDecl { name, ty, alias: false, .. } if Self::is_reservable(ty) => {
                        let ty_id = sandbox.resolve_named_type(&mod_path, name)?;
                        sandbox.check_members(&mod_path, ty_id, name, false)?;
                    }
                    _ => {}
                }
            }
        }
        Ok(())
    }

    /// Runs `step`, then lowers, drop-elaborates, and borrow-checks what it made, reporting a
    /// failure as `label`'s. `generic`: whether archetypes stood for type parameters in it.
    fn check_step(
        &mut self,
        label: &str,
        generic: bool,
        step: impl FnOnce(&mut Self) -> Result<(), String>,
    ) -> Result<(), String> {
        // What this step gives a body: new functions, and ones made earlier but lowered now.
        let bodiless: Vec<FuncId> =
            self.program.functions.iter().filter(|f| f.blocks.is_empty()).map(|f| f.id).collect();
        let known = self.program.functions.len();
        let res = step(self).and_then(|_| self.lower_pending_funcs()).and_then(|_| {
            let lowered: Vec<usize> = (0..self.program.functions.len())
                .filter(|&i| {
                    let f = &self.program.functions[i];
                    !f.blocks.is_empty() && (i >= known || bodiless.contains(&f.id))
                })
                .collect();
            elaborate_drops_of(&mut self.program, &lowered)?;
            let ids: Vec<FuncId> = lowered.iter().map(|&i| self.program.functions[i].id).collect();
            crate::borrowck::check_borrows_where(&self.program, |f| ids.contains(&f))
        });
        res.map_err(|e| {
            let first = e.lines().next().unwrap_or_default().to_string();
            if generic {
                format!(
                    "{label} uses its type parameters beyond what their bounds promise: {first}. State what it needs as a bound (a trait, or a constraint such as 'integer' or 'copy'), or declare a parameter 'unchecked' (as in '[T: unchecked]') to check it only where it is used"
                )
            } else {
                format!("{label} does not compile: {first}")
            }
        })
    }

    /// A generic type: instantiated with archetypes, then its members; and again for each method a
    /// `where` clause gates, with archetypes that meet it, so that the method exists.
    fn check_generic_type(&mut self, mod_path: &str, decl: &FuncDecl) -> Result<(), String> {
        let Some(args) = self.archetype_args(mod_path, &decl.params, &decl.where_clauses)? else {
            return Ok(());
        };
        let label = format!("Generic type '{mod_path}::{}'", decl.name);
        let mut ty = TypeId(0);
        self.check_step(&label, true, |c| {
            ty = c.eval_comptime_type_func(mod_path, &decl.name, &args)?;
            Ok(())
        })?;
        self.check_members(mod_path, ty, &decl.name, true)?;
        let gated: Vec<FuncDecl> = self
            .composites
            .get(&ty)
            .map(|c| {
                let mut ms: Vec<FuncDecl> = c.methods.values().map(|(_, m)| m.clone()).collect();
                ms.sort_by(|a, b| a.name.cmp(&b.name));
                ms
            })
            .unwrap_or_default()
            .into_iter()
            .filter(|m| !m.where_clauses.is_empty() && !m.params.iter().any(|p| p.is_comptime))
            .collect();
        for m in gated {
            let mut wheres = decl.where_clauses.clone();
            wheres.extend(m.where_clauses.iter().cloned());
            let Some(args) = self.archetype_args(mod_path, &decl.params, &wheres)? else {
                continue;
            };
            let label = format!("Method '{}::{}'", decl.name, m.name);
            self.check_step(&label, true, |c| {
                c.eval_comptime_type_func(mod_path, &decl.name, &args).map(|_| ())
            })?;
        }
        Ok(())
    }

    /// The members of `ty` that nothing checks until they are used: its generic methods, with
    /// archetypes for their own parameters, and the methods of the traits it implements.
    fn check_members(&mut self, mod_path: &str, ty: TypeId, name: &str, generic: bool) -> Result<(), String> {
        let Some(comp) = self.composites.get(&ty).cloned() else {
            return Ok(());
        };
        let mut methods: Vec<FuncDecl> = comp.methods.values().map(|(_, m)| m.clone()).collect();
        methods.sort_by(|a, b| a.name.cmp(&b.name));
        for m in methods.iter().filter(|m| m.params.iter().any(|p| p.is_comptime)) {
            let own: Vec<&str> = m.params.iter().filter(|p| p.is_comptime).map(|p| p.name.as_str()).collect();
            // A clause on the type's own parameters is met or not by the instance already.
            let wheres: Vec<WherePredicate> =
                m.where_clauses.iter().filter(|w| own.contains(&w.type_param.as_str())).cloned().collect();
            if wheres.len() != m.where_clauses.len() {
                continue;
            }
            let params: Vec<Param> = m.params.iter().filter(|p| p.is_comptime).cloned().collect();
            let Some(args) = self.archetype_args(&comp.def_module, &params, &wheres)? else {
                continue;
            };
            let mut env = comp.comptime_env.clone();
            for (p, a) in params.iter().zip(args) {
                env.insert(p.name.clone(), a);
            }
            let label = format!("Method '{name}::{}'", m.name);
            let def_mod = comp.def_module.clone();
            self.check_step(&label, true, |c| c.schedule_method(&def_mod, ty, &env, m).map(|_| ()))?;
        }
        for (trait_ty, _) in self.collect_trait_impls(ty, None)? {
            let label = format!("'impl {}' for '{name}'", self.traits[&trait_ty].name);
            self.check_impl_methods(mod_path, ty, trait_ty, &label, generic)?;
        }
        Ok(())
    }

    /// A module-level `impl`, for archetypes of its parameters if it has any.
    fn check_module_impl(&mut self, mod_path: &str, d: &ImplDecl) -> Result<(), String> {
        let Some(args) = self.archetype_args(mod_path, &d.comptime_params, &[])? else {
            return Ok(());
        };
        let mut env = HashMap::new();
        for (p, a) in d.comptime_params.iter().zip(args) {
            env.insert(p.name.clone(), a);
        }
        let generic = !d.comptime_params.is_empty();
        let mut found = None;
        let label = "An 'impl' block".to_string();
        self.check_step(&label, generic, |c| {
            let for_ty = c.resolve_type_expr(mod_path, None, &env, &d.for_ty)?;
            let trait_ty = c.resolve_type_expr(mod_path, Some(for_ty), &env, &d.trait_expr)?;
            found = Some((for_ty, trait_ty));
            Ok(())
        })?;
        let Some((for_ty, trait_ty)) = found else {
            return Ok(());
        };
        if !self.traits.contains_key(&trait_ty) {
            return Ok(());
        }
        let label = format!(
            "'impl {} for {}'",
            self.traits[&trait_ty].name,
            self.type_display_name(for_ty)
        );
        self.check_impl_methods(mod_path, for_ty, trait_ty, &label, generic)
    }

    fn check_impl_methods(
        &mut self,
        mod_path: &str,
        ty: TypeId,
        trait_ty: TypeId,
        label: &str,
        generic: bool,
    ) -> Result<(), String> {
        let count = self.traits[&trait_ty].methods.len();
        for idx in 0..count {
            if self.traits[&trait_ty].methods[idx].params.iter().any(|p| p.is_comptime) {
                continue;
            }
            self.check_step(label, generic, |c| {
                c.resolve_trait_impl_method(mod_path, ty, trait_ty, idx, false).map(|_| ())
            })?;
        }
        Ok(())
    }

    /// An argument for each comptime parameter in `params`, or `None` when the generic is to be
    /// checked only where it is used.
    fn archetype_args(
        &mut self,
        mod_path: &str,
        params: &[Param],
        where_clauses: &[WherePredicate],
    ) -> Result<Option<Vec<ComptimeVal>>, String> {
        let mut args = Vec::new();
        for p in params.iter().filter(|p| p.is_comptime) {
            let mut bounds = match &p.ty {
                TypeExpr::MetaType => Vec::new(),
                TypeExpr::TraitBounds(parts) => parts.clone(),
                other => vec![other.clone()],
            };
            for w in where_clauses {
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
            // A structural trait is met by methods of the type's own, a nominal one by an `impl`.
            let structural = info.kind == TraitKind::Structural;
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
                    impl_of: (!structural).then(|| TypeExpr::Named(vec![key.clone()])),
                    is_unsafe_impl: info.kind == TraitKind::Unsafe,
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
