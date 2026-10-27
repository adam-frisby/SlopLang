//! Type inference for unannotated literal bindings (`let x = 5;`, `let mut i = 0;`).
//!
//! Such a binding gets a type variable: a placeholder `TypeId` (structurally `i64` / `f64`). The
//! first coercion that meets a concrete integer (or float) type binds it, and every local of the
//! placeholder type is patched to the bound type, so `let i = 0; while i < n { a[i] }` gives `i`
//! the type `usize`. A variable never escapes into another type: an expression whose consumer is
//! not arithmetic, a `let`, an assignment, a cast, or a typed position defaults it first (see
//! `FuncLowerer::lower_expr`), as does the end of the function.

use super::*;

/// One type variable of the function being lowered.
pub(super) struct TypeVar {
    /// The placeholder type of locals holding the variable.
    ty: TypeId,
    /// A float variable (`let x = 1.5;`) rather than an integer one.
    float: bool,
    /// The type it was bound to (possibly another variable).
    resolved: Option<TypeId>,
    /// Integer literals typed by the variable, checked against the type it is bound to.
    literals: Vec<i128>,
}

impl<'a> FuncLowerer<'a> {
    /// A fresh integer (or float) type variable.
    pub(super) fn new_type_var(&mut self, float: bool) -> TypeId {
        let ty = self.compiler.alloc_distinct_type(if float {
            Type::F64
        } else {
            Type::Int {
                signed: true,
                bits: 64,
            }
        });
        self.type_vars.push(TypeVar {
            ty,
            float,
            resolved: None,
            literals: Vec::new(),
        });
        ty
    }

    fn type_var_index(&self, ty: TypeId) -> Option<usize> {
        self.type_vars.iter().position(|v| v.ty == ty)
    }

    /// `ty` with bound type variables replaced by what they are bound to.
    pub(super) fn resolve_type_var(&self, mut ty: TypeId) -> TypeId {
        while let Some(i) = self.type_var_index(ty)
            && let Some(r) = self.type_vars[i].resolved
        {
            ty = r;
        }
        ty
    }

    /// Whether `ty` is a type variable that is not bound yet.
    pub(super) fn is_open_type_var(&self, ty: TypeId) -> bool {
        self.type_var_index(ty)
            .is_some_and(|i| self.type_vars[i].resolved.is_none())
    }

    /// Records an integer literal typed by an open type variable, to check once it is bound.
    pub(super) fn note_type_var_literal(&mut self, ty: TypeId, value: i128) {
        if let Some(i) = self.type_var_index(ty)
            && self.type_vars[i].resolved.is_none()
        {
            self.type_vars[i].literals.push(value);
        }
    }

    /// Binds the open type variable `var` to `to` (a concrete type or another variable). An
    /// integer variable binds to an integer type (a pattern type's base), a float variable to a
    /// float type; anything else is left for the coercion to reject.
    pub(super) fn bind_type_var(&mut self, var: TypeId, to: TypeId) -> Result<(), String> {
        let to = self.resolve_type_var(to);
        let Some(i) = self.type_var_index(var) else {
            return Ok(());
        };
        if self.type_vars[i].resolved.is_some() || to == var {
            return Ok(());
        }
        let to = match self.compiler.program.types[to.0 as usize] {
            Type::Pattern { base, .. } => base,
            _ => to,
        };
        let float = self.type_vars[i].float;
        if let Some(j) = self.type_var_index(to) {
            if self.type_vars[j].float != float {
                return Ok(());
            }
            let lits = std::mem::take(&mut self.type_vars[i].literals);
            self.type_vars[j].literals.extend(lits);
        } else {
            let fits = match self.compiler.program.types[to.0 as usize] {
                Type::Int { .. } => !float,
                Type::F32 | Type::F64 => float,
                _ => false,
            };
            if !fits
                || matches!(
                    self.compiler.type_kind(to),
                    Some(TypeKind::Enum | TypeKind::OpaqueNewtype)
                )
            {
                return Ok(());
            }
            for v in std::mem::take(&mut self.type_vars[i].literals) {
                self.compiler.check_int_literal(&Wide::from_i128(v), to)?;
            }
        }
        self.type_vars[i].resolved = Some(to);
        self.patch_type_var(var, to);
        Ok(())
    }

    /// Binds an open type variable to its default (`i64` / `f64`).
    pub(super) fn default_type_var(&mut self, var: TypeId) -> Result<(), String> {
        let Some(i) = self.type_var_index(var) else {
            return Ok(());
        };
        if self.type_vars[i].resolved.is_some() {
            return Ok(());
        }
        let default = self.compiler.intern_type(if self.type_vars[i].float {
            Type::F64
        } else {
            Type::Int {
                signed: true,
                bits: 64,
            }
        });
        self.bind_type_var(var, default)
    }

    /// Defaults every open type variable (before a closure captures locals, and at the end of
    /// the function).
    pub(super) fn default_all_type_vars(&mut self) -> Result<(), String> {
        for i in 0..self.type_vars.len() {
            let ty = self.type_vars[i].ty;
            self.default_type_var(ty)?;
        }
        for i in 0..self.body.locals.len() {
            self.body.locals[i] = self.resolve_type_var(self.body.locals[i]);
        }
        Ok(())
    }

    /// Replaces `var` by `to` in the function's locals, scopes, and recorded variable types.
    fn patch_type_var(&mut self, var: TypeId, to: TypeId) {
        for t in &mut self.body.locals {
            if *t == var {
                *t = to;
            }
        }
        for scope in &mut self.scopes {
            for v in scope.iter_mut() {
                if v.ty == var {
                    v.ty = to;
                }
            }
        }
        for v in self.comptime_env.values_mut() {
            if matches!(v, ComptimeVal::Type(t) if *t == var) {
                *v = ComptimeVal::Type(to);
            }
        }
    }
}
