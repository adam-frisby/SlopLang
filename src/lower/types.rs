use super::*;

impl Compiler {
    pub(super) fn is_linear_type(&self, ty_id: TypeId) -> bool {
        if let Some(nt) = self.distinct_types.get(&ty_id) {
            return self.is_linear_type(nt.underlying);
        }
        if self.program.linear_types.iter().any(|(t, _)| *t == ty_id) {
            return true;
        }
        if self.slices.contains_key(&ty_id) {
            return false;
        }
        match &self.program.types[ty_id.0 as usize] {
            Type::Struct(fields) => fields.iter().any(|&f| self.is_linear_type(f)),
            Type::Array { elem, len } => *len > 0 && self.is_linear_type(*elem),
            Type::Union { variants, .. } => variants.iter().any(|&v| self.is_linear_type(v)),
            _ => false,
        }
    }

    pub(super) fn is_copy_type(&self, ty_id: TypeId) -> bool {
        if self.pending_types.contains_key(&ty_id) {
            return false;
        }
        if let Some(nt) = self.distinct_types.get(&ty_id) {
            return self.is_copy_type(nt.underlying);
        }
        if self.is_opaque_type(ty_id) || self.is_linear_type(ty_id) {
            return false;
        }
        if self.program.destructors.iter().any(|(t, _)| *t == ty_id) {
            return false;
        }
        if let Some(comp) = self.composites.get(&ty_id)
            && comp.is_opaque
        {
            return comp.ownership == OpaqueOwnership::Copy;
        }
        if let Some(slice_info) = self.slices.get(&ty_id) {
            return !slice_info.mutable;
        }
        if let Some(tobj_info) = self.trait_objs.get(&ty_id) {
            return !tobj_info.mutable;
        }
        match &self.program.types[ty_id.0 as usize] {
            Type::Ptr { mutable: true, .. } => self.raw_ptrs.contains_key(&ty_id),
            Type::Struct(fields) | Type::Overlay(fields) => {
                fields.iter().all(|&f| self.is_copy_type(f))
            }
            Type::Array { elem, .. } => self.is_copy_type(*elem),
            Type::Union { variants, .. } => variants.iter().all(|&v| self.is_copy_type(v)),
            _ => true,
        }
    }

    /// Whether a value of `ty_id` can own, by value or through `*own` pointers, a `target`. An
    /// undefined type is part of the cycle this is asked from, so it counts.
    fn owns_itself(&self, ty_id: TypeId, target: TypeId, visiting: &mut Vec<TypeId>) -> bool {
        let parts: &[TypeId] = match &self.program.types[ty_id.0 as usize] {
            Type::Struct(parts) | Type::Overlay(parts) => parts,
            Type::Union { variants, .. } => variants,
            Type::Array { elem, .. } => std::slice::from_ref(elem),
            Type::Ptr { pointee, .. } if self.ptr_kind(ty_id) == Some(PtrKind::Own) => {
                std::slice::from_ref(pointee)
            }
            _ => &[],
        };
        // What an `opaque(owns T)` declares it owns, as `Vec` does its elements.
        let declared: &[TypeId] = self.composites.get(&ty_id).map_or(&[], |c| &c.declared.owns);
        for &part in parts.iter().chain(declared) {
            if part == target || self.pending_types.contains_key(&part) {
                return true;
            }
            if !visiting.contains(&part) {
                visiting.push(part);
                if self.owns_itself(part, target, visiting) {
                    return true;
                }
            }
        }
        false
    }

    pub(super) fn is_comptime_only_type(&self, ty_id: TypeId) -> bool {
        self.comptime_only_in(ty_id, &mut Vec::new())
    }

    /// `visiting` breaks cycles through recursive types, which add nothing to what they hold.
    fn comptime_only_in(&self, ty_id: TypeId, visiting: &mut Vec<TypeId>) -> bool {
        if visiting.contains(&ty_id) {
            return false;
        }
        visiting.push(ty_id);
        if let Some(nt) = self.distinct_types.get(&ty_id) {
            return self.comptime_only_in(nt.underlying, visiting);
        }
        if let Some(minfo) = self.maps.get(&ty_id) {
            return self.comptime_only_in(minfo.key_ty, visiting)
                || self.comptime_only_in(minfo.val_ty, visiting);
        }
        match &self.program.types[ty_id.0 as usize] {
            Type::MetaType => true,
            Type::Ptr { pointee, .. } | Type::Array { elem: pointee, .. } => {
                self.comptime_only_in(*pointee, visiting)
            }
            Type::Struct(parts)
            | Type::Overlay(parts)
            | Type::Union {
                variants: parts, ..
            } => parts.iter().any(|&p| self.comptime_only_in(p, visiting)),
            _ => false,
        }
    }

    /// The values a field of type `ty_id` holds beyond its inline structure: those behind an
    /// owning pointer (`*own T`, `?*own T`) or in `uninit` storage, looking through arrays and
    /// transparent aggregates. An `opaque` field is one unit: its own type says what it holds.
    pub(super) fn held_types(&self, ty_id: TypeId, out: &mut Vec<TypeId>) {
        if self.ptr_kind(ty_id) == Some(PtrKind::Own) {
            let (_, pointee) = self.raw_ptrs[&ty_id];
            if !out.contains(&pointee) {
                out.push(pointee);
                self.held_types(pointee, out);
            }
            return;
        }
        if let Some(&inner) = self.uninit_types.get(&ty_id) {
            if !out.contains(&inner) {
                out.push(inner);
                self.held_types(inner, out);
            }
            return;
        }
        if self.composites.get(&ty_id).is_some_and(|c| c.is_opaque) {
            return;
        }
        match &self.program.types[ty_id.0 as usize] {
            Type::Array { elem, .. } => self.held_types(*elem, out),
            Type::Struct(parts) | Type::Union { variants: parts, .. } => {
                for &p in parts {
                    self.held_types(p, out);
                }
            }
            _ => {}
        }
    }

    /// Whether a shared reference to `ty_id` may be turned into a `*mut` pointer: the type
    /// declares `unsafe sync` (and so synchronizes its own state across shared references).
    /// Note: `cell` fields allow field-level mutation and `&raw mut self.field`, not `&raw mut *self`
    /// on the enclosing composite as a whole.
    pub(super) fn permits_interior_mutation(&self, ty_id: TypeId) -> bool {
        let mut ty = ty_id;
        while let Some(nt) = self.distinct_types.get(&ty) {
            ty = nt.underlying;
        }
        self.composites
            .get(&ty)
            .is_some_and(|c| c.is_opaque && c.threads.unsafe_sync)
    }

    /// Whether dropping a value of `ty_id` leaves the borrows it holds unread, so they may already
    /// have ended when it is dropped (`Vec[&i32]` dropped after the `i32`). True for a value that
    /// holds no borrow, for pointers and types without a `drop` hook whose parts all qualify, and
    /// for a type whose hook is `unsafe impl drop(may_dangle T)` when every borrow it holds sits in
    /// `T` values (inline, behind `*own T`, or in `uninit T`) whose own drop qualifies.
    pub(super) fn drop_ignores_borrows(&self, ty_id: TypeId) -> bool {
        self.drop_ignores_borrows_in(ty_id, &mut Vec::new())
    }

    fn drop_ignores_borrows_in(&self, ty_id: TypeId, visiting: &mut Vec<TypeId>) -> bool {
        if visiting.contains(&ty_id) {
            return true;
        }
        if let Some(nt) = self.distinct_types.get(&ty_id) {
            return self.drop_ignores_borrows_in(nt.underlying, visiting);
        }
        if !self.type_contains_safe_borrow(ty_id) || self.raw_ptrs.contains_key(&ty_id) {
            return true;
        }
        visiting.push(ty_id);
        let ignores = if let Some(c) = self.composites.get(&ty_id) {
            let fields: Vec<TypeId> = c
                .fields
                .iter()
                .map(|f| f.1)
                .chain(c.declared.owns.iter().copied())
                .chain(c.declared.borrows.iter().copied())
                .collect();
            if c.drop_fn.is_none() {
                fields.iter().all(|&f| self.drop_ignores_borrows_in(f, visiting))
            } else if c.may_dangle.is_empty() || !c.declared.borrows.is_empty() {
                // `opaque(borrows U)` holds a borrow directly, like a `*ref U` field, so the
                // hook may read it whatever `U` is.
                false
            } else {
                let params = c.may_dangle.clone();
                fields.iter().all(|&f| self.field_may_dangle(f, &params, visiting))
            }
        } else {
            match &self.program.types[ty_id.0 as usize] {
                Type::Struct(parts) | Type::Union { variants: parts, .. } => {
                    parts.clone().iter().all(|&p| self.drop_ignores_borrows_in(p, visiting))
                }
                Type::Array { elem, .. } => self.drop_ignores_borrows_in(*elem, visiting),
                _ => true,
            }
        };
        visiting.pop();
        ignores
    }

    /// For a type whose hook declares `may_dangle` over `params`: whether field `f` holds borrows
    /// only in `params` values (inline, behind `*own`, or in `uninit`) whose own drop ignores them.
    /// A field holding a borrow any other way (a reference `&T`, a view `*ref T`, or a non-`may_dangle`
    /// borrow-carrying type) is one the hook may read.
    fn field_may_dangle(&self, f: TypeId, params: &[TypeId], visiting: &mut Vec<TypeId>) -> bool {
        if !self.carries_borrow(f, true, &mut Vec::new()) {
            return true;
        }
        if params.contains(&f) {
            return self.drop_ignores_borrows_in(f, visiting);
        }
        if let Some(&inner) = self.uninit_types.get(&f) {
            return self.field_may_dangle(inner, params, visiting);
        }
        if self.ptr_kind(f) == Some(PtrKind::Own) {
            let pointee = self.raw_ptrs[&f].1;
            return self.field_may_dangle(pointee, params, visiting);
        }
        if let Some(nt) = self.distinct_types.get(&f) {
            return self.field_may_dangle(nt.underlying, params, visiting);
        }
        if let Some(c) = self.composites.get(&f) {
            if c.drop_fn.is_some() && !self.drop_ignores_borrows_in(f, visiting) {
                return false;
            }
            let parts: Vec<TypeId> = c
                .fields
                .iter()
                .map(|x| x.1)
                .chain(c.declared.owns.iter().copied())
                .chain(c.declared.borrows.iter().copied())
                .collect();
            return parts
                .into_iter()
                .all(|part| self.field_may_dangle(part, params, visiting));
        }
        if self.raw_ptrs.contains_key(&f) || self.slices.contains_key(&f) {
            return false;
        }
        match &self.program.types[f.0 as usize] {
            Type::Struct(parts) | Type::Union { variants: parts, .. } => parts
                .clone()
                .into_iter()
                .all(|p| self.field_may_dangle(p, params, visiting)),
            Type::Array { elem, .. } | Type::Simd { elem, .. } => {
                self.field_may_dangle(*elem, params, visiting)
            }
            _ => false,
        }
    }

    /// Whether a field of type `ty_id` holds a linear value, inline or out of line.
    pub(super) fn field_holds_linear(&self, ty_id: TypeId) -> bool {
        let mut held = Vec::new();
        self.held_types(ty_id, &mut held);
        self.is_linear_type(ty_id) || held.iter().any(|&t| self.is_linear_type(t))
    }

    /// Whether `ty_id` contains an owning pointer outside any `opaque`.
    pub(super) fn holds_own_ptr(&self, ty_id: TypeId) -> bool {
        if self.ptr_kind(ty_id) == Some(PtrKind::Own) {
            return true;
        }
        if self.composites.get(&ty_id).is_some_and(|c| c.is_opaque) {
            return false;
        }
        match &self.program.types[ty_id.0 as usize] {
            Type::Array { elem, .. } => self.holds_own_ptr(*elem),
            Type::Struct(parts) | Type::Union { variants: parts, .. } => {
                parts.iter().any(|&p| self.holds_own_ptr(p))
            }
            _ => false,
        }
    }

    pub(super) fn is_send_type(&self, ty_id: TypeId) -> bool {
        self.auto_trait_holds(ty_id, true, &mut Vec::new())
    }

    pub(super) fn is_sync_type(&self, ty_id: TypeId) -> bool {
        self.auto_trait_holds(ty_id, false, &mut Vec::new())
    }

    /// `send` (`send = true`) or `sync` for `ty_id`. Pointers confer what they hold: `*own T` is
    /// `send` / `sync` as `T` is, `*ref T` as `&T` is, and a raw pointer is neither. `visiting`
    /// breaks cycles through recursive types (`?*own Node` inside `Node`), which count as holding.
    fn auto_trait_holds(&self, ty_id: TypeId, send: bool, visiting: &mut Vec<TypeId>) -> bool {
        if visiting.contains(&ty_id) {
            return true;
        }
        visiting.push(ty_id);
        let holds = self.auto_trait_holds_uncached(ty_id, send, visiting);
        visiting.pop();
        holds
    }

    fn auto_trait_holds_uncached(&self, ty_id: TypeId, send: bool, visiting: &mut Vec<TypeId>) -> bool {
        let mut is = |t: TypeId, send: bool| self.auto_trait_holds(t, send, visiting);
        if let Some(nt) = self.distinct_types.get(&ty_id) {
            return is(nt.underlying, send);
        }
        if self.is_opaque_type(ty_id) {
            return false;
        }
        if let Some(kind) = self.ptr_kind(ty_id) {
            let (mutable, pointee) = self.raw_ptrs[&ty_id];
            return match kind {
                PtrKind::Raw => false,
                PtrKind::Own => is(pointee, send),
                PtrKind::View => is(pointee, send && mutable),
            };
        }
        if let Some(&inner_ty) = self.uninit_types.get(&ty_id) {
            return is(inner_ty, send);
        }
        if let Some(&slice_info) = self.slices.get(&ty_id) {
            return is(slice_info.elem, send && slice_info.mutable);
        }
        if let Some(comp) = self.composites.get(&ty_id)
            && comp.is_opaque
        {
            let t = comp.threads;
            if (send && t.not_send) || (!send && t.not_sync) {
                return false;
            }
            // `unsafe send` / `unsafe sync` asserts the trait outright, as the compiler cannot
            // check raw pointers or `cell` state; conditions on type parameters are written as
            // bounds on the type function (`Mutex[T: send]`).
            if (send && t.unsafe_send) || (!send && t.unsafe_sync) {
                return true;
            }
            // A `cell` field may change through a shared reference, which is not thread-safe
            // without the synchronization `unsafe sync` asserts.
            if !send && !comp.cell_fields.is_empty() {
                return false;
            }
            let declared = comp.declared.owns.iter().all(|&t| is(t, send))
                && comp.declared.borrows.iter().all(|&t| is(t, false));
            return declared && comp.fields.iter().all(|(_, f_ty, _, _)| is(*f_ty, send));
        }
        match &self.program.types[ty_id.0 as usize] {
            Type::Ptr { mutable, pointee } => is(*pointee, send && *mutable),
            Type::Struct(fields) | Type::Overlay(fields) => fields.iter().all(|&f| is(f, send)),
            Type::Array { elem, .. } => is(*elem, send),
            Type::Union { variants, .. } => variants.iter().all(|&v| is(v, send)),
            Type::Pattern { base, .. } => is(*base, send),
            _ => true,
        }
    }

    /// Whether values of `ty_id` may carry a borrow, so that contracts treat the type like a
    /// reference: a safe reference or slice, a view pointer (`*ref T`), values behind an owning
    /// pointer that carry one (`*own &T`), or an `opaque` that declares `borrows T` or owns a
    /// borrowing `T`. A raw pointer carries none.
    ///
    /// An owning pointer confers its pointee's borrows only on the `opaque` that holds it: a bare
    /// `*own T` read out of a container (`let p = self.ptr`) is just an address into it.
    pub(super) fn type_contains_safe_borrow(&self, ty_id: TypeId) -> bool {
        self.carries_borrow(ty_id, false, &mut Vec::new())
    }

    fn carries_borrow(&self, ty_id: TypeId, in_opaque: bool, visiting: &mut Vec<TypeId>) -> bool {
        if visiting.contains(&ty_id) {
            return false;
        }
        visiting.push(ty_id);
        let carries = self.carries_borrow_uncached(ty_id, in_opaque, visiting);
        visiting.pop();
        carries
    }

    fn carries_borrow_uncached(
        &self,
        ty_id: TypeId,
        in_opaque: bool,
        visiting: &mut Vec<TypeId>,
    ) -> bool {
        let is_opaque = self.composites.get(&ty_id).is_some_and(|c| c.is_opaque);
        let mut carries = |t: TypeId| self.carries_borrow(t, in_opaque || is_opaque, visiting);
        if let Some(nt) = self.distinct_types.get(&ty_id) {
            return carries(nt.underlying);
        }
        match self.ptr_kind(ty_id) {
            Some(PtrKind::Raw) => return false,
            Some(PtrKind::View) => return true,
            Some(PtrKind::Own) => return in_opaque && carries(self.raw_ptrs[&ty_id].1),
            None => {}
        }
        if let Some(&inner_ty) = self.uninit_types.get(&ty_id) {
            return carries(inner_ty);
        }
        if self.slices.contains_key(&ty_id) {
            return true;
        }
        if let Some(comp) = self.composites.get(&ty_id)
            && (!comp.declared.borrows.is_empty()
                || comp.declared.owns.iter().any(|&t| carries(t)))
        {
            return true;
        }
        match &self.program.types[ty_id.0 as usize] {
            Type::Ptr { .. } => true,
            Type::Struct(fields) | Type::Overlay(fields) => fields.iter().any(|&f| carries(f)),
            Type::Array { elem, .. } => carries(*elem),
            Type::Union { variants, .. } => variants.iter().any(|&v| carries(v)),
            Type::Pattern { base, .. } => carries(*base),
            _ => false,
        }
    }

    pub(super) fn check_non_borrowing_spawn_callable(&self, ty_id: TypeId) -> Result<(), String> {
        if let Some(cinfo) = self.closures.get(&ty_id)
            && !cinfo.is_move
        {
            return Err(
                "Unscoped 'spawn' requires a non-borrowing 'move fn' closure; borrowing closure captures stack references (use 'spawn_scoped' to borrow stack variables)".to_string(),
            );
        }
        if self.type_contains_safe_borrow(ty_id) {
            return Err(format!(
                "Type '{}' passed to unscoped 'spawn' contains borrowed references ('&T', '&mut T', or slice); 'spawn' requires a non-borrowing 'move fn' (use 'spawn_scoped' to borrow stack variables)",
                self.type_display_name(ty_id)
            ));
        }
        Ok(())
    }

    pub(super) fn is_format_type(&self, ty_id: TypeId) -> bool {
        self.format_holds(ty_id, &mut Vec::new())
    }

    /// Formatting is expanded inline, so a cycle through references needs a `format` hook.
    fn format_holds(&self, ty_id: TypeId, visiting: &mut Vec<TypeId>) -> bool {
        if visiting.contains(&ty_id) {
            return false;
        }
        visiting.push(ty_id);
        let holds = self.format_holds_uncached(ty_id, visiting);
        visiting.pop();
        holds
    }

    fn format_holds_uncached(&self, ty_id: TypeId, visiting: &mut Vec<TypeId>) -> bool {
        if let Some(nt) = self.distinct_types.get(&ty_id) {
            return self.format_holds(nt.underlying, visiting);
        }
        if self.is_opaque_type(ty_id)
            || self.raw_ptrs.contains_key(&ty_id)
            || self.closures.contains_key(&ty_id)
        {
            return false;
        }
        if let Some(&slice_info) = self.slices.get(&ty_id) {
            return slice_info.is_str || self.format_holds(slice_info.elem, visiting);
        }
        if let Some(comp) = self.composites.get(&ty_id) {
            return if comp.is_opaque {
                comp.has_format_hook
            } else {
                comp.fields
                    .iter()
                    .all(|(_, f_ty, _, _)| self.format_holds(*f_ty, visiting))
            };
        }
        if self.enums.contains_key(&ty_id) {
            return true;
        }
        match &self.program.types[ty_id.0 as usize] {
            Type::Void | Type::Int { .. } | Type::F32 | Type::F64 | Type::Bool | Type::Rune => true,
            Type::Ptr { pointee, .. } => self.format_holds(*pointee, visiting),
            Type::Struct(fields) => fields.iter().all(|&f| self.format_holds(f, visiting)),
            Type::Array { elem, .. } => self.format_holds(*elem, visiting),
            Type::Union { variants, .. } => variants.iter().all(|&v| self.format_holds(v, visiting)),
            Type::Pattern { base, .. } => self.format_holds(*base, visiting),
            _ => false,
        }
    }

    pub(super) fn is_clone_type(&self, ty_id: TypeId) -> bool {
        // A cycle clones if everything else in it does: it cannot be what prevents cloning.
        if self.pending_types.contains_key(&ty_id) {
            return true;
        }
        if let Some(nt) = self.distinct_types.get(&ty_id) {
            return self.is_clone_type(nt.underlying);
        }
        if self.is_opaque_type(ty_id) || self.is_linear_type(ty_id) {
            return false;
        }
        if let Some(comp) = self.composites.get(&ty_id) {
            return if comp.is_opaque {
                comp.ownership == OpaqueOwnership::Copy || comp.clone_fn.is_some()
            } else {
                comp.fields
                    .iter()
                    .all(|(_, f_ty, _, _)| self.is_clone_type(*f_ty))
            };
        }
        self.is_copy_type(ty_id)
    }

    pub(super) fn is_default_type(&self, ty_id: TypeId) -> bool {
        if self.is_opaque_type(ty_id) || self.distinct_types.contains_key(&ty_id) {
            return false;
        }
        if let Some(comp) = self.composites.get(&ty_id) {
            return if comp.is_opaque {
                comp.default_fn.is_some()
            } else {
                comp.fields
                    .iter()
                    .all(|(_, f_ty, _, f_def)| f_def.is_some() || self.is_default_type(*f_ty))
            };
        }
        if self.slices.contains_key(&ty_id) || self.raw_ptrs.contains_key(&ty_id) {
            return false;
        }
        match &self.program.types[ty_id.0 as usize] {
            Type::Bool | Type::Int { .. } | Type::Rune | Type::F32 | Type::F64 => true,
            Type::Struct(fields) => fields.iter().all(|&f| self.is_default_type(f)),
            Type::Array { elem, .. } | Type::Simd { elem, .. } => self.is_default_type(*elem),
            Type::Union { variants, .. } => {
                !self.results.contains_key(&ty_id)
                    && !self.errors.contains_key(&ty_id)
                    && !self.unions.contains_key(&ty_id)
                    && !variants.is_empty()
                    && matches!(self.program.types[variants[0].0 as usize], Type::Void)
            }
            _ => false,
        }
    }

    pub(super) fn eval_where_clauses(
        &self,
        env: &HashMap<String, ComptimeVal>,
        clauses: &[WherePredicate],
    ) -> Result<bool, String> {
        for pred in clauses {
            let Some(ComptimeVal::Type(ty_id)) = env.get(&pred.type_param) else {
                return Err(format!(
                    "Unknown comptime type parameter '{}' in 'where' clause",
                    pred.type_param
                ));
            };
            let sat = self.type_satisfies_constraint(*ty_id, pred.constraint);
            let matched = if pred.negated { !sat } else { sat };
            if !matched {
                return Ok(false);
            }
        }
        Ok(true)
    }

    pub(super) fn check_where_clauses_or_err(
        &self,
        env: &HashMap<String, ComptimeVal>,
        clauses: &[WherePredicate],
        item_desc: &str,
    ) -> Result<(), String> {
        for pred in clauses {
            let Some(ComptimeVal::Type(ty_id)) = env.get(&pred.type_param) else {
                return Err(format!(
                    "Unknown comptime type parameter '{}' in 'where' clause of {}",
                    pred.type_param, item_desc
                ));
            };
            let sat = self.type_satisfies_constraint(*ty_id, pred.constraint);
            let matched = if pred.negated { !sat } else { sat };
            if !matched {
                let t_disp = self.type_display_name(*ty_id);
                let neg_prefix = if pred.negated { "!" } else { "" };
                return Err(format!(
                    "Cannot call {}: where-clause constraint '{}: {}{}' is not satisfied for type '{}'",
                    item_desc,
                    pred.type_param,
                    neg_prefix,
                    pred.constraint.name(),
                    t_disp
                ));
            }
        }
        Ok(())
    }

    pub(super) fn type_satisfies_constraint(
        &self,
        ty_id: TypeId,
        constraint: TypeConstraint,
    ) -> bool {
        if self.is_opaque_type(ty_id) {
            return matches!(constraint, TypeConstraint::AnyType);
        }
        let mut cur = &self.program.types[ty_id.0 as usize];
        if let Type::Pattern { base, .. } = cur {
            cur = &self.program.types[base.0 as usize];
        }
        let is_enum = self.enums.contains_key(&ty_id);
        let is_distinct = self.distinct_types.contains_key(&ty_id);
        let is_packed_comp = self.composites.get(&ty_id).is_some_and(|c| c.is_packed);
        match constraint {
            TypeConstraint::AnyType | TypeConstraint::Unchecked => true,
            TypeConstraint::Send => self.is_send_type(ty_id),
            TypeConstraint::Sync => self.is_sync_type(ty_id),
            TypeConstraint::Format => self.is_format_type(ty_id),
            TypeConstraint::Clone => self.is_clone_type(ty_id),
            TypeConstraint::Default => self.is_default_type(ty_id),
            TypeConstraint::Scalar => {
                !is_enum
                    && !is_distinct
                    && !is_packed_comp
                    && matches!(
                        cur,
                        Type::Int { .. }
                            | Type::F32
                            | Type::F64
                            | Type::Bool
                            | Type::Rune
                            | Type::Ptr { .. }
                    )
            }
            TypeConstraint::Number => {
                !is_enum
                    && !is_distinct
                    && !is_packed_comp
                    && matches!(cur, Type::Int { .. } | Type::F32 | Type::F64)
            }
            TypeConstraint::Callable => {
                !is_distinct
                    && (matches!(cur, Type::FnPtr { .. }) || self.closures.contains_key(&ty_id))
            }
            TypeConstraint::FnPtr => !is_distinct && matches!(cur, Type::FnPtr { .. }),
            TypeConstraint::Closure => self.closures.contains_key(&ty_id),
            TypeConstraint::Integer => {
                !is_enum && !is_distinct && !is_packed_comp && matches!(cur, Type::Int { .. })
            }
            TypeConstraint::Signed => {
                !is_enum
                    && !is_distinct
                    && !is_packed_comp
                    && matches!(cur, Type::Int { signed: true, .. })
            }
            TypeConstraint::Unsigned => {
                !is_enum
                    && !is_distinct
                    && !is_packed_comp
                    && matches!(cur, Type::Int { signed: false, .. })
            }
            TypeConstraint::Float => !is_distinct && matches!(cur, Type::F32 | Type::F64),
            TypeConstraint::Aggregate => {
                self.type_satisfies_constraint(ty_id, TypeConstraint::Struct)
                    || self.type_satisfies_constraint(ty_id, TypeConstraint::Tuple)
            }
            TypeConstraint::Struct => self.composites.get(&ty_id).is_some_and(|c| !c.is_opaque),
            TypeConstraint::Tuple => {
                !is_distinct
                    && matches!(cur, Type::Struct(_))
                    && !self.composites.contains_key(&ty_id)
                    && !self.trait_objs.contains_key(&ty_id)
                    && !self.closures.contains_key(&ty_id)
                    && !self.slices.contains_key(&ty_id)
            }
            TypeConstraint::Opaque => self.composites.get(&ty_id).is_some_and(|c| c.is_opaque),
            TypeConstraint::Copy => self.is_copy_type(ty_id),
            TypeConstraint::Affine => !self.is_copy_type(ty_id) && !self.is_linear_type(ty_id),
            TypeConstraint::Linear => self.is_linear_type(ty_id),
            TypeConstraint::Recursive => self.owns_itself(ty_id, ty_id, &mut Vec::new()),
            TypeConstraint::Simd => !is_distinct && matches!(cur, Type::Simd { .. }),
            TypeConstraint::Sequence => {
                !is_distinct
                    && (matches!(cur, Type::Array { .. }) || self.slices.contains_key(&ty_id))
            }
            TypeConstraint::Array => !is_distinct && matches!(cur, Type::Array { .. }),
            TypeConstraint::Slice => self.slices.contains_key(&ty_id),
            TypeConstraint::Discriminated => {
                self.type_satisfies_constraint(ty_id, TypeConstraint::Enum)
                    || self.type_satisfies_constraint(ty_id, TypeConstraint::Union)
                    || self.type_satisfies_constraint(ty_id, TypeConstraint::Error)
            }
            TypeConstraint::Enum => is_enum,
            TypeConstraint::Union => {
                !is_distinct
                    && matches!(cur, Type::Union { .. })
                    && !self.errors.contains_key(&ty_id)
            }
            TypeConstraint::Overlay => !is_distinct && matches!(cur, Type::Overlay(_)),
            TypeConstraint::Error => self.errors.contains_key(&ty_id),
            TypeConstraint::Module => false,
        }
    }

    pub(super) fn type_display_name(&self, ty_id: TypeId) -> String {
        let name = |t: TypeId| self.type_display_name(t);
        match self.type_kind(ty_id) {
            Some(TypeKind::UniversalOpaque) => return "opaque".to_string(),
            Some(TypeKind::Slice) => {
                let sl = self.slices[&ty_id];
                if sl.is_str {
                    return "&str".to_string();
                }
                let m = if sl.mutable { "mut " } else { "" };
                return format!("&{m}[{}]", name(sl.elem));
            }
            Some(TypeKind::Map) => {
                let m = &self.maps[&ty_id];
                return format!("map[{}, {}]", name(m.key_ty), name(m.val_ty));
            }
            Some(TypeKind::Closure) => {
                let c = &self.closures[&ty_id];
                let params: Vec<String> = c.param_tys.iter().map(|a| name(*a)).collect();
                let prefix = if c.is_move { "move " } else { "" };
                return format!(
                    "{prefix}closure fn({}) -> {}",
                    params.join(", "),
                    name(c.ret_ty)
                );
            }
            Some(TypeKind::Distinct) => return self.distinct_types[&ty_id].name.clone(),
            Some(TypeKind::CInt) => return self.c_ints[&ty_id].name().to_string(),
            Some(TypeKind::RawPtr) => {
                let (mutable, pointee) = self.raw_ptrs[&ty_id];
                let m = match (self.ptr_kind(ty_id), mutable) {
                    (Some(PtrKind::Own), _) => "own ",
                    (Some(PtrKind::View), true) => "ref mut ",
                    (Some(PtrKind::View), false) => "ref ",
                    (_, true) => "mut ",
                    (_, false) => "const ",
                };
                return format!("*{m}{}", name(pointee));
            }
            Some(TypeKind::Composite) => return self.composites[&ty_id].name.clone(),
            Some(TypeKind::Trait) => return self.traits[&ty_id].name.clone(),
            Some(TypeKind::TraitObj) => {
                let tobj = &self.trait_objs[&ty_id];
                if let Some(tr) = self.traits.get(&tobj.trait_ty) {
                    return format!("&{}{}", if tobj.mutable { "mut " } else { "" }, tr.name);
                }
            }
            Some(TypeKind::Enum) => return self.enums[&ty_id].0.clone(),
            Some(TypeKind::Union) => return self.unions[&ty_id].name.clone(),
            Some(TypeKind::Uninit) => return format!("uninit {}", name(self.uninit_types[&ty_id])),
            Some(TypeKind::Overlay) => return self.overlays[&ty_id].name.clone(),
            Some(TypeKind::Error) => return self.errors[&ty_id].name.clone(),
            Some(TypeKind::Result) | None => {}
        }
        if let Some(inner) = self.as_optional_type(ty_id) {
            return format!("?{}", name(inner));
        }
        match &self.program.types[ty_id.0 as usize] {
            Type::Pattern { base, ranges } => {
                let ranges: Vec<String> =
                    ranges.iter().map(|(lo, hi)| format!("{lo}..={hi}")).collect();
                format!("{} in {}", name(*base), ranges.join(" | "))
            }
            Type::FnPtr { args, ret } => {
                let params: Vec<String> = args.iter().map(|a| name(*a)).collect();
                let unsafe_kw = if self.unsafe_fn_ptr_types.contains(&ty_id) { "unsafe " } else { "" };
                let extern_kw = if self.program.c_fn_ptr_types.contains(&ty_id) { "extern " } else { "" };
                let mut s = format!("{unsafe_kw}{extern_kw}fn({})", params.join(", "));
                if !matches!(self.program.types[ret.0 as usize], Type::Void) {
                    s.push_str(&format!(" -> {}", name(*ret)));
                }
                if let Some(c) = self.fn_ptr_contract(ty_id)
                    && (!c.ret.is_empty() || !c.flows.is_empty())
                {
                    let items: Vec<String> = c
                        .ret
                        .iter()
                        .map(ToString::to_string)
                        .chain(c.flows.iter().map(|(d, src)| format!("{d}: {src}")))
                        .collect();
                    s.push_str(&format!(" borrows({})", items.join(", ")));
                }
                s
            }
            &Type::Ptr { mutable, pointee } => {
                format!("&{}{}", if mutable { "mut " } else { "" }, name(pointee))
            }
            &Type::Array { elem, len } => format!("[{}; {}]", name(elem), len),
            _ => self.program.type_label(ty_id),
        }
    }

    pub(super) fn packed_field_bit_width(&self, ty_id: TypeId) -> Option<(u16, bool)> {
        if self.raw_ptrs.contains_key(&ty_id)
            || self.named_opaques.contains(&ty_id)
            || self.uninit_types.contains_key(&ty_id)
        {
            return None;
        }
        if let Some(comp) = self.composites.get(&ty_id) {
            return if comp.is_packed {
                Some((comp.total_bits, false))
            } else {
                None
            };
        }
        if let Some(nt) = self.distinct_types.get(&ty_id) {
            return self.packed_field_bit_width(nt.underlying);
        }
        match &self.program.types[ty_id.0 as usize] {
            Type::Bool => Some((1, false)),
            Type::Int { signed, bits } => Some((*bits, *signed)),
            Type::Pattern { base, .. } => self.packed_field_bit_width(*base),
            _ => None,
        }
    }

    /// Checks an integer literal against the integer or pattern type `ty` it initializes: it must
    /// fit the base type and, for a pattern type, lie in its ranges. `Ok(None)` if `ty` is not an
    /// integer type at all.
    pub(super) fn check_int_literal(
        &self,
        v: &Wide,
        ty: TypeId,
    ) -> Result<Option<TypeId>, String> {
        // Structural, so literals also initialize enums, `c_*` integers, and distinct types over
        // integers.
        let base = match self.program.types[ty.0 as usize] {
            Type::Pattern { base, .. } => base,
            _ => ty,
        };
        let Type::Int { signed, bits } = self.program.types[base.0 as usize] else {
            return Ok(None);
        };
        if !v.fits(bits, signed) {
            return Err(format!(
                "Integer literal {v} does not fit in '{}'",
                self.type_display_name(ty)
            ));
        }
        if let Type::Pattern { ranges, .. } = &self.program.types[ty.0 as usize]
            && !crate::ir::pattern_contains(ranges, v)
        {
            return Err(format!(
                "Compile-time value {v} is outside valid pattern ranges of '{}'",
                self.type_display_name(ty)
            ));
        }
        Ok(Some(ty))
    }

    /// `(signed, bits, MIN, MAX)` of an integer or integer pattern type.
    pub(super) fn int_type_reflection(&self, ty_id: TypeId) -> Option<(bool, u16, Wide, Wide)> {
        if matches!(
            self.type_kind(ty_id),
            Some(TypeKind::Enum | TypeKind::Distinct | TypeKind::RawPtr | TypeKind::Composite)
        ) {
            return None;
        }
        match &self.program.types[ty_id.0 as usize] {
            &Type::Int { signed, bits } => Some((
                signed,
                bits,
                Wide::min_value(bits, signed),
                Wide::max_value(bits, signed),
            )),
            Type::Pattern { base, ranges } => {
                let (signed, bits, base_min, base_max) = self.int_type_reflection(*base)?;
                if ranges.is_empty() {
                    Some((signed, bits, base_min, base_max))
                } else {
                    let min = ranges.iter().map(|r| r.0).min().unwrap();
                    let max = ranges.iter().map(|r| r.1).max().unwrap();
                    Some((signed, bits, min, max))
                }
            }
            _ => None,
        }
    }

    /// Evaluates a bound of a pattern type over `base` as a constant of `base`.
    fn eval_pattern_bound(
        &mut self,
        mod_path: &str,
        self_ty: Option<TypeId>,
        env: &HashMap<String, ComptimeVal>,
        expr: &Expr,
        base: TypeId,
    ) -> Result<Wide, String> {
        let v = match self.eval_const_expr_typed(mod_path, self_ty, env, expr, Some(base))?.0 {
            c @ (ConstValue::I64(_) | ConstValue::Wide(_)) => const_to_wide(&c),
            other => {
                return Err(format!(
                    "Pattern range bound must be an integer constant, got {other:?}"
                ));
            }
        };
        if let Some((signed, bits, _, _)) = self.int_type_reflection(base)
            && !v.fits(bits, signed)
        {
            return Err(format!(
                "Pattern range bound {v} does not fit in '{}'",
                self.type_display_name(base)
            ));
        }
        Ok(v)
    }

    pub(super) fn type_expr_mentions_self(te: &TypeExpr) -> bool {
        match te {
            TypeExpr::SelfType => true,
            TypeExpr::Named(p) => p.len() == 1 && p[0] == "Self",
            TypeExpr::Ref { inner, .. }
            | TypeExpr::Ptr { inner, .. }
            | TypeExpr::Optional(inner)
            | TypeExpr::Uninit(inner)
            | TypeExpr::Slice { elem: inner, .. }
            | TypeExpr::RelRef(inner)
            | TypeExpr::RelSlice(inner)
            | TypeExpr::Array { elem: inner, .. }
            | TypeExpr::Simd { elem: inner, .. }
            | TypeExpr::Pattern { base: inner, .. } => Self::type_expr_mentions_self(inner),
            TypeExpr::Enum {
                backing: Some(b), ..
            }
            | TypeExpr::Union {
                backing: Some(b), ..
            }
            | TypeExpr::Error {
                backing: Some(b), ..
            } => Self::type_expr_mentions_self(b),
            TypeExpr::Overlay(fields) => fields
                .iter()
                .any(|(_, te)| Self::type_expr_mentions_self(te)),
            TypeExpr::Result { err, ok } => {
                Self::type_expr_mentions_self(err) || Self::type_expr_mentions_self(ok)
            }
            TypeExpr::ErrorSetUnion(terms)
            | TypeExpr::TraitBounds(terms)
            | TypeExpr::Tuple(terms) => terms.iter().any(Self::type_expr_mentions_self),
            TypeExpr::FnPtr { params, ret, .. } => {
                params.iter().any(Self::type_expr_mentions_self)
                    || Self::type_expr_mentions_self(ret)
            }
            TypeExpr::TypeCall { args, .. } => args.iter().any(|a| match a {
                Expr::TypeVal(inner_te) => Self::type_expr_mentions_self(inner_te),
                Expr::Path(p) => p.len() == 1 && p[0] == "Self",
                _ => false,
            }),
            _ => false,
        }
    }

    pub(super) fn instantiate_trait(
        &mut self,
        mod_path: &str,
        type_name: &str,
        env: &HashMap<String, ComptimeVal>,
        memo_key: Option<(String, String, Vec<ComptimeVal>)>,
        methods: &[TraitMethodDecl],
        kind: TraitKind,
        assoc: &[AssocItem],
    ) -> Result<TypeId, String> {
        let ty_id = self.alloc_distinct_type(Type::Void);
        self.traits.insert(
            ty_id,
            TraitInfo {
                name: type_name.to_string(),
                def_module: mod_path.to_string(),
                comptime_env: env.clone(),
                methods: methods.to_vec(),
                kind,
                assoc: assoc.to_vec(),
            },
        );
        if let Some(key) = memo_key {
            self.memoized_type_calls.insert(key, ty_id);
        }
        Ok(ty_id)
    }

    pub(super) fn instantiate_trait_obj_type(
        &mut self,
        trait_ty: TypeId,
        mutable: bool,
    ) -> Result<TypeId, String> {
        if let Some(&existing) = self.memoized_trait_objs.get(&(trait_ty, mutable)) {
            return Ok(existing);
        }
        let Some(trait_info) = self.traits.get(&trait_ty).cloned() else {
            return Err(format!("Type '{}' is not a trait", self.type_display_name(trait_ty)));
        };
        let mut_prefix = if mutable { "mut " } else { "" };

        // Validate VTable Eligibility (Object Safety)
        for m in &trait_info.methods {
            if m.params.iter().any(|p| p.is_comptime) {
                return Err(format!(
                    "Trait '{}' is not object-safe and cannot form '&{}{}': method '{}' has comptime parameters",
                    trait_info.name, mut_prefix, trait_info.name, m.name
                ));
            }
            let Some(first_param) = m.params.first() else {
                return Err(format!(
                    "Trait '{}' is not object-safe and cannot form '&{}{}': method '{}' has no 'self: &Self' or 'self: &mut Self' receiver",
                    trait_info.name, mut_prefix, trait_info.name, m.name
                ));
            };
            let is_ref_self = first_param.name == "self"
                && matches!(
                    &first_param.ty,
                    TypeExpr::Ref { inner, .. }
                        if matches!(inner.as_ref(), TypeExpr::SelfType)
                            || matches!(inner.as_ref(), TypeExpr::Named(p) if p.len() == 1 && p[0] == "Self")
                );
            if !is_ref_self {
                return Err(format!(
                    "Trait '{}' is not object-safe and cannot form '&{}{}': method '{}' must take 'self: &Self' or 'self: &mut Self' (not by value or without receiver)",
                    trait_info.name, mut_prefix, trait_info.name, m.name
                ));
            }
            for p in &m.params[1..] {
                if Self::type_expr_mentions_self(&p.ty) {
                    return Err(format!(
                        "Trait '{}' is not object-safe and cannot form '&{}{}': parameter '{}' of method '{}' mentions 'Self'",
                        trait_info.name, mut_prefix, trait_info.name, p.name, m.name
                    ));
                }
            }
            if Self::type_expr_mentions_self(&m.ret_ty) {
                return Err(format!(
                    "Trait '{}' is not object-safe and cannot form '&{}{}': return type of method '{}' mentions 'Self'",
                    trait_info.name, mut_prefix, trait_info.name, m.name
                ));
            }
        }

        let u8_ty = self.intern_type(Type::Int {
            signed: false,
            bits: 8,
        });
        let data_ptr_ty = self.intern_type(Type::Ptr {
            mutable,
            pointee: u8_ty,
        });
        let mut method_fn_ptr_tys = Vec::with_capacity(trait_info.methods.len());
        for m in &trait_info.methods {
            let recv_mut = matches!(&m.params[0].ty, TypeExpr::Ref { mutable: true, .. });
            let erased_self_ty = self.intern_type(Type::Ptr {
                mutable: recv_mut,
                pointee: u8_ty,
            });
            let mut arg_tys = Vec::with_capacity(m.params.len());
            arg_tys.push(erased_self_ty);
            for p in &m.params[1..] {
                arg_tys.push(self.resolve_type_expr(
                    &trait_info.def_module,
                    None,
                    &trait_info.comptime_env,
                    &p.ty,
                )?);
            }
            let ret_ty = self.resolve_type_expr(
                &trait_info.def_module,
                None,
                &trait_info.comptime_env,
                &m.ret_ty,
            )?;
            let contract = self.trait_method_contract(m, ret_ty)?;
            method_fn_ptr_tys.push(self.intern_fn_ptr_type(arg_tys, ret_ty, contract, m.is_unsafe));
        }

        let vtable_ty = self.alloc_distinct_type(Type::Struct(method_fn_ptr_tys.clone()));
        let vtable_ptr_ty = self.intern_type(Type::Ptr {
            mutable: false,
            pointee: vtable_ty,
        });
        let obj_ty = self.alloc_distinct_type(Type::Struct(vec![data_ptr_ty, vtable_ptr_ty]));
        self.trait_objs.insert(
            obj_ty,
            TraitObjInfo {
                trait_ty,
                mutable,
                data_ptr_ty,
                vtable_ty,
                vtable_ptr_ty,
                method_fn_ptr_tys,
            },
        );
        self.memoized_trait_objs.insert((trait_ty, mutable), obj_ty);
        Ok(obj_ty)
    }

    /// Returns the function implementing method `method_idx` of trait `trait_ty` for `concrete_ty`.
    /// Conformance is explicit: the type must have exactly one `impl` of the trait (inline in its
    /// body, or module-level in the type's or the trait's module); matching method names alone
    /// never make a type conform. For trait methods with `comptime` parameters, only presence and
    /// arity are checked and `FuncId(0)` is returned (they are instantiated at call sites).
    pub(super) fn resolve_trait_impl_method(
        &mut self,
        _caller_mod: &str,
        concrete_ty: TypeId,
        trait_ty: TypeId,
        method_idx: usize,
        _enforce_orphan_rule: bool,
    ) -> Result<FuncId, String> {
        let trait_info = self.traits[&trait_ty].clone();
        let m = trait_info.methods[method_idx].clone();
        let key = (concrete_ty, trait_ty, m.name.clone());
        if let Some(&fn_id) = self.memoized_impl_methods.get(&key) {
            return Ok(fn_id);
        }
        if trait_info.kind == TraitKind::Structural {
            let fn_id = self.resolve_structural_method(concrete_ty, trait_ty, method_idx)?;
            self.memoized_impl_methods.insert(key, fn_id);
            return Ok(fn_id);
        }
        let type_display = self.type_display_name(concrete_ty);
        let imp = self.find_trait_impl(concrete_ty, trait_ty)?;
        if let Some(c) = imp.consts.iter().find(|c| !trait_info.assoc.iter().any(|a| a.name == c.name)) {
            return Err(format!(
                "'const {}' in {} is not an associated item of trait '{}'",
                c.name, imp.origin, trait_info.name
            ));
        }
        self.check_assoc_items(concrete_ty, trait_ty)?;

        for im in &imp.methods {
            if !trait_info.methods.iter().any(|tm| tm.name == im.name) {
                return Err(format!(
                    "Method '{}' in {} is not declared by trait '{}'",
                    im.name, imp.origin, trait_info.name
                ));
            }
        }
        let Some(decl) = imp.methods.iter().find(|d| d.name == m.name).cloned() else {
            return Err(format!(
                "{} is missing trait method '{}'",
                imp.origin, m.name
            ));
        };
        if decl.params.len() != m.params.len() {
            return Err(format!(
                "Method '{}' in {} has {} parameters, but trait '{}' declares {}",
                m.name,
                imp.origin,
                decl.params.len(),
                trait_info.name,
                m.params.len()
            ));
        }
        if m.params.iter().any(|p| p.is_comptime) {
            return Ok(FuncId(0));
        }

        // The implementation's borrow contract is the trait method's: written out identically or
        // omitted (inherited).
        let mut decl = decl;
        let as_set = |items: &Option<Vec<BorrowContractItem>>| {
            let mut v: Vec<String> = items
                .iter()
                .flatten()
                .map(|i| format!("{i:?}"))
                .collect();
            v.sort();
            v
        };
        if decl.borrows.is_none() {
            decl.borrows = m.borrows.clone();
        } else if as_set(&decl.borrows) != as_set(&m.borrows) {
            return Err(format!(
                "Method '{}' in {} declares a borrows(...) contract that differs from trait '{}'",
                m.name, imp.origin, trait_info.name
            ));
        }
        if decl.is_unsafe != m.is_unsafe {
            let (want, have) = if m.is_unsafe {
                ("unsafe fn", "fn")
            } else {
                ("fn", "unsafe fn")
            };
            return Err(format!(
                "Method '{}' in {} is declared '{have}', but trait '{}' declares it '{want}'",
                m.name, imp.origin, trait_info.name
            ));
        }
        decl.vis = Visibility::Pub;

        let mut expected_param_tys = Vec::new();
        for p in &m.params {
            expected_param_tys.push(self.resolve_type_expr(
                &trait_info.def_module,
                Some(concrete_ty),
                &trait_info.comptime_env,
                &p.ty,
            )?);
        }
        let expected_ret_ty = self.resolve_type_expr(
            &trait_info.def_module,
            Some(concrete_ty),
            &trait_info.comptime_env,
            &m.ret_ty,
        )?;

        let prev = self.schedule_no_private;
        self.schedule_no_private = !imp.private_access;
        let scheduled = self.schedule_method(&imp.def_module, concrete_ty, &imp.env, &decl);
        self.schedule_no_private = prev;
        let fn_id = scheduled?;
        if let Some(f) = self.program.functions.iter_mut().find(|f| f.id == fn_id) {
            f.debug_name = Some(format!("<{} as {}>::{}", type_display, trait_info.name, m.name));
        }
        let (actual_params, actual_ret) = self.func_sigs[&fn_id].clone();
        if actual_params != expected_param_tys || actual_ret != expected_ret_ty {
            return Err(format!(
                "Method '{}' in {} has a signature incompatible with trait '{}'",
                m.name, imp.origin, trait_info.name
            ));
        }
        self.memoized_impl_methods.insert(key, fn_id);
        Ok(fn_id)
    }

    /// The method meeting structural trait `trait_ty`'s method `method_idx` for `concrete_ty`: a
    /// `pub` method of the type's own, or one a trait it implements gives it, with the arity,
    /// safety, borrow contract, and signature the trait declares.
    fn resolve_structural_method(
        &mut self,
        concrete_ty: TypeId,
        trait_ty: TypeId,
        method_idx: usize,
    ) -> Result<FuncId, String> {
        let trait_info = self.traits[&trait_ty].clone();
        let m = &trait_info.methods[method_idx];
        let type_display = self.type_display_name(concrete_ty);
        let unmet = |why: String| {
            format!(
                "Type '{type_display}' does not meet 'trait(structural) {}': {why}",
                trait_info.name
            )
        };
        let own = match (self.composites.get(&concrete_ty), self.distinct_types.get(&concrete_ty)) {
            (Some(c), _) => c
                .methods
                .get(&m.name)
                .map(|(v, d)| (*v, d.clone(), c.def_module.clone(), c.comptime_env.clone())),
            (None, Some(d)) => d
                .methods
                .get(&m.name)
                .map(|(v, f)| (*v, f.clone(), d.def_module.clone(), d.comptime_env.clone())),
            _ => None,
        };
        // What the trait's signature is compared with, and how to get the method's function.
        let (params, is_unsafe, borrows, origin) = match &own {
            Some((vis, decl, ..)) => {
                if !matches!(vis, Visibility::Pub | Visibility::Export) {
                    return Err(unmet(format!("its method '{}' is not 'pub'", m.name)));
                }
                (decl.params.clone(), decl.is_unsafe, decl.borrows.clone(), None)
            }
            None => {
                let mut found = None;
                for t in self.traits_implemented_by(concrete_ty)? {
                    if let Some(i) = self.traits[&t].methods.iter().position(|tm| tm.name == m.name) {
                        found = Some((t, i));
                        break;
                    }
                }
                let Some((t, i)) = found else {
                    return Err(unmet(format!("it has no method '{}'", m.name)));
                };
                let tm = self.traits[&t].methods[i].clone();
                (tm.params, tm.is_unsafe, tm.borrows, Some((t, i)))
            }
        };
        if params.len() != m.params.len()
            || params.iter().zip(&m.params).any(|(a, b)| a.is_comptime != b.is_comptime)
        {
            return Err(unmet(format!(
                "its method '{}' takes {} parameters, and the trait's takes {}",
                m.name,
                params.len(),
                m.params.len()
            )));
        }
        if is_unsafe != m.is_unsafe {
            return Err(unmet(format!(
                "its method '{}' is {}'unsafe fn'",
                m.name,
                if is_unsafe { "" } else { "not " }
            )));
        }
        let as_set = |items: &Option<Vec<BorrowContractItem>>| {
            let mut v: Vec<String> = items.iter().flatten().map(|i| format!("{i:?}")).collect();
            v.sort();
            v
        };
        if as_set(&borrows) != as_set(&m.borrows) {
            return Err(unmet(format!(
                "its method '{}' declares a different borrows(...) contract",
                m.name
            )));
        }
        if m.params.iter().any(|p| p.is_comptime) {
            return Ok(FuncId(0));
        }
        let fn_id = match (own, origin) {
            (Some((_, decl, def_mod, env)), _) => {
                self.schedule_method(&def_mod, concrete_ty, &env, &decl)?
            }
            (None, Some((t, i))) => self.resolve_trait_impl_method("", concrete_ty, t, i, false)?,
            (None, None) => unreachable!("a method was found above"),
        };
        let mut expected_params = Vec::new();
        for p in &m.params {
            expected_params.push(self.resolve_type_expr(
                &trait_info.def_module,
                Some(concrete_ty),
                &trait_info.comptime_env,
                &p.ty,
            )?);
        }
        let expected_ret = self.resolve_type_expr(
            &trait_info.def_module,
            Some(concrete_ty),
            &trait_info.comptime_env,
            &m.ret_ty,
        )?;
        let (actual_params, actual_ret) = self.func_sigs[&fn_id].clone();
        if actual_params != expected_params || actual_ret != expected_ret {
            return Err(unmet(format!(
                "its method '{}' has a different signature",
                m.name
            )));
        }
        Ok(fn_id)
    }

    /// The module that defines a nominal type, if any (builtin and structural types have none).
    fn type_def_module(&self, ty: TypeId) -> Option<String> {
        if let Some(c) = self.composites.get(&ty) {
            return Some(c.def_module.clone());
        }
        if let Some(nt) = self.distinct_types.get(&ty) {
            return Some(nt.def_module.clone());
        }
        self.named_types
            .iter()
            .find(|(_, t)| **t == ty)
            .map(|((m, _), _)| m.clone())
    }

    /// Finds the single `impl` of `trait_ty` for `concrete_ty`, enforcing coherence: at most one
    /// implementation may apply, and a module-level `impl` must live in the module defining the
    /// type or the module defining the trait (the orphan rule).
    pub(super) fn find_trait_impl(
        &mut self,
        concrete_ty: TypeId,
        trait_ty: TypeId,
    ) -> Result<ImplMatch, String> {
        let mut found: Vec<ImplMatch> = self
            .collect_trait_impls(concrete_ty, Some(trait_ty))?
            .into_iter()
            .map(|(_, m)| m)
            .collect();
        let trait_name = self.traits[&trait_ty].name.clone();
        let type_display = self.type_display_name(concrete_ty);
        match found.len() {
            0 => Err(format!(
                "Type '{type_display}' does not implement trait '{trait_name}'; add 'impl {trait_name} {{ ... }}' to the type's body or 'impl {trait_name} for {type_display} {{ ... }}' in the type's or the trait's module{}",
                self.blanket_impl_hint(trait_ty)
            )),
            1 => Ok(found.pop().unwrap()),
            _ => Err(format!(
                "Conflicting implementations of trait '{trait_name}' for '{type_display}': {} and {}",
                found[0].origin, found[1].origin
            )),
        }
    }

    /// For a trait with an impl for every type meeting a bound (`impl[A: Allocator + copy]
    /// Storage for A`), what that bound is, as another way to meet it.
    fn blanket_impl_hint(&mut self, trait_ty: TypeId) -> String {
        fn show(t: &TypeExpr) -> String {
            match t {
                TypeExpr::Named(path) => path.join("::"),
                TypeExpr::Constraint(c) => c.name().to_string(),
                TypeExpr::TraitBounds(all) => all.iter().map(show).collect::<Vec<_>>().join(" + "),
                _ => "its bound".to_string(),
            }
        }
        let impls = self.module_impls.clone().unwrap_or_default();
        for (mod_name, d) in impls.iter() {
            let TypeExpr::Named(target) = &d.for_ty else { continue };
            let Some(p) = d.comptime_params.iter().find(|p| target.len() == 1 && p.name == target[0]) else {
                continue;
            };
            if self.resolve_type_expr(mod_name, None, &HashMap::new(), &d.trait_expr).ok() == Some(trait_ty) {
                return format!("; or meet '{}', as every such type implements it", show(&p.ty));
            }
        }
        String::new()
    }

    /// Whether trait `t` is in scope in `mod_path`: declared there, or reachable under its name
    /// through an import (including the prelude) of the declaring module's item.
    pub(super) fn trait_in_scope(&self, mod_path: &str, t: TypeId) -> bool {
        let Some(tr) = self.traits.get(&t) else {
            return false;
        };
        if tr.def_module == mod_path {
            return true;
        }
        let base = tr.name.split('(').next().unwrap_or(&tr.name).to_string();
        matches!(
            self.resolve_path(mod_path, std::slice::from_ref(&base)),
            Ok(ResolvedItem::Type(m, n) | ResolvedItem::Func(m, n))
                if m == tr.def_module && n == base
        )
    }

    /// The traits `concrete_ty` has an `impl` for, deduplicated, in a deterministic order.
    pub(super) fn traits_implemented_by(&mut self, concrete_ty: TypeId) -> Result<Vec<TypeId>, String> {
        let mut out = Vec::new();
        for (t, _) in self.collect_trait_impls(concrete_ty, None)? {
            if !out.contains(&t) {
                out.push(t);
            }
        }
        Ok(out)
    }

    /// Collects `(trait, impl)` pairs applying to `concrete_ty`, optionally only for `trait_filter`.
    pub(super) fn collect_trait_impls(
        &mut self,
        concrete_ty: TypeId,
        trait_filter: Option<TypeId>,
    ) -> Result<Vec<(TypeId, ImplMatch)>, String> {
        if let Some(cached) = self.trait_impl_cache.get(&(concrete_ty, trait_filter)) {
            return Ok(cached.clone());
        }
        if let Some(tf) = trait_filter
            && let Some(all_cached) = self.trait_impl_cache.get(&(concrete_ty, None))
        {
            let filtered: Vec<_> = all_cached
                .iter()
                .filter(|(t, _)| *t == tf)
                .cloned()
                .collect();
            self.trait_impl_cache
                .insert((concrete_ty, trait_filter), filtered.clone());
            return Ok(filtered);
        }
        // A bound that leads back here (`impl[A: L] L for A`) is unmet, not a loop.
        if !self.impls_in_progress.insert((concrete_ty, trait_filter)) {
            return Ok(Vec::new());
        }
        let found = self.collect_trait_impls_uncached(concrete_ty, trait_filter);
        self.impls_in_progress.remove(&(concrete_ty, trait_filter));
        let found = found?;
        self.trait_impl_cache
            .insert((concrete_ty, trait_filter), found.clone());
        Ok(found)
    }

    /// An `unsafe trait` is implemented only by `unsafe impl`, which is where its author takes
    /// on what it promises; `unsafe impl` of any other trait asserts nothing. A structural trait
    /// is met by methods, and takes no `impl` at all.
    fn check_impl_safety(&self, trait_ty: TypeId, is_unsafe: bool, what: &str) -> Result<(), String> {
        let info = &self.traits[&trait_ty];
        match (info.kind, is_unsafe) {
            (TraitKind::Structural, _) => Err(format!(
                "{what} implements 'trait(structural) {}', which a type meets by having its methods; write them as the type's own methods instead",
                info.name
            )),
            (TraitKind::Unsafe, false) => Err(format!(
                "{what} implements 'unsafe trait {}', whose promises the compiler cannot check; write 'unsafe impl'",
                info.name
            )),
            (TraitKind::Nominal, true) => Err(format!(
                "{what} is 'unsafe impl' of '{}', which is not an 'unsafe trait', so it asserts nothing",
                info.name
            )),
            _ => Ok(()),
        }
    }

    fn collect_trait_impls_uncached(
        &mut self,
        concrete_ty: TypeId,
        trait_filter: Option<TypeId>,
    ) -> Result<Vec<(TypeId, ImplMatch)>, String> {
        let type_display = self.type_display_name(concrete_ty);
        let mut found = Vec::new();

        // 1. `impl Tr { ... }` inside the type's own body.
        for b in self.inline_impls.get(&concrete_ty).cloned().unwrap_or_default() {
            let t = self.resolve_type_expr(&b.def_module, Some(concrete_ty), &b.env, &b.trait_expr)?;
            if !self.traits.contains_key(&t) {
                return Err(format!(
                    "'impl' in the body of '{type_display}' names '{}', which is not a trait",
                    self.type_display_name(t)
                ));
            }
            self.check_impl_safety(t, b.is_unsafe, &format!("'impl' in the body of '{type_display}'"))?;
            if trait_filter.is_none_or(|f| f == t) {
                let trait_name = self.traits[&t].name.clone();
                found.push((
                    t,
                    ImplMatch {
                        def_module: b.def_module.clone(),
                        env: b.env.clone(),
                        methods: b.methods.clone(),
                        private_access: true,
                        origin: format!("'impl {trait_name}' in the body of '{type_display}'"),
                        consts: Vec::new(),
                    },
                ));
            }
        }

        // 2. Module-level `impl Tr for T { ... }` / `impl[...] Tr for F[T] { ... }`.
        if self.module_impls.is_none() {
            let mut all: Vec<(String, crate::ast::ImplDecl)> = Vec::new();
            for (mod_name, ast) in &self.modules {
                for item in &ast.items {
                    if let Item::Impl(d) = item {
                        all.push((mod_name.clone(), d.clone()));
                    }
                }
            }
            all.sort_by(|a, b| a.0.cmp(&b.0));
            self.module_impls = Some(std::sync::Arc::new(all));
        }
        let module_impls = self.module_impls.clone().unwrap();
        for (mod_name, d) in module_impls.iter() {
            let env = if d.comptime_params.is_empty() {
                let for_ty = self.resolve_type_expr(mod_name, None, &HashMap::new(), &d.for_ty)?;
                if for_ty != concrete_ty {
                    continue;
                }
                HashMap::new()
            } else {
                let params: Vec<(String, TypeExpr)> = d
                    .comptime_params
                    .iter()
                    .map(|p| (p.name.clone(), p.ty.clone()))
                    .collect();
                let mut inferred = HashMap::new();
                if self
                    .unify_type_pattern(mod_name, &params, &d.for_ty, concrete_ty, &mut inferred)?
                    .is_none()
                    || params.iter().any(|(n, _)| !inferred.contains_key(n))
                {
                    continue;
                }
                // An impl of another trait needs no look at its bounds, which can be costly:
                // checking them collects impls again (`impl[A: K] L for A` asks for `K`).
                if let Some(f) = trait_filter
                    && let Ok(t) = self.resolve_type_expr(mod_name, Some(concrete_ty), &inferred, &d.trait_expr)
                    && t != f
                {
                    continue;
                }
                let mut bounds_ok = true;
                for (n, bound) in &params {
                    if let Some(ComptimeVal::Type(arg)) = inferred.get(n).cloned()
                        && !matches!(
                            self.eval_comptime_type_bound(mod_name, None, &inferred, bound, arg)?,
                            Some(Ok(_))
                        )
                    {
                        bounds_ok = false;
                    }
                }
                if !bounds_ok {
                    continue;
                }
                // Guard against a pattern that unified loosely: the instantiation must be exact.
                let for_ty = self.resolve_type_expr(mod_name, None, &inferred, &d.for_ty)?;
                if for_ty != concrete_ty {
                    continue;
                }
                inferred
            };
            let t = self.resolve_type_expr(mod_name, Some(concrete_ty), &env, &d.trait_expr)?;
            if !self.traits.contains_key(&t) {
                return Err(format!(
                    "'impl ... for {type_display}' in module '{mod_name}' names '{}', which is not a trait",
                    self.type_display_name(t)
                ));
            }
            if trait_filter.is_some_and(|f| f != t) {
                continue;
            }
            self.check_impl_safety(t, d.is_unsafe, &format!("'impl ... for {type_display}' in module '{mod_name}'"))?;
            let trait_info = self.traits[&t].clone();
            let type_mod = self.type_def_module(concrete_ty);
            if *mod_name != trait_info.def_module && type_mod.as_deref() != Some(mod_name.as_str()) {
                let t_mod = type_mod.unwrap_or_else(|| "<builtin>".to_string());
                return Err(format!(
                    "Orphan rule violation: 'impl {} for {type_display}' in module '{mod_name}' must be written in the module defining '{type_display}' ('{t_mod}') or the module defining '{}' ('{}')",
                    trait_info.name, trait_info.name, trait_info.def_module
                ));
            }
            found.push((
                t,
                ImplMatch {
                    def_module: mod_name.clone(),
                    env,
                    methods: d.methods.clone(),
                    consts: d.consts.clone(),
                    private_access: false,
                    origin: format!(
                        "'impl {} for {type_display}' in module '{mod_name}'",
                        trait_info.name
                    ),
                },
            ));
        }
        Ok(found)
    }

    pub(super) fn get_or_create_vtable(
        &mut self,
        caller_mod: &str,
        concrete_ty: TypeId,
        trait_ty: TypeId,
    ) -> Result<(GlobalId, Vec<FuncId>), String> {
        if let Some(existing) = self.memoized_vtables.get(&(concrete_ty, trait_ty)).cloned() {
            return Ok(existing);
        }
        let obj_ty = self.instantiate_trait_obj_type(trait_ty, false)?;
        let tobj_info = self.trait_objs[&obj_ty].clone();
        let method_count = self.traits[&trait_ty].methods.len();
        let mut thunk_ids = Vec::with_capacity(method_count);

        for m_idx in 0..method_count {
            let target_fn_id =
                self.resolve_trait_impl_method(caller_mod, concrete_ty, trait_ty, m_idx, true)?;
            let fn_ptr_ty = tobj_info.method_fn_ptr_tys[m_idx];
            let Type::FnPtr {
                args: thunk_arg_tys,
                ret: thunk_ret_ty,
            } = self.program.types[fn_ptr_ty.0 as usize].clone()
            else {
                unreachable!()
            };
            let (impl_arg_tys, _) = self.func_sigs[&target_fn_id].clone();
            let thunk_id =
                self.reserve_function(Visibility::Private, None, &thunk_arg_tys, thunk_ret_ty);

            let typed_self_local = LocalId((thunk_arg_tys.len() + 1) as u32);
            let mut locals = vec![thunk_ret_ty];
            locals.extend_from_slice(&thunk_arg_tys);
            locals.push(impl_arg_tys[0]);

            let mut call_args = Vec::with_capacity(thunk_arg_tys.len());
            let self_op = if self.is_copy_type(impl_arg_tys[0]) {
                Operand::Copy(Place::new(typed_self_local))
            } else {
                Operand::Move(Place::new(typed_self_local))
            };
            call_args.push(self_op);
            for (i, &arg_ty) in thunk_arg_tys.iter().enumerate().skip(1) {
                let loc = LocalId((i + 1) as u32);
                if self.is_copy_type(arg_ty) {
                    call_args.push(Operand::Copy(Place::new(loc)));
                } else {
                    call_args.push(Operand::Move(Place::new(loc)));
                }
            }

            let blocks = vec![
                BasicBlock {
                    statements: vec![Statement::Assign(
                        Place::new(typed_self_local),
                        Rvalue::Cast(Operand::Copy(Place::new(LocalId(1))), impl_arg_tys[0]),
                    )],
                    terminator: Terminator::Call {
                        func: Operand::Const(ConstValue::Func(target_fn_id)),
                        args: call_args,
                        destination: Place::new(LocalId(0)),
                        target: BlockId(1),
                    },
                },
                BasicBlock {
                    statements: Vec::new(),
                    terminator: Terminator::Return,
                },
            ];

            let (target_rb, target_pb) = self
                .program
                .functions
                .iter()
                .find(|f| f.id == target_fn_id)
                .map(|f| (f.ret_borrows.clone(), f.param_borrows.clone()))
                .unwrap_or((None, None));

            let thunk_name = format!(
                "<{} as {}>::{}",
                self.type_display_name(concrete_ty),
                self.traits[&trait_ty].name,
                self.traits[&trait_ty].methods[m_idx].name
            );
            if let Some(func) = self.program.functions.iter_mut().find(|f| f.id == thunk_id) {
                func.debug_name = Some(thunk_name);
                func.locals = locals;
                func.blocks = blocks;
                func.ret_borrows = target_rb;
                func.param_borrows = target_pb;
            }
            thunk_ids.push(thunk_id);
        }

        let gl_id = GlobalId(self.program.globals.len() as u32);
        self.program.globals.push(Global {
            id: gl_id,
            ty: tobj_info.vtable_ty,
            mutable: true,
            init: ConstValue::Void,
        });
        self.memoized_vtables
            .insert((concrete_ty, trait_ty), (gl_id, thunk_ids.clone()));
        Ok((gl_id, thunk_ids))
    }

    pub(super) fn resolve_named_type(
        &mut self,
        mod_path: &str,
        name: &str,
    ) -> Result<TypeId, String> {
        let key = (mod_path.to_string(), name.to_string());
        if let Some(&id) = self.named_types.get(&key) {
            return Ok(id);
        }
        let Some((def_mod, orig_name, Item::TypeDecl { vis, ty, alias, .. }, _)) =
            self.find_item_in_module(mod_path, mod_path, name)?
        else {
            return Err(format!("Type '{name}' not found in '{mod_path}'"));
        };
        let def_key = (def_mod.clone(), orig_name.clone());
        if alias || !Self::is_reservable(&ty) {
            if self.resolving_named.contains(&def_key) {
                return Err(format!(
                    "Type '{name}' is defined in terms of itself; only a struct, union, overlay or opaque can refer to itself"
                ));
            }
            self.resolving_named.push(def_key.clone());
        }
        let env = HashMap::new();
        let resolved = if alias {
            self.resolve_type_expr(&def_mod, None, &env, &ty)
        } else if Self::is_reservable(&ty) {
            let id = self.alloc_distinct_type(Type::Void);
            self.named_types.insert(key.clone(), id);
            self.named_types.insert(def_key.clone(), id);
            let built = self.with_reserved_type(id, |c| {
                c.instantiate_type_decl(&def_mod, &orig_name, &env, &ty)
            });
            if built.is_err() {
                self.named_types.remove(&key);
                self.named_types.remove(&def_key);
            }
            built
        } else {
            self.instantiate_type_decl(&def_mod, &orig_name, &env, &ty)
        };
        if alias || !Self::is_reservable(&ty) {
            self.resolving_named.pop();
        }
        let ty_id = resolved?;
        self.named_types.insert(key, ty_id);
        if alias {
            return Ok(ty_id);
        }
        if vis.is_export() {
            self.register_and_validate_exported_type(&def_mod, &orig_name, ty_id, &ty)?;
        }
        Ok(ty_id)
    }

    pub fn as_optional_type(&self, ty_id: TypeId) -> Option<TypeId> {
        if self.results.contains_key(&ty_id)
            || self.errors.contains_key(&ty_id)
            || self.unions.contains_key(&ty_id)
        {
            return None;
        }
        if let Type::Union { variants, .. } = &self.program.types[ty_id.0 as usize]
            && variants.len() == 2
            && matches!(self.program.types[variants[0].0 as usize], Type::Void)
        {
            Some(variants[1])
        } else {
            None
        }
    }

    pub fn as_nullable_raw_ptr(&self, ty_id: TypeId) -> Option<(bool, TypeId, TypeId)> {
        let inner = self.as_optional_type(ty_id)?;
        let &(mutable, pointee) = self.raw_ptrs.get(&inner)?;
        Some((mutable, pointee, inner))
    }

    /// Whether a type expression declares a type whose id can be handed out before it is built.
    pub(super) fn is_reservable(te: &TypeExpr) -> bool {
        matches!(
            te,
            TypeExpr::Struct { .. }
                | TypeExpr::Union { .. }
                | TypeExpr::Overlay(_)
                | TypeExpr::Opaque(_)
        )
    }

    /// Builds the type `id` with `build`. Its id exists first, so that a field can name the type
    /// behind a pointer, directly or through other types being built. A type stays unfinished
    /// until every type of its cycle is defined, and only then does `finish_types` run the
    /// type functions the cycle put off, which therefore never see a half-built argument.
    pub(super) fn with_reserved_type(
        &mut self,
        id: TypeId,
        build: impl FnOnce(&mut Self) -> Result<TypeId, String>,
    ) -> Result<TypeId, String> {
        if self.type_depth >= MAX_TYPE_NESTING {
            return Err(format!(
                "Type '{}' nests more than {MAX_TYPE_NESTING} types deep; it may instantiate itself with ever larger arguments",
                self.type_display_name(id)
            ));
        }
        self.type_depth += 1;
        let depth = self.type_depth;
        self.pending_types.insert(id, depth);
        self.reserved_type = Some(id);
        let built = build(self);
        self.type_depth -= 1;
        self.reserved_type = None;
        if built.is_err() {
            self.pending_types.remove(&id);
            if self.type_depth == 0 {
                self.abandon_types();
            }
            return built;
        }
        if self.cycle_floor >= depth {
            self.cycle_floor = usize::MAX;
            self.finish_types(depth)?;
        }
        built
    }

    /// Forgets the unfinished types after a failed build, which a caller may survive.
    fn abandon_types(&mut self) {
        let pending = std::mem::take(&mut self.pending_types);
        self.memoized_type_calls.retain(|_, t| !pending.contains_key(t));
        self.deferred_types.clear();
        self.reserved_calls.clear();
        self.finishing_types.clear();
        self.finishing = false;
        self.cycle_floor = usize::MAX;
        let held = std::mem::take(&mut self.held_funcs);
        self.pending_funcs.extend(held);
    }

    /// Takes the id reserved for the declaration now starting.
    pub(super) fn take_reserved_type(&mut self) -> Option<TypeId> {
        self.reserved_type.take()
    }

    /// Records the definition of a type, under its reserved id if it has one.
    pub(super) fn define_type(
        &mut self,
        reserved: Option<TypeId>,
        name: &str,
        ty: Type,
    ) -> Result<TypeId, String> {
        let Some(id) = reserved else {
            return Ok(self.alloc_distinct_type(ty));
        };
        self.program.types[id.0 as usize] = ty;
        if self.holds_by_value(id, &mut Vec::new(), &|_, t| t == id) {
            return Err(format!(
                "Type '{name}' holds itself by value, which needs infinite space; put a pointer, `Box` or `Vec` between them"
            ));
        }
        Ok(id)
    }

    /// Whether a value of `ty` has inside it, not behind a pointer, a type `found` accepts.
    fn holds_by_value(
        &self,
        ty: TypeId,
        visiting: &mut Vec<TypeId>,
        found: &dyn Fn(&Self, TypeId) -> bool,
    ) -> bool {
        let parts: &[TypeId] = match &self.program.types[ty.0 as usize] {
            Type::Struct(parts) | Type::Overlay(parts) => parts,
            Type::Union { variants, .. } => variants,
            Type::Array { elem, .. } | Type::Simd { elem, .. } => std::slice::from_ref(elem),
            Type::Pattern { base, .. } => std::slice::from_ref(base),
            _ => &[],
        };
        for &part in parts {
            if found(self, part) {
                return true;
            }
            if !visiting.contains(&part) {
                visiting.push(part);
                if self.holds_by_value(part, visiting, found) {
                    return true;
                }
            }
        }
        false
    }

    /// Whether the size of `ty` is not known yet.
    pub(super) fn layout_is_pending(&self, ty: TypeId) -> bool {
        let pending = |c: &Self, t: TypeId| c.pending_types.contains_key(&t);
        pending(self, ty) || self.holds_by_value(ty, &mut Vec::new(), &pending)
    }

    /// Whether `ty` or a type of its cycle has no definition yet.
    pub(super) fn type_is_unfinished(&self, ty: TypeId) -> bool {
        self.pending_types.contains_key(&ty) || self.finishing_types.contains(&ty)
    }

    /// Whether some type is being built, so that a function body could reach one undefined.
    pub(super) fn types_are_unfinished(&self) -> bool {
        !self.pending_types.is_empty() || !self.finishing_types.is_empty()
    }

    /// The outermost unfinished type `ty` mentions, at any distance, if it mentions one.
    fn unfinished_depth(&self, ty: TypeId, visiting: &mut Vec<TypeId>) -> Option<usize> {
        if visiting.contains(&ty) {
            return None;
        }
        visiting.push(ty);
        if let Some(&depth) = self.pending_types.get(&ty) {
            return Some(depth);
        }
        let parts: Vec<TypeId> = match &self.program.types[ty.0 as usize] {
            Type::Ptr { pointee, .. } => vec![*pointee],
            Type::Struct(parts) | Type::Overlay(parts) => parts.clone(),
            Type::Union { variants, .. } => variants.clone(),
            Type::Array { elem, .. } | Type::Simd { elem, .. } => vec![*elem],
            Type::Pattern { base, .. } => vec![*base],
            Type::FnPtr { args, ret } => args.iter().chain([ret]).copied().collect(),
            _ => Vec::new(),
        };
        let slice_elem = self.slices.get(&ty).map(|s| s.elem);
        parts
            .into_iter()
            .chain(slice_elem)
            .filter_map(|p| self.unfinished_depth(p, visiting))
            .min()
    }

    /// Puts off the call `fname(args)` if an argument is unfinished and the call has one shape
    /// (`-> type { return struct { ... }; }`), so that its id is known without running it.
    pub(super) fn defer_type_call(
        &mut self,
        mod_path: &str,
        fname: &str,
        args: &[ComptimeVal],
    ) -> Result<Option<TypeId>, String> {
        if self.pending_types.is_empty() {
            return Ok(None);
        }
        let Some(depth) = args
            .iter()
            .filter_map(|a| match a {
                ComptimeVal::Type(t) => self.unfinished_depth(*t, &mut Vec::new()),
                _ => None,
            })
            .min()
        else {
            return Ok(None);
        };
        let Some((def_mod, orig_name, Item::Func(decl), _)) =
            self.find_item_in_module(mod_path, mod_path, fname)?
        else {
            return Ok(None);
        };
        let [Stmt::Return(Some(Expr::TypeVal(te)))] = decl.body.stmts.as_slice() else {
            return Ok(None);
        };
        if !Self::is_reservable(te) {
            return Ok(None);
        }
        let id = self.alloc_distinct_type(Type::Void);
        self.pending_types.insert(id, depth);
        self.cycle_floor = self.cycle_floor.min(depth);
        let key = (def_mod.clone(), orig_name.clone(), args.to_vec());
        self.memoized_type_calls.insert(key.clone(), id);
        self.reserved_calls.insert(key, id);
        self.deferred_types.push_back(DeferredType {
            id,
            mod_path: def_mod,
            fname: orig_name,
            args: args.to_vec(),
        });
        Ok(Some(id))
    }

    /// Ends the cycle of types at `depth` or deeper: all of them have definitions, so the type
    /// functions they put off can run. Those run with each other's ids still undefined, which
    /// a question about such a type answers as `is_copy_type` and `is_clone_type` describe.
    fn finish_types(&mut self, depth: usize) -> Result<(), String> {
        let queued: Vec<TypeId> = self.deferred_types.iter().map(|d| d.id).collect();
        let done: Vec<TypeId> = self
            .pending_types
            .iter()
            .filter(|(t, d)| **d >= depth && !queued.contains(t))
            .map(|(t, _)| *t)
            .collect();
        for t in &done {
            self.pending_types.remove(t);
        }
        self.finishing_types.extend(done);
        if self.finishing {
            return Ok(());
        }
        self.finishing = true;
        while let Some(call) = self.deferred_types.pop_front() {
            let built = self.with_reserved_type(call.id, |c| {
                match c.eval_comptime_func(&call.mod_path, &call.fname, &call.args)? {
                    ComptimeVal::Type(t) if t == call.id => Ok(t),
                    other => Err(format!(
                        "Type function '{}' returned {}, not the type it declares",
                        call.fname,
                        c.comptime_val_label(&other)
                    )),
                }
            });
            if let Err(e) = built {
                self.finishing = false;
                return Err(e);
            }
            self.pending_types.remove(&call.id);
            self.finishing_types.push(call.id);
        }
        self.finishing = false;
        self.cycle_floor = usize::MAX;
        // Unions built while a variant had no definition yet could not see its destructor.
        if let Some(first) = self.finishing_types.iter().map(|t| t.0).min() {
            for t in first..self.program.types.len() as u32 {
                self.ensure_union_destructor(TypeId(t));
            }
        }
        self.finishing_types.clear();
        let held = std::mem::take(&mut self.held_funcs);
        self.pending_funcs.extend(held);
        Ok(())
    }

    pub(super) fn instantiate_type_decl(
        &mut self,
        mod_path: &str,
        type_name: &str,
        env: &HashMap<String, ComptimeVal>,
        ty_expr: &TypeExpr,
    ) -> Result<TypeId, String> {
        match ty_expr {
            TypeExpr::BareOpaque => {
                self.instantiate_named_opaque(mod_path, type_name, env, None, &[])
            }
            TypeExpr::OpaqueDef { methods } => {
                self.instantiate_named_opaque(mod_path, type_name, env, None, methods)
            }
            TypeExpr::Distinct {
                underlying,
                methods,
            } => {
                self.instantiate_distinct_type(mod_path, type_name, env, None, underlying, methods)
            }
            TypeExpr::Trait(methods, kind, assoc) => {
                self.instantiate_trait(mod_path, type_name, env, None, methods, *kind, assoc)
            }
            TypeExpr::Enum { backing, variants } => {
                self.instantiate_enum(mod_path, None, env, type_name, backing.as_deref(), variants)
            }
            TypeExpr::Union { backing, variants } => self.instantiate_union(
                mod_path,
                type_name,
                env,
                None,
                backing.as_deref(),
                variants,
            ),
            TypeExpr::Overlay(fields) => {
                self.instantiate_overlay(mod_path, type_name, env, None, fields)
            }
            TypeExpr::Error {
                backing,
                ok_flag,
                variants,
            } => self.instantiate_error(
                mod_path,
                type_name,
                env,
                None,
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
                type_name,
                false,
                *is_packed,
                OpaqueOwnership::Copy,
                ThreadDecl::default(),
                env,
                None,
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
                self.instantiate_opaque_body(mod_path, type_name, env, None, body)
            }
            other => self.resolve_type_expr(mod_path, None, env, other),
        }
    }

    pub(super) fn instantiate_named_opaque(
        &mut self,
        mod_path: &str,
        type_name: &str,
        env: &HashMap<String, ComptimeVal>,
        memo_key: Option<(String, String, Vec<ComptimeVal>)>,
        methods: &[FuncDecl],
    ) -> Result<TypeId, String> {
        let (inherent_methods, impl_methods) = Self::split_impl_methods(methods);
        let methods: &[FuncDecl] = &inherent_methods;
        let ty_id = self.alloc_distinct_type(Type::Int {
            signed: false,
            bits: 8,
        });
        self.named_opaques.insert(ty_id);
        self.register_inline_impls(ty_id, mod_path, env, impl_methods);
        let mut method_map = HashMap::new();
        for m in methods {
            method_map.insert(m.name.clone(), (m.vis, m.clone()));
        }
        let info = CompositeInfo {
            name: type_name.to_string(),
            is_opaque: true,
            is_packed: false,
            total_bits: 0,
            packed_offsets: Vec::new(),
            ownership: OpaqueOwnership::Affine,
            threads: ThreadDecl::default(),
            cell_fields: Vec::new(),
            has_format_hook: false,
            def_module: mod_path.to_string(),
            comptime_env: env.clone(),
            fields: Vec::new(),
            rel_fields: HashMap::new(),
            consts: HashMap::new(),
            statics: HashMap::new(),
            methods: std::sync::Arc::new(method_map),
            method_fn_ids: HashMap::new(),
            default_fn: None,
            clone_fn: None,
            drop_fn: None,
            format_fn: None,
            declared: DeclaredContents::default(),
            may_dangle: Vec::new(),
        };
        self.composites.insert(ty_id, std::sync::Arc::new(info));
        if let Some(key) = memo_key {
            self.memoized_type_calls.insert(key, ty_id);
        } else if !type_name.starts_with('<') {
            self.named_types
                .insert((mod_path.to_string(), type_name.to_string()), ty_id);
        }
        if let Ok(Some((_, _, Item::TypeDecl { vis, .. }, _))) =
            self.find_item_in_module(mod_path, mod_path, type_name)
            && vis.is_export()
        {
            self.exported_type_set.insert(ty_id);
        }
        for m in methods {
            if m.vis.is_export() && m.params.iter().any(|p| p.is_comptime) {
                return Err(format!(
                    "Exported method '{}.{}' cannot have 'comptime' parameters",
                    type_name, m.name
                ));
            }
            if !m.params.iter().any(|p| p.is_comptime)
                && self.eval_where_clauses(env, &m.where_clauses)?
            {
                let fn_id = self.schedule_method(mod_path, ty_id, env, m)?;
                self.composite_mut(ty_id)
                    .method_fn_ids
                    .insert(m.name.clone(), fn_id);
            }
        }
        Ok(ty_id)
    }

    pub(super) fn instantiate_distinct_type(
        &mut self,
        mod_path: &str,
        type_name: &str,
        env: &HashMap<String, ComptimeVal>,
        memo_key: Option<(String, String, Vec<ComptimeVal>)>,
        underlying_expr: &TypeExpr,
        methods: &[FuncDecl],
    ) -> Result<TypeId, String> {
        let (inherent_methods, impl_methods) = Self::split_impl_methods(methods);
        let methods: &[FuncDecl] = &inherent_methods;
        let underlying_id = self.resolve_type_expr(mod_path, None, env, underlying_expr)?;
        let mut base_underlying = underlying_id;
        while let Some(nt) = self.distinct_types.get(&base_underlying) {
            base_underlying = nt.underlying;
        }
        // Positional or named fields would only be reachable through `as`; a named struct gives
        // the same nominal type with usable fields. (Also through an `alias`.)
        let is_anon_struct = self
            .memoized_anon_records
            .values()
            .any(|&t| t == base_underlying);
        let is_tuple = matches!(
            self.program.types[base_underlying.0 as usize],
            Type::Struct(_)
        ) && self.type_kind(base_underlying).is_none();
        if is_anon_struct || is_tuple {
            let what = if is_tuple {
                "a tuple"
            } else {
                "an anonymous struct"
            };
            return Err(format!(
                "Distinct type '{type_name}' wraps {what}, whose fields it would hide; declare 'struct {type_name} {{ ... }}' for a nominal struct with usable fields"
            ));
        }
        if self.is_opaque_type(base_underlying) {
            return Err(format!(
                "Distinct type '{}' cannot wrap unsized opaque type '{}'",
                type_name,
                self.type_display_name(underlying_id)
            ));
        }
        let underlying_stage3 = self.program.types[underlying_id.0 as usize].clone();
        let ty_id = self.alloc_distinct_type(underlying_stage3);
        if self.is_linear_type(underlying_id) {
            self.program
                .linear_types
                .push((ty_id, type_name.to_string()));
        }
        if let Some(&(_, dtor_fn)) = self
            .program
            .destructors
            .iter()
            .find(|(t, _)| *t == underlying_id)
        {
            self.program.destructors.push((ty_id, dtor_fn));
        }
        let mut method_map = HashMap::new();
        for m in methods {
            method_map.insert(m.name.clone(), (m.vis, m.clone()));
        }
        self.register_inline_impls(ty_id, mod_path, env, impl_methods.clone());
        self.distinct_types.insert(
            ty_id,
            DistinctTypeInfo {
                name: type_name.to_string(),
                def_module: mod_path.to_string(),
                underlying: underlying_id,
                comptime_env: env.clone(),
                methods: method_map,
                method_fn_ids: HashMap::new(),
            },
        );
        if let Some(key) = memo_key {
            self.memoized_type_calls.insert(key, ty_id);
        } else if !type_name.starts_with('<') {
            self.named_types
                .insert((mod_path.to_string(), type_name.to_string()), ty_id);
        }
        if let Ok(Some((_, _, Item::TypeDecl { vis, .. }, _))) =
            self.find_item_in_module(mod_path, mod_path, type_name)
            && vis.is_export()
        {
            self.exported_type_set.insert(ty_id);
        }
        for m in methods {
            if m.vis.is_export() && m.params.iter().any(|p| p.is_comptime) {
                return Err(format!(
                    "Exported method '{}.{}' cannot have 'comptime' parameters",
                    type_name, m.name
                ));
            }
            if !m.params.iter().any(|p| p.is_comptime)
                && self.eval_where_clauses(env, &m.where_clauses)?
            {
                let fn_id = self.schedule_method(mod_path, ty_id, env, m)?;
                self.distinct_types
                    .get_mut(&ty_id)
                    .unwrap()
                    .method_fn_ids
                    .insert(m.name.clone(), fn_id);
            }
        }
        Ok(ty_id)
    }

    pub(super) fn instantiate_enum(
        &mut self,
        mod_path: &str,
        self_ty: Option<TypeId>,
        env: &HashMap<String, ComptimeVal>,
        type_name: &str,
        backing: Option<&TypeExpr>,
        variants: &[(String, Option<i128>)],
    ) -> Result<TypeId, String> {
        let (signed, bits) = if let Some(b_te) = backing {
            let b_ty = self.resolve_type_expr(mod_path, self_ty, env, b_te)?;
            if self.enums.contains_key(&b_ty)
                || self.composites.contains_key(&b_ty)
                || self.distinct_types.contains_key(&b_ty)
            {
                return Err(format!(
                    "Enum '{}' backing type must be a primitive integer type (e.g. 'u8', 'u3', 'i16'), found '{}'",
                    type_name,
                    self.type_display_name(b_ty)
                ));
            }
            match self.program.types[b_ty.0 as usize] {
                Type::Int { signed, bits } => (signed, bits),
                _ => {
                    return Err(format!(
                        "Enum '{}' backing type must be a primitive integer type (e.g. 'u8', 'u3', 'i16'), found '{}'",
                        type_name,
                        self.type_display_name(b_ty)
                    ));
                }
            }
        } else {
            // Without an explicit backing type: the smallest integer that fits every value, except
            // for `export enum`, which keeps the 32-bit size of a C `enum`.
            let mut next = 0i128;
            let (mut lo, mut hi) = (0i128, 0i128);
            for (_, explicit) in variants {
                let v = explicit.unwrap_or(next);
                lo = lo.min(v);
                hi = hi.max(v);
                next = v + 1;
            }
            let exported = matches!(
                self.find_item_in_module(mod_path, mod_path, type_name),
                Ok(Some((_, _, Item::TypeDecl { vis, .. }, _))) if vis.is_export()
            );
            let signed = lo < 0;
            let width = [8u16, 16, 32, 64]
                .into_iter()
                .find(|&b| {
                    crate::wide::Wide::from_i128(lo).fits(b, signed)
                        && crate::wide::Wide::from_i128(hi).fits(b, signed)
                })
                .unwrap_or(64);
            if exported { (signed, width.max(32)) } else { (signed, width) }
        };
        let mut next_val = 0i128;
        let mut resolved = Vec::with_capacity(variants.len());
        for (vname, explicit) in variants {
            let val = explicit.unwrap_or(next_val);
            if let Some(range) = int_range_violation(val, bits, signed) {
                return Err(format!(
                    "Enum variant '{type_name}::{vname}' discriminant {val} does not fit in backing integer type {range}"
                ));
            }
            resolved.push((vname.clone(), val));
            next_val = val + 1;
        }
        let ty_id = self.alloc_distinct_type(Type::Int { signed, bits });
        self.enums.insert(ty_id, (type_name.to_string(), resolved));
        Ok(ty_id)
    }

    pub(super) fn resolve_variant_payload_ty(
        &mut self,
        mod_path: &str,
        owner_name: &str,
        vname: &str,
        env: &HashMap<String, ComptimeVal>,
        payload: &Option<TypeExpr>,
    ) -> Result<TypeId, String> {
        match payload {
            None => Ok(self.intern_type(Type::Void)),
            Some(TypeExpr::Struct {
                is_packed,
                fields,
                methods,
            }) => self.instantiate_composite(
                mod_path,
                &format!("{owner_name}::{vname}"),
                false,
                *is_packed,
                OpaqueOwnership::Copy,
                ThreadDecl::default(),
                env,
                None,
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
            Some(te) => {
                let p_ty = self.resolve_type_expr(mod_path, None, env, te)?;
                if self.is_opaque_type(p_ty) {
                    return Err(format!(
                        "Unsized type 'opaque' cannot be stored by value in variant '{}::{}'; use '*const opaque', '*mut opaque', '&opaque', or '&mut opaque'",
                        owner_name, vname
                    ));
                }
                Ok(p_ty)
            }
        }
    }

    /// The tag of an `error` / `errorcode` declared with a C backing type (`what(Int)`):
    /// `(backing type, unsigned tag of its width)`; without one, a `u32` tag.
    fn resolve_error_backing(
        &mut self,
        mod_path: &str,
        env: &HashMap<String, ComptimeVal>,
        backing: Option<&TypeExpr>,
        what: &str,
        type_name: &str,
    ) -> Result<(Option<TypeId>, TypeId), String> {
        let Some(b_expr) = backing else {
            let t = self.intern_type(Type::Int {
                signed: false,
                bits: 32,
            });
            return Ok((None, t));
        };
        let b_id = self.resolve_type_expr(mod_path, None, env, b_expr)?;
        let is_valid_c_int = self.c_ints.contains_key(&b_id)
            || (!self.enums.contains_key(&b_id)
                && !self.distinct_types.contains_key(&b_id)
                && !self.raw_ptrs.contains_key(&b_id)
                && !self.named_opaques.contains(&b_id)
                && !self.composites.contains_key(&b_id)
                && matches!(
                    self.program.types[b_id.0 as usize],
                    Type::Int {
                        bits: 8 | 16 | 32 | 64,
                        ..
                    }
                ));
        if !is_valid_c_int {
            return Err(format!(
                "Backing type '{}' of '{what}({type_name})' must be a C-compatible integer type ('c_int', 'i8'..'i64', 'u8'..'u64', 'isize', 'usize')",
                self.type_display_name(b_id)
            ));
        }
        let Type::Int { bits, .. } = self.program.types[b_id.0 as usize] else {
            unreachable!()
        };
        let t = self.intern_type(Type::Int {
            signed: false,
            bits,
        });
        Ok((Some(b_id), t))
    }

    /// The type a payload-less `error` variant `vname` names, if it names one (an embedded
    /// error: a comptime type binding or a declared type).
    fn resolve_embedded_type(
        &mut self,
        mod_path: &str,
        env: &HashMap<String, ComptimeVal>,
        vname: &str,
    ) -> Result<Option<TypeId>, String> {
        let path: Vec<String> = vname.split("::").map(str::to_string).collect();
        if path.len() == 1
            && let Some(ComptimeVal::Type(t_id)) = env.get(&path[0])
        {
            return Ok(Some(*t_id));
        }
        if let Ok(ResolvedItem::Type(tmod, tname)) = self.resolve_path(mod_path, &path) {
            return Ok(Some(self.resolve_named_type(&tmod, &tname)?));
        }
        Ok(None)
    }

    /// Registers a tagged `union` with `variants`. With an explicit integer `backing` (`union(Int)`)
    /// or inline variant values (`= N`), the tag uses that integer type and stores those values;
    /// otherwise the tag is a `u32` variant index. `what` names the union in errors.
    fn register_union(
        &mut self,
        reserved: Option<TypeId>,
        name: &str,
        what: &str,
        c_backing: Option<TypeId>,
        variants: Vec<(String, TypeId, Option<i128>)>,
    ) -> Result<TypeId, String> {
        let mut resolved_variants: Vec<(String, TypeId)> = Vec::with_capacity(variants.len());
        let mut tag_values = Vec::with_capacity(variants.len());
        let mut next_val = 0i128;
        for (vname, p_ty, explicit) in variants {
            let val = explicit.unwrap_or(next_val);
            if let Some((other, _)) = resolved_variants
                .iter()
                .zip(tag_values.iter())
                .find(|&(_, &ov)| ov == val)
            {
                return Err(format!(
                    "Variants '{}::{vname}' and '{}::{}' of {what} have the same value {val}",
                    name, name, other.0
                ));
            }
            resolved_variants.push((vname, p_ty));
            tag_values.push(val);
            next_val = val + 1;
        }
        let (signed, bits) = if let Some(b_ty) = c_backing {
            let Type::Int { signed, bits } = self.program.types[b_ty.0 as usize] else {
                return Err(format!(
                    "{what} backing type '{}' must be a primitive or C integer type",
                    self.type_display_name(b_ty)
                ));
            };
            let b_name = self.type_display_name(b_ty);
            for ((vname, _), &val) in resolved_variants.iter().zip(tag_values.iter()) {
                if int_range_violation(val, bits, signed).is_some() {
                    let (min, max) = (Wide::min_value(bits, signed), Wide::max_value(bits, signed));
                    return Err(format!(
                        "Value {val} of '{name}::{vname}' does not fit backing type '{b_name}' (range {min}..={max})"
                    ));
                }
            }
            (signed, bits)
        } else {
            let any_negative = tag_values.iter().any(|&v| v < 0);
            let bits = if tag_values
                .iter()
                .all(|&v| Wide::from_i128(v).fits(32, any_negative))
            {
                32
            } else {
                64
            };
            for ((vname, _), &val) in resolved_variants.iter().zip(tag_values.iter()) {
                if let Some(range) = int_range_violation(val, bits, any_negative) {
                    return Err(format!(
                        "Value {val} of '{name}::{vname}' does not fit tag integer type {range}"
                    ));
                }
            }
            (any_negative, bits)
        };
        let tag_ty = self.intern_type(Type::Int { signed, bits });
        let ty_id = self.define_type(
            reserved,
            name,
            Type::Union {
                tag: tag_ty,
                variants: resolved_variants.iter().map(|v| v.1).collect(),
            },
        )?;
        self.program.tagged_unions.push(ty_id);
        if tag_values
            .iter()
            .enumerate()
            .any(|(i, &v)| v != i as i128)
        {
            self.program
                .union_tag_values
                .push((ty_id, tag_values.clone()));
        }
        self.unions.insert(
            ty_id,
            UnionTypeInfo {
                name: name.to_string(),
                variants: resolved_variants,
                c_backing,
                tag_values,
            },
        );
        self.ensure_union_destructor(ty_id);
        Ok(ty_id)
    }

    /// Registers an `error` type (`info.leaves` sorted, see `sort_error_leaves`) with tag `tag_ty`:
    /// a tagged union with one variant per leaf.
    fn register_error(&mut self, info: ErrorTypeInfo, tag_ty: TypeId) -> TypeId {
        let ty_id = self.alloc_distinct_type(Type::Union {
            tag: tag_ty,
            variants: info.leaves.iter().map(|l| l.payload_ty).collect(),
        });
        self.program.tagged_unions.push(ty_id);
        self.errors.insert(ty_id, info);
        self.ensure_union_destructor(ty_id);
        ty_id
    }

    /// Records `ty_id` as the result of the type-function call `memo_key`, if it is one.
    fn memoize_type_call(
        &mut self,
        memo_key: Option<(String, String, Vec<ComptimeVal>)>,
        ty_id: TypeId,
    ) {
        if let Some(key) = memo_key {
            self.memoized_type_calls.insert(key, ty_id);
        }
    }

    /// The variants described by the `UnionSpec` / `ErrorSpec` records (or `(name, type)`
    /// tuples) given to `@Union` / `@Error` (`kind`).
    fn variant_specs(
        &mut self,
        items: Vec<ComptimeVal>,
        kind: &str,
    ) -> Result<Vec<(String, TypeId)>, String> {
        let void_ty = self.intern_type(Type::Void);
        let mut specs: Vec<(String, TypeId)> = Vec::with_capacity(items.len());
        for item in items {
            let (vname, p_ty) = match item {
                ComptimeVal::Record(entries) => {
                    let Some((_, ComptimeVal::Str(n))) =
                        entries.iter().find(|(k, _)| k == "name")
                    else {
                        return Err(format!(
                            "'@{kind}' variant descriptor is missing string field 'name'"
                        ));
                    };
                    let p_ty = match entries.iter().find(|(k, _)| k == "payload") {
                        Some((_, ComptimeVal::Type(t))) => *t,
                        None => void_ty,
                        _ => {
                            return Err(format!(
                                "'@{kind}' variant descriptor '{n}' field 'payload' must be a type"
                            ));
                        }
                    };
                    (n.clone(), p_ty)
                }
                ComptimeVal::Tuple(elems) if elems.len() == 2 => {
                    let (ComptimeVal::Str(n), ComptimeVal::Type(t)) = (&elems[0], &elems[1]) else {
                        return Err(format!(
                            "'@{kind}' tuple descriptor must be '(&str, type)'"
                        ));
                    };
                    (n.clone(), *t)
                }
                _ => {
                    return Err(format!(
                        "'@{kind}' expects {kind}Spec records with 'name: &str' and 'payload: type'"
                    ));
                }
            };
            if specs.iter().any(|(n, _)| n == &vname) {
                return Err(format!("Duplicate variant '{vname}' in '@{kind}'"));
            }
            if self.is_opaque_type(p_ty) {
                return Err(format!(
                    "Unsized type 'opaque' cannot be stored by value in '@{kind}' variant '{vname}'"
                ));
            }
            specs.push((vname, p_ty));
        }
        Ok(specs)
    }

    pub(super) fn instantiate_union(
        &mut self,
        mod_path: &str,
        type_name: &str,
        env: &HashMap<String, ComptimeVal>,
        memo_key: Option<(String, String, Vec<ComptimeVal>)>,
        backing: Option<&TypeExpr>,
        variants: &[(String, Option<TypeExpr>, Option<i128>)],
    ) -> Result<TypeId, String> {
        let reserved = self.take_reserved_type();
        let mut resolved_variants = Vec::with_capacity(variants.len());
        for (vname, payload_expr, val_opt) in variants {
            if resolved_variants
                .iter()
                .any(|(n, _, _): &(String, TypeId, Option<i128>)| n == vname)
            {
                return Err(format!(
                    "Duplicate variant '{}' in union '{}'",
                    vname, type_name
                ));
            }
            let p_ty =
                self.resolve_variant_payload_ty(mod_path, type_name, vname, env, payload_expr)?;
            resolved_variants.push((vname.clone(), p_ty, *val_opt));
        }
        let c_backing = match backing {
            Some(te) => {
                let b_ty = self.resolve_type_expr(mod_path, None, env, te)?;
                if self.enums.contains_key(&b_ty) {
                    return Err(format!(
                        "Union '{type_name}' cannot link to enum '{}'; specify an integer backing type ('union(u16)') and write '= value' on union variants directly (use '{type_name}::Tag' for the tag enum)",
                        self.type_display_name(b_ty)
                    ));
                }
                if self.composites.contains_key(&b_ty)
                    || self.distinct_types.contains_key(&b_ty)
                    || self.raw_ptrs.contains_key(&b_ty)
                    || self.named_opaques.contains(&b_ty)
                    || !matches!(self.program.types[b_ty.0 as usize], Type::Int { .. })
                {
                    return Err(format!(
                        "Union '{type_name}' backing type must be a primitive or C integer type (e.g. 'u8', 'u16', 'c_int'), found '{}'",
                        self.type_display_name(b_ty)
                    ));
                }
                Some(b_ty)
            }
            None => None,
        };
        let what = format!("Union '{type_name}'");
        let ty_id =
            self.register_union(reserved, type_name, &what, c_backing, resolved_variants)?;
        self.memoize_type_call(memo_key, ty_id);
        Ok(ty_id)
    }

    pub(super) fn instantiate_overlay(
        &mut self,
        mod_path: &str,
        type_name: &str,
        env: &HashMap<String, ComptimeVal>,
        memo_key: Option<(String, String, Vec<ComptimeVal>)>,
        fields: &[(String, TypeExpr)],
    ) -> Result<TypeId, String> {
        let reserved = self.take_reserved_type();
        let mut resolved_fields = Vec::with_capacity(fields.len());
        let mut field_tys = Vec::with_capacity(fields.len());
        for (fname, f_expr) in fields {
            if resolved_fields
                .iter()
                .any(|(n, _): &(String, TypeId)| n == fname)
            {
                return Err(format!(
                    "Duplicate field '{}' in overlay '{}'",
                    fname, type_name
                ));
            }
            let f_ty = self.resolve_type_expr(mod_path, None, env, f_expr)?;
            if let Some(tr) = self.traits.get(&f_ty) {
                return Err(format!(
                    "Trait '{}' is an unsized meta-type constraint and cannot be stored by value in field '{}' of overlay '{}'",
                    tr.name, fname, type_name
                ));
            }
            if self.is_opaque_type(f_ty) {
                return Err(format!(
                    "Unsized type '{}' cannot be stored by value in field '{}' of overlay '{}'",
                    self.type_display_name(f_ty),
                    fname,
                    type_name
                ));
            }
            resolved_fields.push((fname.clone(), f_ty));
            field_tys.push(f_ty);
        }
        let ty_id = self.define_type(reserved, type_name, Type::Overlay(field_tys))?;
        self.overlays.insert(
            ty_id,
            OverlayTypeInfo {
                name: type_name.to_string(),
                fields: resolved_fields,
            },
        );
        if let Some(key) = memo_key {
            self.memoized_type_calls.insert(key, ty_id);
        }
        Ok(ty_id)
    }

    #[allow(clippy::too_many_arguments)]
    pub(super) fn instantiate_error(
        &mut self,
        mod_path: &str,
        type_name: &str,
        env: &HashMap<String, ComptimeVal>,
        memo_key: Option<(String, String, Vec<ComptimeVal>)>,
        backing: Option<&TypeExpr>,
        ok_flag: Option<&(String, i128)>,
        items: &[(String, Option<TypeExpr>, Option<i128>)],
    ) -> Result<TypeId, String> {
        let (c_backing, tag_ty) =
            self.resolve_error_backing(mod_path, env, backing, "error", type_name)?;
        let (ok_name, ok_val) = ok_flag
            .cloned()
            .unwrap_or_else(|| ("Ok".to_string(), 0));
        let is_exported = matches!(
            self.find_item_in_module(mod_path, mod_path, type_name),
            Ok(Some((_, _, Item::TypeDecl { vis, .. }, _))) if vis.is_export()
        );
        let explicit = items.iter().filter(|(_, _, v)| v.is_some()).count();
        let has_custom_codes = is_exported || backing.is_some() || ok_flag.is_some() || explicit > 0;
        let mut has_embedded = false;
        let mut leaves: Vec<ErrorLeafInfo> = Vec::new();
        for (vname, payload, val_opt) in items {
            if payload.is_none() && val_opt.is_none() {
                let maybe_emb_ty = self.resolve_embedded_type(mod_path, env, vname)?;
                if maybe_emb_ty.is_none() && vname.contains("::") {
                    return Err(format!(
                        "Cannot resolve embedded error path '{}' in error '{}'",
                        vname, type_name
                    ));
                }
                if let Some(emb_ty) = maybe_emb_ty {
                    if is_exported {
                        return Err(format!(
                            "Exported error '{type_name}' cannot embed other error sets ('{vname}'); declare its variants directly"
                        ));
                    }
                    if has_custom_codes {
                        return Err(format!(
                            "Error '{type_name}' cannot mix embedded error sets with explicit variant values, backing type, or 'ok' sentinel"
                        ));
                    }
                    let Some(emb_err) = self.errors.get(&emb_ty).cloned() else {
                        return Err(format!(
                            "Embedded type '{}' in error '{}' is not an `error` type",
                            vname, type_name
                        ));
                    };
                    has_embedded = true;
                    for key in &emb_err.decl_order {
                        let leaf = emb_err
                            .leaves
                            .iter()
                            .find(|l| &l.key == key)
                            .unwrap()
                            .clone();
                        if let Some(existing) = leaves.iter().find(|l| l.key == leaf.key) {
                            if existing.payload_ty != leaf.payload_ty {
                                return Err(format!(
                                    "Conflicting payload types for embedded error variant '{}::{}'",
                                    leaf.key.error_name, leaf.key.variant_name
                                ));
                            }
                        } else {
                            leaves.push(leaf);
                        }
                    }
                    continue;
                }
            }
            if has_custom_codes && vname == &ok_name {
                return Err(format!(
                    "Variant '{type_name}::{vname}' conflicts with reserved success flag '{ok_name} = {ok_val}'"
                ));
            }
            let key = ErrorLeafKey {
                def_module: mod_path.to_string(),
                error_name: type_name.to_string(),
                variant_name: vname.clone(),
            };
            if leaves.iter().any(|l| l.key == key) {
                return Err(format!(
                    "Duplicate variant '{}' in error '{}'",
                    vname, type_name
                ));
            }
            let payload_ty =
                self.resolve_variant_payload_ty(mod_path, type_name, vname, env, payload)?;
            if self.is_linear_type(payload_ty) {
                return Err(format!(
                    "Error variant '{}::{}' cannot carry a linear payload",
                    type_name, vname
                ));
            }
            leaves.push(ErrorLeafInfo { key, payload_ty });
        }
        let (leaves, decl_order) = sort_error_leaves(leaves);
        let has_payloads = leaves
            .iter()
            .any(|l| !matches!(self.program.types[l.payload_ty.0 as usize], Type::Void));

        let mut computed_values: Option<Vec<i128>> = None;
        if !has_embedded {
            let mut values: Vec<Option<i128>> = vec![None; leaves.len()];
            if explicit > 0 {
                if let Some((vname, _, _)) = items.iter().find(|(_, _, v)| v.is_none()) {
                    return Err(format!(
                        "Variant '{type_name}::{vname}' needs an explicit value: once one variant of an 'error' has '= N', all must"
                    ));
                }
                for (vname, _, v) in items {
                    let idx = leaves
                        .iter()
                        .position(|l| l.key.variant_name == *vname)
                        .unwrap();
                    values[idx] = *v;
                }
                for (vname, _, v) in items {
                    let v = v.unwrap();
                    if let Some((other, _, _)) =
                        items.iter().find(|(o, _, ov)| o != vname && *ov == Some(v))
                    {
                        return Err(format!(
                            "Variants '{type_name}::{vname}' and '{type_name}::{other}' have the same value {v}"
                        ));
                    }
                }
            } else {
                // Automatic enumeration starts at 1, reserving 0 for the default `Ok = 0` success flag.
                let mut next = 1i128;
                for key in &decl_order {
                    if let Some(idx) = leaves.iter().position(|l| l.key == *key)
                        && values[idx].is_none()
                    {
                        values[idx] = Some(next);
                        next += 1;
                    }
                }
            }
            let values: Vec<i128> = values.into_iter().map(Option::unwrap).collect();
            if has_custom_codes {
                for (idx, &v) in values.iter().enumerate() {
                    if v == ok_val {
                        let vname = &leaves[idx].key.variant_name;
                        return Err(format!(
                            "Variant '{type_name}::{vname}' cannot have value {v} because '{ok_name} = {ok_val}' is reserved for the success flag"
                        ));
                    }
                }
            }
            if let Some(b_ty) = c_backing
                && let Type::Int { signed, bits } = self.program.types[b_ty.0 as usize]
            {
                let b_name = self.type_display_name(b_ty);
                let ok = (ok_name.as_str(), ok_val);
                let named = values
                    .iter()
                    .enumerate()
                    .map(|(idx, &v)| (leaves[idx].key.variant_name.as_str(), v));
                for (vname, v) in std::iter::once(ok).chain(named) {
                    if int_range_violation(v, bits, signed).is_some() {
                        let (min, max) =
                            (Wide::min_value(bits, signed), Wide::max_value(bits, signed));
                        return Err(format!(
                            "Value {v} of '{type_name}::{vname}' does not fit backing type '{b_name}' (range {min}..={max})"
                        ));
                    }
                }
            } else if has_custom_codes {
                let mut all_vals = vec![(ok_name.as_str(), ok_val)];
                for (idx, &v) in values.iter().enumerate() {
                    all_vals.push((leaves[idx].key.variant_name.as_str(), v));
                }
                let any_negative = all_vals.iter().any(|&(_, v)| v < 0);
                let any_above_int = all_vals.iter().any(|&(_, v)| v > i128::from(i32::MAX));
                for (vname, v) in all_vals {
                    if v < i128::from(i32::MIN) || v > i128::from(u32::MAX) {
                        return Err(format!(
                            "Value {v} of '{type_name}::{vname}' does not fit a C enum ('int' or 'unsigned int')"
                        ));
                    }
                    if any_negative && any_above_int && v > i128::from(i32::MAX) {
                        return Err(format!(
                            "Values of 'error {type_name}' mix negative values with values above INT_MAX ({vname} = {v}); a C enum needs them to fit one of 'int' or 'unsigned int'"
                        ));
                    }
                }
            }
            computed_values = Some(values);
        }

        let ty_id = self.register_error(
            ErrorTypeInfo {
                name: type_name.to_string(),
                leaves,
                decl_order,
                has_payloads,
                has_embedded,
                c_backing,
                ok_flag: (ok_name, ok_val),
            },
            tag_ty,
        );
        if let Some(values) = computed_values {
            let tag_bits = match self.program.types[tag_ty.0 as usize] {
                Type::Int { bits, .. } => bits,
                _ => 32,
            };
            if values.iter().enumerate().any(|(i, &v)| v != i as i128) {
                let stored = values
                    .iter()
                    .map(|&v| {
                        if tag_bits >= 128 {
                            v
                        } else {
                            v.rem_euclid(1i128 << tag_bits)
                        }
                    })
                    .collect();
                self.program.union_tag_values.push((ty_id, stored));
            }
            self.export_error_values.insert(ty_id, values);
        }
        self.memoize_type_call(memo_key, ty_id);
        Ok(ty_id)
    }

    pub(super) fn combine_error_types(
        &mut self,
        lhs_ty: TypeId,
        rhs_ty: TypeId,
    ) -> Result<TypeId, String> {
        let Some(lhs_err) = self.errors.get(&lhs_ty).cloned() else {
            return Err(format!(
                "Left operand of error union '||' is not an `error` type ({})",
                self.type_display_name(lhs_ty)
            ));
        };
        let Some(rhs_err) = self.errors.get(&rhs_ty).cloned() else {
            return Err(format!(
                "Right operand of error union '||' is not an `error` type ({})",
                self.type_display_name(rhs_ty)
            ));
        };
        if lhs_ty == rhs_ty {
            return Ok(lhs_ty);
        }
        let mut leaves = lhs_err.leaves.clone();
        let mut decl_order = lhs_err.decl_order.clone();
        for key in &rhs_err.decl_order {
            if !decl_order.contains(key) {
                decl_order.push(key.clone());
            }
        }
        for leaf in rhs_err.leaves {
            if let Some(existing) = leaves.iter().find(|l| l.key == leaf.key) {
                if existing.payload_ty != leaf.payload_ty {
                    return Err(format!(
                        "Conflicting payload types for error variant '{}::{}'",
                        leaf.key.error_name, leaf.key.variant_name
                    ));
                }
            } else {
                leaves.push(leaf);
            }
        }
        leaves.sort_by(|a, b| a.key.cmp(&b.key));
        let canonical_key: Vec<(ErrorLeafKey, TypeId)> = leaves
            .iter()
            .map(|l| (l.key.clone(), l.payload_ty))
            .collect();
        if let Some(&existing_ty) = self.memoized_error_unions.get(&canonical_key) {
            return Ok(existing_ty);
        }
        let has_payloads = leaves
            .iter()
            .any(|l| !matches!(self.program.types[l.payload_ty.0 as usize], Type::Void));
        let tag_ty = self.intern_type(Type::Int {
            signed: false,
            bits: 32,
        });
        let ty_id = self.register_error(
            ErrorTypeInfo {
                name: format!("{} || {}", lhs_err.name, rhs_err.name),
                leaves,
                decl_order,
                has_payloads,
                has_embedded: true,
                c_backing: None,
                ok_flag: ("Ok".to_string(), 0),
            },
            tag_ty,
        );
        self.memoized_error_unions.insert(canonical_key, ty_id);
        Ok(ty_id)
    }

    pub(super) fn instantiate_result_type(
        &mut self,
        err_ty: TypeId,
        ok_ty: TypeId,
    ) -> Result<TypeId, String> {
        if !self.errors.contains_key(&err_ty) {
            let t_disp = self
                .composites
                .get(&err_ty)
                .map(|c| c.name.clone())
                .unwrap_or_else(|| self.program.types[err_ty.0 as usize].to_string());
            return Err(format!(
                "Error type '{}' in result type '{}!...' must be an `error` type",
                t_disp, t_disp
            ));
        }
        if let Some(&existing) = self.memoized_results.get(&(err_ty, ok_ty)) {
            return Ok(existing);
        }
        let u8_ty = self.intern_type(Type::Int {
            signed: false,
            bits: 8,
        });
        let ty_id = self.alloc_distinct_type(Type::Union {
            tag: u8_ty,
            variants: vec![ok_ty, err_ty],
        });
        self.results.insert(ty_id, ResultTypeInfo { err_ty, ok_ty });
        self.memoized_results.insert((err_ty, ok_ty), ty_id);
        self.ensure_union_destructor(ty_id);
        Ok(ty_id)
    }

    pub(super) fn type_has_destructor(&self, ty_id: TypeId) -> bool {
        if self.program.destructors.iter().any(|(t, _)| *t == ty_id) {
            return true;
        }
        match &self.program.types[ty_id.0 as usize] {
            Type::Struct(fields) => fields.iter().any(|&f| self.type_has_destructor(f)),
            Type::Array { elem, len } => *len > 0 && self.type_has_destructor(*elem),
            _ => false,
        }
    }

    /// The destructor of `ty`, whose `drop` hook is `hook`: the hook, then each field in order, as
    /// nothing else would drop them. Linear fields are left out, since a linear value must
    /// be moved out before its owner goes. A type with nothing more to drop keeps the hook alone.
    fn hook_then_fields(&mut self, ty: TypeId, hook: FuncId) -> FuncId {
        let fields: Vec<TypeId> =
            self.composites.get(&ty).map(|c| c.fields.iter().map(|f| f.1).collect()).unwrap_or_default();
        let droppable: Vec<u32> = (0..fields.len() as u32)
            .filter(|&i| {
                let f = fields[i as usize];
                !self.is_copy_type(f) && !self.is_linear_type(f)
            })
            .collect();
        if droppable.is_empty() {
            return hook;
        }
        let self_ref = self.intern_type(Type::Ptr { mutable: true, pointee: ty });
        let void_ty = self.intern_type(Type::Void);
        let glue = self.reserve_function(Visibility::Private, None, &[self_ref], void_ty);
        let (reborrow, unit) = (LocalId(2), LocalId(3));
        let field = |i: u32| Place {
            local: LocalId(1),
            projections: vec![Projection::Deref, Projection::Field(i)],
        };
        let mut blocks = vec![BasicBlock {
            statements: vec![Statement::Assign(
                Place::new(reborrow),
                Rvalue::Ref {
                    mutable: true,
                    place: Place {
                        local: LocalId(1),
                        projections: vec![Projection::Deref],
                    },
                },
            )],
            terminator: Terminator::Call {
                func: Operand::Const(ConstValue::Func(hook)),
                args: vec![Operand::Move(Place::new(reborrow))],
                destination: Place::new(unit),
                target: BlockId(1),
            },
        }];
        for (n, &i) in droppable.iter().enumerate() {
            blocks.push(BasicBlock {
                statements: Vec::new(),
                terminator: Terminator::Drop {
                    place: field(i),
                    target: BlockId(n as u32 + 2),
                },
            });
        }
        blocks.push(BasicBlock {
            statements: vec![Statement::Assign(
                Place::new(LocalId(0)),
                Rvalue::Use(Operand::Const(ConstValue::Void)),
            )],
            terminator: Terminator::Return,
        });
        let name = self.type_display_name(ty);
        if let Some(func) = self.program.functions.iter_mut().find(|f| f.id == glue) {
            func.locals = vec![void_ty, self_ref, self_ref, void_ty];
            func.blocks = blocks;
            func.debug_name = Some(format!("{name}::drop with its fields"));
        }
        glue
    }

    /// Writes the destructors of the unions `ty` holds by value, which a type built before
    /// its parts were defined has not had yet.
    fn ensure_nested_union_destructors(&mut self, ty: TypeId) {
        match self.program.types[ty.0 as usize].clone() {
            Type::Union { .. } => self.ensure_union_destructor(ty),
            Type::Struct(parts) => {
                for part in parts {
                    self.ensure_nested_union_destructors(part);
                }
            }
            _ => {}
        }
    }

    pub(super) fn ensure_union_destructor(&mut self, union_ty: TypeId) {
        if self.program.destructors.iter().any(|(t, _)| *t == union_ty) {
            return;
        }
        if self.is_linear_type(union_ty) {
            return;
        }
        let Type::Union { tag, variants } = self.program.types[union_ty.0 as usize].clone() else {
            return;
        };
        // The destructor is written once, so `finish_types` waits for every variant to exist.
        if self.layout_is_pending(union_ty) {
            return;
        }
        for &v in &variants {
            self.ensure_nested_union_destructors(v);
        }
        if !variants.iter().any(|&v| self.type_has_destructor(v)) {
            return;
        }
        let self_ref_ty = self.intern_type(Type::Ptr {
            mutable: true,
            pointee: union_ty,
        });
        let void_ty = self.intern_type(Type::Void);
        let dtor_fn_id = self.reserve_function(Visibility::Private, None, &[self_ref_ty], void_ty);
        self.program.destructors.push((union_ty, dtor_fn_id));

        let discr_local = LocalId(2);
        let mut locals = vec![void_ty, self_ref_ty, tag];
        let mut blocks = Vec::new();
        // bb0: discr = Discriminant(*_1); SwitchInt
        blocks.push(BasicBlock {
            statements: vec![Statement::Assign(
                Place::new(discr_local),
                Rvalue::Discriminant(Place {
                    local: LocalId(1),
                    projections: vec![Projection::Deref],
                }),
            )],
            terminator: Terminator::Unreachable,
        });
        let join_bb = BlockId(1);
        blocks.push(BasicBlock {
            statements: vec![Statement::Assign(
                Place::new(LocalId(0)),
                Rvalue::Use(Operand::Const(ConstValue::Void)),
            )],
            terminator: Terminator::Return,
        });
        let mut targets = Vec::new();
        for (v_idx, &v_ty) in variants.iter().enumerate() {
            if self.type_has_destructor(v_ty) {
                let drop_bb = BlockId(blocks.len() as u32);
                blocks.push(BasicBlock {
                    statements: Vec::new(),
                    terminator: Terminator::Drop {
                        place: Place {
                            local: LocalId(1),
                            projections: vec![Projection::Deref, Projection::Variant(v_idx as u32)],
                        },
                        target: join_bb,
                    },
                });
                targets.push((v_idx as i128, drop_bb));
            }
        }
        blocks[0].terminator = Terminator::SwitchInt {
            discr: Operand::Copy(Place::new(discr_local)),
            targets,
            otherwise: join_bb,
        };
        if let Some(func) = self
            .program
            .functions
            .iter_mut()
            .find(|f| f.id == dtor_fn_id)
        {
            func.locals = std::mem::take(&mut locals);
            func.blocks = blocks;
        }
    }

    /// The `T::Tag` enum of union or error `union_ty`, synthesized on first use with one variant
    /// per union/error variant using its backing integer type and tag values.
    pub(super) fn union_tag_enum(&mut self, union_ty: TypeId) -> TypeId {
        if let Some(&t) = self.union_tag_enums.get(&union_ty) {
            return t;
        }
        if let Some(info) = self.unions.get(&union_ty).cloned() {
            let Type::Union { tag, .. } = self.program.types[union_ty.0 as usize] else {
                unreachable!()
            };
            let tag_int = self.program.types[tag.0 as usize].clone();
            let tag_ty = self.alloc_distinct_type(tag_int);
            let variants = info
                .variants
                .iter()
                .zip(info.tag_values.iter())
                .map(|((n, _), &v)| (n.clone(), v))
                .collect();
            self.enums
                .insert(tag_ty, (format!("{}::Tag", info.name), variants));
            self.union_tag_enums.insert(union_ty, tag_ty);
            return tag_ty;
        }
        let einfo = self.errors[&union_ty].clone();
        let tag_int = if let Some(b_ty) = einfo.c_backing {
            self.program.types[b_ty.0 as usize].clone()
        } else if let Type::Union { tag, .. } = self.program.types[union_ty.0 as usize] {
            self.program.types[tag.0 as usize].clone()
        } else {
            Type::Int {
                signed: false,
                bits: 32,
            }
        };
        let tag_ty = self.alloc_distinct_type(tag_int);
        let vals = self.export_error_values.get(&union_ty).cloned();
        let variants = einfo
            .leaves
            .iter()
            .enumerate()
            .map(|(i, l)| {
                let v = vals
                    .as_ref()
                    .and_then(|vs| vs.get(i).copied())
                    .unwrap_or(i as i128);
                (l.key.variant_name.clone(), v)
            })
            .collect();
        self.enums
            .insert(tag_ty, (format!("{}::Tag", einfo.name), variants));
        self.union_tag_enums.insert(union_ty, tag_ty);
        tag_ty
    }

    /// Separates inherent methods from methods declared in `impl Tr { ... }` blocks of a type body.
    fn split_impl_methods(methods: &[FuncDecl]) -> (Vec<FuncDecl>, Vec<FuncDecl>) {
        methods.iter().cloned().partition(|m| m.impl_of.is_none())
    }

    /// Records the inline `impl Tr { ... }` blocks of a freshly instantiated type.
    fn register_inline_impls(
        &mut self,
        ty_id: TypeId,
        mod_path: &str,
        env: &HashMap<String, ComptimeVal>,
        impl_methods: Vec<FuncDecl>,
    ) {
        let mut blocks: Vec<InlineImpl> = Vec::new();
        for m in impl_methods {
            let trait_expr = m.impl_of.clone().expect("impl method carries its trait");
            if let Some(b) = blocks.iter_mut().find(|b| b.trait_expr == trait_expr) {
                b.methods.push(m);
            } else {
                blocks.push(InlineImpl {
                    trait_expr,
                    is_unsafe: m.is_unsafe_impl,
                    def_module: mod_path.to_string(),
                    env: env.clone(),
                    methods: vec![m],
                });
            }
        }
        if !blocks.is_empty() {
            self.inline_impls.entry(ty_id).or_default().extend(blocks);
        }
    }

    /// The borrow contract of a trait method, used for its vtable slot. Trait methods are part of a
    /// public interface, so the same rules as `pub` functions apply: explicit `borrows(...)` by
    /// parameter name, `self` / single-input return elision, and no elided parameter flows.
    pub(super) fn trait_method_contract(
        &self,
        m: &TraitMethodDecl,
        ret_ty: TypeId,
    ) -> Result<FnContract, String> {
        let names: Vec<&str> = m.params.iter().map(|p| p.name.as_str()).collect();
        let position = |name: &str| -> Result<LocalId, String> {
            names
                .iter()
                .position(|n| *n == name)
                .map(|i| LocalId((i + 1) as u32))
                .ok_or_else(|| {
                    format!(
                        "Unknown parameter '{name}' in borrows(...) contract on trait method '{}'",
                        m.name
                    )
                })
        };
        let mut contract = FnContract::default();
        let mut has_ret_item = false;
        for item in m.borrows.iter().flatten() {
            match item {
                BorrowContractItem::Return { name, contents } => {
                    has_ret_item = true;
                    let loc = position(name)?;
                    contract.ret.push(if *contents { loc.contents() } else { loc });
                }
                BorrowContractItem::ParamFlow { dst, src } => {
                    contract.flows.push((position(dst)?, position(src)?));
                }
            }
        }
        let explicit_empty = m.borrows.as_ref().is_some_and(|i| i.is_empty());
        if !has_ret_item && !explicit_empty && self.type_contains_safe_ref(ret_ty) {
            // The receiver is always a reference (`&Self` / `&mut Self`), so `self` elision applies.
            contract.ret = vec![LocalId(1)];
        }
        Ok(contract)
    }

    /// Resolves the contract of a written function type `fn(...) -> R [borrows(...)]`. Parameters are
    /// named positionally (`_1`, `_2`, ...). Like `pub` functions, the return contract may be elided
    /// when at most one parameter carries a reference; parameter-to-parameter flows are never elided.
    pub(super) fn fn_type_contract(
        &self,
        args: &[TypeId],
        ret: TypeId,
        items: Option<&[BorrowContractItem]>,
    ) -> Result<FnContract, String> {
        let position = |name: &str| -> Result<LocalId, String> {
            let idx = name
                .strip_prefix('_')
                .and_then(|d| d.parse::<usize>().ok())
                .filter(|&i| i >= 1 && i <= args.len())
                .ok_or_else(|| {
                    format!(
                        "Function type contract names unknown parameter '{name}' (expected '_1'..='_{}')",
                        args.len()
                    )
                })?;
            Ok(LocalId(idx as u32))
        };
        let mut contract = FnContract::default();
        let mut has_ret_item = false;
        for item in items.unwrap_or(&[]) {
            match item {
                BorrowContractItem::Return { name, contents } => {
                    has_ret_item = true;
                    let loc = position(name)?;
                    contract.ret.push(if *contents { loc.contents() } else { loc });
                }
                BorrowContractItem::ParamFlow { dst, src } => {
                    contract.flows.push((position(dst)?, position(src)?));
                }
            }
        }
        let explicit_empty = items.is_some_and(|i| i.is_empty());
        if !has_ret_item && !explicit_empty && self.type_contains_safe_ref(ret) {
            let ref_params: Vec<LocalId> = args
                .iter()
                .enumerate()
                .filter(|(_, t)| self.type_contains_safe_ref(**t))
                .map(|(i, _)| LocalId((i + 1) as u32))
                .collect();
            if ref_params.len() > 1 {
                return Err(
                    "Function type returns a reference and takes multiple reference parameters; add an explicit 'borrows(_N, ...)' contract"
                        .to_string(),
                );
            }
            contract.ret = ref_params;
        }
        Ok(contract)
    }

    /// Resolves `opaque(owns T)` / `opaque(borrows T)`, the contents an `opaque` holds without a
    /// visible field. Owning a linear `T` makes an instantiation linear, regardless of which
    /// lifecycle hooks the type declares.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn declared_contents(
        &mut self,
        type_name: &str,
        ownership: OpaqueOwnership,
        owns: &[String],
        borrows: &[String],
        env: &HashMap<String, ComptimeVal>,
        fields: &[FieldDecl],
        has_drop_hook: bool,
    ) -> Result<(OpaqueOwnership, DeclaredContents), String> {
        // Lint: an owning container (one with a `drop` hook) that holds a type parameter only behind
        // a raw pointer owns nothing as far as the checker knows, so linear elements would be lost.
        if has_drop_hook {
            for f in fields {
                let mut behind_raw = Vec::new();
                Self::collect_type_params_behind(&f.ty, true, false, &mut behind_raw);
                for name in behind_raw {
                    if !owns.contains(&name) && matches!(env.get(&name), Some(ComptimeVal::Type(_)))
                    {
                        self.warn(format!(
                            "opaque '{type_name}' has a 'drop' hook and holds '{name}' behind a raw pointer (field '{}'), which owns nothing; use '*own {name}' if it owns these values, or linear '{name}' values would be discarded silently",
                            f.name
                        ));
                    }
                }
            }
        }
        let mut held_names = Vec::new();
        for f in fields {
            Self::collect_type_params_behind(&f.ty, false, false, &mut held_names);
        }
        let resolve = |name: &String, modifier: &str| match env.get(name) {
            Some(ComptimeVal::Type(t)) => Ok(*t),
            _ => Err(format!(
                "'{modifier} {name}' on opaque '{type_name}' does not name a comptime type parameter in scope"
            )),
        };
        let mut result = ownership;
        let mut declared = DeclaredContents::default();
        for name in owns {
            let t = resolve(name, "owns")?;
            if held_names.contains(name) {
                self.warn(format!(
                    "'owns {name}' on opaque '{type_name}' is redundant: a field already holds '{name}' behind '*own' or in 'uninit' storage"
                ));
            }
            if self.is_linear_type(t) {
                if ownership == OpaqueOwnership::Affine {
                    return Err(format!(
                        "'owns {name}' on 'opaque(affine) {type_name}' has linear type '{}'; 'opaque(affine)' types must be droppable without consumption (use 'opaque' or 'opaque(linear)')",
                        self.type_display_name(t)
                    ));
                }
                result = OpaqueOwnership::Linear;
            }
            declared.owns.push(t);
        }
        for name in borrows {
            declared.borrows.push(resolve(name, "borrows")?);
        }
        Ok((result, declared))
    }

    /// Collects the single-segment type names a field type expression holds behind a raw pointer
    /// (`raw`: `*const T` / `*mut T`) or as owned contents (`!raw`: `*own T`, `uninit T`), possibly
    /// nested inside arrays or optionals.
    fn collect_type_params_behind(te: &TypeExpr, raw: bool, behind: bool, out: &mut Vec<String>) {
        match te {
            TypeExpr::Ptr { inner, kind, .. } => {
                let held = match kind {
                    PtrKind::Raw => raw,
                    PtrKind::Own => !raw,
                    PtrKind::View => false,
                };
                if held {
                    Self::collect_type_params_behind(inner, raw, true, out);
                }
            }
            TypeExpr::Uninit(inner) => {
                Self::collect_type_params_behind(inner, raw, behind || !raw, out);
            }
            TypeExpr::Optional(inner) | TypeExpr::Array { elem: inner, .. } => {
                Self::collect_type_params_behind(inner, raw, behind, out);
            }
            TypeExpr::Named(path) if behind && path.len() == 1 => {
                if !out.contains(&path[0]) {
                    out.push(path[0].clone());
                }
            }
            _ => {}
        }
    }

    #[allow(clippy::too_many_arguments)]
    pub(super) fn instantiate_composite(
        &mut self,
        mod_path: &str,
        type_name: &str,
        is_opaque: bool,
        is_packed: bool,
        ownership: OpaqueOwnership,
        threads: ThreadDecl,
        env: &HashMap<String, ComptimeVal>,
        memo_key: Option<(String, String, Vec<ComptimeVal>)>,
        fields: &[FieldDecl],
        consts: &[ConstDecl],
        statics: &[StaticDecl],
        methods: &[FuncDecl],
        default_hook: Option<(Vec<WherePredicate>, Block)>,
        clone_hooks: &[CloneHookDecl],
        drop_hooks: &[DropHookDecl],
        format_hook: Option<(String, String, Option<String>, Block)>,
        declared: DeclaredContents,
    ) -> Result<TypeId, String> {
        let reserved = self.take_reserved_type();
        // Compile-time fields (`const Handle: type = *own u8;`, `const N: usize = 4;`) are known to the
        // fields and methods, by name and as `Self::Handle`, before the type is.
        let mut with_assoc = env.clone();
        for c in consts.iter().filter(|c| c.field) {
            let bounded = c.ty.as_ref().is_some_and(|te| self.is_bound_expr(mod_path, &with_assoc, te));
            match self.eval_field(mod_path, None, &with_assoc, c, &format!("'{type_name}'")) {
                Ok((_, _, v)) => {
                    with_assoc.insert(c.name.clone(), v);
                }
                // A bound is checked where the field is written; anything else is evaluated
                // again where it is used, once what it names exists.
                Err(e) if bounded => return Err(e),
                Err(_) => {}
            }
        }
        let env = &with_assoc;
        let (inherent_methods, impl_methods) = Self::split_impl_methods(methods);
        let methods: &[FuncDecl] = &inherent_methods;
        let mut matched_drop_hooks = Vec::new();
        for h in drop_hooks {
            if self.eval_where_clauses(env, &h.where_clauses)? {
                matched_drop_hooks.push(h);
            }
        }
        if matched_drop_hooks.len() > 1 {
            return Err(format!(
                "Conflicting 'drop' hooks match for struct '{type_name}'"
            ));
        }
        if matched_drop_hooks.is_empty() {
            for h in drop_hooks {
                for w in &h.where_clauses {
                    if w.constraint == TypeConstraint::Linear
                        && w.negated
                        && let Some(ComptimeVal::Type(t_id)) = env.get(&w.type_param)
                        && self.is_linear_type(*t_id)
                    {
                        return Err(format!(
                            "Opaque type '{type_name}' defines 'drop' with 'where {}: !linear', but is missing a matching 'impl drop where {}: linear' teardown hook",
                            w.type_param, w.type_param
                        ));
                    }
                }
            }
        }
        let selected_drop = matched_drop_hooks.into_iter().next();

        let mut matched_clone_hooks = Vec::new();
        for h in clone_hooks {
            if self.eval_where_clauses(env, &h.where_clauses)? {
                matched_clone_hooks.push(h);
            }
        }
        if matched_clone_hooks.len() > 1 {
            return Err(format!(
                "Conflicting 'clone' hooks match for struct '{type_name}'"
            ));
        }
        let selected_clone = matched_clone_hooks.into_iter().next();

        let mut effective_ownership = ownership;
        if is_packed
            && is_opaque
            && effective_ownership == OpaqueOwnership::Default
            && selected_drop.is_none()
            && selected_clone.is_none()
        {
            effective_ownership = OpaqueOwnership::Copy;
        }
        if is_opaque
            && let Some(dh) = selected_drop
            && dh
                .where_clauses
                .iter()
                .any(|w| w.constraint == TypeConstraint::Linear && !w.negated)
        {
            if effective_ownership == OpaqueOwnership::Affine {
                return Err(format!(
                    "Affine opaque '{type_name}' ('opaque(affine)') cannot select a 'where ...: linear' drop hook; use 'opaque' or 'opaque(linear)'"
                ));
            }
            effective_ownership = OpaqueOwnership::Linear;
        }

        let is_linear = is_opaque && effective_ownership == OpaqueOwnership::Linear;
        if is_linear && selected_clone.is_some() {
            return Err(format!(
                "Linear opaque '{type_name}' cannot implement `clone`; linear values must be consumed exactly once"
            ));
        }
        if is_opaque && effective_ownership == OpaqueOwnership::Copy {
            if selected_drop.is_some() {
                return Err(format!(
                    "Copy opaque '{type_name}' ('opaque(copy)') cannot implement `drop`"
                ));
            }
            if selected_clone.is_some() {
                return Err(format!(
                    "Copy opaque '{type_name}' ('opaque(copy)') is implicitly copyable and cannot define a custom `clone` hook"
                ));
            }
        }
        let mut field_tys = Vec::with_capacity(fields.len());
        let mut field_infos = Vec::with_capacity(fields.len());
        let mut rel_fields = HashMap::new();
        let mut packed_offsets = Vec::new();
        let mut total_bits = 0u16;
        let mut contents_linear = false;
        for (idx, f) in fields.iter().enumerate() {
            if is_packed
                && matches!(
                    f.ty,
                    TypeExpr::RelRef(_) | TypeExpr::RelSlice(_) | TypeExpr::RelStr
                )
            {
                return Err(format!(
                    "'&rel' relative references are not permitted inside packed type '{}' (field '{}')",
                    type_name, f.name
                ));
            }
            let f_ty = match &f.ty {
                TypeExpr::RelRef(inner) => {
                    if !is_opaque {
                        return Err(format!(
                            "'&rel' relative references are only permitted in 'opaque' field declarations (found in struct '{}', field '{}')",
                            type_name, f.name
                        ));
                    }
                    let elem_ty = self.resolve_type_expr(mod_path, None, env, inner)?;
                    let isize_ty = self.intern_type(Type::Int {
                        signed: true,
                        bits: 64,
                    });
                    rel_fields.insert(idx as u32, RelFieldKind::Elem(elem_ty));
                    isize_ty
                }
                TypeExpr::RelSlice(inner) => {
                    if !is_opaque {
                        return Err(format!(
                            "'&rel' relative references are only permitted in 'opaque' field declarations (found in struct '{}', field '{}')",
                            type_name, f.name
                        ));
                    }
                    let elem_ty = self.resolve_type_expr(mod_path, None, env, inner)?;
                    let isize_ty = self.intern_type(Type::Int {
                        signed: true,
                        bits: 64,
                    });
                    let usize_ty = self.intern_type(Type::Int {
                        signed: false,
                        bits: 64,
                    });
                    let repr_ty = self.intern_type(Type::Struct(vec![isize_ty, usize_ty]));
                    rel_fields.insert(idx as u32, RelFieldKind::Slice(elem_ty));
                    repr_ty
                }
                TypeExpr::RelStr => {
                    if !is_opaque {
                        return Err(format!(
                            "'&rel' relative references are only permitted in 'opaque' field declarations (found in struct '{}', field '{}')",
                            type_name, f.name
                        ));
                    }
                    let isize_ty = self.intern_type(Type::Int {
                        signed: true,
                        bits: 64,
                    });
                    let usize_ty = self.intern_type(Type::Int {
                        signed: false,
                        bits: 64,
                    });
                    let repr_ty = self.intern_type(Type::Struct(vec![isize_ty, usize_ty]));
                    rel_fields.insert(idx as u32, RelFieldKind::Str);
                    repr_ty
                }
                other => self.resolve_type_expr(mod_path, None, env, other)?,
            };
            if let Some(tr) = self.traits.get(&f_ty) {
                return Err(format!(
                    "Trait '{}' is an unsized meta-type constraint and cannot be stored by value in field '{}' of '{}'; use a generic comptime type parameter or '&{}'",
                    tr.name, f.name, type_name, tr.name
                ));
            }
            if self.is_opaque_type(f_ty) {
                return Err(format!(
                    "Unsized type 'opaque' cannot be stored by value in field '{}' of '{}'; use '*const opaque', '*mut opaque', '&opaque', or '&mut opaque'",
                    f.name, type_name
                ));
            }
            if is_packed {
                if self.layout_is_pending(f_ty) {
                    return Err(format!(
                        "Field '{}' of packed type '{}' needs the size of a type still being defined",
                        f.name, type_name
                    ));
                }
                let Some((f_bits, _)) = self.packed_field_bit_width(f_ty) else {
                    return Err(format!(
                        "Field '{}' of packed type '{}' has non-packable type '{}'; packed fields must be integers (i1..i512, u1..u512), bool, enum, or nested packed types",
                        f.name,
                        type_name,
                        self.type_display_name(f_ty)
                    ));
                };
                packed_offsets.push((total_bits, f_bits));
                total_bits = total_bits.saturating_add(f_bits);
            }
            if is_opaque {
                match effective_ownership {
                    OpaqueOwnership::Copy => {
                        if !self.is_copy_type(f_ty) {
                            return Err(format!(
                                "Field '{}' of 'opaque(copy) {}' has non-copy type",
                                f.name, type_name
                            ));
                        }
                        if self.holds_own_ptr(f_ty) {
                            return Err(format!(
                                "Field '{}' of 'opaque(copy) {}' holds an owning pointer ('*own'); a copy would duplicate the values it owns",
                                f.name, type_name
                            ));
                        }
                    }
                    OpaqueOwnership::Affine => {
                        if self.field_holds_linear(f_ty) {
                            return Err(format!(
                                "Field '{}' of 'opaque(affine) {}' holds a linear value; 'opaque(affine)' types must be droppable without consumption (use 'opaque' or 'opaque(linear)')",
                                f.name, type_name
                            ));
                        }
                    }
                    // Bare `opaque` is affine by default and upgrades to linear when holding a
                    // linear value (inline, behind `*own`, or in `uninit` storage).
                    OpaqueOwnership::Default => contents_linear |= self.field_holds_linear(f_ty),
                    OpaqueOwnership::Linear => {}
                }
            } else if self.holds_own_ptr(f_ty) {
                return Err(format!(
                    "Field '{}' of struct '{}' holds an owning pointer ('*own'); only 'opaque' fields may own values, since anyone can take a 'struct' apart",
                    f.name, type_name
                ));
            }
            field_tys.push(f_ty);
            field_infos.push((f.name.clone(), f_ty, f.vis, f.default_val.clone()));
        }

        if is_packed && (total_bits == 0 || total_bits > 512) {
            return Err(format!(
                "Packed type '{}' has total bit width {} which is outside the supported 1..=512 bit range",
                type_name, total_bits
            ));
        }
        let is_linear = is_linear || contents_linear;
        if contents_linear {
            effective_ownership = OpaqueOwnership::Linear;
            if selected_clone.is_some() {
                return Err(format!(
                    "Opaque '{type_name}' holds a linear value, so it is linear and cannot implement `clone`"
                ));
            }
        } else if effective_ownership == OpaqueOwnership::Default {
            effective_ownership = OpaqueOwnership::Affine;
        }

        // Every distinct struct/opaque declaration gets a distinct TypeId so its field names,
        // defaults, and methods in `self.composites` never collide (tuples use `intern_type`).
        let repr = if is_packed {
            Type::Int {
                signed: false,
                bits: total_bits,
            }
        } else {
            Type::Struct(field_tys)
        };
        let ty_id = self.define_type(reserved, type_name, repr)?;
        if is_linear {
            let label = match &memo_key {
                Some((_, fname, args)) => format!(
                    "{fname}[{}]",
                    args.iter()
                        .map(|a| self.comptime_val_label(a))
                        .collect::<Vec<_>>()
                        .join(", ")
                ),
                None => type_name.to_string(),
            };
            self.program.linear_types.push((ty_id, label));
        }

        let mut const_map = HashMap::new();
        for c in consts {
            const_map.insert(c.name.clone(), (c.vis, c.clone()));
        }
        let mut static_map = HashMap::new();
        for s in statics {
            static_map.insert(s.name.clone(), (s.vis, s.clone()));
        }
        let mut method_map = HashMap::new();
        for m in methods {
            method_map.insert(m.name.clone(), (m.vis, m.clone()));
        }

        let info = CompositeInfo {
            name: type_name.to_string(),
            is_opaque,
            is_packed,
            total_bits,
            packed_offsets,
            ownership: effective_ownership,
            threads,
            cell_fields: fields
                .iter()
                .enumerate()
                .filter(|(_, f)| f.is_cell)
                .map(|(i, _)| i)
                .collect(),
            has_format_hook: format_hook.is_some(),
            def_module: mod_path.to_string(),
            comptime_env: env.clone(),
            fields: field_infos,
            rel_fields,
            consts: const_map,
            statics: static_map,
            methods: std::sync::Arc::new(method_map),
            method_fn_ids: HashMap::new(),
            default_fn: None,
            clone_fn: None,
            drop_fn: None,
            format_fn: None,
            declared,
            may_dangle: Vec::new(),
        };
        self.composites.insert(ty_id, std::sync::Arc::new(info));
        // Stage 3 sees an opaque's fields but not which pointers own what, so it is told
        // directly which opaques carry borrows.
        if is_opaque && self.type_contains_safe_borrow(ty_id) {
            self.program.loan_types.push(ty_id);
        }
        let label = match &memo_key {
            Some((_, fname, args)) => format!(
                "{fname}[{}]",
                args.iter()
                    .map(|a| self.comptime_val_label(a))
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
            None => type_name.to_string(),
        };
        self.program.type_names.push((ty_id, label));
        let names = self.composites[&ty_id].fields.iter().map(|f| f.0.clone()).collect();
        self.program.field_names.push((ty_id, names));
        self.register_inline_impls(ty_id, mod_path, env, impl_methods);
        if let Some(key) = memo_key {
            self.memoized_type_calls.insert(key, ty_id);
        } else if !type_name.starts_with('<') {
            self.named_types
                .insert((mod_path.to_string(), type_name.to_string()), ty_id);
        }

        for c in consts {
            let _ = self.resolve_associated_const(ty_id, &c.name)?;
        }
        for s in statics {
            let _ = self.resolve_associated_static(ty_id, &s.name)?;
        }

        // Instantiate non-generic inherent methods eagerly (only if their `where` clauses are satisfied);
        // generic inherent methods (with `comptime` parameters) are instantiated on demand at call sites.
        if let Ok(Some((_, _, Item::TypeDecl { vis, .. }, _))) =
            self.find_item_in_module(mod_path, mod_path, type_name)
            && vis.is_export()
        {
            self.exported_type_set.insert(ty_id);
        }
        for m in methods {
            if m.vis.is_export() && m.params.iter().any(|p| p.is_comptime) {
                return Err(format!(
                    "Exported method '{}.{}' cannot have 'comptime' parameters",
                    type_name, m.name
                ));
            }
            if !m.params.iter().any(|p| p.is_comptime)
                && self.eval_where_clauses(env, &m.where_clauses)?
            {
                let fn_id = self.schedule_method(mod_path, ty_id, env, m)?;
                self.composite_mut(ty_id)
                    .method_fn_ids
                    .insert(m.name.clone(), fn_id);
            }
        }

        // Instantiate `default`, `clone`, `drop`, `format` lifecycle hooks on `struct`
        if let Some((where_clauses, def_blk)) = default_hook
            && self.eval_where_clauses(env, &where_clauses)?
        {
            let decl = FuncDecl {
                vis: Visibility::Pub,
                name: format!("{type_name}::default"),
                params: vec![],
                ret_ty: TypeExpr::SelfType,
                borrows: None,
                where_clauses: Vec::new(),
                body: def_blk,
                is_unsafe: false,
                impl_of: None,
                is_unsafe_impl: false,
            };
            let fn_id = self.schedule_method(mod_path, ty_id, env, &decl)?;
            self.composite_mut(ty_id).default_fn = Some(fn_id);
        }

        if let Some(clone_hook) = selected_clone {
            let decl = FuncDecl {
                vis: Visibility::Pub,
                name: format!("{type_name}::clone"),
                params: vec![crate::ast::Param {
                    is_comptime: false,
                    default: None,
                    is_mut: false,
                    name: clone_hook.self_name.clone(),
                    ty: TypeExpr::Ref {
                        mutable: false,
                        inner: Box::new(TypeExpr::SelfType),
                },
                }],
                ret_ty: TypeExpr::SelfType,
                borrows: None,
                where_clauses: Vec::new(),
                body: clone_hook.body.clone(),
                is_unsafe: false,
                impl_of: None,
                is_unsafe_impl: false,
            };
            let fn_id = self.schedule_method(mod_path, ty_id, env, &decl)?;
            self.composite_mut(ty_id).clone_fn = Some(fn_id);
        }

        if let Some(drop_hook) = selected_drop {
            let decl = FuncDecl {
                vis: Visibility::Pub,
                name: format!("{type_name}::drop"),
                params: vec![crate::ast::Param {
                    is_comptime: false,
                    default: None,
                    is_mut: false,
                    name: drop_hook.self_name.clone(),
                    ty: TypeExpr::Ref {
                        mutable: true,
                        inner: Box::new(TypeExpr::SelfType),
                },
                }],
                ret_ty: TypeExpr::Void,
                borrows: None,
                where_clauses: Vec::new(),
                body: drop_hook.body.clone(),
                is_unsafe: false,
                impl_of: None,
                is_unsafe_impl: false,
            };
            let fn_id = self.schedule_method(mod_path, ty_id, env, &decl)?;
            let mut may_dangle = Vec::new();
            for name in &drop_hook.may_dangle {
                let Some(ComptimeVal::Type(t)) = env.get(name) else {
                    return Err(format!(
                        "'may_dangle {name}' on the 'drop' hook of '{type_name}' does not name a comptime type parameter in scope"
                    ));
                };
                may_dangle.push(*t);
            }
            let comp = self.composite_mut(ty_id);
            comp.drop_fn = Some(fn_id);
            comp.may_dangle = may_dangle;
            let destructor = self.hook_then_fields(ty_id, fn_id);
            self.program.destructors.push((ty_id, destructor));
            if self.drop_ignores_borrows(ty_id) {
                self.program.dangle_types.push(ty_id);
            }
        }

        if let Some((self_name, fmt_name, opt_spec_name, fmt_blk)) = format_hook {
            let mut params = vec![
                crate::ast::Param {
                    is_comptime: false,
                    default: None,
                    is_mut: false,
                    name: self_name,
                    ty: TypeExpr::Ref {
                        mutable: false,
                        inner: Box::new(TypeExpr::SelfType),
                },
                },
                crate::ast::Param {
                    is_comptime: false,
                    default: None,
                    is_mut: false,
                    name: fmt_name,
                    ty: TypeExpr::Ref {
                        mutable: true,
                        inner: Box::new(TypeExpr::Named(vec![
                            "core".to_string(),
                            "fmt".to_string(),
                            "Formatter".to_string(),
                        ])),
                },
                },
            ];
            let takes_spec = if let Some(spec_name) = opt_spec_name {
                params.push(crate::ast::Param {
                    is_comptime: false,
                    default: None,
                    is_mut: false,
                    name: spec_name,
                    ty: TypeExpr::StrRef,
                });
                true
            } else {
                false
            };
            let decl = FuncDecl {
                vis: Visibility::Pub,
                name: format!("{type_name}::format"),
                params,
                ret_ty: TypeExpr::Void,
                borrows: None,
                where_clauses: Vec::new(),
                body: fmt_blk,
                is_unsafe: false,
                impl_of: None,
                is_unsafe_impl: false,
            };
            let fn_id = self.schedule_method(mod_path, ty_id, env, &decl)?;
            self.composite_mut(ty_id).format_fn = Some((fn_id, takes_spec));
        }

        Ok(ty_id)
    }

    pub(super) fn type_contains_safe_ref(&self, ty_id: TypeId) -> bool {
        self.type_contains_safe_borrow(ty_id)
    }

    pub(super) fn apply_func_borrow_contracts(
        &mut self,
        fn_id: FuncId,
        decl: &FuncDecl,
        param_tys: &[TypeId],
        ret_ty: TypeId,
    ) -> Result<(), String> {
        let rt_params: Vec<(String, TypeId)> = decl
            .params
            .iter()
            .filter(|p| !p.is_comptime)
            .map(|p| p.name.clone())
            .zip(param_tys.iter().copied())
            .collect();

        let first_is_self = rt_params.first().is_some_and(|(n, _)| n == "self");
        // Every `pub` and `export` function has a signature-only borrow contract; private and
        // `pub(mod)` functions, called only from their own module, have theirs inferred.
        let is_pub = decl.vis.is_public_or_export();
        let ref_params: Vec<LocalId> = rt_params
            .iter()
            .enumerate()
            .filter(|(_, (_, ty))| self.type_contains_safe_ref(*ty))
            .map(|(i, _)| LocalId((i + 1) as u32))
            .collect();

        let mut ret_list = Vec::new();
        let mut param_list = Vec::new();
        let mut has_ret_item = false;
        let mut has_param_item = false;
        for item in decl.borrows.iter().flatten() {
            match item {
                BorrowContractItem::Return { name, contents } => {
                    has_ret_item = true;
                    let Some(idx) = rt_params.iter().position(|(pname, _)| pname == name) else {
                        return Err(format!(
                            "Unknown runtime parameter '{}' in borrows(...) contract on '{}'",
                            name, decl.name
                        ));
                    };
                    let loc = LocalId((idx + 1) as u32);
                    let loc = if *contents { loc.contents() } else { loc };
                    if !ret_list.contains(&loc) {
                        ret_list.push(loc);
                    }
                }
                BorrowContractItem::ParamFlow { dst, src } => {
                    has_param_item = true;
                    let Some(dst_idx) = rt_params.iter().position(|(pname, _)| pname == dst) else {
                        return Err(format!(
                            "Unknown destination parameter '{}' in borrows({}: {}) contract on '{}'",
                            dst, dst, src, decl.name
                        ));
                    };
                    let Some(src_idx) = rt_params.iter().position(|(pname, _)| pname == src) else {
                        return Err(format!(
                            "Unknown source parameter '{}' in borrows({}: {}) contract on '{}'",
                            src, dst, src, decl.name
                        ));
                    };
                    let pair = (LocalId((dst_idx + 1) as u32), LocalId((src_idx + 1) as u32));
                    if !param_list.contains(&pair) {
                        param_list.push(pair);
                    }
                }
            }
        }
        // `borrows()` (an explicit clause with no return items) declares that the return borrows nothing.
        let explicit_empty = decl.borrows.as_ref().is_some_and(|items| items.is_empty());

        let ret_borrows = if has_ret_item || explicit_empty {
            Some(ret_list)
        } else if is_pub && self.type_contains_safe_ref(ret_ty) {
            // Elision rules count as a defined contract: they depend only on the signature.
            if first_is_self && self.type_contains_safe_ref(rt_params[0].1) {
                Some(vec![LocalId(1)])
            } else if ref_params.len() == 1 {
                Some(vec![ref_params[0]])
            } else if ref_params.len() > 1 {
                return Err(format!(
                    "Public function '{}' returns a reference and takes multiple reference parameters; add an explicit 'borrows(...)' contract",
                    decl.name
                ));
            } else {
                Some(Vec::new())
            }
        } else {
            None
        };

        // Parameter-to-parameter flows are never elided: a `pub` function that stores a reference from
        // one parameter into another (including `self`) must declare `borrows(dst: src)`.
        let param_borrows = if is_pub || has_param_item {
            Some(param_list)
        } else {
            None
        };

        if let Some(func) = self.program.functions.iter_mut().find(|f| f.id == fn_id) {
            func.ret_borrows = ret_borrows;
            func.param_borrows = param_borrows;
        }
        Ok(())
    }

    pub(super) fn schedule_method(
        &mut self,
        mod_path: &str,
        owner_ty: TypeId,
        env: &HashMap<String, ComptimeVal>,
        decl: &FuncDecl,
    ) -> Result<FuncId, String> {
        let mut sig_env = env.clone();
        let mut param_tys = Vec::new();
        for p in &decl.params {
            if !p.is_comptime {
                if matches!(p.ty, TypeExpr::Constraint(_) | TypeExpr::TraitBounds(_)) {
                    return Err(format!(
                        "Parameter '{}' of '{}' has a meta-type constraint by value; use '[T: ...]({}: T)' for static dispatch or '&Trait' for dynamic dispatch",
                        p.name, decl.name, p.name
                    ));
                }
                let pty = self.resolve_type_expr(mod_path, Some(owner_ty), &sig_env, &p.ty)?;
                if let Some(tr) = self.traits.get(&pty) {
                    return Err(format!(
                        "Trait '{}' is an unsized meta-type constraint and cannot be passed by value in parameter '{}' of '{}'; use '[T: {}]({}: T)' for static dispatch or '({}: &{})' for dynamic dispatch",
                        tr.name, p.name, decl.name, tr.name, p.name, p.name, tr.name
                    ));
                }
                if self.is_opaque_type(pty) {
                    return Err(format!(
                        "Unsized type '{}' cannot be passed by value in parameter '{}' of '{}'; use '*const {0}', '*mut {0}', '&{0}', or '&mut {0}'",
                        self.type_display_name(pty),
                        p.name,
                        decl.name
                    ));
                }
                sig_env.insert(format!("__var_ty:{}", p.name), ComptimeVal::Type(pty));
                param_tys.push(pty);
            }
        }
        if let TypeExpr::OpaqueTrait(bound_expr) = &decl.ret_ty {
            if decl.vis.is_export() {
                return Err(format!(
                    "Exported method '{}' cannot return existential 'opaque Trait'; 'export fn' requires a C-compatible return type",
                    decl.name
                ));
            }
            let void_ty = self.intern_type(Type::Void);
            let fn_id = self.reserve_function(decl.vis, None, &param_tys, void_ty);
            if decl.is_unsafe {
                self.unsafe_fns.insert(fn_id);
            }
            if self.schedule_no_private {
                self.no_private_access_fns.insert(fn_id);
            }
            self.opaque_ret_funcs.insert(
                fn_id,
                OpaqueRetBound {
                    bound_mod: mod_path.to_string(),
                    owner_ty: Some(owner_ty),
                    env: sig_env.clone(),
                    bound_expr: (**bound_expr).clone(),
                },
            );
            let pending = PendingFunc {
                func_id: fn_id,
                module_path: mod_path.to_string(),
                owner_ty: Some(owner_ty),
                decl: decl.clone(),
                comptime_env: sig_env,
                closure_captures: Vec::new(),
            };
            self.lower_function_body(pending)?;
            let (_, ret_ty) = self.func_sigs[&fn_id].clone();
            self.apply_func_borrow_contracts(fn_id, decl, &param_tys, ret_ty)?;
            return Ok(fn_id);
        }
        let ret_ty = self.resolve_type_expr(mod_path, Some(owner_ty), &sig_env, &decl.ret_ty)?;
        if let Some(tr) = self.traits.get(&ret_ty) {
            return Err(format!(
                "Trait '{}' is an unsized meta-type constraint and cannot be returned by value from '{}'",
                tr.name, decl.name
            ));
        }
        if self.is_opaque_type(ret_ty) {
            return Err(format!(
                "Unsized type '{}' cannot be returned by value from '{}'; use '*const {0}', '*mut {0}', '&{0}', or '&mut {0}'",
                self.type_display_name(ret_ty),
                decl.name
            ));
        }
        let fn_id = self.reserve_function(decl.vis, None, &param_tys, ret_ty);
        if decl.is_unsafe {
            self.unsafe_fns.insert(fn_id);
        }
        if self.schedule_no_private {
            self.no_private_access_fns.insert(fn_id);
        }
        self.apply_func_borrow_contracts(fn_id, decl, &param_tys, ret_ty)?;
        if decl.vis.is_export() {
            let owner_name = self.type_display_name(owner_ty);
            let export_sym = format!("{}_{}", owner_name, decl.name);
            self.setup_export_function(fn_id, export_sym, decl, &param_tys, ret_ty)?;
        }
        if self
            .composites
            .get(&owner_ty)
            .is_some_and(|c| c.is_opaque && c.ownership == OpaqueOwnership::Linear)
            && param_tys.first() == Some(&owner_ty)
            && let Some(func) = self.program.functions.iter_mut().find(|f| f.id == fn_id)
        {
            func.linear_self = Some(owner_ty);
        }
        self.pending_funcs.push(PendingFunc {
            func_id: fn_id,
            module_path: mod_path.to_string(),
            owner_ty: Some(owner_ty),
            decl: decl.clone(),
            comptime_env: sig_env,
            closure_captures: Vec::new(),
        });
        Ok(fn_id)
    }

    pub(super) fn reserve_function(
        &mut self,
        _vis: Visibility,
        export: Option<String>,
        param_tys: &[TypeId],
        ret_ty: TypeId,
    ) -> FuncId {
        let fn_id = FuncId((self.program.externs.len() + self.program.functions.len()) as u32);
        let mut locals = vec![ret_ty];
        locals.extend_from_slice(param_tys);
        self.program.functions.push(Function {
            id: fn_id,
            arg_count: param_tys.len(),
            ret_borrows: None,
            param_borrows: None,
            linear_self: None,
            linear_owner: false,
            debug_name: None,
            param_names: Vec::new(),
            local_names: Vec::new(),
            export,
            locals,
            blocks: Vec::new(),
        });
        self.func_sigs.insert(fn_id, (param_tys.to_vec(), ret_ty));
        fn_id
    }

    pub(super) fn get_or_instantiate_func(
        &mut self,
        mod_path: &str,
        name: &str,
        comptime_args: &[ComptimeVal],
    ) -> Result<FuncId, String> {
        let key = (
            mod_path.to_string(),
            name.to_string(),
            comptime_args.to_vec(),
        );
        if let Some(&id) = self.resolved_funcs.get(&key) {
            return Ok(id);
        }
        let overloads = self.find_funcs_in_module(mod_path, mod_path, name)?;
        if overloads.is_empty() {
            return Err(format!("Function '{name}' not found in '{mod_path}'"));
        }

        let mut matching_overloads: Vec<(FuncDecl, HashMap<String, ComptimeVal>, u32)> = Vec::new();
        let mut last_constraint_err: Option<String> = None;

        for (_, _, decl) in overloads {
            let ct_count = decl.params.iter().filter(|p| p.is_comptime).count();
            if ct_count != comptime_args.len() {
                continue;
            }
            let mut env = HashMap::new();
            let mut ct_idx = 0;
            let mut spec_sum = 0u32;
            let mut ok = true;
            for p in &decl.params {
                if p.is_comptime {
                    let val = comptime_args[ct_idx].clone();
                    match &val {
                        ComptimeVal::Type(arg_ty) => {
                            match self
                                .eval_comptime_type_bound(mod_path, None, &env, &p.ty, *arg_ty)?
                            {
                                Some(Ok(s)) => spec_sum += s as u32,
                                Some(Err(e)) => {
                                    last_constraint_err = Some(format!(
                                        "{} (for parameter '{}' in '{}')",
                                        e, p.name, name
                                    ));
                                    ok = false;
                                    break;
                                }
                                None => {
                                    ok = false;
                                    break;
                                }
                            }
                        }
                        ComptimeVal::ConstExpr(_, cexpr) => {
                            if let Ok(param_ty) =
                                self.resolve_type_expr(mod_path, None, &env, &p.ty)
                                && let Some(tobj) = self.trait_objs.get(&param_ty).cloned()
                            {
                                if let Expr::Ref {
                                    mutable: ref_mut,
                                    expr: inner,
                                } = cexpr
                                {
                                    if tobj.mutable && !*ref_mut {
                                        last_constraint_err = Some(format!(
                                            "Cannot pass immutable comptime reference to '&mut {}' parameter '{}' in '{}'",
                                            self.type_display_name(tobj.trait_ty),
                                            p.name,
                                            name
                                        ));
                                        ok = false;
                                        break;
                                    }
                                    if let Expr::StructLit { ty: inner_te, .. } = inner.as_ref() {
                                        let concrete_ty =
                                            self.resolve_type_expr(mod_path, None, &env, inner_te)?;
                                        let m_count = self.traits[&tobj.trait_ty].methods.len();
                                        for m_idx in 0..m_count {
                                            if let Err(e) = self.resolve_trait_impl_method(
                                                mod_path,
                                                concrete_ty,
                                                tobj.trait_ty,
                                                m_idx,
                                                true,
                                            ) {
                                                last_constraint_err = Some(e);
                                                ok = false;
                                                break;
                                            }
                                        }
                                        if !ok {
                                            break;
                                        }
                                        spec_sum += 6;
                                    }
                                } else {
                                    last_constraint_err = Some(format!(
                                        "Comptime parameter '{}' in '{}' expects a reference to a type implementing '{}'",
                                        p.name,
                                        name,
                                        self.type_display_name(tobj.trait_ty)
                                    ));
                                    ok = false;
                                    break;
                                }
                            }
                        }
                        ComptimeVal::Module(_) => {
                            if matches!(p.ty, TypeExpr::Constraint(TypeConstraint::Module)) {
                                spec_sum += TypeConstraint::Module.specificity() as u32;
                            } else {
                                last_constraint_err = Some(format!(
                                    "Comptime module value is only valid for a 'module' parameter (for parameter '{}' in '{}')",
                                    p.name, name
                                ));
                                ok = false;
                                break;
                            }
                        }
                        _ => {
                            if matches!(p.ty, TypeExpr::Constraint(TypeConstraint::Module)) {
                                last_constraint_err = Some(format!(
                                    "Comptime parameter '{}' in '{}' requires a 'module' value",
                                    p.name, name
                                ));
                                ok = false;
                                break;
                            }
                            // A value cannot meet a bound on types. Any type that is not a trait
                            // shows whether `p.ty` is one.
                            let probe = self.intern_type(Type::Void);
                            if self
                                .eval_comptime_type_bound(mod_path, None, &env, &p.ty, probe)?
                                .is_some()
                            {
                                ok = false;
                                break;
                            }
                        }
                    }
                    env.insert(p.name.clone(), val);
                    ct_idx += 1;
                }
            }
            // `where` clauses (including negative bounds `[T: !sync]`) select overloads too.
            if ok && let Err(e) =
                self.check_where_clauses_or_err(&env, &decl.where_clauses, &format!("'{name}'"))
            {
                last_constraint_err = Some(e);
                ok = false;
            }
            if ok {
                matching_overloads.push((decl, env, spec_sum));
            }
        }

        if matching_overloads.is_empty() {
            return Err(last_constraint_err.unwrap_or_else(|| {
                format!(
                    "No overload of '{name}' in '{mod_path}' matches {} comptime arguments",
                    comptime_args.len()
                )
            }));
        }

        let cands: Vec<(String, FuncDecl, HashMap<String, ComptimeVal>, u32)> = matching_overloads
            .into_iter()
            .map(|(d, e, s)| (mod_path.to_string(), d, e, s))
            .collect();
        let idx = self.most_specific_overload(name, &cands)?;
        let decl = cands.into_iter().nth(idx).unwrap().1;
        if name == "spawn"
            && let Some(ComptimeVal::Type(f_ty)) = comptime_args.first()
        {
            self.check_non_borrowing_spawn_callable(*f_ty)?;
        }
        let fn_id = self.instantiate_specific_func_decl(mod_path, &decl, comptime_args)?;
        self.resolved_funcs.insert(key, fn_id);
        Ok(fn_id)
    }

    /// Picks the overload that is more specific than every other matching overload. Specificity is
    /// a partial order: candidate `A` beats `B` when each of `A`'s comptime bounds is subsumed by
    /// `B`'s (`signed` ⊑ `integer` ⊑ `number` ⊑ `scalar` ⊑ `type`; `A + B` ⊑ `A`), and `A` is
    /// either strictly more specific somewhere or ahead on its pattern-shape score (concrete
    /// receivers before structural ones before blanket `T`). Overlapping but incomparable bounds
    /// (`T: send` vs `T: number` for an `i32`) are an ambiguity error rather than a guess.
    /// Candidates are `(defining module, decl, comptime env, pattern-shape score)`; returns the
    /// index of the winner.
    pub(super) fn most_specific_overload(
        &mut self,
        name: &str,
        candidates: &[(String, FuncDecl, HashMap<String, ComptimeVal>, u32)],
    ) -> Result<usize, String> {
        if candidates.len() == 1 {
            return Ok(0);
        }
        let mut bounds: Vec<Vec<Vec<BoundAtom>>> = Vec::with_capacity(candidates.len());
        for (cand_mod, decl, env, _) in candidates {
            let mut per_param = Vec::new();
            for p in decl.params.iter().filter(|p| p.is_comptime) {
                per_param.push(self.bound_atoms(cand_mod, env, &p.ty));
            }
            bounds.push(per_param);
        }
        let beats = |a: usize, b: usize| -> bool {
            let (ba, bb) = (&bounds[a], &bounds[b]);
            if ba.len() != bb.len() {
                return candidates[a].3 > candidates[b].3;
            }
            let le = ba.iter().zip(bb).all(|(x, y)| bound_le(x, y));
            let strict = ba.iter().zip(bb).any(|(x, y)| !bound_le(y, x));
            le && (strict || candidates[a].3 > candidates[b].3)
        };
        let n = candidates.len();
        if let Some(w) = (0..n).find(|&w| (0..n).all(|o| o == w || beats(w, o))) {
            return Ok(w);
        }
        // Report two candidates that neither beats: the first non-dominated pair.
        let (a, b) = (0..n)
            .flat_map(|a| (0..n).map(move |b| (a, b)))
            .find(|&(a, b)| a < b && !beats(a, b) && !beats(b, a))
            .unwrap_or((0, 1));
        let sig = |d: &FuncDecl| {
            d.params
                .iter()
                .filter(|p| p.is_comptime)
                .map(|p| format!("comptime {}: {}", p.name, type_expr_label(&p.ty)))
                .collect::<Vec<_>>()
                .join(", ")
        };
        Err(format!(
            "Ambiguous call to overloaded '{name}': candidates '{name}({})' (module '{}') and '{name}({})' (module '{}') both match and neither constraint is more specific; qualify the call or make the constraints disjoint",
            sig(&candidates[a].1),
            candidates[a].0,
            sig(&candidates[b].1),
            candidates[b].0
        ))
    }

    /// The atoms of a comptime bound: meta-type constraints and traits. `type` has no atoms.
    fn bound_atoms(
        &mut self,
        mod_path: &str,
        env: &HashMap<String, ComptimeVal>,
        te: &TypeExpr,
    ) -> Vec<BoundAtom> {
        match te {
            TypeExpr::MetaType => Vec::new(),
            TypeExpr::BareOpaque => vec![BoundAtom::Constraint(TypeConstraint::Opaque)],
            TypeExpr::Constraint(TypeConstraint::AnyType) => Vec::new(),
            TypeExpr::Constraint(c) => vec![BoundAtom::Constraint(*c)],
            TypeExpr::TraitBounds(parts) => parts
                .iter()
                .flat_map(|p| self.bound_atoms(mod_path, env, p))
                .collect(),
            other => match self.resolve_type_expr(mod_path, None, env, other) {
                Ok(t) if self.traits.contains_key(&t) => vec![BoundAtom::Trait(t)],
                Ok(t) => vec![BoundAtom::Exact(t)],
                Err(_) => vec![BoundAtom::Opaque(format!("{other:?}"))],
            },
        }
    }

    pub(super) fn instantiate_specific_func_decl(
        &mut self,
        mod_path: &str,
        decl: &FuncDecl,
        comptime_args: &[ComptimeVal],
    ) -> Result<FuncId, String> {
        let specific_key = (
            mod_path.to_string(),
            format!("{}#{:?}", decl.name, decl.params),
            comptime_args.to_vec(),
        );
        if let Some(&id) = self.resolved_funcs.get(&specific_key) {
            return Ok(id);
        }
        let simple_key = (
            mod_path.to_string(),
            decl.name.clone(),
            comptime_args.to_vec(),
        );
        let mut env = HashMap::new();
        let mut ct_idx = 0;
        for p in &decl.params {
            if p.is_comptime {
                env.insert(p.name.clone(), comptime_args[ct_idx].clone());
                ct_idx += 1;
            }
        }
        let mut param_tys = Vec::new();
        for p in &decl.params {
            if !p.is_comptime {
                if matches!(p.ty, TypeExpr::Constraint(_) | TypeExpr::TraitBounds(_)) {
                    return Err(format!(
                        "Parameter '{}' of '{}' has a meta-type constraint by value; use '[T: ...]({}: T)' for static dispatch or '&Trait' for dynamic dispatch",
                        p.name, decl.name, p.name
                    ));
                }
                let pty = self.resolve_type_expr(mod_path, None, &env, &p.ty)?;
                if let Some(tr) = self.traits.get(&pty) {
                    return Err(format!(
                        "Trait '{}' is an unsized meta-type constraint and cannot be passed by value in parameter '{}' of '{}'; use '[T: {}]({}: T)' for static dispatch or '({}: &{})' for dynamic dispatch",
                        tr.name, p.name, decl.name, tr.name, p.name, p.name, tr.name
                    ));
                }
                if self.is_opaque_type(pty) {
                    return Err(format!(
                        "Unsized type '{}' cannot be passed by value in parameter '{}' of '{}'; use '*const {0}', '*mut {0}', '&{0}', or '&mut {0}'",
                        self.type_display_name(pty),
                        p.name,
                        decl.name
                    ));
                }
                env.insert(format!("__var_ty:{}", p.name), ComptimeVal::Type(pty));
                param_tys.push(pty);
            }
        }
        let export = if decl.name == "main" {
            Some("main".to_string())
        } else {
            None
        };
        if let TypeExpr::OpaqueTrait(bound_expr) = &decl.ret_ty {
            if decl.vis.is_export() {
                return Err(format!(
                    "Exported function '{}' cannot return existential 'opaque Trait'; 'export fn' requires a C-compatible return type",
                    decl.name
                ));
            }
            let void_ty = self.intern_type(Type::Void);
            let fn_id = self.reserve_function(decl.vis, export, &param_tys, void_ty);
            if decl.is_unsafe {
                self.unsafe_fns.insert(fn_id);
            }
            self.opaque_ret_funcs.insert(
                fn_id,
                OpaqueRetBound {
                    bound_mod: mod_path.to_string(),
                    owner_ty: None,
                    env: env.clone(),
                    bound_expr: (**bound_expr).clone(),
                },
            );
            self.resolved_funcs.insert(specific_key, fn_id);
            self.resolved_funcs.entry(simple_key).or_insert(fn_id);
            let pending = PendingFunc {
                func_id: fn_id,
                module_path: mod_path.to_string(),
                owner_ty: None,
                decl: decl.clone(),
                comptime_env: env,
                closure_captures: Vec::new(),
            };
            self.lower_function_body(pending)?;
            let (_, ret_ty) = self.func_sigs[&fn_id].clone();
            self.apply_func_borrow_contracts(fn_id, decl, &param_tys, ret_ty)?;
            return Ok(fn_id);
        }
        let ret_ty = self.resolve_type_expr(mod_path, None, &env, &decl.ret_ty)?;
        if let Some(tr) = self.traits.get(&ret_ty) {
            return Err(format!(
                "Trait '{}' is an unsized meta-type constraint and cannot be returned by value from '{}'",
                tr.name, decl.name
            ));
        }
        if self.is_opaque_type(ret_ty) {
            return Err(format!(
                "Unsized type '{}' cannot be returned by value from '{}'; use '*const {0}', '*mut {0}', '&{0}', or '&mut {0}'",
                self.type_display_name(ret_ty),
                decl.name
            ));
        }
        let fn_id = self.reserve_function(decl.vis, export, &param_tys, ret_ty);
        if decl.is_unsafe {
            self.unsafe_fns.insert(fn_id);
        }
        self.apply_func_borrow_contracts(fn_id, decl, &param_tys, ret_ty)?;
        if decl.vis.is_export() {
            self.setup_export_function(fn_id, decl.name.clone(), decl, &param_tys, ret_ty)?;
        }
        self.resolved_funcs.insert(specific_key, fn_id);
        self.resolved_funcs.entry(simple_key).or_insert(fn_id);
        self.pending_funcs.push(PendingFunc {
            func_id: fn_id,
            module_path: mod_path.to_string(),
            owner_ty: None,
            decl: decl.clone(),
            comptime_env: env,
            closure_captures: Vec::new(),
        });
        Ok(fn_id)
    }

    pub fn resolve_type_expr(
        &mut self,
        mod_path: &str,
        self_ty: Option<TypeId>,
        env: &HashMap<String, ComptimeVal>,
        ty_expr: &TypeExpr,
    ) -> Result<TypeId, String> {
        match ty_expr {
            TypeExpr::Void => Ok(self.intern_type(Type::Void)),
            TypeExpr::BareOpaque => Ok(self.intern_opaque_type()),
            TypeExpr::OpaqueDef { methods } => {
                self.instantiate_named_opaque(mod_path, "<anon_opaque>", env, None, methods)
            }
            TypeExpr::Distinct {
                underlying,
                methods,
            } => self.instantiate_distinct_type(
                mod_path,
                "<anon_distinct>",
                env,
                None,
                underlying,
                methods,
            ),
            TypeExpr::OpaqueTrait(_) => Err(
                "'opaque Trait' existential types are only permitted in function return types ('-> opaque Trait'); use '[T: Trait](x: T)' or '&Trait' for parameters"
                    .to_string(),
            ),
            TypeExpr::Never => Ok(self.intern_type(Type::Never)),
            TypeExpr::Bool => Ok(self.intern_type(Type::Bool)),
            TypeExpr::Rune => Ok(self.intern_type(Type::Rune)),
            TypeExpr::F32 => Ok(self.intern_type(Type::F32)),
            TypeExpr::F64 => Ok(self.intern_type(Type::F64)),
            TypeExpr::Isize => Ok(self.intern_type(Type::Int {
                signed: true,
                bits: 64,
            })),
            TypeExpr::Usize => Ok(self.intern_type(Type::Int {
                signed: false,
                bits: 64,
            })),
            TypeExpr::Int { signed, bits } => Ok(self.intern_type(Type::Int {
                signed: *signed,
                bits: *bits,
            })),
            TypeExpr::ComputedInt { signed, bits } => {
                let is_signed = match signed.as_ref() {
                    Expr::Path(p) if p.len() == 2 && p[0].is_empty() => match p[1].as_str() {
                        "signed" => true,
                        "unsigned" => false,
                        other => {
                            return Err(format!(
                                "Invalid signedness '.{other}' in '@Int'; expected '.signed' or '.unsigned' (or a comptime bool)"
                            ));
                        }
                    },
                    other => match self.eval_comptime_val(mod_path, self_ty, env, other)? {
                        ComptimeVal::Bool(b) => b,
                        _ => {
                            return Err(
                                "First argument of '@Int' must be '.signed', '.unsigned', or a comptime bool"
                                    .to_string(),
                            );
                        }
                    },
                };
                let bits_val = self.eval_comptime_int(mod_path, self_ty, env, bits)?;
                if !(1..=512).contains(&bits_val) {
                    return Err(format!(
                        "Bit width {bits_val} in '@Int' is outside the supported 1..=512 range"
                    ));
                }
                Ok(self.intern_type(Type::Int {
                    signed: is_signed,
                    bits: bits_val as u16,
                }))
            }
            TypeExpr::CInt(ck) => Ok(self.intern_c_int_type(*ck)),
            TypeExpr::MetaType | TypeExpr::Constraint(_) | TypeExpr::TraitBounds(_) => {
                Ok(self.intern_type(Type::MetaType))
            }
            TypeExpr::Trait(methods, kind, assoc) => {
                self.instantiate_trait(mod_path, "<anon_trait>", env, None, methods, *kind, assoc)
            }
            TypeExpr::SelfType => {
                self_ty.ok_or_else(|| "'Self' type used outside of a struct/record context".to_string())
            }
            TypeExpr::Ref { mutable, inner } => {
                if let TypeExpr::Constraint(c) = inner.as_ref() {
                    return Err(format!(
                        "Built-in meta-type constraint '{}' cannot be used as a dynamic trait object '&{}{}'",
                        c.name(),
                        if *mutable { "mut " } else { "" },
                        c.name()
                    ));
                }
                if matches!(inner.as_ref(), TypeExpr::MetaType) {
                    return Err("Meta-type 'type' cannot be used as a dynamic trait object".to_string());
                }
                if matches!(inner.as_ref(), TypeExpr::TraitBounds(_)) {
                    return Err(
                        "Multi-trait bounds ('A + B') are only valid on comptime type parameters; define a combined trait for dynamic dispatch"
                            .to_string(),
                    );
                }
                let pointee = self.resolve_type_expr(mod_path, self_ty, env, inner)?;
                if self.traits.contains_key(&pointee) {
                    return self.instantiate_trait_obj_type(pointee, *mutable);
                }
                Ok(self.intern_type(Type::Ptr {
                    mutable: *mutable,
                    pointee,
                }))
            }
            TypeExpr::Ptr {
                mutable,
                inner,
                kind,
            } => {
                let pointee = self.resolve_type_expr(mod_path, self_ty, env, inner)?;
                Ok(self.intern_kind_ptr_type(*kind, *mutable, pointee))
            }
            TypeExpr::Slice { mutable, elem } => {
                let elem_id = self.resolve_type_expr(mod_path, self_ty, env, elem)?;
                if self.is_opaque_type(elem_id) {
                    return Err(
                        "Unsized type 'opaque' has unknown element size and cannot form a slice '&[opaque]'"
                            .to_string(),
                    );
                }
                Ok(self.intern_slice_type(*mutable, elem_id))
            }
            TypeExpr::StrRef => Ok(self.intern_str_type()),
            TypeExpr::RelRef(_) | TypeExpr::RelSlice(_) | TypeExpr::RelStr => Err(
                "'&rel' relative references are only permitted in 'opaque' field declarations"
                    .to_string(),
            ),
            TypeExpr::Optional(inner) => {
                let inner_id = self.resolve_type_expr(mod_path, self_ty, env, inner)?;
                if self.is_opaque_type(inner_id) {
                    return Err(
                        "Unsized type 'opaque' cannot be stored by value in '?opaque'; use '?*const opaque', '?*mut opaque', '?&opaque', or '?&mut opaque'"
                            .to_string(),
                    );
                }
                let u8_id = self.intern_type(Type::Int {
                    signed: false,
                    bits: 8,
                });
                let void_id = self.intern_type(Type::Void);
                let opt_id = self.intern_type(Type::Union {
                    tag: u8_id,
                    variants: vec![void_id, inner_id],
                });
                self.ensure_union_destructor(opt_id);
                Ok(opt_id)
            }
            TypeExpr::Uninit(inner) => {
                let inner_id = self.resolve_type_expr(mod_path, self_ty, env, inner)?;
                self.intern_uninit_type(inner_id)
            }
            TypeExpr::ErrorSetUnion(terms) => {
                let mut acc = self.resolve_type_expr(mod_path, self_ty, env, &terms[0])?;
                for term in &terms[1..] {
                    let next = self.resolve_type_expr(mod_path, self_ty, env, term)?;
                    acc = self.combine_error_types(acc, next)?;
                }
                Ok(acc)
            }
            TypeExpr::Result { err, ok } => {
                let err_id = self.resolve_type_expr(mod_path, self_ty, env, err)?;
                let ok_id = self.resolve_type_expr(mod_path, self_ty, env, ok)?;
                if self.is_opaque_type(ok_id) {
                    return Err(
                        "Unsized type 'opaque' cannot be used by value in result type 'E!opaque'"
                            .to_string(),
                    );
                }
                self.instantiate_result_type(err_id, ok_id)
            }
            TypeExpr::Array { elem, len } => {
                let elem_id = self.resolve_type_expr(mod_path, self_ty, env, elem)?;
                if self.is_opaque_type(elem_id) {
                    return Err(
                        "Unsized type 'opaque' has unknown size and cannot be an array element '[opaque; N]'"
                            .to_string(),
                    );
                }
                let len_val = self.eval_comptime_int(mod_path, self_ty, env, len)?;
                Ok(self.intern_type(Type::Array {
                    elem: elem_id,
                    len: len_val as u64,
                }))
            }
            TypeExpr::Simd { elem, len } => {
                let elem_id = self.resolve_type_expr(mod_path, self_ty, env, elem)?;
                if self.is_opaque_type(elem_id) {
                    return Err(
                        "Unsized type 'opaque' cannot be a SIMD vector element".to_string(),
                    );
                }
                let len_val = self.eval_comptime_int(mod_path, self_ty, env, len)?;
                Ok(self.intern_type(Type::Simd {
                    elem: elem_id,
                    len: len_val as u64,
                }))
            }
            TypeExpr::Pattern { base, ranges } => {
                let base_id = self.resolve_type_expr(mod_path, self_ty, env, base)?;
                if self.is_opaque_type(base_id) {
                    return Err(
                        "Unsized type 'opaque' cannot be a pattern base type".to_string(),
                    );
                }
                let mut resolved_ranges = Vec::with_capacity(ranges.len());
                for (lo_e, hi_e) in ranges {
                    let lo = self.eval_pattern_bound(mod_path, self_ty, env, lo_e, base_id)?;
                    let hi = self.eval_pattern_bound(mod_path, self_ty, env, hi_e, base_id)?;
                    if lo > hi {
                        return Err(format!("Invalid pattern range {lo}..={hi}: lower > upper"));
                    }
                    resolved_ranges.push((lo, hi));
                }
                Ok(self.intern_type(Type::Pattern {
                    base: base_id,
                    ranges: resolved_ranges,
                }))
            }
            TypeExpr::Tuple(elems) => {
                let mut tys = Vec::with_capacity(elems.len());
                for e in elems {
                    let e_id = self.resolve_type_expr(mod_path, self_ty, env, e)?;
                    if self.is_opaque_type(e_id) {
                        return Err(
                            "Unsized type 'opaque' cannot be stored by value in a tuple"
                                .to_string(),
                        );
                    }
                    tys.push(e_id);
                }
                Ok(self.intern_type(Type::Struct(tys)))
            }
            TypeExpr::FnPtr {
                params,
                ret,
                borrows,
                is_unsafe,
            } => {
                let mut args = Vec::with_capacity(params.len());
                for p in params {
                    args.push(self.resolve_type_expr(mod_path, self_ty, env, p)?);
                }
                let ret_id = self.resolve_type_expr(mod_path, self_ty, env, ret)?;
                let contract = self.fn_type_contract(&args, ret_id, borrows.as_deref())?;
                Ok(self.intern_fn_ptr_type(args, ret_id, contract, *is_unsafe))
            }
            TypeExpr::CFnPtr {
                params,
                ret,
                is_unsafe,
            } => {
                let mut args = Vec::with_capacity(params.len());
                for p in params {
                    let arg = self.resolve_type_expr(mod_path, self_ty, env, p)?;
                    self.reject_owned_across_ffi(arg, "a parameter of an 'extern fn' pointer type")?;
                    args.push(arg);
                }
                let ret_id = self.resolve_type_expr(mod_path, self_ty, env, ret)?;
                self.reject_owned_across_ffi(ret_id, "the return type of an 'extern fn' pointer type")?;
                Ok(self.intern_c_fn_ptr_type(args, ret_id, *is_unsafe))
            }
            TypeExpr::Enum { backing, variants } => self.instantiate_enum(
                mod_path,
                self_ty,
                env,
                "<anon_enum>",
                backing.as_deref(),
                variants,
            ),
            TypeExpr::Union { backing, variants } => self.instantiate_union(
                mod_path,
                "<anon_union>",
                env,
                None,
                backing.as_deref(),
                variants,
            ),
            TypeExpr::Overlay(fields) => {
                let mut key = Vec::with_capacity(fields.len());
                for (fname, f_expr) in fields {
                    key.push((fname.clone(), self.resolve_type_expr(mod_path, None, env, f_expr)?));
                }
                let key = (true, false, key);
                if let Some(&t) = self.memoized_anon_records.get(&key) {
                    return Ok(t);
                }
                let t = self.instantiate_overlay(mod_path, "<anon_overlay>", env, None, fields)?;
                self.memoized_anon_records.insert(key, t);
                Ok(t)
            }
            TypeExpr::Error {
                backing,
                ok_flag,
                variants,
            } => self.instantiate_error(
                mod_path,
                "<anon_error>",
                env,
                None,
                backing.as_deref(),
                ok_flag.as_ref(),
                variants,
            ),
            TypeExpr::Struct {
                is_packed,
                fields,
                methods,
            } => self.resolve_anon_struct(mod_path, env, *is_packed, fields, methods),
            TypeExpr::Opaque(body) => {
                self.instantiate_opaque_body(mod_path, "<anon_opaque>", env, None, body)
            }
            TypeExpr::Map { key, val } => {
                let key_ty = self.resolve_type_expr(mod_path, self_ty, env, key)?;
                let val_ty = self.resolve_type_expr(mod_path, self_ty, env, val)?;
                Ok(self.intern_map_type(key_ty, val_ty))
            }
            TypeExpr::BackingType(inner) => {
                self.resolve_backing_type(mod_path, self_ty, env, inner)
            }
            TypeExpr::SynthesizedStruct { is_packed, fields } => {
                self.instantiate_synthesized_struct(mod_path, self_ty, env, *is_packed, fields)
            }
            TypeExpr::SynthesizedTuple(elems) => {
                self.instantiate_synthesized_tuple(mod_path, self_ty, env, elems)
            }
            TypeExpr::SynthesizedEnum { backing, variants } => {
                self.instantiate_synthesized_enum(mod_path, self_ty, env, backing, variants)
            }
            TypeExpr::SynthesizedUnion { backing, variants } => self
                .instantiate_synthesized_union(
                    mod_path,
                    self_ty,
                    env,
                    backing.as_deref(),
                    variants,
                ),
            TypeExpr::SynthesizedError(variants) => {
                self.instantiate_synthesized_error(mod_path, self_ty, env, variants)
            }
            TypeExpr::Named(path) => self.resolve_type_path(mod_path, self_ty, env, path),
            TypeExpr::TypeCall { path, args } => {
                self.resolve_type_call(mod_path, self_ty, env, path, args)
            }
        }
    }

    /// `@backing_type(T)`: the integer storing an enum, a union or error tag, a packed struct, or a
    /// pattern type.
    fn resolve_backing_type(
        &mut self,
        mod_path: &str,
        self_ty: Option<TypeId>,
        env: &HashMap<String, ComptimeVal>,
        inner: &TypeExpr,
    ) -> Result<TypeId, String> {
        let t_id = self.resolve_type_expr(mod_path, self_ty, env, inner)?;
        if self.enums.contains_key(&t_id)
            && let Type::Int { signed, bits } = self.program.types[t_id.0 as usize]
        {
            return Ok(self.intern_type(Type::Int { signed, bits }));
        }
        if self.unions.contains_key(&t_id)
            && let Type::Union { tag, .. } = self.program.types[t_id.0 as usize]
        {
            return Ok(tag);
        }
        if let Some(einfo) = self.errors.get(&t_id) {
            if let Some(c_b) = einfo.c_backing {
                return Ok(c_b);
            }
            if let Type::Union { tag, .. } = self.program.types[t_id.0 as usize] {
                return Ok(tag);
            }
        }
        if let Some(comp) = self.composites.get(&t_id)
            && comp.is_packed
        {
            if comp.is_opaque && self_ty != Some(t_id) {
                return Err(format!(
                    "Cannot inspect backing type of opaque type '{}'; 'opaque' types encapsulate their representation",
                    self.type_display_name(t_id)
                ));
            }
            return Ok(self.intern_type(Type::Int {
                signed: false,
                bits: comp.total_bits,
            }));
        }
        if let Type::Pattern { base, .. } = self.program.types[t_id.0 as usize] {
            return Ok(base);
        }
        if let Some(nt) = self.distinct_types.get(&t_id) {
            return Ok(nt.underlying);
        }
        Err(format!(
            "'@backing_type' expects an 'enum', 'union', 'error', 'distinct', 'packed struct', or pattern type, found '{}'",
            self.type_display_name(t_id)
        ))
    }

    /// `list[i]` / `map[k]` in type position: a type held by a comptime list or map.
    fn resolve_type_index(
        &mut self,
        mod_path: &str,
        self_ty: Option<TypeId>,
        env: &HashMap<String, ComptimeVal>,
        path: &[String],
        index: &Expr,
    ) -> Result<TypeId, String> {
        if let Some(mut cur) = env.get(&path[0]).cloned() {
            let mut ok = true;
            for seg in &path[1..] {
                let next_opt = match &cur {
                    ComptimeVal::Record(fields) => fields
                        .iter()
                        .find(|(k, _)| k == seg)
                        .map(|(_, v)| v.clone()),
                    _ => None,
                };
                if let Some(v) = next_opt {
                    cur = v;
                } else {
                    ok = false;
                    break;
                }
            }
            if ok && let ComptimeVal::List(items, _) = cur {
                let idx = self.eval_comptime_int(mod_path, self_ty, env, index)?;
                if idx < 0 || (idx as usize) >= items.len() {
                    return Err(format!(
                        "Index {} out of bounds for comptime list '{}' of length {}",
                        idx,
                        path.join("."),
                        items.len()
                    ));
                }
                if let ComptimeVal::Type(t_id) = items[idx as usize] {
                    return Ok(t_id);
                }
                return Err(format!(
                    "Element {} of '{}' does not hold a type",
                    idx,
                    path.join(".")
                ));
            }
        }
        let expanded = self.expand_module_path(env, path);
        let Some(map_id) =
            self.resolve_map_expr(mod_path, self_ty, env, &Expr::Path(expanded.clone()))?
        else {
            return Err(format!("'{}' is not a comptime map", expanded.join("::")));
        };
        let map_inst = self.map_instances[map_id as usize].clone();
        let map_info = self.maps[&map_inst.map_ty];
        let (mkey, _, _) =
            self.eval_map_key(mod_path, self_ty, env, index, Some(map_info.key_ty))?;
        let Some(entry) = map_inst.entries.iter().find(|e| e.key == mkey) else {
            return Err(format!(
                "Key {:?} not found in comptime map '{}'",
                mkey,
                expanded.join("::")
            ));
        };
        let ComptimeVal::Type(t_id) = entry.val_comptime else {
            return Err(format!(
                "Map '{}' entry used in type position does not hold a type",
                expanded.join("::")
            ));
        };
        Ok(t_id)
    }

    /// A named type: a comptime type binding (or a field of a comptime record), `Union::Tag`,
    /// a declared type, or a constant holding a type.
    /// The associated type `name` of `owner`: its own compile-time field (public, or seen from
    /// inside it), else what an impl gives it. An associated value that is not a type is an error.
    pub(super) fn assoc_type(
        &mut self,
        owner: TypeId,
        name: &str,
        self_ty: Option<TypeId>,
    ) -> Result<Option<TypeId>, String> {
        let own = self.composites.get(&owner).is_some_and(|c| c.consts.contains_key(name));
        let val = if own {
            let (_, _, val, vis, _) = self.resolve_associated_const(owner, name)?;
            if vis == Visibility::Private && self_ty != Some(owner) {
                return Err(format!(
                    "'{}::{name}' is private to '{}'",
                    self.type_display_name(owner),
                    self.type_display_name(owner)
                ));
            }
            val
        } else if let Some((_, _, val)) = self.impl_assoc_const(owner, name)? {
            val
        } else {
            return Ok(None);
        };
        match val {
            ComptimeVal::Type(t) => Ok(Some(t)),
            other => Err(format!(
                "'{}::{name}' is {other:?}, not a type",
                self.type_display_name(owner)
            )),
        }
    }

    pub(super) fn resolve_type_path(
        &mut self,
        mod_path: &str,
        self_ty: Option<TypeId>,
        env: &HashMap<String, ComptimeVal>,
        path: &[String],
    ) -> Result<TypeId, String> {
        if path.len() == 1
            && let Some(ComptimeVal::Type(t_id)) = env.get(&path[0])
        {
            return Ok(*t_id);
        }
        if path.len() >= 2
            && let Some(mut cur) = env.get(&path[0]).cloned()
        {
            let mut ok = true;
            for seg in &path[1..] {
                let next_opt = match &cur {
                    ComptimeVal::Record(fields) => fields
                        .iter()
                        .find(|(k, _)| k == seg)
                        .map(|(_, v)| v.clone()),
                    ComptimeVal::Type(u_id)
                        if seg == "Tag"
                            && (self.unions.contains_key(u_id)
                                || self.errors.contains_key(u_id)) =>
                    {
                        Some(ComptimeVal::Type(self.union_tag_enum(*u_id)))
                    }
                    _ => None,
                };
                if let Some(v) = next_opt {
                    cur = v;
                } else {
                    ok = false;
                    break;
                }
            }
            if ok && let ComptimeVal::Type(t_id) = cur {
                return Ok(t_id);
            }
        }
        // `Union::Tag` / `Error::Tag`: the union or error's tag enum.
        if path.len() >= 2
            && path.last().map(String::as_str) == Some("Tag")
            && let Ok(owner) = self.resolve_type_expr(
                mod_path,
                self_ty,
                env,
                &TypeExpr::Named(path[..path.len() - 1].to_vec()),
            )
            && (self.unions.contains_key(&owner) || self.errors.contains_key(&owner))
        {
            return Ok(self.union_tag_enum(owner));
        }
        // `Self::Handle`, `A::Handle`, `Slots[T, N]::Handle`: a type's associated type, its own
        // compile-time field or what an impl of a trait gives it.
        if path.len() == 2
            && path[0] == "Self"
            && let Some(ComptimeVal::Type(t)) = env.get(&path[1])
        {
            return Ok(*t);
        }
        if path.len() >= 2 {
            let prefix = &path[..path.len() - 1];
            let owner = if prefix.len() == 1 && prefix[0] == "Self" {
                self_ty
            } else {
                self.resolve_type_expr(mod_path, self_ty, env, &TypeExpr::Named(prefix.to_vec())).ok()
            };
            if let Some(owner) = owner {
                if let Some(t) = self.assoc_type(owner, path.last().unwrap(), self_ty)? {
                    return Ok(t);
                }
                return Err(format!(
                    "Type '{}' has no associated type '{}'",
                    self.type_display_name(owner),
                    path.last().unwrap()
                ));
            }
        }
        let expanded = self.expand_module_path(env, path);
        match self.resolve_path(mod_path, &expanded)? {
            ResolvedItem::Type(tmod, tname) => self.resolve_named_type(&tmod, &tname),
            ResolvedItem::Const(cmod, cname) => {
                let (_, _, cv, _) = self.resolve_top_const(&cmod, &cname)?;
                if let ComptimeVal::Type(t_id) = cv {
                    Ok(t_id)
                } else {
                    Err(format!(
                        "Constant '{}::{}' does not evaluate to a type",
                        cmod, cname
                    ))
                }
            }
            other => Err(format!(
                "Expected type for path '{}', found {other:?}",
                expanded.join("::")
            )),
        }
    }

    /// `F(args)` in type position: a call of a comptime type function.
    fn resolve_type_call(
        &mut self,
        mod_path: &str,
        self_ty: Option<TypeId>,
        env: &HashMap<String, ComptimeVal>,
        path: &[String],
        args: &[Expr],
    ) -> Result<TypeId, String> {
        let expanded = self.expand_module_path(env, path);
        let resolved = self.resolve_path(mod_path, &expanded);
        // `ts[i]` / `MAP[key]`: an element of a comptime list or map of types.
        if let [index] = args
            && (env
                .get(&path[0])
                .is_some_and(|v| !matches!(v, ComptimeVal::Module(_)))
                || matches!(&resolved, Ok(r) if !matches!(r, ResolvedItem::Func(..))))
        {
            return self.resolve_type_index(mod_path, self_ty, env, path, index);
        }
        let ResolvedItem::Func(fmod, fname) = resolved?
        else {
            return Err(format!(
                "'{}' is not a comptime type function",
                expanded.join("::")
            ));
        };
        let mut given = Vec::with_capacity(args.len());
        for arg in args {
            given.push(if Self::is_placeholder(arg) {
                None
            } else {
                Some(self.eval_comptime_val(mod_path, self_ty, env, arg)?)
            });
        }
        let ct_args = self.complete_comptime_args_of(&fmod, &fname, &given)?;
        self.eval_comptime_type_func(&fmod, &fname, &ct_args)
    }

    /// An anonymous `struct { ... }` type expression.
    fn resolve_anon_struct(
        &mut self,
        mod_path: &str,
        env: &HashMap<String, ComptimeVal>,
        is_packed: bool,
        fields: &[FieldDecl],
        methods: &[FuncDecl],
    ) -> Result<TypeId, String> {
        // Anonymous structs are structural data: the same ordered `(name, type)` fields give
        // the same type. Behaviour and defaults belong to a named (nominal) struct.
        if let Some(m) = methods.first() {
            return Err(format!(
                "Anonymous struct cannot declare method '{}': an anonymous struct is structural data; declare a named struct ('struct Name {{ ... }}' or 'type Name = struct {{ ... }}') to give it methods",
                m.name
            ));
        }
        if let Some(f) = fields.iter().find(|f| f.default_val.is_some()) {
            return Err(format!(
                "Anonymous struct cannot give field '{}' a default value: an anonymous struct is structural data; declare a named struct ('struct Name {{ ... }}' or 'type Name = struct {{ ... }}') to give its fields defaults",
                f.name
            ));
        }
        let mut tys = Vec::with_capacity(fields.len());
        for f in fields {
            let f_ty = self.resolve_type_expr(mod_path, None, env, &f.ty)?;
            tys.push((f.name.clone(), f_ty));
        }
        let key = (false, is_packed, tys);
        if let Some(&t) = self.memoized_anon_records.get(&key) {
            return Ok(t);
        }
        let t = self.instantiate_composite(
            mod_path,
            "<anon_struct>",
            false,
            is_packed,
            OpaqueOwnership::Copy,
            ThreadDecl::default(),
            env,
            None,
            fields,
            &[],
            &[],
            &[],
            None,
            &[],
            &[],
            None,
            DeclaredContents::default(),
        )?;
        let label = self.structural_struct_label(is_packed, &key.2);
        if let Some(comp) = self.composites.get_mut(&t) {
            std::sync::Arc::make_mut(comp).name = label.clone();
        }
        self.program.type_names.retain(|(id, _)| *id != t);
        self.program.type_names.push((t, label));
        self.memoized_anon_records.insert(key, t);
        Ok(t)
    }

    /// Instantiates an `opaque { ... }` body as the composite `name` (memoized under
    /// `memo_key` when it is the result of a type function).
    pub(super) fn instantiate_opaque_body(
        &mut self,
        mod_path: &str,
        name: &str,
        env: &HashMap<String, ComptimeVal>,
        memo_key: Option<(String, String, Vec<ComptimeVal>)>,
        body: &OpaqueBody,
    ) -> Result<TypeId, String> {
        let OpaqueBody {
            is_packed,
            ownership,
            threads,
            owns,
            borrows,
            fields,
            consts,
            statics,
            methods,
            default_hook,
            clone_hooks,
            drop_hooks,
            format_hook,
        } = body;
        let (ownership, declared) = self.declared_contents(
            name,
            *ownership,
            owns,
            borrows,
            env,
            fields,
            !drop_hooks.is_empty(),
        )?;
        self.instantiate_composite(
            mod_path,
            name,
            true,
            *is_packed,
            ownership,
            *threads,
            env,
            memo_key,
            fields,
            consts,
            statics,
            methods,
            default_hook.clone(),
            clone_hooks,
            drop_hooks,
            format_hook.clone(),
            declared,
        )
    }

    fn instantiate_synthesized_struct(
        &mut self,
        mod_path: &str,
        self_ty: Option<TypeId>,
        env: &HashMap<String, ComptimeVal>,
        is_packed: bool,
        fields_expr: &Expr,
    ) -> Result<TypeId, String> {
        let intrinsic_name = if is_packed { "@PackedStruct" } else { "@Struct" };
        let val = self.eval_comptime_val(mod_path, self_ty, env, fields_expr)?;
        let ComptimeVal::List(items, _) = val else {
            return Err(format!(
                "'{intrinsic_name}' expects a comptime slice of FieldSpec ('&[FieldSpec]')"
            ));
        };
        let mut spec_key: Vec<(String, TypeId)> = Vec::with_capacity(items.len());
        for item in items {
            let (fname, fty) = match item {
                ComptimeVal::Record(entries) => {
                    let Some((_, ComptimeVal::Str(n))) =
                        entries.iter().find(|(k, _)| k == "name")
                    else {
                        return Err(format!(
                            "'{intrinsic_name}' field descriptor is missing string field 'name'"
                        ));
                    };
                    let Some((_, ComptimeVal::Type(t))) = entries.iter().find(|(k, _)| k == "ty")
                    else {
                        return Err(format!(
                            "'{intrinsic_name}' field descriptor '{}' is missing type field 'ty'",
                            n
                        ));
                    };
                    (n.clone(), *t)
                }
                ComptimeVal::Tuple(elems) if elems.len() == 2 => {
                    let (ComptimeVal::Str(n), ComptimeVal::Type(t)) = (&elems[0], &elems[1]) else {
                        return Err(format!(
                            "'{intrinsic_name}' tuple descriptor must be '(&str, type)'"
                        ));
                    };
                    (n.clone(), *t)
                }
                _ => {
                    return Err(format!(
                        "'{intrinsic_name}' expects FieldSpec records with 'name: &str' and 'ty: type'"
                    ));
                }
            };
            if spec_key.iter().any(|(n, _)| n == &fname) {
                return Err(format!("Duplicate field '{fname}' in '{intrinsic_name}'"));
            }
            if let Some(tr) = self.traits.get(&fty) {
                return Err(format!(
                    "Trait '{}' is an unsized meta-type constraint and cannot be stored by value in field '{}' of '{}'",
                    tr.name, fname, intrinsic_name
                ));
            }
            if self.is_opaque_type(fty) {
                return Err(format!(
                    "Unsized type 'opaque' cannot be stored by value in field '{}' of '{}'",
                    fname, intrinsic_name
                ));
            }
            spec_key.push((fname, fty));
        }

        self.structural_struct(mod_path, is_packed, spec_key, intrinsic_name)
    }


    /// The structural anonymous struct with `fields` (packed when `is_packed`): every anonymous
    /// struct without methods or field defaults that has the same ordered fields is this one
    /// type, however it is written (`struct { ... }`, `@Struct`, `@entries` records). `what`
    /// names the construct in errors.
    pub(super) fn structural_struct(
        &mut self,
        def_module: &str,
        is_packed: bool,
        fields: Vec<(String, TypeId)>,
        what: &str,
    ) -> Result<TypeId, String> {
        let key = (false, is_packed, fields.clone());
        if let Some(&t) = self.memoized_anon_records.get(&key) {
            return Ok(t);
        }
        let mut field_tys = Vec::with_capacity(fields.len());
        let mut field_infos = Vec::with_capacity(fields.len());
        let mut packed_offsets = Vec::new();
        let mut total_bits = 0u16;
        for (fname, fty) in &fields {
            if is_packed {
                let Some((f_bits, _)) = self.packed_field_bit_width(*fty) else {
                    return Err(format!(
                        "Field '{fname}' of '{what}' has non-packable type '{}'; packed fields must be integers (i1..i512, u1..u512), bool, enum, or nested packed types",
                        self.type_display_name(*fty)
                    ));
                };
                packed_offsets.push((total_bits, f_bits));
                total_bits = total_bits.saturating_add(f_bits);
            }
            field_tys.push(*fty);
            field_infos.push((fname.clone(), *fty, Visibility::Pub, None));
        }
        if is_packed && (total_bits == 0 || total_bits > 512) {
            return Err(format!(
                "'{what}' has total bit width {total_bits} which is outside the supported 1..=512 bit range"
            ));
        }

        let ty_id = if is_packed {
            self.alloc_distinct_type(Type::Int {
                signed: false,
                bits: total_bits,
            })
        } else {
            self.alloc_distinct_type(Type::Struct(field_tys))
        };
        let label = self.structural_struct_label(is_packed, &fields);
        let info = CompositeInfo {
            name: label.clone(),
            is_opaque: false,
            is_packed,
            total_bits,
            packed_offsets,
            ownership: OpaqueOwnership::Copy,
            threads: ThreadDecl::default(),
            cell_fields: Vec::new(),
            has_format_hook: false,
            def_module: def_module.to_string(),
            comptime_env: HashMap::new(),
            fields: field_infos,
            rel_fields: HashMap::new(),
            consts: HashMap::new(),
            statics: HashMap::new(),
            methods: std::sync::Arc::new(HashMap::new()),
            method_fn_ids: HashMap::new(),
            default_fn: None,
            clone_fn: None,
            drop_fn: None,
            format_fn: None,
            declared: DeclaredContents::default(),
            may_dangle: Vec::new(),
        };
        let names = info.fields.iter().map(|f| f.0.clone()).collect();
        self.composites.insert(ty_id, std::sync::Arc::new(info));
        self.program.type_names.push((ty_id, label));
        self.program.field_names.push((ty_id, names));
        self.memoized_anon_records.insert(key, ty_id);
        Ok(ty_id)
    }

    /// The display name of a structural anonymous struct: `struct { x: i32, y: f64 }`.
    fn structural_struct_label(&self, is_packed: bool, fields: &[(String, TypeId)]) -> String {
        let fields: Vec<String> = fields
            .iter()
            .map(|(n, t)| format!("{n}: {}", self.type_display_name(*t)))
            .collect();
        let packed = if is_packed { "packed " } else { "" };
        format!("{packed}struct {{ {} }}", fields.join(", "))
    }

    fn instantiate_synthesized_tuple(
        &mut self,
        mod_path: &str,
        self_ty: Option<TypeId>,
        env: &HashMap<String, ComptimeVal>,
        elems_expr: &Expr,
    ) -> Result<TypeId, String> {
        let val = self.eval_comptime_val(mod_path, self_ty, env, elems_expr)?;
        let ComptimeVal::List(items, _) = val else {
            return Err("'@Tuple' expects a comptime slice of types ('&[type]')".to_string());
        };
        let mut tys = Vec::with_capacity(items.len());
        for item in items {
            let ComptimeVal::Type(t_id) = item else {
                return Err("'@Tuple' elements must be types ('type')".to_string());
            };
            if self.is_opaque_type(t_id) {
                return Err(
                    "Unsized type 'opaque' cannot be stored by value in '@Tuple'".to_string(),
                );
            }
            tys.push(t_id);
        }
        Ok(self.intern_type(Type::Struct(tys)))
    }

    fn instantiate_synthesized_enum(
        &mut self,
        mod_path: &str,
        self_ty: Option<TypeId>,
        env: &HashMap<String, ComptimeVal>,
        backing_expr: &TypeExpr,
        variants_expr: &Expr,
    ) -> Result<TypeId, String> {
        let b_ty = self.resolve_type_expr(mod_path, self_ty, env, backing_expr)?;
        if self.enums.contains_key(&b_ty)
            || self.composites.contains_key(&b_ty)
            || self.distinct_types.contains_key(&b_ty)
        {
            return Err(format!(
                "'@Enum' backing type must be a primitive integer type (e.g. 'u8', 'u3', 'i16'), found '{}'",
                self.type_display_name(b_ty)
            ));
        }
        let Type::Int { signed, bits } = self.program.types[b_ty.0 as usize] else {
            return Err(format!(
                "'@Enum' backing type must be a primitive integer type (e.g. 'u8', 'u3', 'i16'), found '{}'",
                self.type_display_name(b_ty)
            ));
        };
        let val = self.eval_comptime_val(mod_path, self_ty, env, variants_expr)?;
        let ComptimeVal::List(items, _) = val else {
            return Err("'@Enum' expects a comptime slice of EnumSpec ('&[EnumSpec]')".to_string());
        };
        let mut resolved: Vec<(String, i128)> = Vec::with_capacity(items.len());
        for item in items {
            let (vname, disc) = match item {
                ComptimeVal::Record(entries) => {
                    let Some((_, ComptimeVal::Str(n))) =
                        entries.iter().find(|(k, _)| k == "name")
                    else {
                        return Err(
                            "'@Enum' variant descriptor is missing string field 'name'".to_string()
                        );
                    };
                    let Some((_, ComptimeVal::Int(v))) =
                        entries.iter().find(|(k, _)| k == "value")
                    else {
                        return Err(format!(
                            "'@Enum' variant descriptor '{n}' is missing integer field 'value'"
                        ));
                    };
                    (n.clone(), *v)
                }
                ComptimeVal::Tuple(elems) if elems.len() == 2 => {
                    let (ComptimeVal::Str(n), ComptimeVal::Int(v)) = (&elems[0], &elems[1]) else {
                        return Err("'@Enum' tuple descriptor must be '(&str, i64)'".to_string());
                    };
                    (n.clone(), *v)
                }
                _ => {
                    return Err(
                        "'@Enum' expects EnumSpec records with 'name: &str' and 'value: i64'"
                            .to_string(),
                    );
                }
            };
            if resolved.iter().any(|(n, _)| n == &vname) {
                return Err(format!("Duplicate variant '{vname}' in '@Enum'"));
            }
            if let Some(range) = int_range_violation(disc, bits, signed) {
                return Err(format!(
                    "'@Enum' variant '{vname}' discriminant {disc} does not fit in backing integer type {range}"
                ));
            }
            resolved.push((vname, disc));
        }

        if let Some(&existing) = self.synthesized_enums.get(&(b_ty, resolved.clone())) {
            return Ok(existing);
        }
        let ty_id = self.alloc_distinct_type(Type::Int { signed, bits });
        let label = format!("@Enum({})", self.type_display_name(b_ty));
        self.enums.insert(ty_id, (label, resolved.clone()));
        self.synthesized_enums.insert((b_ty, resolved), ty_id);
        Ok(ty_id)
    }

    fn instantiate_synthesized_union(
        &mut self,
        mod_path: &str,
        self_ty: Option<TypeId>,
        env: &HashMap<String, ComptimeVal>,
        backing_expr: Option<&TypeExpr>,
        variants_expr: &Expr,
    ) -> Result<TypeId, String> {
        let opt_backing: Option<TypeId> = match backing_expr {
            None => None,
            Some(TypeExpr::Void) => None,
            Some(TypeExpr::Named(p))
                if p.len() == 1 && (p[0] == "null" || p[0] == "void" || p[0] == "none") =>
            {
                if let Some(ComptimeVal::Type(t_id)) = env.get(&p[0]) {
                    if matches!(self.program.types[t_id.0 as usize], Type::Void) {
                        None
                    } else {
                        Some(*t_id)
                    }
                } else {
                    None
                }
            }
            Some(te) => {
                let t = self.resolve_type_expr(mod_path, self_ty, env, te)?;
                if matches!(self.program.types[t.0 as usize], Type::Void) {
                    None
                } else {
                    Some(t)
                }
            }
        };

        let val = self.eval_comptime_val(mod_path, self_ty, env, variants_expr)?;
        let ComptimeVal::List(items, _) = val else {
            return Err(
                "'@Union' expects a comptime slice of UnionSpec ('&[UnionSpec]')".to_string(),
            );
        };
        let resolved_variants = self.variant_specs(items, "Union")?;

        if let Some(&existing) = self
            .synthesized_unions
            .get(&(opt_backing, resolved_variants.clone()))
        {
            return Ok(existing);
        }

        if let Some(b_ty) = opt_backing
            && (self.enums.contains_key(&b_ty)
                || self.composites.contains_key(&b_ty)
                || self.distinct_types.contains_key(&b_ty)
                || !matches!(self.program.types[b_ty.0 as usize], Type::Int { .. }))
        {
            return Err(format!(
                "'@Union' backing type '{}' must be an integer type (or 'null')",
                self.type_display_name(b_ty)
            ));
        }
        let variants_with_vals = resolved_variants
            .iter()
            .map(|(n, p)| (n.clone(), *p, None))
            .collect();
        let ty_id = self.register_union(
            None,
            "<synthesized_union>",
            "'@Union'",
            opt_backing,
            variants_with_vals,
        )?;
        self.synthesized_unions
            .insert((opt_backing, resolved_variants), ty_id);
        Ok(ty_id)
    }

    fn instantiate_synthesized_error(
        &mut self,
        mod_path: &str,
        self_ty: Option<TypeId>,
        env: &HashMap<String, ComptimeVal>,
        variants_expr: &Expr,
    ) -> Result<TypeId, String> {
        let val = self.eval_comptime_val(mod_path, self_ty, env, variants_expr)?;
        let ComptimeVal::List(items, _) = val else {
            return Err(
                "'@Error' expects a comptime slice of ErrorSpec ('&[ErrorSpec]')".to_string(),
            );
        };
        let spec_key = self.variant_specs(items, "Error")?;
        let mut leaves: Vec<ErrorLeafInfo> = Vec::with_capacity(spec_key.len());
        for (vname, payload_ty) in &spec_key {
            if self.is_linear_type(*payload_ty) {
                return Err(format!(
                    "'@Error' variant '{vname}' cannot carry a linear payload"
                ));
            }
            leaves.push(ErrorLeafInfo {
                key: ErrorLeafKey {
                    def_module: mod_path.to_string(),
                    error_name: "<synthesized_error>".to_string(),
                    variant_name: vname.clone(),
                },
                payload_ty: *payload_ty,
            });
        }
        if let Some(&existing) = self.synthesized_errors.get(&spec_key) {
            return Ok(existing);
        }
        let (leaves, decl_order) = sort_error_leaves(leaves);
        let has_payloads = leaves
            .iter()
            .any(|l| !matches!(self.program.types[l.payload_ty.0 as usize], Type::Void));
        let tag_ty = self.intern_type(Type::Int {
            signed: false,
            bits: 32,
        });
        let ty_id = self.register_error(
            ErrorTypeInfo {
                name: "<synthesized_error>".to_string(),
                leaves,
                decl_order,
                has_payloads,
                has_embedded: false,
                c_backing: None,
                ok_flag: ("Ok".to_string(), 0),
            },
            tag_ty,
        );
        self.synthesized_errors.insert(spec_key, ty_id);
        Ok(ty_id)
    }
}

/// Error leaves in declaration order, as `(leaves sorted by key, declaration order)`: the
/// sorted order fixes tag numbering, the declaration order is what users see.
fn sort_error_leaves(mut leaves: Vec<ErrorLeafInfo>) -> (Vec<ErrorLeafInfo>, Vec<ErrorLeafKey>) {
    let decl_order = leaves.iter().map(|l| l.key.clone()).collect();
    leaves.sort_by(|a, b| a.key.cmp(&b.key));
    (leaves, decl_order)
}

/// One conjunct of a comptime bound, for overload subsumption.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) enum BoundAtom {
    Constraint(TypeConstraint),
    Trait(TypeId),
    Exact(TypeId),
    /// A bound that could not be resolved independently; only equal to itself.
    Opaque(String),
}

/// The parent of a structural meta-type constraint in the kind tree (`None` below `type` or for
/// cross-cutting properties such as `send`, `copy`, `format`).
fn constraint_parent(c: TypeConstraint) -> Option<TypeConstraint> {
    use TypeConstraint as C;
    match c {
        C::Number => Some(C::Scalar),
        C::Integer | C::Float => Some(C::Number),
        C::Signed | C::Unsigned => Some(C::Integer),
        C::FnPtr | C::Closure => Some(C::Callable),
        C::Array | C::Slice => Some(C::Sequence),
        C::Struct | C::Tuple => Some(C::Aggregate),
        C::Enum | C::Union | C::Error => Some(C::Discriminated),
        _ => None,
    }
}

fn atom_le(a: &BoundAtom, b: &BoundAtom) -> bool {
    match (a, b) {
        (BoundAtom::Constraint(x), BoundAtom::Constraint(y)) => {
            let mut cur = Some(*x);
            while let Some(c) = cur {
                if c == *y {
                    return true;
                }
                cur = constraint_parent(c);
            }
            false
        }
        _ => a == b,
    }
}

/// Bound `a` is at least as specific as `b`: every requirement of `b` is implied by one of `a`'s.
fn bound_le(a: &[BoundAtom], b: &[BoundAtom]) -> bool {
    b.iter().all(|y| a.iter().any(|x| atom_le(x, y)))
}

/// Short source-like rendering of a bound for diagnostics.
fn type_expr_label(te: &TypeExpr) -> String {
    match te {
        TypeExpr::MetaType => "type".to_string(),
        TypeExpr::BareOpaque => "opaque".to_string(),
        TypeExpr::Constraint(c) => c.name().to_string(),
        TypeExpr::Named(path) => path.join("::"),
        TypeExpr::TraitBounds(parts) => parts
            .iter()
            .map(type_expr_label)
            .collect::<Vec<_>>()
            .join(" + "),
        other => format!("{other:?}"),
    }
}

/// `None` if `v` fits a `bits`-wide integer, else the type and its range for a diagnostic
/// (`'u8' (0..=255)`).
pub(super) fn int_range_violation(v: i128, bits: u16, signed: bool) -> Option<String> {
    if Wide::from_i128(v).fits(bits, signed) {
        return None;
    }
    let prefix = if signed { 'i' } else { 'u' };
    let (min, max) = (Wide::min_value(bits, signed), Wide::max_value(bits, signed));
    Some(format!("'{prefix}{bits}' ({min}..={max})"))
}
