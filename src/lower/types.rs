use super::*;

impl Compiler {
    pub(super) fn is_linear_type(&self, ty_id: TypeId) -> bool {
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
        if self.is_opaque_type(ty_id) || self.is_linear_type(ty_id) {
            return false;
        }
        if self.program.destructors.iter().any(|(t, _)| *t == ty_id) {
            return false;
        }
        if let Some(comp) = self.composites.get(&ty_id)
            && comp.is_struct
        {
            return comp.ownership == StructOwnership::Copy;
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

    fn is_raw_ptr_or_raw_ptr_array(&self, ty_id: TypeId) -> bool {
        if self.raw_ptrs.contains_key(&ty_id) {
            return true;
        }
        if let Type::Array { elem, .. } = self.program.types[ty_id.0 as usize] {
            return self.is_raw_ptr_or_raw_ptr_array(elem);
        }
        false
    }

    pub(super) fn is_send_type(&self, ty_id: TypeId) -> bool {
        if self.is_opaque_type(ty_id) || self.raw_ptrs.contains_key(&ty_id) {
            return false;
        }
        if let Some(&inner_ty) = self.uninit_types.get(&ty_id) {
            return self.is_send_type(inner_ty);
        }
        if let Some(&slice_info) = self.slices.get(&ty_id) {
            return if slice_info.mutable {
                self.is_send_type(slice_info.elem)
            } else {
                self.is_sync_type(slice_info.elem)
            };
        }
        if let Some(comp) = self.composites.get(&ty_id) {
            if comp.is_struct && comp.is_sync {
                return comp.fields.iter().all(|(_, f_ty, _, _)| {
                    self.is_raw_ptr_or_raw_ptr_array(*f_ty) || self.is_send_type(*f_ty)
                });
            }
        }
        match &self.program.types[ty_id.0 as usize] {
            Type::Ptr { mutable, pointee } => {
                if *mutable {
                    self.is_send_type(*pointee)
                } else {
                    self.is_sync_type(*pointee)
                }
            }
            Type::Struct(fields) | Type::Overlay(fields) => {
                fields.iter().all(|&f| self.is_send_type(f))
            }
            Type::Array { elem, .. } => self.is_send_type(*elem),
            Type::Union { variants, .. } => variants.iter().all(|&v| self.is_send_type(v)),
            Type::Pattern { base, .. } => self.is_send_type(*base),
            _ => true,
        }
    }

    pub(super) fn is_sync_type(&self, ty_id: TypeId) -> bool {
        if self.is_opaque_type(ty_id) || self.raw_ptrs.contains_key(&ty_id) {
            return false;
        }
        if let Some(&inner_ty) = self.uninit_types.get(&ty_id) {
            return self.is_sync_type(inner_ty);
        }
        if let Some(&slice_info) = self.slices.get(&ty_id) {
            return self.is_sync_type(slice_info.elem);
        }
        if let Some(comp) = self.composites.get(&ty_id) {
            if comp.is_struct && comp.is_sync {
                return comp.fields.iter().all(|(_, f_ty, _, _)| {
                    self.is_raw_ptr_or_raw_ptr_array(*f_ty) || self.is_send_type(*f_ty)
                });
            }
        }
        match &self.program.types[ty_id.0 as usize] {
            Type::Ptr { pointee, .. } => self.is_sync_type(*pointee),
            Type::Struct(fields) | Type::Overlay(fields) => {
                fields.iter().all(|&f| self.is_sync_type(f))
            }
            Type::Array { elem, .. } => self.is_sync_type(*elem),
            Type::Union { variants, .. } => variants.iter().all(|&v| self.is_sync_type(v)),
            Type::Pattern { base, .. } => self.is_sync_type(*base),
            _ => true,
        }
    }

    pub(super) fn type_contains_safe_borrow(&self, ty_id: TypeId) -> bool {
        if self.raw_ptrs.contains_key(&ty_id) {
            return false;
        }
        if let Some(&inner_ty) = self.uninit_types.get(&ty_id) {
            return self.type_contains_safe_borrow(inner_ty);
        }
        if self.slices.contains_key(&ty_id) {
            return true;
        }
        match &self.program.types[ty_id.0 as usize] {
            Type::Ptr { .. } => true,
            Type::Struct(fields) | Type::Overlay(fields) => {
                fields.iter().any(|&f| self.type_contains_safe_borrow(f))
            }
            Type::Array { elem, .. } => self.type_contains_safe_borrow(*elem),
            Type::Union { variants, .. } => {
                variants.iter().any(|&v| self.type_contains_safe_borrow(v))
            }
            Type::Pattern { base, .. } => self.type_contains_safe_borrow(*base),
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
        if self.is_opaque_type(ty_id)
            || self.raw_ptrs.contains_key(&ty_id)
            || self.closures.contains_key(&ty_id)
        {
            return false;
        }
        if let Some(&slice_info) = self.slices.get(&ty_id) {
            return slice_info.is_str || self.is_format_type(slice_info.elem);
        }
        if let Some(comp) = self.composites.get(&ty_id) {
            return if comp.is_struct {
                comp.has_format_hook
            } else {
                comp.fields
                    .iter()
                    .all(|(_, f_ty, _, _)| self.is_format_type(*f_ty))
            };
        }
        if self.enums.contains_key(&ty_id) {
            return true;
        }
        match &self.program.types[ty_id.0 as usize] {
            Type::Void | Type::Int { .. } | Type::F32 | Type::F64 | Type::Bool | Type::Rune => true,
            Type::Ptr { pointee, .. } => self.is_format_type(*pointee),
            Type::Struct(fields) => fields.iter().all(|&f| self.is_format_type(f)),
            Type::Array { elem, .. } => self.is_format_type(*elem),
            Type::Union { variants, .. } => variants.iter().all(|&v| self.is_format_type(v)),
            Type::Pattern { base, .. } => self.is_format_type(*base),
            _ => false,
        }
    }

    pub(super) fn is_clone_type(&self, ty_id: TypeId) -> bool {
        if self.is_opaque_type(ty_id) || self.is_linear_type(ty_id) {
            return false;
        }
        if let Some(comp) = self.composites.get(&ty_id) {
            return if comp.is_struct {
                comp.ownership == StructOwnership::Copy || comp.clone_fn.is_some()
            } else {
                comp.fields
                    .iter()
                    .all(|(_, f_ty, _, _)| self.is_clone_type(*f_ty))
            };
        }
        self.is_copy_type(ty_id)
    }

    pub(super) fn is_default_type(&self, ty_id: TypeId) -> bool {
        if self.is_opaque_type(ty_id) || self.opaque_newtypes.contains_key(&ty_id) {
            return false;
        }
        if let Some(comp) = self.composites.get(&ty_id) {
            return if comp.is_struct {
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
                let t_disp = self
                    .composites
                    .get(ty_id)
                    .map(|c| c.name.clone())
                    .unwrap_or_else(|| self.program.types[ty_id.0 as usize].to_string());
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
        let is_newtype = self.opaque_newtypes.contains_key(&ty_id);
        let is_packed_comp = self.composites.get(&ty_id).is_some_and(|c| c.is_packed);
        match constraint {
            TypeConstraint::AnyType => true,
            TypeConstraint::Send => self.is_send_type(ty_id),
            TypeConstraint::Sync => self.is_sync_type(ty_id),
            TypeConstraint::Format => self.is_format_type(ty_id),
            TypeConstraint::Clone => self.is_clone_type(ty_id),
            TypeConstraint::Default => self.is_default_type(ty_id),
            TypeConstraint::Scalar => {
                !is_enum
                    && !is_newtype
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
                    && !is_newtype
                    && !is_packed_comp
                    && matches!(cur, Type::Int { .. } | Type::F32 | Type::F64)
            }
            TypeConstraint::Callable => {
                matches!(cur, Type::FnPtr { .. }) || self.closures.contains_key(&ty_id)
            }
            TypeConstraint::FnPtr => matches!(cur, Type::FnPtr { .. }),
            TypeConstraint::Closure => self.closures.contains_key(&ty_id),
            TypeConstraint::Integer => {
                !is_enum && !is_newtype && !is_packed_comp && matches!(cur, Type::Int { .. })
            }
            TypeConstraint::Signed => {
                !is_enum
                    && !is_newtype
                    && !is_packed_comp
                    && matches!(cur, Type::Int { signed: true, .. })
            }
            TypeConstraint::Unsigned => {
                !is_enum
                    && !is_newtype
                    && !is_packed_comp
                    && matches!(cur, Type::Int { signed: false, .. })
            }
            TypeConstraint::Float => !is_newtype && matches!(cur, Type::F32 | Type::F64),
            TypeConstraint::Aggregate => {
                self.type_satisfies_constraint(ty_id, TypeConstraint::Record)
                    || self.type_satisfies_constraint(ty_id, TypeConstraint::Tuple)
            }
            TypeConstraint::Record => self.composites.get(&ty_id).is_some_and(|c| !c.is_struct),
            TypeConstraint::Tuple => {
                matches!(cur, Type::Struct(_))
                    && !self.composites.contains_key(&ty_id)
                    && !self.trait_objs.contains_key(&ty_id)
                    && !self.closures.contains_key(&ty_id)
                    && !self.slices.contains_key(&ty_id)
            }
            TypeConstraint::Struct => self.composites.get(&ty_id).is_some_and(|c| c.is_struct),
            TypeConstraint::Copy => self.is_copy_type(ty_id),
            TypeConstraint::Affine => !self.is_copy_type(ty_id) && !self.is_linear_type(ty_id),
            TypeConstraint::Linear => self.is_linear_type(ty_id),
            TypeConstraint::Simd => matches!(cur, Type::Simd { .. }),
            TypeConstraint::Sequence => {
                matches!(cur, Type::Array { .. }) || self.slices.contains_key(&ty_id)
            }
            TypeConstraint::Array => matches!(cur, Type::Array { .. }),
            TypeConstraint::Slice => self.slices.contains_key(&ty_id),
            TypeConstraint::Discriminated => {
                self.type_satisfies_constraint(ty_id, TypeConstraint::Enum)
                    || self.type_satisfies_constraint(ty_id, TypeConstraint::Union)
                    || self.type_satisfies_constraint(ty_id, TypeConstraint::Error)
            }
            TypeConstraint::Enum => is_enum,
            TypeConstraint::Union => {
                matches!(cur, Type::Union { .. }) && !self.errors.contains_key(&ty_id)
            }
            TypeConstraint::Overlay => matches!(cur, Type::Overlay(_)),
            TypeConstraint::Error => self.errors.contains_key(&ty_id),
            TypeConstraint::Module => false,
        }
    }

    pub(super) fn type_display_name(&self, ty_id: TypeId) -> String {
        if self.is_universal_opaque_type(ty_id) {
            return "opaque".to_string();
        }
        if let Some(minfo) = self.maps.get(&ty_id) {
            return format!(
                "map[{}, {}]",
                self.type_display_name(minfo.key_ty),
                self.type_display_name(minfo.val_ty)
            );
        }
        if let Type::FnPtr { args, ret } = &self.program.types[ty_id.0 as usize] {
            let params: Vec<String> = args.iter().map(|a| self.type_display_name(*a)).collect();
            let mut s = format!("fn({})", params.join(", "));
            if !matches!(self.program.types[ret.0 as usize], Type::Void) {
                s.push_str(&format!(" -> {}", self.type_display_name(*ret)));
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
            return s;
        }
        if let Some(nt) = self.opaque_newtypes.get(&ty_id) {
            return nt.name.clone();
        }
        if let Some(&ck) = self.c_ints.get(&ty_id) {
            return ck.name().to_string();
        }
        if let Some(&(mutable, pointee)) = self.raw_ptrs.get(&ty_id) {
            return format!(
                "*{}{}",
                if mutable { "mut " } else { "const " },
                self.type_display_name(pointee)
            );
        }
        if let Some(comp) = self.composites.get(&ty_id) {
            return comp.name.clone();
        }
        if let Some(tr) = self.traits.get(&ty_id) {
            return tr.name.clone();
        }
        if let Some(tobj) = self.trait_objs.get(&ty_id)
            && let Some(tr) = self.traits.get(&tobj.trait_ty)
        {
            return format!("&{}{}", if tobj.mutable { "mut " } else { "" }, tr.name);
        }
        if let Some((ename, _)) = self.enums.get(&ty_id) {
            return ename.clone();
        }
        if let Some(uinfo) = self.unions.get(&ty_id) {
            return uinfo.name.clone();
        }
        if let Some(&inner) = self.uninit_types.get(&ty_id) {
            return format!("uninit {}", self.type_display_name(inner));
        }
        if let Some(ov) = self.overlays.get(&ty_id) {
            return ov.name.clone();
        }
        if let Some(einfo) = self.errors.get(&ty_id) {
            return einfo.name.clone();
        }
        if let Type::Ptr { mutable, pointee } = self.program.types[ty_id.0 as usize]
            && !self.slices.contains_key(&ty_id)
        {
            return format!(
                "&{}{}",
                if mutable { "mut " } else { "" },
                self.type_display_name(pointee)
            );
        }
        if let Type::Array { elem, len } = self.program.types[ty_id.0 as usize] {
            return format!("[{}; {}]", self.type_display_name(elem), len);
        }
        self.program.types[ty_id.0 as usize].to_string()
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
        if let Some(nt) = self.opaque_newtypes.get(&ty_id) {
            return self.packed_field_bit_width(nt.underlying);
        }
        match &self.program.types[ty_id.0 as usize] {
            Type::Bool => Some((1, false)),
            Type::Int { signed, bits } => Some((*bits, *signed)),
            Type::Pattern { base, .. } => self.packed_field_bit_width(*base),
            _ => None,
        }
    }

    pub(super) fn int_type_reflection(&self, ty_id: TypeId) -> Option<(bool, u16, i128, i128)> {
        if self.enums.contains_key(&ty_id)
            || self.opaque_newtypes.contains_key(&ty_id)
            || self.raw_ptrs.contains_key(&ty_id)
            || self.named_opaques.contains(&ty_id)
            || self.composites.contains_key(&ty_id)
        {
            return None;
        }
        match &self.program.types[ty_id.0 as usize] {
            Type::Int { signed, bits } => {
                let (min, max) = if *signed {
                    let lo = if *bits >= 128 {
                        i128::MIN
                    } else if *bits == 1 {
                        -1
                    } else {
                        -(1i128 << (*bits - 1))
                    };
                    let hi = if *bits >= 128 {
                        i128::MAX
                    } else if *bits == 1 {
                        0
                    } else {
                        (1i128 << (*bits - 1)) - 1
                    };
                    (lo, hi)
                } else {
                    let hi = if *bits >= 128 {
                        u128::MAX as i128
                    } else {
                        ((1u128 << *bits) - 1) as i128
                    };
                    (0, hi)
                };
                Some((*signed, *bits, min, max))
            }
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
            TypeExpr::Enum { backing: Some(b), .. } => Self::type_expr_mentions_self(b),
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
    ) -> Result<TypeId, String> {
        let ty_id = self.alloc_distinct_type(Type::Void);
        self.traits.insert(
            ty_id,
            TraitInfo {
                name: type_name.to_string(),
                def_module: mod_path.to_string(),
                comptime_env: env.clone(),
                methods: methods.to_vec(),
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
            return Err(format!("Type {trait_ty} is not a trait"));
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
            method_fn_ptr_tys.push(self.intern_fn_ptr_type(arg_tys, ret_ty, contract));
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
        let type_display = self.type_display_name(concrete_ty);
        let imp = self.find_trait_impl(concrete_ty, trait_ty)?;

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

    /// The module that defines a nominal type, if any (builtin and structural types have none).
    fn type_def_module(&self, ty: TypeId) -> Option<String> {
        if let Some(c) = self.composites.get(&ty) {
            return Some(c.def_module.clone());
        }
        if let Some(nt) = self.opaque_newtypes.get(&ty) {
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
                "Type '{type_display}' does not implement trait '{trait_name}'; add 'impl {trait_name} {{ ... }}' to the type's body or 'impl {trait_name} for {type_display} {{ ... }}' in the type's or the trait's module"
            )),
            1 => Ok(found.pop().unwrap()),
            _ => Err(format!(
                "Conflicting implementations of trait '{trait_name}' for '{type_display}': {} and {}",
                found[0].origin, found[1].origin
            )),
        }
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
    fn collect_trait_impls(
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
                    },
                ));
            }
        }

        // 2. Module-level `impl Tr for T { ... }` / `impl(comptime ...) Tr for F(T) { ... }`.
        let mut module_impls: Vec<(String, crate::ast::ImplDecl)> = Vec::new();
        for (mod_name, ast) in &self.modules {
            for item in &ast.items {
                if let Item::Impl(d) = item {
                    module_impls.push((mod_name.clone(), d.clone()));
                }
            }
        }
        module_impls.sort_by(|a, b| a.0.cmp(&b.0));
        for (mod_name, d) in module_impls {
            let env = if d.comptime_params.is_empty() {
                let for_ty = self.resolve_type_expr(&mod_name, None, &HashMap::new(), &d.for_ty)?;
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
                    .unify_type_pattern(&mod_name, &params, &d.for_ty, concrete_ty, &mut inferred)?
                    .is_none()
                    || params.iter().any(|(n, _)| !inferred.contains_key(n))
                {
                    continue;
                }
                let mut bounds_ok = true;
                for (n, bound) in &params {
                    if let Some(ComptimeVal::Type(arg)) = inferred.get(n).cloned()
                        && !matches!(
                            self.eval_comptime_type_bound(&mod_name, None, &inferred, bound, arg)?,
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
                let for_ty = self.resolve_type_expr(&mod_name, None, &inferred, &d.for_ty)?;
                if for_ty != concrete_ty {
                    continue;
                }
                inferred
            };
            let t = self.resolve_type_expr(&mod_name, Some(concrete_ty), &env, &d.trait_expr)?;
            if !self.traits.contains_key(&t) {
                return Err(format!(
                    "'impl ... for {type_display}' in module '{mod_name}' names '{}', which is not a trait",
                    self.type_display_name(t)
                ));
            }
            if trait_filter.is_some_and(|f| f != t) {
                continue;
            }
            let trait_info = self.traits[&t].clone();
            let type_mod = self.type_def_module(concrete_ty);
            if mod_name != trait_info.def_module && type_mod.as_deref() != Some(mod_name.as_str()) {
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
        let Some((def_mod, orig_name, Item::TypeDecl { vis, ty, .. }, _)) =
            self.find_item_in_module(mod_path, mod_path, name)?
        else {
            return Err(format!("Type '{name}' not found in '{mod_path}'"));
        };
        let env = HashMap::new();
        let ty_id = self.instantiate_type_decl(&def_mod, &orig_name, &env, &ty)?;
        self.named_types.insert(key, ty_id);
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

    pub(super) fn instantiate_type_decl(
        &mut self,
        mod_path: &str,
        type_name: &str,
        env: &HashMap<String, ComptimeVal>,
        ty_expr: &TypeExpr,
    ) -> Result<TypeId, String> {
        match ty_expr {
            TypeExpr::Opaque => self.instantiate_named_opaque(mod_path, type_name, env, None, &[]),
            TypeExpr::OpaqueDef { methods } => {
                self.instantiate_named_opaque(mod_path, type_name, env, None, methods)
            }
            TypeExpr::OpaqueNewtype {
                underlying,
                methods,
            } => {
                self.instantiate_opaque_newtype(mod_path, type_name, env, None, underlying, methods)
            }
            TypeExpr::Trait(methods) => {
                self.instantiate_trait(mod_path, type_name, env, None, methods)
            }
            TypeExpr::Enum { backing, variants } => {
                self.instantiate_enum(mod_path, None, env, type_name, backing.as_deref(), variants)
            }
            TypeExpr::Union(variants) => {
                self.instantiate_union(mod_path, type_name, env, None, variants)
            }
            TypeExpr::Overlay(fields) => {
                self.instantiate_overlay(mod_path, type_name, env, None, fields)
            }
            TypeExpr::Error(items) => self.instantiate_error(mod_path, type_name, env, None, items),
            TypeExpr::Record {
                is_packed,
                fields,
                methods,
            } => self.instantiate_composite(
                mod_path,
                type_name,
                false,
                *is_packed,
                StructOwnership::Copy,
                false,
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
            ),
            TypeExpr::Struct {
                is_packed,
                ownership,
                is_sync,
                owns,
                fields,
                consts,
                statics,
                methods,
                default_hook,
                clone_hooks,
                drop_hooks,
                format_hook,
            } => {
                let ownership = self.owned_ownership(
                    type_name,
                    *ownership,
                    owns,
                    env,
                    fields,
                    !drop_hooks.is_empty(),
                )?;
                self.instantiate_composite(
                    mod_path,
                    type_name,
                    true,
                    *is_packed,
                    ownership,
                    *is_sync,
                    env,
                    None,
                    fields,
                    consts,
                    statics,
                    methods,
                    default_hook.clone(),
                    clone_hooks,
                    drop_hooks,
                    format_hook.clone(),
                )
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
            is_struct: true,
            is_packed: false,
            total_bits: 0,
            packed_offsets: Vec::new(),
            ownership: StructOwnership::Affine,
            is_sync: false,
            has_format_hook: false,
            def_module: mod_path.to_string(),
            comptime_env: env.clone(),
            fields: Vec::new(),
            rel_fields: HashMap::new(),
            consts: HashMap::new(),
            statics: HashMap::new(),
            methods: method_map,
            method_fn_ids: HashMap::new(),
            default_fn: None,
            clone_fn: None,
            drop_fn: None,
            format_fn: None,
        };
        self.composites.insert(ty_id, info);
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
                self.composites
                    .get_mut(&ty_id)
                    .unwrap()
                    .method_fn_ids
                    .insert(m.name.clone(), fn_id);
            }
        }
        Ok(ty_id)
    }

    pub(super) fn instantiate_opaque_newtype(
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
        if self.is_opaque_type(underlying_id) {
            return Err(format!(
                "Opaque newtype '{}' cannot wrap unsized opaque type '{}'",
                type_name,
                self.type_display_name(underlying_id)
            ));
        }
        let underlying_stage3 = self.program.types[underlying_id.0 as usize].clone();
        let ty_id = self.alloc_distinct_type(underlying_stage3);
        let mut method_map = HashMap::new();
        for m in methods {
            method_map.insert(m.name.clone(), (m.vis, m.clone()));
        }
        self.register_inline_impls(ty_id, mod_path, env, impl_methods.clone());
        self.opaque_newtypes.insert(
            ty_id,
            OpaqueNewtypeInfo {
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
                self.opaque_newtypes
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
                || self.opaque_newtypes.contains_key(&b_ty)
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
            (false, 32)
        };
        let mut next_val = 0i128;
        let mut resolved = Vec::with_capacity(variants.len());
        for (vname, explicit) in variants {
            let val = explicit.unwrap_or(next_val);
            if !signed && bits < 128 {
                let max = ((1u128 << bits) - 1) as i128;
                if val < 0 || val > max {
                    return Err(format!(
                        "Enum variant '{}::{}' discriminant {} does not fit in backing integer type 'u{}' (0..={})",
                        type_name, vname, val, bits, max
                    ));
                }
            } else if signed && bits < 128 {
                let min = if bits == 1 { -1 } else { -(1i128 << (bits - 1)) };
                let max = if bits == 1 { 0 } else { (1i128 << (bits - 1)) - 1 };
                if val < min || val > max {
                    return Err(format!(
                        "Enum variant '{}::{}' discriminant {} does not fit in backing integer type 'i{}' ({}..={})",
                        type_name, vname, val, bits, min, max
                    ));
                }
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
            Some(TypeExpr::Record {
                is_packed,
                fields,
                methods,
            }) => self.instantiate_composite(
                mod_path,
                &format!("{owner_name}::{vname}"),
                false,
                *is_packed,
                StructOwnership::Copy,
                false,
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

    pub(super) fn instantiate_union(
        &mut self,
        mod_path: &str,
        type_name: &str,
        env: &HashMap<String, ComptimeVal>,
        memo_key: Option<(String, String, Vec<ComptimeVal>)>,
        variants: &[(String, Option<TypeExpr>)],
    ) -> Result<TypeId, String> {
        let mut resolved_variants = Vec::with_capacity(variants.len());
        let mut variant_tys = Vec::with_capacity(variants.len());
        for (vname, payload_expr) in variants {
            if resolved_variants
                .iter()
                .any(|(n, _): &(String, TypeId)| n == vname)
            {
                return Err(format!(
                    "Duplicate variant '{}' in union '{}'",
                    vname, type_name
                ));
            }
            let p_ty =
                self.resolve_variant_payload_ty(mod_path, type_name, vname, env, payload_expr)?;
            resolved_variants.push((vname.clone(), p_ty));
            variant_tys.push(p_ty);
        }
        let tag_ty = self.intern_type(Type::Int {
            signed: false,
            bits: 32,
        });
        let ty_id = self.alloc_distinct_type(Type::Union {
            tag: tag_ty,
            variants: variant_tys,
        });
        self.unions.insert(
            ty_id,
            UnionTypeInfo {
                name: type_name.to_string(),
                variants: resolved_variants,
            },
        );
        if let Some(key) = memo_key {
            self.memoized_type_calls.insert(key, ty_id);
        }
        self.ensure_union_destructor(ty_id);
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
        let ty_id = self.alloc_distinct_type(Type::Overlay(field_tys));
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

    pub(super) fn instantiate_error(
        &mut self,
        mod_path: &str,
        type_name: &str,
        env: &HashMap<String, ComptimeVal>,
        memo_key: Option<(String, String, Vec<ComptimeVal>)>,
        items: &[(String, Option<TypeExpr>)],
    ) -> Result<TypeId, String> {
        let mut leaves: Vec<ErrorLeafInfo> = Vec::new();
        for (vname, payload) in items {
            if payload.is_none() {
                let path: Vec<String> = vname.split("::").map(str::to_string).collect();
                let maybe_emb_ty = if path.len() == 1
                    && let Some(ComptimeVal::Type(t_id)) = env.get(&path[0])
                {
                    Some(*t_id)
                } else if let Ok(ResolvedItem::Type(tmod, tname)) =
                    self.resolve_path(mod_path, &path)
                {
                    Some(self.resolve_named_type(&tmod, &tname)?)
                } else if path.len() > 1 {
                    return Err(format!(
                        "Cannot resolve embedded error path '{}' in error '{}'",
                        vname, type_name
                    ));
                } else {
                    None
                };
                if let Some(emb_ty) = maybe_emb_ty {
                    let Some(emb_err) = self.errors.get(&emb_ty).cloned() else {
                        return Err(format!(
                            "Embedded type '{}' in error '{}' is not an `error` type",
                            vname, type_name
                        ));
                    };
                    for leaf in emb_err.leaves {
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
        leaves.sort_by(|a, b| a.key.cmp(&b.key));
        let canonical_key: Vec<(ErrorLeafKey, TypeId)> = leaves
            .iter()
            .map(|l| (l.key.clone(), l.payload_ty))
            .collect();
        if !canonical_key.is_empty()
            && let Some(&existing_ty) = self.memoized_error_unions.get(&canonical_key)
        {
            if let Some(key) = memo_key {
                self.memoized_type_calls.insert(key, existing_ty);
            }
            return Ok(existing_ty);
        }

        let tag_ty = self.intern_type(Type::Int {
            signed: false,
            bits: 32,
        });
        let variant_tys: Vec<TypeId> = leaves.iter().map(|l| l.payload_ty).collect();
        let ty_id = self.alloc_distinct_type(Type::Union {
            tag: tag_ty,
            variants: variant_tys,
        });
        self.errors.insert(
            ty_id,
            ErrorTypeInfo {
                name: type_name.to_string(),
                leaves,
            },
        );
        if !canonical_key.is_empty() {
            self.memoized_error_unions.insert(canonical_key, ty_id);
        }
        if let Some(key) = memo_key {
            self.memoized_type_calls.insert(key, ty_id);
        }
        self.ensure_union_destructor(ty_id);
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
                self.program.types[lhs_ty.0 as usize]
            ));
        };
        let Some(rhs_err) = self.errors.get(&rhs_ty).cloned() else {
            return Err(format!(
                "Right operand of error union '||' is not an `error` type ({})",
                self.program.types[rhs_ty.0 as usize]
            ));
        };
        let mut leaves = lhs_err.leaves.clone();
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
        let tag_ty = self.intern_type(Type::Int {
            signed: false,
            bits: 32,
        });
        let variant_tys: Vec<TypeId> = leaves.iter().map(|l| l.payload_ty).collect();
        let ty_id = self.alloc_distinct_type(Type::Union {
            tag: tag_ty,
            variants: variant_tys,
        });
        let name = format!("{} || {}", lhs_err.name, rhs_err.name);
        self.errors.insert(ty_id, ErrorTypeInfo { name, leaves });
        self.memoized_error_unions.insert(canonical_key, ty_id);
        self.ensure_union_destructor(ty_id);
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
            _ => false,
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
                BorrowContractItem::Return(name) => {
                    has_ret_item = true;
                    contract.ret.push(position(name)?);
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
                BorrowContractItem::Return(name) => {
                    has_ret_item = true;
                    contract.ret.push(position(name)?);
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

    /// Applies `opaque(owns T, ...)`: an instantiation is linear if any owned type argument is linear,
    /// regardless of which lifecycle hooks the type declares.
    pub(super) fn owned_ownership(
        &mut self,
        type_name: &str,
        ownership: StructOwnership,
        owns: &[String],
        env: &HashMap<String, ComptimeVal>,
        fields: &[FieldDecl],
        has_drop_hook: bool,
    ) -> Result<StructOwnership, String> {
        // Lint: an owning container (one with a `drop` hook) that holds a type parameter behind a raw
        // pointer or `uninit` storage without declaring `owns` would hide linear elements from the checker.
        if has_drop_hook {
            for f in fields {
                let mut hidden = Vec::new();
                Self::collect_indirect_type_params(&f.ty, false, &mut hidden);
                for name in hidden {
                    if !owns.contains(&name) && matches!(env.get(&name), Some(ComptimeVal::Type(_)))
                    {
                        self.warn(format!(
                            "opaque '{type_name}' has a 'drop' hook and holds '{name}' behind a raw pointer or 'uninit' storage (field '{}') but does not declare 'owns({name})'; linear '{name}' values would be discarded silently",
                            f.name
                        ));
                    }
                }
            }
        }
        let mut result = ownership;
        for name in owns {
            match env.get(name) {
                Some(ComptimeVal::Type(t)) => {
                    if self.is_linear_type(*t) {
                        result = StructOwnership::Linear;
                    }
                }
                _ => {
                    return Err(format!(
                        "'owns({name})' on opaque '{type_name}' does not name a comptime type parameter in scope"
                    ));
                }
            }
        }
        Ok(result)
    }

    /// Collects single-segment type names that appear behind `*const`/`*mut`/`uninit` (possibly
    /// nested inside arrays or optionals) in a field type expression.
    fn collect_indirect_type_params(te: &TypeExpr, indirect: bool, out: &mut Vec<String>) {
        match te {
            TypeExpr::Ptr { inner, .. } | TypeExpr::Uninit(inner) => {
                Self::collect_indirect_type_params(inner, true, out);
            }
            TypeExpr::Optional(inner) => Self::collect_indirect_type_params(inner, indirect, out),
            TypeExpr::Array { elem, .. } => Self::collect_indirect_type_params(elem, indirect, out),
            TypeExpr::Named(path) if indirect && path.len() == 1 => {
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
        is_struct: bool,
        is_packed: bool,
        ownership: StructOwnership,
        is_sync: bool,
        env: &HashMap<String, ComptimeVal>,
        memo_key: Option<(String, String, Vec<ComptimeVal>)>,
        fields: &[FieldDecl],
        consts: &[ConstDecl],
        statics: &[StaticDecl],
        methods: &[FuncDecl],
        default_hook: Option<Block>,
        clone_hooks: &[CloneHookDecl],
        drop_hooks: &[DropHookDecl],
        format_hook: Option<(String, String, Option<String>, Block)>,
    ) -> Result<TypeId, String> {
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
                            "Struct '{type_name}' defines 'drop' with 'where {}: !linear', but is missing a matching 'drop(self: &mut Self) where {}: linear' teardown hook",
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
            && is_struct
            && effective_ownership == StructOwnership::Affine
            && selected_drop.is_none()
            && selected_clone.is_none()
        {
            effective_ownership = StructOwnership::Copy;
        }
        if is_struct
            && let Some(dh) = selected_drop
            && dh
                .where_clauses
                .iter()
                .any(|w| w.constraint == TypeConstraint::Linear && !w.negated)
        {
            effective_ownership = StructOwnership::Linear;
        }

        let is_linear = is_struct && effective_ownership == StructOwnership::Linear;
        if is_linear && selected_clone.is_some() {
            return Err(format!(
                "Linear opaque '{type_name}' cannot implement `clone`; linear values must be consumed exactly once"
            ));
        }
        if is_struct && effective_ownership == StructOwnership::Copy {
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
                    if !is_struct {
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
                    if !is_struct {
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
                    if !is_struct {
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
            if is_struct {
                match effective_ownership {
                    StructOwnership::Copy => {
                        if !self.is_copy_type(f_ty) {
                            return Err(format!(
                                "Field '{}' of 'opaque(copy) {}' has non-copy type",
                                f.name, type_name
                            ));
                        }
                    }
                    StructOwnership::Affine => {
                        if self.is_linear_type(f_ty) {
                            return Err(format!(
                                "Field '{}' of affine opaque '{}' has linear type; declare 'opaque(linear) {}' (or 'opaque(owns T)' for a generic container) instead",
                                f.name, type_name, type_name
                            ));
                        }
                    }
                    StructOwnership::Linear => {}
                }
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

        // Every distinct record/struct declaration gets a distinct TypeId so its field names,
        // defaults, and methods in `self.composites` never collide (tuples use `intern_type`).
        let ty_id = if is_packed {
            self.alloc_distinct_type(Type::Int {
                signed: false,
                bits: total_bits,
            })
        } else {
            self.alloc_distinct_type(Type::Struct(field_tys))
        };
        if is_linear {
            let label = match &memo_key {
                Some((_, fname, args)) => format!(
                    "{fname}({})",
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
            is_struct,
            is_packed,
            total_bits,
            packed_offsets,
            ownership: effective_ownership,
            is_sync,
            has_format_hook: format_hook.is_some(),
            def_module: mod_path.to_string(),
            comptime_env: env.clone(),
            fields: field_infos,
            rel_fields,
            consts: const_map,
            statics: static_map,
            methods: method_map,
            method_fn_ids: HashMap::new(),
            default_fn: None,
            clone_fn: None,
            drop_fn: None,
            format_fn: None,
        };
        self.composites.insert(ty_id, info);
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
                self.composites
                    .get_mut(&ty_id)
                    .unwrap()
                    .method_fn_ids
                    .insert(m.name.clone(), fn_id);
            }
        }

        // Instantiate `default`, `clone`, `drop`, `format` lifecycle hooks on `struct`
        if let Some(def_blk) = default_hook {
            let decl = FuncDecl {
                vis: Visibility::Pub,
                name: format!("{type_name}::default"),
                params: vec![],
                ret_ty: TypeExpr::SelfType,
                borrows: None,
                where_clauses: Vec::new(),
                body: def_blk,
                impl_of: None,
            };
            let fn_id = self.schedule_method(mod_path, ty_id, env, &decl)?;
            self.composites.get_mut(&ty_id).unwrap().default_fn = Some(fn_id);
        }

        if let Some(clone_hook) = selected_clone {
            let decl = FuncDecl {
                vis: Visibility::Pub,
                name: format!("{type_name}::clone"),
                params: vec![crate::ast::Param {
                    is_comptime: false,
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
                impl_of: None,
            };
            let fn_id = self.schedule_method(mod_path, ty_id, env, &decl)?;
            self.composites.get_mut(&ty_id).unwrap().clone_fn = Some(fn_id);
        }

        if let Some(drop_hook) = selected_drop {
            let decl = FuncDecl {
                vis: Visibility::Pub,
                name: format!("{type_name}::drop"),
                params: vec![crate::ast::Param {
                    is_comptime: false,
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
                impl_of: None,
            };
            let fn_id = self.schedule_method(mod_path, ty_id, env, &decl)?;
            self.composites.get_mut(&ty_id).unwrap().drop_fn = Some(fn_id);
            self.program.destructors.push((ty_id, fn_id));
        }

        if let Some((self_name, fmt_name, opt_spec_name, fmt_blk)) = format_hook {
            let mut params = vec![
                crate::ast::Param {
                    is_comptime: false,
                    is_mut: false,
                    name: self_name,
                    ty: TypeExpr::Ref {
                        mutable: false,
                        inner: Box::new(TypeExpr::SelfType),
                    },
                },
                crate::ast::Param {
                    is_comptime: false,
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
                impl_of: None,
            };
            let fn_id = self.schedule_method(mod_path, ty_id, env, &decl)?;
            self.composites.get_mut(&ty_id).unwrap().format_fn = Some((fn_id, takes_spec));
        }

        Ok(ty_id)
    }

    pub(super) fn type_contains_safe_ref(&self, ty_id: TypeId) -> bool {
        if self.raw_ptrs.contains_key(&ty_id) {
            return false;
        }
        if self.slices.contains_key(&ty_id) {
            return true;
        }
        match &self.program.types[ty_id.0 as usize] {
            Type::Ptr { .. } => true,
            Type::Struct(fields) | Type::Overlay(fields) => {
                fields.iter().any(|&f| self.type_contains_safe_ref(f))
            }
            Type::Array { elem, .. } => self.type_contains_safe_ref(*elem),
            Type::Union { variants, .. } => {
                variants.iter().any(|&v| self.type_contains_safe_ref(v))
            }
            Type::Pattern { base, .. } => self.type_contains_safe_ref(*base),
            _ => false,
        }
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
        // Every `pub`, `pub(pkg)`, and `export` function has a signature-only borrow contract;
        // private functions have theirs inferred from the body.
        let is_pub = matches!(
            decl.vis,
            Visibility::Pub | Visibility::PubPkg | Visibility::Export
        );
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
                BorrowContractItem::Return(name) => {
                    has_ret_item = true;
                    let Some(idx) = rt_params.iter().position(|(pname, _)| pname == name) else {
                        return Err(format!(
                            "Unknown runtime parameter '{}' in borrows(...) contract on '{}'",
                            name, decl.name
                        ));
                    };
                    let loc = LocalId((idx + 1) as u32);
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
                        "Parameter '{}' of '{}' has a meta-type constraint by value; use '(comptime T: ..., {}: T)' for static dispatch or '&Trait' for dynamic dispatch",
                        p.name, decl.name, p.name
                    ));
                }
                let pty = self.resolve_type_expr(mod_path, Some(owner_ty), &sig_env, &p.ty)?;
                if let Some(tr) = self.traits.get(&pty) {
                    return Err(format!(
                        "Trait '{}' is an unsized meta-type constraint and cannot be passed by value in parameter '{}' of '{}'; use '(comptime T: {}, {}: T)' for static dispatch or '({}: &{})' for dynamic dispatch",
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
            .is_some_and(|c| c.is_struct && c.ownership == StructOwnership::Linear)
            && param_tys.first() == Some(&owner_ty)
        {
            if let Some(func) = self.program.functions.iter_mut().find(|f| f.id == fn_id) {
                func.linear_self = Some(owner_ty);
            }
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
            debug_name: None,
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
                            if self
                                .eval_comptime_type_bound(mod_path, None, &env, &p.ty, TypeId(0))?
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
            TypeExpr::Opaque => vec![BoundAtom::Constraint(TypeConstraint::Struct)],
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
                        "Parameter '{}' of '{}' has a meta-type constraint by value; use '(comptime T: ..., {}: T)' for static dispatch or '&Trait' for dynamic dispatch",
                        p.name, decl.name, p.name
                    ));
                }
                let pty = self.resolve_type_expr(mod_path, None, &env, &p.ty)?;
                if let Some(tr) = self.traits.get(&pty) {
                    return Err(format!(
                        "Trait '{}' is an unsized meta-type constraint and cannot be passed by value in parameter '{}' of '{}'; use '(comptime T: {}, {}: T)' for static dispatch or '({}: &{})' for dynamic dispatch",
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
            TypeExpr::Opaque => Ok(self.intern_opaque_type()),
            TypeExpr::OpaqueDef { methods } => {
                self.instantiate_named_opaque(mod_path, "<anon_opaque>", env, None, methods)
            }
            TypeExpr::OpaqueNewtype {
                underlying,
                methods,
            } => self.instantiate_opaque_newtype(
                mod_path,
                "<anon_newtype>",
                env,
                None,
                underlying,
                methods,
            ),
            TypeExpr::OpaqueTrait(_) => Err(
                "'opaque Trait' existential types are only permitted in function return types ('-> opaque Trait'); use '(comptime T: Trait, x: T)' or '&Trait' for parameters"
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
            TypeExpr::Trait(methods) => {
                self.instantiate_trait(mod_path, "<anon_trait>", env, None, methods)
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
            TypeExpr::Ptr { mutable, inner } => {
                let pointee = self.resolve_type_expr(mod_path, self_ty, env, inner)?;
                Ok(self.intern_raw_ptr_type(*mutable, pointee))
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
                    let lo = self.eval_comptime_int(mod_path, self_ty, env, lo_e)?;
                    let hi = self.eval_comptime_int(mod_path, self_ty, env, hi_e)?;
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
            } => {
                let mut args = Vec::with_capacity(params.len());
                for p in params {
                    args.push(self.resolve_type_expr(mod_path, self_ty, env, p)?);
                }
                let ret_id = self.resolve_type_expr(mod_path, self_ty, env, ret)?;
                let contract = self.fn_type_contract(&args, ret_id, borrows.as_deref())?;
                Ok(self.intern_fn_ptr_type(args, ret_id, contract))
            }
            TypeExpr::Enum { backing, variants } => self.instantiate_enum(
                mod_path,
                self_ty,
                env,
                "<anon_enum>",
                backing.as_deref(),
                variants,
            ),
            TypeExpr::Union(variants) => {
                self.instantiate_union(mod_path, "<anon_union>", env, None, variants)
            }
            TypeExpr::Overlay(fields) => {
                self.instantiate_overlay(mod_path, "<anon_overlay>", env, None, fields)
            }
            TypeExpr::Error(items) => {
                self.instantiate_error(mod_path, "<anon_error>", env, None, items)
            }
            TypeExpr::Record {
                is_packed,
                fields,
                methods,
            } => {
                self.instantiate_composite(
                    mod_path,
                    "<anon_record>",
                    false,
                    *is_packed,
                    StructOwnership::Copy,
                    false,
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
                )
            }
            TypeExpr::Struct {
                is_packed,
                ownership,
                is_sync,
                owns,
                fields,
                consts,
                statics,
                methods,
                default_hook,
                clone_hooks,
                drop_hooks,
                format_hook,
            } => {
                let ownership = self.owned_ownership(
                    "<anon_struct>",
                    *ownership,
                    owns,
                    env,
                    fields,
                    !drop_hooks.is_empty(),
                )?;
                self.instantiate_composite(
                mod_path,
                "<anon_struct>",
                true,
                *is_packed,
                ownership,
                *is_sync,
                env,
                None,
                fields,
                consts,
                statics,
                methods,
                default_hook.clone(),
                clone_hooks,
                drop_hooks,
                format_hook.clone(),
            )
            }
            TypeExpr::Map { key, val } => {
                let key_ty = self.resolve_type_expr(mod_path, self_ty, env, key)?;
                let val_ty = self.resolve_type_expr(mod_path, self_ty, env, val)?;
                Ok(self.intern_map_type(key_ty, val_ty))
            }
            TypeExpr::TypeIndex { path, index } => {
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
            TypeExpr::Named(path) => {
                if path.len() == 1
                    && let Some(ComptimeVal::Type(t_id)) = env.get(&path[0])
                {
                    return Ok(*t_id);
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
            TypeExpr::TypeCall { path, args } => {
                let expanded = self.expand_module_path(env, path);
                let ResolvedItem::Func(fmod, fname) = self.resolve_path(mod_path, &expanded)?
                else {
                    return Err(format!(
                        "'{}' is not a comptime type function",
                        expanded.join("::")
                    ));
                };
                let mut ct_args = Vec::with_capacity(args.len());
                for arg in args {
                    ct_args.push(self.eval_comptime_val(mod_path, self_ty, env, arg)?);
                }
                self.eval_comptime_type_func(&fmod, &fname, &ct_args)
            }
        }
    }
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
        C::Record | C::Tuple => Some(C::Aggregate),
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
        TypeExpr::Opaque => "opaque".to_string(),
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
