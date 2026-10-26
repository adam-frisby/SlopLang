use std::collections::{BTreeMap, BTreeSet};

use crate::ir::{
    BasicBlock, BlockId, ConstValue, FuncId, Function, LocalId, Operand, Place, Program,
    Projection, Rvalue, Statement, Terminator, Type, TypeId,
};

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
struct MovePath {
    local: LocalId,
    fields: Vec<u32>,
}

impl MovePath {
    fn from_place(program: &Program, func: &Function, place: &Place) -> Option<Self> {
        let mut fields = Vec::new();
        let mut cur_ty = *func.locals.get(place.local.0 as usize)?;
        for proj in &place.projections {
            match proj {
                Projection::Field(idx) => match program.types.get(cur_ty.0 as usize)? {
                    Type::Struct(ftys) => {
                        cur_ty = *ftys.get(*idx as usize)?;
                        fields.push(*idx);
                    }
                    Type::Overlay(ftys) => {
                        let _ = ftys.get(*idx as usize)?;
                        break;
                    }
                    _ => return None,
                },
                Projection::Variant(_) => {
                    if !matches!(
                        program.types.get(cur_ty.0 as usize),
                        Some(Type::Union { .. })
                    ) {
                        return None;
                    }
                    break;
                }
                _ => return None,
            }
        }
        Some(Self {
            local: place.local,
            fields,
        })
    }

    fn deref_prefix_from_place(program: &Program, func: &Function, place: &Place) -> Option<Self> {
        let deref_pos = place
            .projections
            .iter()
            .position(|p| matches!(p, Projection::Deref))?;
        let mut fields = Vec::new();
        let mut cur_ty = *func.locals.get(place.local.0 as usize)?;
        for proj in &place.projections[..deref_pos] {
            match proj {
                Projection::Field(idx) => {
                    let Type::Struct(ftys) = program.types.get(cur_ty.0 as usize)? else {
                        return None;
                    };
                    cur_ty = *ftys.get(*idx as usize)?;
                    fields.push(*idx);
                }
                _ => return None,
            }
        }
        Some(Self {
            local: place.local,
            fields,
        })
    }

    fn to_place(&self) -> Place {
        Place {
            local: self.local,
            projections: self.fields.iter().copied().map(Projection::Field).collect(),
        }
    }
}

fn place_projects_through_overlay_field(
    program: &Program,
    func: &Function,
    place: &Place,
) -> bool {
    let Some(mut cur_ty) = func.locals.get(place.local.0 as usize).copied() else {
        return false;
    };
    for proj in &place.projections {
        match proj {
            Projection::Deref => {
                if let Some(Type::Ptr { pointee, .. }) = program.types.get(cur_ty.0 as usize) {
                    cur_ty = *pointee;
                } else {
                    return false;
                }
            }
            Projection::Field(idx) => match program.types.get(cur_ty.0 as usize) {
                Some(Type::Struct(fields)) => {
                    let Some(&next) = fields.get(*idx as usize) else {
                        return false;
                    };
                    cur_ty = next;
                }
                Some(Type::Overlay(_)) => return true,
                _ => return false,
            },
            Projection::Variant(v_idx) => {
                if let Some(Type::Union { variants, .. }) = program.types.get(cur_ty.0 as usize)
                    && let Some(&next) = variants.get(*v_idx as usize)
                {
                    cur_ty = next;
                } else {
                    return false;
                }
            }
            Projection::Index(_) => match program.types.get(cur_ty.0 as usize) {
                Some(Type::Array { elem, .. } | Type::Simd { elem, .. }) => cur_ty = *elem,
                _ => return false,
            },
        }
    }
    false
}

#[derive(Debug, Clone, PartialEq, Eq, Default)]
struct InitState {
    maybe_init: BTreeSet<MovePath>,
    maybe_uninit: BTreeSet<MovePath>,
}

/// Runs Stage 3 Move Checking and Drop Elaboration on all functions in `program`.
///
/// - Verifies that no uninitialized or moved `MovePath` is read by `copy` or `move`.
/// - Rewrites every `Terminator::Drop { place, target }` into:
///   - `Terminator::Goto { target }` when the value is statically uninitialized/moved or trivially droppable.
///   - Direct `Terminator::Call` to the registered destructor when statically initialized.
///   - Field-by-field drop chains when a struct is partially moved.
///   - Dynamic drop-flag guarded `SwitchInt` + `Call` when initialization varies across control-flow branches.
pub fn elaborate_drops(program: &mut Program) -> Result<(), String> {
    let destructors: BTreeMap<TypeId, FuncId> = program.destructors.iter().copied().collect();
    let void_ty = program.intern_type(Type::Void);
    let bool_ty = program.intern_type(Type::Bool);

    for func_idx in 0..program.functions.len() {
        elaborate_function(program, func_idx, &destructors, void_ty, bool_ty)?;
    }
    Ok(())
}

fn is_direct_linear_struct(program: &Program, ty_id: TypeId) -> bool {
    program.linear_types.iter().any(|(t, _)| *t == ty_id)
}

fn linear_type_name(program: &Program, ty_id: TypeId) -> Option<&str> {
    if let Some((_, name)) = program.linear_types.iter().find(|(t, _)| *t == ty_id) {
        return Some(name.as_str());
    }
    match program.types.get(ty_id.0 as usize) {
        Some(
            Type::Struct(fields)
            | Type::Union {
                variants: fields, ..
            },
        ) => fields.iter().find_map(|&v| linear_type_name(program, v)),
        Some(Type::Array { elem, len }) if *len > 0 => linear_type_name(program, *elem),
        _ => None,
    }
}

fn type_needs_drop(
    program: &Program,
    destructors: &BTreeMap<TypeId, FuncId>,
    ty_id: TypeId,
) -> bool {
    if destructors.contains_key(&ty_id) || linear_type_name(program, ty_id).is_some() {
        return true;
    }
    match program.types.get(ty_id.0 as usize) {
        Some(Type::Struct(fields)) => fields
            .iter()
            .any(|&f| type_needs_drop(program, destructors, f)),
        _ => false,
    }
}

fn collect_leaf_paths_for_type(
    program: &Program,
    destructors: &BTreeMap<TypeId, FuncId>,
    ty_id: TypeId,
    prefix: &mut Vec<u32>,
    out: &mut Vec<Vec<u32>>,
) {
    // If a struct has its own destructor or is a nominal `linear struct`, treat it as an atomic drop unit
    // unless fields are moved; if it does not, decompose into its fields.
    if !destructors.contains_key(&ty_id)
        && !is_direct_linear_struct(program, ty_id)
        && let Some(Type::Struct(fields)) = program.types.get(ty_id.0 as usize)
        && !fields.is_empty()
    {
        for (i, &fty) in fields.iter().enumerate() {
            prefix.push(i as u32);
            collect_leaf_paths_for_type(program, destructors, fty, prefix, out);
            prefix.pop();
        }
        return;
    }
    out.push(prefix.clone());
}

fn expand_to_leaf_paths(
    program: &Program,
    destructors: &BTreeMap<TypeId, FuncId>,
    func: &Function,
    path: &MovePath,
) -> Vec<MovePath> {
    let mut cur_ty = func.locals[path.local.0 as usize];
    for &f in &path.fields {
        if let Some(Type::Struct(ftys)) = program.types.get(cur_ty.0 as usize) {
            cur_ty = ftys[f as usize];
        }
    }
    let mut suffixes = Vec::new();
    let mut prefix = Vec::new();
    collect_leaf_paths_for_type(program, destructors, cur_ty, &mut prefix, &mut suffixes);
    suffixes
        .into_iter()
        .map(|mut s| {
            let mut fields = path.fields.clone();
            fields.append(&mut s);
            MovePath {
                local: path.local,
                fields,
            }
        })
        .collect()
}

fn mark_initialized(
    program: &Program,
    destructors: &BTreeMap<TypeId, FuncId>,
    func: &Function,
    state: &mut InitState,
    path: &MovePath,
) {
    for leaf in expand_to_leaf_paths(program, destructors, func, path) {
        state.maybe_init.insert(leaf.clone());
        state.maybe_uninit.remove(&leaf);
    }
}

fn mark_uninitialized(
    program: &Program,
    destructors: &BTreeMap<TypeId, FuncId>,
    func: &Function,
    state: &mut InitState,
    path: &MovePath,
) {
    for leaf in expand_to_leaf_paths(program, destructors, func, path) {
        state.maybe_uninit.insert(leaf.clone());
        state.maybe_init.remove(&leaf);
    }
}

/// The first enclosing type along `path`'s field projections that has a registered destructor,
/// if any (the path itself being a strict sub-place of it).
fn drop_hook_owner_on_path(
    program: &Program,
    destructors: &BTreeMap<TypeId, FuncId>,
    func: &Function,
    path: &MovePath,
) -> Option<TypeId> {
    let mut ty = *func.locals.get(path.local.0 as usize)?;
    for &idx in &path.fields {
        if destructors.contains_key(&ty) {
            return Some(ty);
        }
        let Some(Type::Struct(fields)) = program.types.get(ty.0 as usize) else {
            return None;
        };
        ty = *fields.get(idx as usize)?;
    }
    None
}

fn check_and_apply_operand(
    program: &Program,
    destructors: &BTreeMap<TypeId, FuncId>,
    func: &Function,
    state: &mut InitState,
    op: &Operand,
    check_errors: bool,
) -> Result<(), String> {
    match op {
        Operand::Copy(place) | Operand::Move(place) => {
            if let Some(path) = MovePath::from_place(program, func, place) {
                // A field may not be moved out of a value whose type has a `drop` hook: the hook
                // would later run on the partially moved value.
                if check_errors
                    && matches!(op, Operand::Move(_))
                    && let Some(owner) = drop_hook_owner_on_path(program, destructors, func, &path)
                {
                    return Err(format!(
                        "Cannot move '{}' out of a value of type '{}' because that type has a 'drop' hook (it would run on the partially moved value) in {}",
                        place,
                        program.type_label(owner),
                        func.label()
                    ));
                }
                let leaves = expand_to_leaf_paths(program, destructors, func, &path);
                if check_errors {
                    for leaf in &leaves {
                        if state.maybe_uninit.contains(leaf) {
                            return Err(format!(
                                "Use of moved or uninitialized value '{}' in {}",
                                place, func.label()
                            ));
                        }
                    }
                }
                if matches!(op, Operand::Move(_))
                    && !place_projects_through_overlay_field(program, func, place)
                {
                    for leaf in leaves {
                        state.maybe_uninit.insert(leaf.clone());
                        state.maybe_init.remove(&leaf);
                    }
                }
            } else if check_errors
                && let Some(prefix_path) = MovePath::deref_prefix_from_place(program, func, place)
            {
                let leaves = expand_to_leaf_paths(program, destructors, func, &prefix_path);
                for leaf in &leaves {
                    if state.maybe_uninit.contains(leaf) {
                        return Err(format!(
                            "Use of moved or uninitialized value '{}' in {}",
                            place, func.label()
                        ));
                    }
                }
            }
            Ok(())
        }
        Operand::Const(_) => Ok(()),
    }
}

fn apply_statement(
    program: &Program,
    destructors: &BTreeMap<TypeId, FuncId>,
    func: &Function,
    state: &mut InitState,
    stmt: &Statement,
    check_errors: bool,
) -> Result<(), String> {
    match stmt {
        Statement::StorageLive(local) => {
            let root = MovePath {
                local: *local,
                fields: Vec::new(),
            };
            mark_uninitialized(program, destructors, func, state, &root);
            Ok(())
        }
        Statement::StorageDead(local) => {
            let root = MovePath {
                local: *local,
                fields: Vec::new(),
            };
            mark_uninitialized(program, destructors, func, state, &root);
            Ok(())
        }
        Statement::SetDiscriminant(place, _) => {
            if let Some(path) = MovePath::from_place(program, func, place) {
                mark_initialized(program, destructors, func, state, &path);
            }
            Ok(())
        }
        Statement::Assign(dest, rvalue) => {
            match rvalue {
                Rvalue::Use(op)
                | Rvalue::UnaryOp(_, op)
                | Rvalue::Cast(op, _)
                | Rvalue::Transmute(op, _) => {
                    check_and_apply_operand(program, destructors, func, state, op, check_errors)?;
                }
                Rvalue::BinaryOp(_, lhs, rhs) => {
                    check_and_apply_operand(program, destructors, func, state, lhs, check_errors)?;
                    check_and_apply_operand(program, destructors, func, state, rhs, check_errors)?;
                }
                Rvalue::Ref { place, .. } | Rvalue::Discriminant(place) => {
                    check_and_apply_operand(
                        program,
                        destructors,
                        func,
                        state,
                        &Operand::Copy(place.clone()),
                        check_errors,
                    )?;
                }
                Rvalue::Aggregate(_, ops) | Rvalue::OverlayType(ops) => {
                    for op in ops {
                        check_and_apply_operand(
                            program,
                            destructors,
                            func,
                            state,
                            op,
                            check_errors,
                        )?;
                    }
                }
                Rvalue::ArrayType { elem, len } | Rvalue::SimdType { elem, len } => {
                    check_and_apply_operand(program, destructors, func, state, elem, check_errors)?;
                    check_and_apply_operand(program, destructors, func, state, len, check_errors)?;
                }
                Rvalue::UnionType { tag, variants } => {
                    check_and_apply_operand(program, destructors, func, state, tag, check_errors)?;
                    for op in variants {
                        check_and_apply_operand(
                            program,
                            destructors,
                            func,
                            state,
                            op,
                            check_errors,
                        )?;
                    }
                }
                Rvalue::PatternType { base, ranges } => {
                    check_and_apply_operand(program, destructors, func, state, base, check_errors)?;
                    for (lo, hi) in ranges {
                        check_and_apply_operand(
                            program,
                            destructors,
                            func,
                            state,
                            lo,
                            check_errors,
                        )?;
                        check_and_apply_operand(
                            program,
                            destructors,
                            func,
                            state,
                            hi,
                            check_errors,
                        )?;
                    }
                }
                Rvalue::Union { payload, .. } => {
                    check_and_apply_operand(
                        program,
                        destructors,
                        func,
                        state,
                        payload,
                        check_errors,
                    )?;
                }
            }
            if let Some(dest_path) = MovePath::from_place(program, func, dest) {
                mark_initialized(program, destructors, func, state, &dest_path);
            } else if check_errors
                && let Some(prefix_path) = MovePath::deref_prefix_from_place(program, func, dest)
            {
                let leaves = expand_to_leaf_paths(program, destructors, func, &prefix_path);
                for leaf in &leaves {
                    if state.maybe_uninit.contains(leaf) {
                        return Err(format!(
                            "Use of moved or uninitialized value '{}' in {}",
                            dest, func.label()
                        ));
                    }
                }
            }
            Ok(())
        }
    }
}

fn place_type(program: &Program, func: &Function, place: &Place) -> Result<TypeId, String> {
    let mut cur_ty = *func
        .locals
        .get(place.local.0 as usize)
        .ok_or_else(|| format!("Undefined local {} in {}", place.local, func.id))?;
    for proj in &place.projections {
        match proj {
            Projection::Deref => {
                let Some(Type::Ptr { pointee, .. }) = program.types.get(cur_ty.0 as usize) else {
                    return Err(format!("Cannot deref non-pointer type {cur_ty}"));
                };
                cur_ty = *pointee;
            }
            Projection::Field(idx) => match program.types.get(cur_ty.0 as usize) {
                Some(Type::Struct(fields) | Type::Overlay(fields)) => {
                    cur_ty = fields[*idx as usize];
                }
                _ => return Err(format!("Cannot access field on {cur_ty}")),
            },
            Projection::Variant(v_idx) => {
                let Some(Type::Union { variants, .. }) = program.types.get(cur_ty.0 as usize)
                else {
                    return Err(format!("Cannot access variant on {cur_ty}"));
                };
                cur_ty = variants[*v_idx as usize];
            }
            Projection::Index(_) => {
                let Some(Type::Array { elem, .. } | Type::Simd { elem, .. }) =
                    program.types.get(cur_ty.0 as usize)
                else {
                    return Err(format!("Cannot index non-array/simd {cur_ty}"));
                };
                cur_ty = *elem;
            }
        }
    }
    Ok(cur_ty)
}

fn elaborate_function(
    program: &mut Program,
    func_idx: usize,
    destructors: &BTreeMap<TypeId, FuncId>,
    unit_ty: TypeId,
    bool_ty: TypeId,
) -> Result<(), String> {
    let func = program.functions[func_idx].clone();
    let num_blocks = func.blocks.len();
    if num_blocks == 0 {
        return Ok(());
    }

    // 1. Build entry InitState for bb0
    let mut entry0 = InitState::default();
    for local_idx in 0..func.locals.len() {
        let root = MovePath {
            local: LocalId(local_idx as u32),
            fields: Vec::new(),
        };
        if (1..=func.arg_count).contains(&local_idx) {
            mark_initialized(program, destructors, &func, &mut entry0, &root);
        } else {
            mark_uninitialized(program, destructors, &func, &mut entry0, &root);
        }
    }

    let mut block_in: Vec<InitState> = vec![InitState::default(); num_blocks];
    let mut block_out: Vec<InitState> = vec![InitState::default(); num_blocks];
    block_in[0] = entry0;

    // 2. Fixed-point forward dataflow analysis
    let mut changed = true;
    while changed {
        changed = false;
        for bb in 0..num_blocks {
            let mut state = block_in[bb].clone();
            for stmt in &func.blocks[bb].statements {
                apply_statement(program, destructors, &func, &mut state, stmt, false)?;
            }

            // Apply terminator effects onto successor edges
            let mut succs: Vec<(BlockId, InitState)> = Vec::new();
            match &func.blocks[bb].terminator {
                Terminator::Goto { target } => {
                    succs.push((*target, state.clone()));
                }
                Terminator::SwitchInt {
                    discr,
                    targets,
                    otherwise,
                } => {
                    check_and_apply_operand(program, destructors, &func, &mut state, discr, false)?;
                    for (_, t) in targets {
                        succs.push((*t, state.clone()));
                    }
                    succs.push((*otherwise, state.clone()));
                }
                Terminator::Call {
                    func: callee,
                    args,
                    destination,
                    target,
                } => {
                    check_and_apply_operand(
                        program,
                        destructors,
                        &func,
                        &mut state,
                        callee,
                        false,
                    )?;
                    for a in args {
                        check_and_apply_operand(program, destructors, &func, &mut state, a, false)?;
                    }
                    let mut after_call = state.clone();
                    if let Some(dest_path) = MovePath::from_place(program, &func, destination) {
                        mark_initialized(program, destructors, &func, &mut after_call, &dest_path);
                    }
                    succs.push((*target, after_call));
                }
                Terminator::Drop { place, target } => {
                    let mut after_drop = state.clone();
                    if let Some(drop_path) = MovePath::from_place(program, &func, place) {
                        mark_uninitialized(
                            program,
                            destructors,
                            &func,
                            &mut after_drop,
                            &drop_path,
                        );
                    }
                    succs.push((*target, after_drop));
                }
                Terminator::Return | Terminator::Unreachable => {}
            }

            if block_out[bb] != state {
                block_out[bb] = state;
                changed = true;
            }

            for (succ_bb, edge_state) in succs {
                let s_idx = succ_bb.0 as usize;
                let before_init_len = block_in[s_idx].maybe_init.len();
                let before_uninit_len = block_in[s_idx].maybe_uninit.len();
                block_in[s_idx]
                    .maybe_init
                    .extend(edge_state.maybe_init.into_iter());
                block_in[s_idx]
                    .maybe_uninit
                    .extend(edge_state.maybe_uninit.into_iter());
                if block_in[s_idx].maybe_init.len() != before_init_len
                    || block_in[s_idx].maybe_uninit.len() != before_uninit_len
                {
                    changed = true;
                }
            }
        }
    }

    // 3. Verify move-check errors on the converged states
    for bb in 0..num_blocks {
        let mut state = block_in[bb].clone();
        for stmt in &func.blocks[bb].statements {
            apply_statement(program, destructors, &func, &mut state, stmt, true)?;
        }
        match &func.blocks[bb].terminator {
            Terminator::SwitchInt { discr, .. } => {
                check_and_apply_operand(program, destructors, &func, &mut state, discr, true)?;
            }
            Terminator::Call {
                func: callee, args, ..
            } => {
                check_and_apply_operand(program, destructors, &func, &mut state, callee, true)?;
                for a in args {
                    check_and_apply_operand(program, destructors, &func, &mut state, a, true)?;
                }
            }
            _ => {}
        }
    }

    // 4. Identify any dynamic drop flags needed (when a leaf path is BOTH maybe_init and maybe_uninit at a Drop)
    let mut drop_flags: BTreeMap<MovePath, LocalId> = BTreeMap::new();
    let mut new_locals = func.locals.clone();

    for bb in 0..num_blocks {
        if let Terminator::Drop { place, .. } = &func.blocks[bb].terminator
            && let Some(path) = MovePath::from_place(program, &func, place)
        {
            for leaf in expand_to_leaf_paths(program, destructors, &func, &path) {
                let leaf_place = leaf.to_place();
                let leaf_ty = place_type(program, &func, &leaf_place)?;
                if destructors.contains_key(&leaf_ty)
                    && block_out[bb].maybe_init.contains(&leaf)
                    && block_out[bb].maybe_uninit.contains(&leaf)
                    && !drop_flags.contains_key(&leaf)
                {
                    let flag_local = LocalId(new_locals.len() as u32);
                    new_locals.push(bool_ty);
                    drop_flags.insert(leaf, flag_local);
                }
            }
        }
    }

    let mut new_blocks = func.blocks.clone();

    // 5. If any dynamic drop flags exist, instrument assignments and moves to maintain the boolean flags
    if !drop_flags.is_empty() {
        for (bb_idx, blk) in new_blocks.iter_mut().enumerate().take(num_blocks) {
            let mut updated_stmts = Vec::new();
            if bb_idx == 0 {
                for (leaf, &flag_id) in &drop_flags {
                    let is_arg = (1..=func.arg_count).contains(&(leaf.local.0 as usize));
                    updated_stmts.push(Statement::Assign(
                        Place::new(flag_id),
                        Rvalue::Use(Operand::Const(ConstValue::Bool(is_arg))),
                    ));
                }
            }
            for stmt in &blk.statements {
                // Check for moves inside stmt
                if let Statement::Assign(dest, rval) = stmt {
                    let mut moved_places = Vec::new();
                    match rval {
                        Rvalue::Use(Operand::Move(p))
                        | Rvalue::UnaryOp(_, Operand::Move(p))
                        | Rvalue::Cast(Operand::Move(p), _)
                        | Rvalue::Transmute(Operand::Move(p), _)
                        | Rvalue::Union {
                            payload: Operand::Move(p),
                            ..
                        } => moved_places.push(p.clone()),
                        Rvalue::BinaryOp(_, l, r) => {
                            if let Operand::Move(p) = l {
                                moved_places.push(p.clone());
                            }
                            if let Operand::Move(p) = r {
                                moved_places.push(p.clone());
                            }
                        }
                        Rvalue::Aggregate(_, ops) => {
                            for op in ops {
                                if let Operand::Move(p) = op {
                                    moved_places.push(p.clone());
                                }
                            }
                        }
                        _ => {}
                    }
                    updated_stmts.push(stmt.clone());
                    for mp in moved_places {
                        if !place_projects_through_overlay_field(program, &func, &mp)
                            && let Some(mpath) = MovePath::from_place(program, &func, &mp)
                        {
                            for leaf in expand_to_leaf_paths(program, destructors, &func, &mpath) {
                                if let Some(&flag_id) = drop_flags.get(&leaf) {
                                    updated_stmts.push(Statement::Assign(
                                        Place::new(flag_id),
                                        Rvalue::Use(Operand::Const(ConstValue::Bool(false))),
                                    ));
                                }
                            }
                        }
                    }
                    if let Some(dpath) = MovePath::from_place(program, &func, dest) {
                        for leaf in expand_to_leaf_paths(program, destructors, &func, &dpath) {
                            if let Some(&flag_id) = drop_flags.get(&leaf) {
                                updated_stmts.push(Statement::Assign(
                                    Place::new(flag_id),
                                    Rvalue::Use(Operand::Const(ConstValue::Bool(true))),
                                ));
                            }
                        }
                    }
                } else {
                    updated_stmts.push(stmt.clone());
                }
            }
            blk.statements = updated_stmts;
        }
    }

    // 6. Rewrite every `Terminator::Drop` in `0..num_blocks`
    for bb in 0..num_blocks {
        let Terminator::Drop { place, target } = new_blocks[bb].terminator.clone() else {
            continue;
        };

        let ty_id = place_type(program, &func, &place)?;
        if !type_needs_drop(program, destructors, ty_id) {
            new_blocks[bb].terminator = Terminator::Goto { target };
            continue;
        }

        if let Some(path) = MovePath::from_place(program, &func, &place)
            && !place_projects_through_overlay_field(program, &func, &place)
        {
            let leaves = expand_to_leaf_paths(program, destructors, &func, &path);
            // Collect only the leaves that need drop and are at least `maybe_init`
            let mut active_leaves = Vec::new();
            for leaf in leaves {
                let leaf_place = leaf.to_place();
                let leaf_ty = place_type(program, &func, &leaf_place)?;
                if block_out[bb].maybe_init.contains(&leaf) {
                    if let Some(lin_name) = linear_type_name(program, leaf_ty) {
                        let is_allowed_consuming_self = leaf.local == LocalId(1)
                            && leaf.fields.is_empty()
                            && func.linear_self == Some(leaf_ty);
                        if !is_allowed_consuming_self {
                            return Err(format!(
                                "Linear value '{}' of type '{}' must be explicitly consumed before going out of scope in {}",
                                leaf_place, lin_name, func.label()
                            ));
                        }
                    }
                    if destructors.contains_key(&leaf_ty) {
                        active_leaves.push((leaf, leaf_place, leaf_ty));
                    }
                }
            }

            if active_leaves.is_empty() {
                new_blocks[bb].terminator = Terminator::Goto { target };
                continue;
            }

            // Chain the drops of `active_leaves` ending at `target`
            let mut cur_bb = bb;
            for (idx, (leaf, leaf_place, leaf_ty)) in active_leaves.iter().enumerate() {
                let next_target = if idx + 1 == active_leaves.len() {
                    target
                } else {
                    let next_bb = BlockId(new_blocks.len() as u32);
                    new_blocks.push(BasicBlock {
                        statements: Vec::new(),
                        terminator: Terminator::Unreachable,
                    });
                    next_bb
                };

                let dtor_fn = destructors[leaf_ty];
                let ptr_ty = program.intern_type(Type::Ptr {
                    mutable: true,
                    pointee: *leaf_ty,
                });
                let ptr_local = LocalId(new_locals.len() as u32);
                new_locals.push(ptr_ty);
                let unit_local = LocalId(new_locals.len() as u32);
                new_locals.push(unit_ty);

                if let Some(&flag_id) = drop_flags.get(leaf) {
                    // Dynamic drop flag check
                    let call_bb = BlockId(new_blocks.len() as u32);
                    new_blocks.push(BasicBlock {
                        statements: vec![
                            Statement::Assign(
                                Place::new(flag_id),
                                Rvalue::Use(Operand::Const(ConstValue::Bool(false))),
                            ),
                            Statement::Assign(
                                Place::new(ptr_local),
                                Rvalue::Ref {
                                    mutable: true,
                                    place: leaf_place.clone(),
                                },
                            ),
                        ],
                        terminator: Terminator::Call {
                            func: Operand::Const(ConstValue::Func(dtor_fn)),
                            args: vec![Operand::Move(Place::new(ptr_local))],
                            destination: Place::new(unit_local),
                            target: next_target,
                        },
                    });
                    new_blocks[cur_bb].terminator = Terminator::SwitchInt {
                        discr: Operand::Copy(Place::new(flag_id)),
                        targets: vec![(1, call_bb)],
                        otherwise: next_target,
                    };
                } else {
                    // Statically initialized drop
                    new_blocks[cur_bb].statements.push(Statement::Assign(
                        Place::new(ptr_local),
                        Rvalue::Ref {
                            mutable: true,
                            place: leaf_place.clone(),
                        },
                    ));
                    new_blocks[cur_bb].terminator = Terminator::Call {
                        func: Operand::Const(ConstValue::Func(dtor_fn)),
                        args: vec![Operand::Move(Place::new(ptr_local))],
                        destination: Place::new(unit_local),
                        target: next_target,
                    };
                }

                cur_bb = next_target.0 as usize;
            }
        } else {
            if let Some(lin_name) = linear_type_name(program, ty_id) {
                return Err(format!(
                    "Linear value '{}' of type '{}' cannot be dropped via `@drop` in {}; call a consuming method instead",
                    place, lin_name, func.label()
                ));
            }
            // Deref/Index/Overlay-field place drop: unconditionally call destructor(s) if registered
            let mut suffixes = Vec::new();
            let mut prefix = Vec::new();
            collect_leaf_paths_for_type(program, destructors, ty_id, &mut prefix, &mut suffixes);
            let mut drop_targets = Vec::new();
            for suffix in suffixes {
                let mut leaf_place = place.clone();
                for f in suffix {
                    leaf_place.projections.push(Projection::Field(f));
                }
                let leaf_ty = place_type(program, &func, &leaf_place)?;
                if let Some(&dtor_fn) = destructors.get(&leaf_ty) {
                    drop_targets.push((leaf_place, leaf_ty, dtor_fn));
                }
            }
            if drop_targets.is_empty() {
                new_blocks[bb].terminator = Terminator::Goto { target };
            } else {
                let total_drops = drop_targets.len();
                let mut cur_bb = bb;
                for (idx, (leaf_place, leaf_ty, dtor_fn)) in drop_targets.into_iter().enumerate() {
                    let next_target = if idx + 1 == total_drops {
                        target
                    } else {
                        let next_bb = BlockId(new_blocks.len() as u32);
                        new_blocks.push(BasicBlock {
                            statements: Vec::new(),
                            terminator: Terminator::Unreachable,
                        });
                        next_bb
                    };
                    let ptr_ty = program.intern_type(Type::Ptr {
                        mutable: true,
                        pointee: leaf_ty,
                    });
                    let ptr_local = LocalId(new_locals.len() as u32);
                    new_locals.push(ptr_ty);
                    let unit_local = LocalId(new_locals.len() as u32);
                    new_locals.push(unit_ty);

                    new_blocks[cur_bb].statements.push(Statement::Assign(
                        Place::new(ptr_local),
                        Rvalue::Ref {
                            mutable: true,
                            place: leaf_place,
                        },
                    ));
                    new_blocks[cur_bb].terminator = Terminator::Call {
                        func: Operand::Const(ConstValue::Func(dtor_fn)),
                        args: vec![Operand::Move(Place::new(ptr_local))],
                        destination: Place::new(unit_local),
                        target: next_target,
                    };
                    cur_bb = next_target.0 as usize;
                }
            }
        }
    }

    program.functions[func_idx].locals = new_locals;
    program.functions[func_idx].blocks = new_blocks;
    Ok(())
}
