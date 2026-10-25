use std::collections::{BTreeMap, BTreeSet};

use crate::ir::{
    BlockId, ConstValue, FuncId, Function, LocalId, Operand, Place, Program, Projection, Rvalue,
    Statement, Terminator, Type,
};

#[derive(Debug, Clone, PartialEq, Eq)]
struct Loan {
    place: Place,
    mutable: bool,
}

/// Runs Non-Lexical Lifetimes (NLL) Borrow Checking on all functions in `program`.
///
/// Enforces:
/// 1. **Aliasing XOR Mutability**:
///    - `&mut P` conflicts with any live `&P` or `&mut P` on an overlapping place.
///    - `&P` conflicts with any live `&mut P` on an overlapping place.
/// 2. **No Mutation While Borrowed**:
///    - Assigning to, moving from, or dropping `P` conflicts with any live `&P` or `&mut P`.
/// 3. **No Reads While Mutably Borrowed**:
///    - Reading (`copy`, `move`, `discriminant`) `P` conflicts with any live `&mut P`.
/// 4. **Reference Mutability & No Moving Behind References**:
///    - Writing through or taking `&mut` through an immutable reference (`&T`) is rejected.
///    - Moving (`move (*_p)`) out of a dereferenced pointer is rejected.
/// 5. **Lifetime / Stack Discipline (`StorageDead`, Return, & Interprocedural `borrows(...)` Contracts)**:
///    - `StorageDead(_x)` while a loan of `_x` is still live is rejected.
///    - Returning a reference derived from a local stack variable is rejected.
///    - Functions with an explicit `borrows(_1, ...)` contract are checked locally against that contract,
///      while unannotated internal functions have their return-borrow summary inferred automatically.
pub fn check_borrows(program: &Program) -> Result<(), String> {
    let (inferred_origins, param_flows) = infer_borrow_summaries(program);
    let mut effective_summaries: BTreeMap<FuncId, BTreeSet<LocalId>> = BTreeMap::new();
    let mut effective_param_flows: ParamFlows = BTreeMap::new();
    for func in &program.functions {
        if let Some(explicit) = &func.ret_borrows {
            effective_summaries.insert(func.id, explicit.iter().copied().collect());
        } else {
            effective_summaries.insert(
                func.id,
                inferred_origins.get(&func.id).cloned().unwrap_or_default(),
            );
        }
        if let Some(explicit_pf) = &func.param_borrows {
            let mut map: BTreeMap<LocalId, BTreeSet<LocalId>> = BTreeMap::new();
            for &(dst, src) in explicit_pf {
                map.entry(dst).or_default().insert(src);
            }
            effective_param_flows.insert(func.id, map);
        } else {
            effective_param_flows.insert(
                func.id,
                param_flows.get(&func.id).cloned().unwrap_or_default(),
            );
        }
    }

    for func in &program.functions {
        if let Some(explicit) = &func.ret_borrows
            && let Some(actual_origins) = inferred_origins.get(&func.id)
        {
            for &origin_param in actual_origins {
                if !explicit.contains(&origin_param) {
                    return Err(format!(
                        "Borrow check error in {}: return value borrows from parameter '{}', which is not permitted by explicit contract borrows({})",
                        func.id,
                        origin_param,
                        explicit
                            .iter()
                            .map(ToString::to_string)
                            .collect::<Vec<_>>()
                            .join(", ")
                    ));
                }
            }
        }
        if let Some(explicit_pf) = &func.param_borrows
            && let Some(actual_pf) = param_flows.get(&func.id)
        {
            for (&dst_param, src_set) in actual_pf {
                for &src_param in src_set {
                    if dst_param != src_param && !explicit_pf.contains(&(dst_param, src_param)) {
                        return Err(format!(
                            "Borrow check error in {}: parameter '{}' borrows from parameter '{}', which is not permitted by explicit borrows(...) contract",
                            func.id, dst_param, src_param
                        ));
                    }
                }
            }
        }
        check_function(program, func, &effective_summaries, &effective_param_flows)?;
    }
    Ok(())
}

type ParamFlows = BTreeMap<FuncId, BTreeMap<LocalId, BTreeSet<LocalId>>>;

/// Computes, for every function in `program`:
/// 1. Which 1-based parameter locals (`_1..=arg_count`) its return place `_0` may borrow from at `return;`.
/// 2. Which parameter locals may flow into which other mutable parameter locals (`param_flows`, e.g. `stash(dst, x)`).
fn infer_borrow_summaries(program: &Program) -> (BTreeMap<FuncId, BTreeSet<LocalId>>, ParamFlows) {
    let mut inferred: BTreeMap<FuncId, BTreeSet<LocalId>> = BTreeMap::new();
    let mut param_flows: ParamFlows = BTreeMap::new();
    for func in &program.functions {
        inferred.insert(func.id, BTreeSet::new());
        param_flows.insert(func.id, BTreeMap::new());
    }

    let mut global_changed = true;
    while global_changed {
        global_changed = false;
        for func in &program.functions {
            let num_blocks = func.blocks.len();
            if num_blocks == 0 {
                continue;
            }
            type Origins = BTreeMap<LocalId, BTreeSet<LocalId>>;
            let mut origins_in: Vec<Origins> = vec![BTreeMap::new(); num_blocks];
            for i in 1..=func.arg_count {
                let param = LocalId(i as u32);
                origins_in[0].insert(param, BTreeSet::from([param]));
            }

            let mut local_changed = true;
            while local_changed {
                local_changed = false;
                for bb in 0..num_blocks {
                    let mut orig = origins_in[bb].clone();
                    for stmt in &func.blocks[bb].statements {
                        match stmt {
                            Statement::StorageLive(l) | Statement::StorageDead(l) => {
                                orig.remove(l);
                            }
                            Statement::SetDiscriminant(_, _) => {}
                            Statement::Assign(dest, rval) => {
                                let mut rhs = BTreeSet::new();
                                match rval {
                                    Rvalue::Use(op)
                                    | Rvalue::UnaryOp(_, op)
                                    | Rvalue::Cast(op, _)
                                    | Rvalue::Union { payload: op, .. } => {
                                        if let Operand::Copy(p) | Operand::Move(p) = op
                                            && place_type_contains_ptr(program, func, p)
                                            && let Some(os) = orig.get(&p.local)
                                        {
                                            rhs.extend(os.iter().copied());
                                        }
                                    }
                                    Rvalue::BinaryOp(_, l, r) => {
                                        for op in [l, r] {
                                            if let Operand::Copy(p) | Operand::Move(p) = op
                                                && place_type_contains_ptr(program, func, p)
                                                && let Some(os) = orig.get(&p.local)
                                            {
                                                rhs.extend(os.iter().copied());
                                            }
                                        }
                                    }
                                    Rvalue::Ref { place, .. } => {
                                        if place.projections.contains(&Projection::Deref)
                                            && let Some(os) = orig.get(&place.local)
                                        {
                                            rhs.extend(os.iter().copied());
                                        }
                                    }
                                    Rvalue::Aggregate(_, ops) => {
                                        for op in ops {
                                            if let Operand::Copy(p) | Operand::Move(p) = op
                                                && place_type_contains_ptr(program, func, p)
                                                && let Some(os) = orig.get(&p.local)
                                            {
                                                rhs.extend(os.iter().copied());
                                            }
                                        }
                                    }
                                    Rvalue::Discriminant(_)
                                    | Rvalue::ArrayType { .. }
                                    | Rvalue::SimdType { .. }
                                    | Rvalue::OverlayType(_)
                                    | Rvalue::UnionType { .. }
                                    | Rvalue::PatternType { .. } => {}
                                }
                                let dest_has_ptr = place_type_contains_ptr(program, func, dest);
                                if !dest_has_ptr {
                                    if dest.projections.is_empty() {
                                        orig.remove(&dest.local);
                                    }
                                } else if dest.projections.is_empty() {
                                    if rhs.is_empty() {
                                        orig.remove(&dest.local);
                                    } else {
                                        orig.insert(dest.local, rhs);
                                    }
                                } else if !rhs.is_empty() {
                                    if dest.projections.contains(&Projection::Deref)
                                        && let Some(owners) = orig.get(&dest.local).cloned()
                                    {
                                        for owner in owners {
                                            orig.entry(owner)
                                                .or_default()
                                                .extend(rhs.iter().copied());
                                        }
                                    }
                                    orig.entry(dest.local).or_default().extend(rhs);
                                }
                            }
                        }
                    }

                    let mut succs: Vec<(BlockId, Origins)> = Vec::new();
                    match &func.blocks[bb].terminator {
                        Terminator::Goto { target } | Terminator::Drop { target, .. } => {
                            succs.push((*target, orig));
                        }
                        Terminator::SwitchInt {
                            targets, otherwise, ..
                        } => {
                            for (_, t) in targets {
                                succs.push((*t, orig.clone()));
                            }
                            succs.push((*otherwise, orig));
                        }
                        Terminator::Call {
                            func: callee_op,
                            args,
                            destination,
                            target,
                        } => {
                            let mut call_origins = BTreeSet::new();
                            if let Operand::Const(ConstValue::Func(callee_id)) = callee_op
                                && let Some(callee_fn) =
                                    program.functions.iter().find(|f| f.id == *callee_id)
                            {
                                let summary: BTreeSet<LocalId> =
                                    if let Some(explicit) = &callee_fn.ret_borrows {
                                        explicit.iter().copied().collect()
                                    } else {
                                        inferred.get(callee_id).cloned().unwrap_or_default()
                                    };
                                for param in summary {
                                    let idx = param.0.saturating_sub(1) as usize;
                                    if let Some(Operand::Copy(p) | Operand::Move(p)) = args.get(idx)
                                        && let Some(os) = orig.get(&p.local)
                                    {
                                        call_origins.extend(os.iter().copied());
                                    }
                                }
                                let callee_flows: BTreeMap<LocalId, BTreeSet<LocalId>> =
                                    if let Some(explicit_pf) = &callee_fn.param_borrows {
                                        let mut m: BTreeMap<LocalId, BTreeSet<LocalId>> =
                                            BTreeMap::new();
                                        for &(dst_p, src_p) in explicit_pf {
                                            m.entry(dst_p).or_default().insert(src_p);
                                        }
                                        m
                                    } else {
                                        param_flows.get(callee_id).cloned().unwrap_or_default()
                                    };
                                for (&dst_param, src_params) in &callee_flows {
                                    let dst_idx = dst_param.0.saturating_sub(1) as usize;
                                    let mut flowed = BTreeSet::new();
                                    for &sp in src_params {
                                        let s_idx = sp.0.saturating_sub(1) as usize;
                                        if let Some(Operand::Copy(p) | Operand::Move(p)) =
                                            args.get(s_idx)
                                            && let Some(os) = orig.get(&p.local)
                                        {
                                            flowed.extend(os.iter().copied());
                                        }
                                    }
                                    if !flowed.is_empty()
                                        && let Some(Operand::Copy(dp) | Operand::Move(dp)) =
                                            args.get(dst_idx)
                                    {
                                        if let Some(owners) = orig.get(&dp.local).cloned() {
                                            for owner in owners {
                                                orig.entry(owner)
                                                    .or_default()
                                                    .extend(flowed.iter().copied());
                                            }
                                        }
                                        orig.entry(dp.local).or_default().extend(flowed);
                                    }
                                }
                            } else {
                                for a in args {
                                    if let Operand::Copy(p) | Operand::Move(p) = a
                                        && let Some(os) = orig.get(&p.local)
                                    {
                                        call_origins.extend(os.iter().copied());
                                    }
                                }
                            }

                            let dest_has_ptr = func
                                .locals
                                .get(destination.local.0 as usize)
                                .is_some_and(|&t| type_contains_ptr(program, t));
                            if !dest_has_ptr {
                                orig.remove(&destination.local);
                            } else if destination.projections.is_empty() {
                                if call_origins.is_empty() {
                                    orig.remove(&destination.local);
                                } else {
                                    orig.insert(destination.local, call_origins);
                                }
                            } else if !call_origins.is_empty() {
                                orig.entry(destination.local)
                                    .or_default()
                                    .extend(call_origins);
                            }
                            succs.push((*target, orig));
                        }
                        Terminator::Return => {
                            if let Some(ret_os) = orig.get(&LocalId(0)) {
                                let entry = inferred.entry(func.id).or_default();
                                let before = entry.len();
                                entry.extend(ret_os.iter().copied());
                                if entry.len() != before {
                                    global_changed = true;
                                }
                            }
                            for i in 1..=func.arg_count {
                                let param = LocalId(i as u32);
                                if let Some(p_os) = orig.get(&param) {
                                    for &src_p in p_os {
                                        if src_p != param {
                                            let f_entry = param_flows
                                                .entry(func.id)
                                                .or_default()
                                                .entry(param)
                                                .or_default();
                                            if f_entry.insert(src_p) {
                                                global_changed = true;
                                            }
                                        }
                                    }
                                }
                            }
                        }
                        Terminator::Unreachable => {}
                    }

                    for (succ_bb, edge_orig) in succs {
                        let s_idx = succ_bb.0 as usize;
                        for (loc, oset) in edge_orig {
                            let entry = origins_in[s_idx].entry(loc).or_default();
                            let before = entry.len();
                            entry.extend(oset);
                            if entry.len() != before {
                                local_changed = true;
                            }
                        }
                    }
                }
            }
        }
    }

    (inferred, param_flows)
}

/// Checks if two places `a` and `b` may refer to overlapping memory locations.
fn places_overlap(a: &Place, b: &Place) -> bool {
    if a.local != b.local {
        return false;
    }
    for (pa, pb) in a.projections.iter().zip(b.projections.iter()) {
        match (pa, pb) {
            (Projection::Deref, Projection::Deref) => continue,
            (Projection::Field(fa), Projection::Field(fb)) if fa == fb => continue,
            (Projection::Variant(va), Projection::Variant(vb)) if va == vb => continue,
            // Two dynamic array indices `_a[_i]` and `_a[_j]` may alias at runtime
            (Projection::Index(_), Projection::Index(_)) => continue,
            _ => return false,
        }
    }
    true
}

/// Validates whether `place` traverses an immutable reference (`&T`) when `require_mut` is true,
/// or traverses any reference when `is_move` is true.
fn check_deref_permissions(
    program: &Program,
    func: &Function,
    place: &Place,
    require_mut: bool,
    is_move: bool,
) -> Result<(), String> {
    let mut cur_ty = *func
        .locals
        .get(place.local.0 as usize)
        .ok_or_else(|| format!("Undefined local {} in {}", place.local, func.id))?;

    for proj in &place.projections {
        match proj {
            Projection::Deref => {
                let Some(Type::Ptr { mutable, pointee }) = program.types.get(cur_ty.0 as usize)
                else {
                    return Err(format!("Cannot deref non-pointer type {cur_ty}"));
                };
                if (require_mut || is_move) && !*mutable {
                    return Err(format!(
                        "Cannot mutate, move out of, or mutably borrow '{}' through an immutable reference in {}",
                        place, func.id
                    ));
                }
                cur_ty = *pointee;
            }
            Projection::Field(idx) => match program.types.get(cur_ty.0 as usize) {
                Some(Type::Struct(fields) | Type::Overlay(fields)) => {
                    cur_ty = *fields
                        .get(*idx as usize)
                        .ok_or_else(|| format!("Field .{idx} out of bounds on {cur_ty}"))?;
                }
                _ => return Err(format!("Cannot access field .{idx} on {cur_ty}")),
            },
            Projection::Variant(v_idx) => {
                let Some(Type::Union { variants, .. }) = program.types.get(cur_ty.0 as usize)
                else {
                    return Err(format!("Cannot access variant .v{v_idx} on {cur_ty}"));
                };
                cur_ty = *variants
                    .get(*v_idx as usize)
                    .ok_or_else(|| format!("Variant .v{v_idx} out of bounds on {cur_ty}"))?;
            }
            Projection::Index(_) => {
                let Some(Type::Array { elem, .. } | Type::Simd { elem, .. }) =
                    program.types.get(cur_ty.0 as usize)
                else {
                    return Err(format!("Cannot index non-array/simd type {cur_ty}"));
                };
                cur_ty = *elem;
            }
        }
    }
    Ok(())
}

/// Collects all locals whose values are read when evaluating/accessing `place`.
/// - If `is_lhs_write` is true (`place = ...`), the base local is only read if `place` has projections
///   that dereference it (`(*_p) = ...` reads `_p`); field/index writes also read any index locals.
fn collect_place_reads(place: &Place, is_lhs_write: bool, out: &mut BTreeSet<LocalId>) {
    if !is_lhs_write || place.projections.contains(&Projection::Deref) {
        out.insert(place.local);
    }
    for proj in &place.projections {
        if let Projection::Index(idx_local) = proj {
            out.insert(*idx_local);
        }
    }
}

fn collect_operand_reads(op: &Operand, out: &mut BTreeSet<LocalId>) {
    if let Operand::Copy(p) | Operand::Move(p) = op {
        collect_place_reads(p, false, out);
    }
}

fn type_contains_ptr(program: &Program, ty_id: crate::ir::TypeId) -> bool {
    match program.types.get(ty_id.0 as usize) {
        Some(Type::Ptr { .. }) => true,
        Some(
            Type::Struct(fields)
            | Type::Overlay(fields)
            | Type::Union {
                variants: fields, ..
            },
        ) => fields.iter().any(|&f| type_contains_ptr(program, f)),
        Some(Type::Array { elem, .. }) => type_contains_ptr(program, *elem),
        _ => false,
    }
}

fn place_type_contains_ptr(program: &Program, func: &Function, place: &Place) -> bool {
    let Some(&(mut cur_ty)) = func.locals.get(place.local.0 as usize) else {
        return false;
    };
    for proj in &place.projections {
        match proj {
            Projection::Deref => {
                let Some(Type::Ptr { pointee, .. }) = program.types.get(cur_ty.0 as usize) else {
                    return false;
                };
                cur_ty = *pointee;
            }
            Projection::Field(idx) => {
                let Some(Type::Struct(fields) | Type::Overlay(fields)) =
                    program.types.get(cur_ty.0 as usize)
                else {
                    return false;
                };
                let Some(&fty) = fields.get(*idx as usize) else {
                    return false;
                };
                cur_ty = fty;
            }
            Projection::Variant(idx) => {
                let Some(Type::Union { variants, .. }) = program.types.get(cur_ty.0 as usize)
                else {
                    return false;
                };
                let Some(&vty) = variants.get(*idx as usize) else {
                    return false;
                };
                cur_ty = vty;
            }
            Projection::Index(_) => {
                let Some(Type::Array { elem, .. } | Type::Simd { elem, .. }) =
                    program.types.get(cur_ty.0 as usize)
                else {
                    return false;
                };
                cur_ty = *elem;
            }
        }
    }
    type_contains_ptr(program, cur_ty)
}

fn statement_reads_and_def(
    program: &Program,
    func: &Function,
    stmt: &Statement,
) -> (BTreeSet<LocalId>, Option<LocalId>) {
    let mut reads = BTreeSet::new();
    let mut def = None;

    match stmt {
        Statement::StorageLive(l) | Statement::StorageDead(l) => {
            def = Some(*l);
        }
        Statement::SetDiscriminant(place, _) => {
            collect_place_reads(place, true, &mut reads);
        }
        Statement::Assign(dest, rval) => {
            if dest.projections.is_empty() {
                def = Some(dest.local);
            } else {
                collect_place_reads(dest, true, &mut reads);
            }
            match rval {
                Rvalue::Use(op) | Rvalue::UnaryOp(_, op) | Rvalue::Cast(op, _) => {
                    collect_operand_reads(op, &mut reads);
                }
                Rvalue::BinaryOp(_, l, r) => {
                    collect_operand_reads(l, &mut reads);
                    collect_operand_reads(r, &mut reads);
                }
                Rvalue::Ref { place, .. } => {
                    // Taking `&(*_p).0` reads the pointer `_p`, and borrowing a composite/closure
                    // that holds pointers inside its fields keeps that composite live!
                    if place.projections.contains(&Projection::Deref)
                        || func
                            .locals
                            .get(place.local.0 as usize)
                            .is_some_and(|&t| type_contains_ptr(program, t))
                    {
                        reads.insert(place.local);
                    }
                    for proj in &place.projections {
                        if let Projection::Index(idx_local) = proj {
                            reads.insert(*idx_local);
                        }
                    }
                }
                Rvalue::Aggregate(_, ops) | Rvalue::OverlayType(ops) => {
                    for op in ops {
                        collect_operand_reads(op, &mut reads);
                    }
                }
                Rvalue::ArrayType { elem, len } | Rvalue::SimdType { elem, len } => {
                    collect_operand_reads(elem, &mut reads);
                    collect_operand_reads(len, &mut reads);
                }
                Rvalue::UnionType { tag, variants } => {
                    collect_operand_reads(tag, &mut reads);
                    for op in variants {
                        collect_operand_reads(op, &mut reads);
                    }
                }
                Rvalue::PatternType { base, ranges } => {
                    collect_operand_reads(base, &mut reads);
                    for (lo, hi) in ranges {
                        collect_operand_reads(lo, &mut reads);
                        collect_operand_reads(hi, &mut reads);
                    }
                }
                Rvalue::Union { payload, .. } => {
                    collect_operand_reads(payload, &mut reads);
                }
                Rvalue::Discriminant(place) => {
                    collect_place_reads(place, false, &mut reads);
                }
            }
        }
    }

    (reads, def)
}

fn terminator_reads_and_def(term: &Terminator) -> (BTreeSet<LocalId>, Option<LocalId>) {
    let mut reads = BTreeSet::new();
    let mut def = None;

    match term {
        Terminator::Goto { .. } | Terminator::Unreachable => {}
        Terminator::Return => {
            reads.insert(LocalId(0));
        }
        Terminator::SwitchInt { discr, .. } => {
            collect_operand_reads(discr, &mut reads);
        }
        Terminator::Call {
            func,
            args,
            destination,
            ..
        } => {
            if destination.projections.is_empty() {
                def = Some(destination.local);
            } else {
                collect_place_reads(destination, true, &mut reads);
            }
            collect_operand_reads(func, &mut reads);
            for a in args {
                collect_operand_reads(a, &mut reads);
            }
        }
        Terminator::Drop { place, .. } => {
            collect_place_reads(place, false, &mut reads);
        }
    }

    (reads, def)
}

fn check_function(
    program: &Program,
    func: &Function,
    effective_summaries: &BTreeMap<FuncId, BTreeSet<LocalId>>,
    param_flows: &ParamFlows,
) -> Result<(), String> {
    // Skip comptime-only type functions where `&T` constructs a pointer `Type` rather than borrowing memory
    let is_comptime_only = func
        .locals
        .iter()
        .any(|&ty_id| matches!(program.types.get(ty_id.0 as usize), Some(Type::MetaType)));
    if is_comptime_only {
        return Ok(());
    }

    let num_blocks = func.blocks.len();
    if num_blocks == 0 {
        return Ok(());
    }

    // 1. Backward Liveness Analysis for Locals
    // `live_out[bb]` is the set of locals live at the exit of `bb`.
    // `live_in[bb]` is the set of locals live at the entry of `bb`.
    let mut live_in: Vec<BTreeSet<LocalId>> = vec![BTreeSet::new(); num_blocks];
    let mut live_out: Vec<BTreeSet<LocalId>> = vec![BTreeSet::new(); num_blocks];

    let mut changed = true;
    while changed {
        changed = false;
        for bb in (0..num_blocks).rev() {
            let block = &func.blocks[bb];
            let mut out = BTreeSet::new();
            match &block.terminator {
                Terminator::Goto { target }
                | Terminator::Call { target, .. }
                | Terminator::Drop { target, .. } => {
                    out.extend(live_in[target.0 as usize].iter().copied());
                }
                Terminator::SwitchInt {
                    targets, otherwise, ..
                } => {
                    for (_, t) in targets {
                        out.extend(live_in[t.0 as usize].iter().copied());
                    }
                    out.extend(live_in[otherwise.0 as usize].iter().copied());
                }
                Terminator::Return | Terminator::Unreachable => {}
            }

            if live_out[bb] != out {
                live_out[bb] = out.clone();
                changed = true;
            }

            // Walk backward through terminator then statements
            let (t_reads, t_def) = terminator_reads_and_def(&block.terminator);
            if let Some(d) = t_def {
                out.remove(&d);
            }
            out.extend(t_reads);

            for stmt in block.statements.iter().rev() {
                let (s_reads, s_def) = statement_reads_and_def(program, func, stmt);
                if let Some(d) = s_def {
                    out.remove(&d);
                }
                out.extend(s_reads);
            }

            if live_in[bb] != out {
                live_in[bb] = out;
                changed = true;
            }
        }
    }

    // 2. Assign a unique `Loan` to every `Rvalue::Ref` in the function
    let mut loans: Vec<Loan> = Vec::new();
    let mut ref_loan_map: BTreeMap<(usize, usize), usize> = BTreeMap::new();
    for (bb_idx, blk) in func.blocks.iter().enumerate() {
        for (stmt_idx, stmt) in blk.statements.iter().enumerate() {
            if let Statement::Assign(_, Rvalue::Ref { mutable, place }) = stmt {
                let id = loans.len();
                loans.push(Loan {
                    place: place.clone(),
                    mutable: *mutable,
                });
                ref_loan_map.insert((bb_idx, stmt_idx), id);
            }
        }
    }

    // 3. Forward Points-To / Loan Propagation Dataflow Analysis
    // `points_to_in[bb]` maps `LocalId -> BTreeSet<LoanId>` (which loans a reference local may hold).
    type PointsTo = BTreeMap<LocalId, BTreeSet<usize>>;
    let mut points_to_in: Vec<PointsTo> = vec![BTreeMap::new(); num_blocks];

    let apply_points_to_stmt =
        |bb_idx: usize, stmt_idx: usize, stmt: &Statement, pt: &mut PointsTo| {
            match stmt {
                Statement::StorageLive(l) | Statement::StorageDead(l) => {
                    pt.remove(l);
                }
                Statement::SetDiscriminant(_, _) => {}
                Statement::Assign(dest, rval) => {
                    let mut rhs_loans = BTreeSet::new();
                    match rval {
                        Rvalue::Use(op) | Rvalue::UnaryOp(_, op) | Rvalue::Cast(op, _) => {
                            if let Operand::Copy(p) | Operand::Move(p) = op
                                && place_type_contains_ptr(program, func, p)
                                && let Some(ls) = pt.get(&p.local)
                            {
                                rhs_loans.extend(ls.iter().copied());
                            }
                        }
                        Rvalue::BinaryOp(_, l, r) => {
                            for op in [l, r] {
                                if let Operand::Copy(p) | Operand::Move(p) = op
                                    && place_type_contains_ptr(program, func, p)
                                    && let Some(ls) = pt.get(&p.local)
                                {
                                    rhs_loans.extend(ls.iter().copied());
                                }
                            }
                        }
                        Rvalue::Ref { place, .. } => {
                            let loan_id = ref_loan_map[&(bb_idx, stmt_idx)];
                            rhs_loans.insert(loan_id);
                            // If reborrowing through a pointer (`&(*_p)`) or borrowing a composite/closure
                            // that holds loans in its fields, inherit `_p`'s underlying loans too!
                            if let Some(ls) = pt.get(&place.local) {
                                rhs_loans.extend(ls.iter().copied());
                            }
                        }
                        Rvalue::Aggregate(_, ops) => {
                            for op in ops {
                                if let Operand::Copy(p) | Operand::Move(p) = op
                                    && place_type_contains_ptr(program, func, p)
                                    && let Some(ls) = pt.get(&p.local)
                                {
                                    rhs_loans.extend(ls.iter().copied());
                                }
                            }
                        }
                        Rvalue::Union { payload, .. } => {
                            if let Operand::Copy(p) | Operand::Move(p) = payload
                                && place_type_contains_ptr(program, func, p)
                                && let Some(ls) = pt.get(&p.local)
                            {
                                rhs_loans.extend(ls.iter().copied());
                            }
                        }
                        Rvalue::Discriminant(_)
                        | Rvalue::ArrayType { .. }
                        | Rvalue::SimdType { .. }
                        | Rvalue::OverlayType(_)
                        | Rvalue::UnionType { .. }
                        | Rvalue::PatternType { .. } => {}
                    }

                    let dest_has_ptr = place_type_contains_ptr(program, func, dest);
                    if !dest_has_ptr {
                        if dest.projections.is_empty() {
                            pt.remove(&dest.local);
                        }
                    } else if dest.projections.is_empty() {
                        if rhs_loans.is_empty() {
                            pt.remove(&dest.local);
                        } else {
                            pt.insert(dest.local, rhs_loans);
                        }
                    } else if !rhs_loans.is_empty() {
                        if dest.projections.contains(&Projection::Deref)
                            && let Some(ptr_loans) = pt.get(&dest.local).cloned()
                        {
                            for l_id in ptr_loans {
                                let target_loc = loans[l_id].place.local;
                                pt.entry(target_loc)
                                    .or_default()
                                    .extend(rhs_loans.iter().copied());
                            }
                        }
                        pt.entry(dest.local).or_default().extend(rhs_loans);
                    }
                }
            }
        };

    let mut pt_changed = true;
    while pt_changed {
        pt_changed = false;
        for bb in 0..num_blocks {
            let mut pt = points_to_in[bb].clone();
            for (stmt_idx, stmt) in func.blocks[bb].statements.iter().enumerate() {
                apply_points_to_stmt(bb, stmt_idx, stmt, &mut pt);
            }

            let mut succs: Vec<(BlockId, PointsTo)> = Vec::new();
            match &func.blocks[bb].terminator {
                Terminator::Goto { target } | Terminator::Drop { target, .. } => {
                    succs.push((*target, pt));
                }
                Terminator::SwitchInt {
                    targets, otherwise, ..
                } => {
                    for (_, t) in targets {
                        succs.push((*t, pt.clone()));
                    }
                    succs.push((*otherwise, pt));
                }
                Terminator::Call {
                    func: callee_op,
                    args,
                    destination,
                    target,
                } => {
                    let mut arg_loans = BTreeSet::new();
                    if let Operand::Const(ConstValue::Func(callee_id)) = callee_op
                        && let Some(summary) = effective_summaries.get(callee_id)
                    {
                        for param in summary {
                            let idx = param.0.saturating_sub(1) as usize;
                            if let Some(Operand::Copy(p) | Operand::Move(p)) = args.get(idx)
                                && let Some(ls) = pt.get(&p.local)
                            {
                                arg_loans.extend(ls.iter().copied());
                            }
                        }
                        if let Some(flows) = param_flows.get(callee_id) {
                            for (&dst_param, src_params) in flows {
                                let dst_idx = dst_param.0.saturating_sub(1) as usize;
                                let mut flowed_loans = BTreeSet::new();
                                for &sp in src_params {
                                    let s_idx = sp.0.saturating_sub(1) as usize;
                                    if let Some(Operand::Copy(p) | Operand::Move(p)) =
                                        args.get(s_idx)
                                        && let Some(ls) = pt.get(&p.local)
                                    {
                                        flowed_loans.extend(ls.iter().copied());
                                    }
                                }
                                if !flowed_loans.is_empty()
                                    && let Some(Operand::Copy(dp) | Operand::Move(dp)) =
                                        args.get(dst_idx)
                                {
                                    if let Some(dst_ptr_loans) = pt.get(&dp.local).cloned() {
                                        for l_id in dst_ptr_loans {
                                            let target_loc = loans[l_id].place.local;
                                            pt.entry(target_loc)
                                                .or_default()
                                                .extend(flowed_loans.iter().copied());
                                        }
                                    }
                                    pt.entry(dp.local).or_default().extend(flowed_loans);
                                }
                            }
                        }
                    } else {
                        for a in args {
                            if let Operand::Copy(p) | Operand::Move(p) = a
                                && let Some(ls) = pt.get(&p.local)
                            {
                                arg_loans.extend(ls.iter().copied());
                            }
                        }
                    }
                    let dest_has_ptr = func
                        .locals
                        .get(destination.local.0 as usize)
                        .is_some_and(|&t| type_contains_ptr(program, t));
                    if !dest_has_ptr {
                        pt.remove(&destination.local);
                    } else if destination.projections.is_empty() {
                        if arg_loans.is_empty() {
                            pt.remove(&destination.local);
                        } else {
                            pt.insert(destination.local, arg_loans);
                        }
                    } else if !arg_loans.is_empty() {
                        pt.entry(destination.local).or_default().extend(arg_loans);
                    }
                    succs.push((*target, pt));
                }
                Terminator::Return | Terminator::Unreachable => {}
            }

            for (succ_bb, edge_pt) in succs {
                let s_idx = succ_bb.0 as usize;
                for (loc, lset) in edge_pt {
                    let entry = points_to_in[s_idx].entry(loc).or_default();
                    let before = entry.len();
                    entry.extend(lset);
                    if entry.len() != before {
                        pt_changed = true;
                    }
                }
            }
        }
    }

    // 4. Check Every Statement and Terminator Against Active (Live) Loans
    for bb in 0..num_blocks {
        let block = &func.blocks[bb];

        // Compute the exact set of live locals AFTER each statement `i` (`live_after_stmt[i]`)
        // and AFTER the terminator (`live_out[bb]`).
        let mut live_after_stmt: Vec<BTreeSet<LocalId>> =
            vec![BTreeSet::new(); block.statements.len()];
        let mut cur_live = live_out[bb].clone();
        let (t_reads, t_def) = terminator_reads_and_def(&block.terminator);
        if let Some(d) = t_def {
            cur_live.remove(&d);
        }
        cur_live.extend(t_reads);

        for (i, stmt) in block.statements.iter().enumerate().rev() {
            live_after_stmt[i] = cur_live.clone();
            let (s_reads, s_def) = statement_reads_and_def(program, func, stmt);
            if let Some(d) = s_def {
                cur_live.remove(&d);
            }
            cur_live.extend(s_reads);
        }

        let mut pt = points_to_in[bb].clone();

        let active_loans_for =
            |pt_map: &PointsTo, live_locals: &BTreeSet<LocalId>| -> BTreeSet<usize> {
                let mut active = BTreeSet::new();
                for &loc in live_locals {
                    if let Some(ls) = pt_map.get(&loc) {
                        active.extend(ls.iter().copied());
                    }
                }
                active
            };

        for (stmt_idx, stmt) in block.statements.iter().enumerate() {
            // Active loans across this statement are those held by locals that are live AFTER this statement
            // (or used within the statement itself, e.g. when a statement mutates `_1` and also reads a ref `_2` to `_1`!).
            let (s_reads, _) = statement_reads_and_def(program, func, stmt);
            let mut live_during = live_after_stmt[stmt_idx].clone();
            live_during.extend(s_reads);
            let active_before = active_loans_for(&pt, &live_during);

            match stmt {
                Statement::StorageLive(_) => {}
                Statement::StorageDead(local) => {
                    let active_after = active_loans_for(&pt, &live_after_stmt[stmt_idx]);
                    for loan_id in active_after {
                        let loan = &loans[loan_id];
                        if loan.place.local == *local
                            && !loan.place.projections.contains(&Projection::Deref)
                        {
                            return Err(format!(
                                "Borrow check error in {}: `{}` goes out of scope (StorageDead) while still borrowed by '{}'",
                                func.id, local, loan.place
                            ));
                        }
                    }
                }
                Statement::SetDiscriminant(place, _) => {
                    check_deref_permissions(program, func, place, true, false)?;
                    check_write_conflicts(func, place, &active_before, &loans)?;
                }
                Statement::Assign(dest, rval) => {
                    check_deref_permissions(program, func, dest, true, false)?;

                    // 1. Check Rvalue reads, moves, and new borrows
                    match rval {
                        Rvalue::Use(op) | Rvalue::UnaryOp(_, op) | Rvalue::Cast(op, _) => {
                            check_operand_borrows(program, func, op, &active_before, &loans)?;
                        }
                        Rvalue::BinaryOp(_, l, r) => {
                            check_operand_borrows(program, func, l, &active_before, &loans)?;
                            check_operand_borrows(program, func, r, &active_before, &loans)?;
                        }
                        Rvalue::Ref { mutable, place } => {
                            check_deref_permissions(program, func, place, *mutable, false)?;
                            let new_loan_id = ref_loan_map[&(bb, stmt_idx)];
                            // Check conflicts with all OTHER loans that remain live after this statement
                            let mut pt_after = pt.clone();
                            apply_points_to_stmt(bb, stmt_idx, stmt, &mut pt_after);
                            let active_after =
                                active_loans_for(&pt_after, &live_after_stmt[stmt_idx]);

                            for other_id in active_after {
                                if other_id == new_loan_id {
                                    continue;
                                }
                                // If `new_loan` is a reborrow of `other_id` (e.g. `_3 = &mut (*_2)` where `_2` holds `other_id`),
                                // reborrowing from `_2` is allowed as long as `_2` itself isn't accessed while `_3` is live!
                                if place.projections.contains(&Projection::Deref)
                                    && pt
                                        .get(&place.local)
                                        .is_some_and(|ls| ls.contains(&other_id))
                                {
                                    continue;
                                }
                                let other = &loans[other_id];
                                if places_overlap(place, &other.place)
                                    && (*mutable || other.mutable)
                                {
                                    return Err(format!(
                                        "Borrow check error in {}: cannot borrow '{}' as {} because '{}' is already borrowed as {}",
                                        func.id,
                                        place,
                                        if *mutable { "mutable" } else { "immutable" },
                                        other.place,
                                        if other.mutable {
                                            "mutable"
                                        } else {
                                            "immutable"
                                        }
                                    ));
                                }
                            }
                        }
                        Rvalue::Aggregate(_, ops) | Rvalue::OverlayType(ops) => {
                            for op in ops {
                                check_operand_borrows(program, func, op, &active_before, &loans)?;
                            }
                        }
                        Rvalue::ArrayType { elem, len } | Rvalue::SimdType { elem, len } => {
                            check_operand_borrows(program, func, elem, &active_before, &loans)?;
                            check_operand_borrows(program, func, len, &active_before, &loans)?;
                        }
                        Rvalue::UnionType { tag, variants } => {
                            check_operand_borrows(program, func, tag, &active_before, &loans)?;
                            for op in variants {
                                check_operand_borrows(program, func, op, &active_before, &loans)?;
                            }
                        }
                        Rvalue::PatternType { base, ranges } => {
                            check_operand_borrows(program, func, base, &active_before, &loans)?;
                            for (lo, hi) in ranges {
                                check_operand_borrows(program, func, lo, &active_before, &loans)?;
                                check_operand_borrows(program, func, hi, &active_before, &loans)?;
                            }
                        }
                        Rvalue::Union { payload, .. } => {
                            check_operand_borrows(program, func, payload, &active_before, &loans)?;
                        }
                        Rvalue::Discriminant(place) => {
                            check_deref_permissions(program, func, place, false, false)?;
                            check_read_conflicts(func, place, &active_before, &loans)?;
                        }
                    }

                    // 2. Check LHS destination write conflicts against loans live AFTER this statement
                    let mut pt_after = pt.clone();
                    apply_points_to_stmt(bb, stmt_idx, stmt, &mut pt_after);
                    let active_after = active_loans_for(&pt_after, &live_after_stmt[stmt_idx]);
                    check_write_conflicts(func, dest, &active_after, &loans)?;
                }
            }

            apply_points_to_stmt(bb, stmt_idx, stmt, &mut pt);
        }

        // Check Terminator
        let (t_reads, _) = terminator_reads_and_def(&block.terminator);
        let mut live_during_term = live_out[bb].clone();
        live_during_term.extend(t_reads);
        let active_term = active_loans_for(&pt, &live_during_term);

        match &block.terminator {
            Terminator::Goto { .. } | Terminator::Unreachable => {}
            Terminator::SwitchInt { discr, .. } => {
                check_operand_borrows(program, func, discr, &active_term, &loans)?;
            }
            Terminator::Call {
                func: callee,
                args,
                destination,
                ..
            } => {
                check_operand_borrows(program, func, callee, &active_term, &loans)?;
                for a in args {
                    check_operand_borrows(program, func, a, &active_term, &loans)?;
                }
                check_deref_permissions(program, func, destination, true, false)?;
                let active_after_call = active_loans_for(&pt, &live_out[bb]);
                check_write_conflicts(func, destination, &active_after_call, &loans)?;
            }
            Terminator::Drop { place, .. } => {
                let active_after_drop = active_loans_for(&pt, &live_out[bb]);
                check_write_conflicts(func, place, &active_after_drop, &loans)?;
            }
            Terminator::Return => {
                // At Return, `_0` cannot hold a loan to any local stack variable!
                // (Returning a reference derived from an incoming pointer argument `_1..=arg_count` via `(*_arg)` is allowed,
                //  whereas returning `&local` where `!loan.place.projections.contains(&Projection::Deref)` is a dangling stack pointer!)
                if let Some(ret_loans) = pt.get(&LocalId(0)) {
                    for &loan_id in ret_loans {
                        let loan = &loans[loan_id];
                        if !loan.place.projections.contains(&Projection::Deref) {
                            return Err(format!(
                                "Borrow check error in {}: cannot return reference to local variable '{}'",
                                func.id, loan.place
                            ));
                        }
                    }
                }
            }
        }
    }

    Ok(())
}

fn check_operand_borrows(
    program: &Program,
    func: &Function,
    op: &Operand,
    active_loans: &BTreeSet<usize>,
    loans: &[Loan],
) -> Result<(), String> {
    match op {
        Operand::Copy(place) => {
            check_deref_permissions(program, func, place, false, false)?;
            check_read_conflicts(func, place, active_loans, loans)
        }
        Operand::Move(place) => {
            check_deref_permissions(program, func, place, false, true)?;
            check_write_conflicts(func, place, active_loans, loans)
        }
        Operand::Const(_) => Ok(()),
    }
}

fn check_read_conflicts(
    func: &Function,
    place: &Place,
    active_loans: &BTreeSet<usize>,
    loans: &[Loan],
) -> Result<(), String> {
    for &loan_id in active_loans {
        let loan = &loans[loan_id];
        if loan.mutable && places_overlap(place, &loan.place) {
            return Err(format!(
                "Borrow check error in {}: cannot read '{}' because it is mutably borrowed via '{}'",
                func.id, place, loan.place
            ));
        }
    }
    Ok(())
}

fn check_write_conflicts(
    func: &Function,
    place: &Place,
    active_loans: &BTreeSet<usize>,
    loans: &[Loan],
) -> Result<(), String> {
    for &loan_id in active_loans {
        let loan = &loans[loan_id];
        if places_overlap(place, &loan.place) {
            return Err(format!(
                "Borrow check error in {}: cannot mutate or move '{}' because it is currently borrowed via '{}'",
                func.id, place, loan.place
            ));
        }
    }
    Ok(())
}
