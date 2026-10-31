use std::collections::BTreeMap;

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

/// The move paths seen in the function being elaborated, numbered for `PathSet`.
#[derive(Default)]
struct PathTable {
    ids: std::collections::HashMap<MovePath, usize>,
    paths: Vec<MovePath>,
    by_local: BTreeMap<LocalId, Vec<usize>>,
}

thread_local! {
    static PATHS: std::cell::RefCell<PathTable> = std::cell::RefCell::default();
}

fn path_id(path: &MovePath) -> usize {
    PATHS.with_borrow_mut(|table| {
        if let Some(&id) = table.ids.get(path) {
            return id;
        }
        let id = table.paths.len();
        table.ids.insert(path.clone(), id);
        table.paths.push(path.clone());
        table.by_local.entry(path.local).or_default().push(id);
        id
    })
}

/// A set of move paths as bits, because the dataflow copies its state at every block: with
/// ordered sets of paths that copy made elaboration quadratic with a large constant.
#[derive(Debug, Clone, Default)]
struct PathSet {
    bits: Vec<u64>,
}

impl PathSet {
    fn insert(&mut self, path: MovePath) {
        let id = path_id(&path);
        if self.bits.len() <= id / 64 {
            self.bits.resize(id / 64 + 1, 0);
        }
        self.bits[id / 64] |= 1 << (id % 64);
    }

    fn clear_id(&mut self, id: usize) {
        if let Some(word) = self.bits.get_mut(id / 64) {
            *word &= !(1 << (id % 64));
        }
    }

    fn remove(&mut self, path: &MovePath) {
        self.clear_id(path_id(path));
    }

    fn contains(&self, path: &MovePath) -> bool {
        let id = path_id(path);
        self.bits.get(id / 64).is_some_and(|word| word & (1 << (id % 64)) != 0)
    }

    /// Removes `path` and every path inside it.
    fn remove_within(&mut self, path: &MovePath) {
        let ids = PATHS.with_borrow(|table| {
            let of_local = table.by_local.get(&path.local).map_or(&[][..], |ids| ids);
            let within = |&&id: &&usize| table.paths[id].fields.starts_with(&path.fields);
            of_local.iter().filter(within).copied().collect::<Vec<_>>()
        });
        for id in ids {
            self.clear_id(id);
        }
    }

    /// Adds everything in `other`, returning whether that changed `self`.
    fn union_with(&mut self, other: &PathSet) -> bool {
        if self.bits.len() < other.bits.len() {
            self.bits.resize(other.bits.len(), 0);
        }
        let mut changed = false;
        for (word, new) in self.bits.iter_mut().zip(&other.bits) {
            changed |= *new & !*word != 0;
            *word |= new;
        }
        changed
    }

    fn iter(&self) -> Vec<MovePath> {
        let mut out = Vec::new();
        PATHS.with_borrow(|table| {
            for (i, &word) in self.bits.iter().enumerate() {
                let mut rest = word;
                while rest != 0 {
                    out.push(table.paths[i * 64 + rest.trailing_zeros() as usize].clone());
                    rest &= rest - 1;
                }
            }
        });
        out
    }
}

impl PartialEq for PathSet {
    fn eq(&self, other: &PathSet) -> bool {
        let len = self.bits.len().max(other.bits.len());
        (0..len).all(|i| {
            self.bits.get(i).copied().unwrap_or(0) == other.bits.get(i).copied().unwrap_or(0)
        })
    }
}

impl Eq for PathSet {}

#[derive(Debug, Clone, PartialEq, Eq, Default)]
struct InitState {
    maybe_init: PathSet,
    maybe_uninit: PathSet,
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
    elaborate_drops_from(program, 0)
}

/// `elaborate_drops` for the functions from index `first`, the rest being done already.
pub fn elaborate_drops_from(program: &mut Program, first: usize) -> Result<(), String> {
    let destructors: BTreeMap<TypeId, FuncId> = program.destructors.iter().copied().collect();
    let void_ty = program.intern_type(Type::Void);
    let bool_ty = program.intern_type(Type::Bool);

    for func_idx in first..program.functions.len() {
        check_linear_raw_stores(program, &program.functions[func_idx])?;
        elaborate_function(program, func_idx, &destructors, void_ty, bool_ty)?;
    }
    Ok(())
}

/// A place the move checker cannot follow: reached through a pointer, or an `uninit` field.
fn is_untracked_place(program: &Program, func: &Function, place: &Place) -> bool {
    place.projections.contains(&Projection::Deref)
        || place_projects_through_overlay_field(program, func, place)
}

fn is_linear_place(program: &Program, func: &Function, place: &Place) -> bool {
    place_type(program, func, place).is_ok_and(|ty| linear_type_name(program, ty).is_some())
}

fn successors(term: &Terminator) -> Vec<BlockId> {
    match term {
        Terminator::Goto { target }
        | Terminator::Call { target, .. }
        | Terminator::Drop { target, .. } => vec![*target],
        Terminator::SwitchInt {
            targets, otherwise, ..
        } => targets
            .iter()
            .map(|(_, b)| *b)
            .chain(std::iter::once(*otherwise))
            .collect(),
        Terminator::Return | Terminator::Unreachable => Vec::new(),
    }
}

/// Rejects storing a linear value where the move checker cannot follow it unless the storage
/// owns it: through an owning pointer (`*own T`, whose containing type is linear when `T` is), or
/// into `uninit` storage inside a method of a linear type. Any other store (through a raw pointer,
/// or into `uninit` storage elsewhere) must refill, on every path, a slot the function first moved
/// a linear value out of, as `core::mem::swap` and `core::mem::replace` do: a refill hands back
/// what it took, while any other store adds a value nothing will consume. Stage 2 rejects even
/// owned stores in methods of non-linear types.
fn check_linear_raw_stores(program: &Program, func: &Function) -> Result<(), String> {
    if func.blocks.is_empty() {
        return Ok(());
    }
    // Must-analysis over the untracked slots vacated on every path; `None` is an unvisited block.
    let num_blocks = func.blocks.len();
    let mut block_in: Vec<Option<Vec<Place>>> = vec![None; num_blocks];
    block_in[0] = Some(Vec::new());
    let mut worklist = vec![0];
    while let Some(b) = worklist.pop() {
        let mut vacated = block_in[b].clone().unwrap_or_default();
        apply_raw_store_block(program, func, &func.blocks[b], &mut vacated, false)?;
        for succ in successors(&func.blocks[b].terminator) {
            let s = succ.0 as usize;
            let next: Vec<Place> = match &block_in[s] {
                None => vacated.clone(),
                Some(old) => old.iter().filter(|p| vacated.contains(p)).cloned().collect(),
            };
            if block_in[s].as_ref() != Some(&next) {
                block_in[s] = Some(next);
                worklist.push(s);
            }
        }
    }
    for (b, block) in func.blocks.iter().enumerate() {
        if let Some(mut vacated) = block_in[b].clone() {
            apply_raw_store_block(program, func, block, &mut vacated, true)?;
        }
    }
    Ok(())
}

fn apply_raw_store_block(
    program: &Program,
    func: &Function,
    block: &BasicBlock,
    vacated: &mut Vec<Place>,
    check_errors: bool,
) -> Result<(), String> {
    for stmt in &block.statements {
        match stmt {
            Statement::Assign(dest, rvalue) => {
                for op in rvalue_operands(rvalue) {
                    vacate_operand(program, func, op, vacated);
                }
                fill_place(program, func, dest, vacated, check_errors)?;
            }
            Statement::StorageLive(local) | Statement::StorageDead(local) => {
                forget_local(*local, vacated);
            }
            Statement::SetDiscriminant(..) | Statement::Line(_) => {}
        }
    }
    if let Terminator::Call {
        args, destination, ..
    } = &block.terminator
    {
        for op in args {
            vacate_operand(program, func, op, vacated);
        }
        fill_place(program, func, destination, vacated, check_errors)?;
    }
    Ok(())
}

fn rvalue_operands(rvalue: &Rvalue) -> Vec<&Operand> {
    match rvalue {
        Rvalue::Use(op)
        | Rvalue::UnaryOp(_, op)
        | Rvalue::Cast(op, _)
        | Rvalue::Transmute(op, _)
        | Rvalue::Union { payload: op, .. } => vec![op],
        Rvalue::BinaryOp(_, lhs, rhs) => vec![lhs, rhs],
        Rvalue::Aggregate(_, ops) | Rvalue::OverlayType(ops) => ops.iter().collect(),
        Rvalue::ArrayType { elem, len } | Rvalue::SimdType { elem, len } => vec![elem, len],
        Rvalue::UnionType { tag, variants } => std::iter::once(tag).chain(variants).collect(),
        Rvalue::PatternType { base, ranges } => std::iter::once(base)
            .chain(ranges.iter().flat_map(|(lo, hi)| [lo, hi]))
            .collect(),
        Rvalue::Ref { .. } | Rvalue::Discriminant(_) => Vec::new(),
    }
}

/// Moving a linear value out of an untracked slot leaves that slot free to be refilled.
fn vacate_operand(program: &Program, func: &Function, op: &Operand, vacated: &mut Vec<Place>) {
    if let Operand::Move(place) = op
        && is_untracked_place(program, func, place)
        && is_linear_place(program, func, place)
        && !vacated.contains(place)
    {
        vacated.push(place.clone());
    }
}

/// Writing a whole local re-points any slot reached through it; storing a linear value in an
/// untracked slot must refill one this function vacated.
fn fill_place(
    program: &Program,
    func: &Function,
    dest: &Place,
    vacated: &mut Vec<Place>,
    check_errors: bool,
) -> Result<(), String> {
    if dest.projections.is_empty() {
        forget_local(dest.local, vacated);
        return Ok(());
    }
    if !is_untracked_place(program, func, dest) || !is_linear_place(program, func, dest) {
        return Ok(());
    }
    let owned = match last_deref_ptr(program, func, dest) {
        Some(ptr) if program.own_ptr_types.contains(&ptr) => true,
        Some(ptr) if program.raw_ptr_types.contains(&ptr) => false,
        // A local, or a place reached through a reference: `uninit` storage the value holds.
        _ => func.linear_owner && place_projects_through_overlay_field(program, func, dest),
    };
    if owned {
        return Ok(());
    }
    if let Some(pos) = vacated.iter().position(|p| p == dest) {
        vacated.remove(pos);
    } else if check_errors {
        let ty = place_type(program, func, dest)?;
        return Err(format!(
            "Linear value of type '{}' is stored in '{}', where the move checker cannot follow it, in {}; store it through an owning pointer ('*own T') or in 'uninit' storage of a linear type, or refill a slot the function first moved a value out of (as 'core::mem::replace' does)",
            program.type_label(ty),
            func.place_label(program, dest),
            func.label()
        ));
    }
    Ok(())
}

/// The type of the last pointer `place` dereferences, if any.
fn last_deref_ptr(program: &Program, func: &Function, place: &Place) -> Option<TypeId> {
    let mut ty = func.locals.get(place.local.0 as usize).copied()?;
    let mut last = None;
    for proj in &place.projections {
        let next = match (proj, program.types.get(ty.0 as usize)) {
            (Projection::Deref, Some(Type::Ptr { pointee, .. })) => {
                last = Some(ty);
                *pointee
            }
            (Projection::Field(i), Some(Type::Struct(fields) | Type::Overlay(fields))) => {
                fields[*i as usize]
            }
            (Projection::Variant(v), Some(Type::Union { variants, .. })) => variants[*v as usize],
            (Projection::Index(_), Some(Type::Array { elem, .. } | Type::Simd { elem, .. })) => {
                *elem
            }
            _ => return last,
        };
        ty = next;
    }
    last
}

fn forget_local(local: LocalId, vacated: &mut Vec<Place>) {
    vacated.retain(|p| {
        p.local != local
            && !p
                .projections
                .iter()
                .any(|proj| *proj == Projection::Index(local))
    });
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
    // Moving a value moves its parts, including the linear fields tracked inside an atomic
    // `move self` (see `linear_field_paths`).
    state.maybe_init.remove_within(path);
}

/// Field paths (relative to a value of type `ty_id`) of the linear values held inline in it,
/// looking through transparent structs. A consuming `move self` method of a linear opaque is
/// allowed to retire `self`, but only after moving each of these out.
fn linear_field_paths(
    program: &Program,
    destructors: &BTreeMap<TypeId, FuncId>,
    ty_id: TypeId,
    prefix: &mut Vec<u32>,
    out: &mut Vec<Vec<u32>>,
) {
    let Some(Type::Struct(fields)) = program.types.get(ty_id.0 as usize) else {
        return;
    };
    for (i, &fty) in fields.iter().enumerate() {
        if linear_type_name(program, fty).is_none() {
            continue;
        }
        prefix.push(i as u32);
        let transparent = !destructors.contains_key(&fty)
            && !is_direct_linear_struct(program, fty)
            && matches!(program.types.get(fty.0 as usize), Some(Type::Struct(_)));
        if transparent {
            linear_field_paths(program, destructors, fty, prefix, out);
        } else {
            out.push(prefix.clone());
        }
        prefix.pop();
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
                                func.place_label(program, place), func.label()
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
                            func.place_label(program, place), func.label()
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
        Statement::Line(_) => Ok(()),
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
                // A type with a `drop` hook is one unit: its fields cannot start it.
                for n in 0..dest.projections.len() {
                    let whole = Place {
                        local: dest.local,
                        projections: dest.projections[..n].to_vec(),
                    };
                    if check_errors
                        && destructors.contains_key(&place_type(program, func, &whole)?)
                        && MovePath::from_place(program, func, &whole)
                            .is_some_and(|p| state.maybe_uninit.contains(&p))
                    {
                        return Err(format!(
                            "Cannot assign a field of '{}' before it holds a value in {}: '{}' has a 'drop' hook, so it must be initialized whole",
                            func.place_label(program, &whole),
                            func.label(),
                            program.type_label(place_type(program, func, &whole)?)
                        ));
                    }
                }
                mark_initialized(program, destructors, func, state, &dest_path);
            } else if check_errors
                && let Some(prefix_path) = MovePath::deref_prefix_from_place(program, func, dest)
            {
                let leaves = expand_to_leaf_paths(program, destructors, func, &prefix_path);
                for leaf in &leaves {
                    if state.maybe_uninit.contains(leaf) {
                        return Err(format!(
                            "Use of moved or uninitialized value '{}' in {}",
                            func.place_label(program, dest), func.label()
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
                    return Err(format!(
                        "Cannot deref non-pointer type '{}'",
                        program.type_label(cur_ty)
                    ));
                };
                cur_ty = *pointee;
            }
            Projection::Field(idx) => match program.types.get(cur_ty.0 as usize) {
                Some(Type::Struct(fields) | Type::Overlay(fields)) => {
                    cur_ty = fields[*idx as usize];
                }
                _ => return Err(format!("Cannot access field on '{}'", program.type_label(cur_ty))),
            },
            Projection::Variant(v_idx) => {
                let Some(Type::Union { variants, .. }) = program.types.get(cur_ty.0 as usize)
                else {
                    return Err(format!(
                        "Cannot access variant on '{}'",
                        program.type_label(cur_ty)
                    ));
                };
                cur_ty = variants[*v_idx as usize];
            }
            Projection::Index(_) => {
                let Some(Type::Array { elem, .. } | Type::Simd { elem, .. }) =
                    program.types.get(cur_ty.0 as usize)
                else {
                    return Err(format!(
                        "Cannot index non-array/simd '{}'",
                        program.type_label(cur_ty)
                    ));
                };
                cur_ty = *elem;
            }
        }
    }
    Ok(cur_ty)
}

/// The source line in force at statement `stmt` of block `bb` (`stmt` past the last statement
/// for the terminator): from the nearest `Statement::Line` before it, along any path from the
/// entry if its block has none.
pub(crate) fn line_at(func: &Function, bb: usize, stmt: usize) -> Option<u32> {
    let last_line = |statements: &[Statement]| {
        statements.iter().rev().find_map(|s| match s {
            Statement::Line(line) => Some(*line),
            _ => None,
        })
    };
    let mut entry: Vec<Option<Option<u32>>> = vec![None; func.blocks.len()];
    let mut work = vec![(0usize, None)];
    while let Some((b, line)) = work.pop() {
        if entry[b].is_some() {
            continue;
        }
        entry[b] = Some(line);
        let out = last_line(&func.blocks[b].statements).or(line);
        for succ in successors(&func.blocks[b].terminator) {
            work.push((succ.0 as usize, out));
        }
    }
    last_line(&func.blocks[bb].statements[..stmt]).or(entry[bb].flatten())
}

/// `err` with the source line of the place it was found, if known.
pub(crate) fn with_line(func: &Function, err: String, at: Option<(usize, usize)>) -> String {
    match at.and_then(|(bb, stmt)| line_at(func, bb, stmt)) {
        Some(line) => format!("{err} (line {line})"),
        None => err,
    }
}

/// `err`, about `func` as a whole, with the line where its body starts, if known.
pub(crate) fn with_first_line(func: &Function, err: String) -> String {
    let first = func.blocks.iter().flat_map(|b| &b.statements).find_map(|s| match s {
        Statement::Line(line) => Some(*line),
        _ => None,
    });
    match first {
        Some(line) => format!("{err} (function body at line {line})"),
        None => err,
    }
}

fn elaborate_function(
    program: &mut Program,
    func_idx: usize,
    destructors: &BTreeMap<TypeId, FuncId>,
    unit_ty: TypeId,
    bool_ty: TypeId,
) -> Result<(), String> {
    let func = program.functions[func_idx].clone();
    PATHS.with_borrow_mut(|table| *table = PathTable::default());
    let at = std::cell::Cell::new(None);
    elaborate_function_at(program, func_idx, destructors, unit_ty, bool_ty, &at)
        .map_err(|e| with_line(&func, e, at.get()))
}

fn elaborate_function_at(
    program: &mut Program,
    func_idx: usize,
    destructors: &BTreeMap<TypeId, FuncId>,
    unit_ty: TypeId,
    bool_ty: TypeId,
    at: &std::cell::Cell<Option<(usize, usize)>>,
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
            if local_idx == 1
                && let Some(self_ty) = func.linear_self
            {
                let mut fields = Vec::new();
                linear_field_paths(program, destructors, self_ty, &mut Vec::new(), &mut fields);
                for fields in fields {
                    entry0.maybe_init.insert(MovePath {
                        local: root.local,
                        fields,
                    });
                }
            }
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
                changed |= block_in[s_idx].maybe_init.union_with(&edge_state.maybe_init);
                changed |= block_in[s_idx].maybe_uninit.union_with(&edge_state.maybe_uninit);
            }
        }
    }

    // 3. Verify move-check errors on the converged states
    for (bb, entry) in block_in.iter().enumerate() {
        let mut state = entry.clone();
        for (i, stmt) in func.blocks[bb].statements.iter().enumerate() {
            at.set(Some((bb, i)));
            apply_statement(program, destructors, &func, &mut state, stmt, true)?;
        }
        at.set(Some((bb, func.blocks[bb].statements.len())));
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

    for (bb, exit) in block_out.iter().enumerate() {
        if let Terminator::Drop { place, .. } = &func.blocks[bb].terminator
            && let Some(path) = MovePath::from_place(program, &func, place)
        {
            for leaf in expand_to_leaf_paths(program, destructors, &func, &path) {
                let leaf_place = leaf.to_place();
                let leaf_ty = place_type(program, &func, &leaf_place)?;
                if destructors.contains_key(&leaf_ty)
                    && exit.maybe_init.contains(&leaf)
                    && exit.maybe_uninit.contains(&leaf)
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
        let flag_updates = |place: &Place, value: bool| -> Vec<Statement> {
            let Some(path) = MovePath::from_place(program, &func, place) else {
                return Vec::new();
            };
            expand_to_leaf_paths(program, destructors, &func, &path)
                .iter()
                .filter_map(|leaf| drop_flags.get(leaf))
                .map(|&flag_id| {
                    Statement::Assign(
                        Place::new(flag_id),
                        Rvalue::Use(Operand::Const(ConstValue::Bool(value))),
                    )
                })
                .collect()
        };
        // Blocks to run after a call returns: its destination is initialized only then.
        let mut after_calls = Vec::new();
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
                        if !place_projects_through_overlay_field(program, &func, &mp) {
                            updated_stmts.extend(flag_updates(&mp, false));
                        }
                    }
                    updated_stmts.extend(flag_updates(dest, true));
                } else {
                    updated_stmts.push(stmt.clone());
                }
            }
            // A call takes its arguments as it starts, and fills its destination as it returns.
            if let Terminator::Call {
                func: callee,
                args,
                destination,
                target,
            } = &mut blk.terminator
            {
                for op in std::iter::once(&*callee).chain(args.iter()) {
                    if let Operand::Move(p) = op
                        && !place_projects_through_overlay_field(program, &func, p)
                    {
                        updated_stmts.extend(flag_updates(p, false));
                    }
                }
                let filled = flag_updates(destination, true);
                if !filled.is_empty() {
                    let after = BlockId((num_blocks + after_calls.len()) as u32);
                    after_calls.push(BasicBlock {
                        statements: filled,
                        terminator: Terminator::Goto { target: *target },
                    });
                    *target = after;
                }
            }
            blk.statements = updated_stmts;
        }
        new_blocks.extend(after_calls);
    }

    // 6. Rewrite every `Terminator::Drop` in `0..num_blocks`
    for bb in 0..num_blocks {
        let Terminator::Drop { place, target } = new_blocks[bb].terminator.clone() else {
            continue;
        };
        at.set(Some((bb, func.blocks[bb].statements.len())));

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
                                func.place_label(program, &leaf_place), lin_name, func.label()
                            ));
                        }
                        // Retiring `self` must not take an unconsumed linear field with it.
                        let unconsumed_field = block_out[bb].maybe_init.iter().into_iter().find_map(|p| {
                            if p.local != leaf.local || p.fields.is_empty() {
                                return None;
                            }
                            let place = p.to_place();
                            let ty = place_type(program, &func, &place).ok()?;
                            linear_type_name(program, ty).is_some().then_some((place, ty))
                        });
                        if let Some((field_place, field_ty)) = unconsumed_field {
                            return Err(format!(
                                "Linear field '{}' of type '{}' must be moved out before 'self' is retired in {}",
                                func.place_label(program, &field_place),
                                program.type_label(field_ty),
                                func.label()
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
                    func.place_label(program, &place), lin_name, func.label()
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
