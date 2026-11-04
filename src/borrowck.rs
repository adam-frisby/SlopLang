use std::collections::{BTreeMap, BTreeSet};
use std::rc::Rc;

use crate::ir::{
    BlockId, ConstValue, FnContract, FuncId, Function, LocalId, Operand, Place, Program,
    Projection, Rvalue, Statement, Terminator, Type,
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
    check_borrows_where(program, |_| true)
}

/// `check_borrows` for the functions `checked` picks, against what every function borrows.
pub fn check_borrows_where(program: &Program, checked: impl Fn(FuncId) -> bool) -> Result<(), String> {
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

    check_fn_value_contracts(program, &effective_summaries, &effective_param_flows)?;

    for func in program.functions.iter().filter(|f| checked(f.id)) {
        if let Some(explicit) = &func.ret_borrows
            && let Some(actual_origins) = inferred_origins.get(&func.id)
        {
            for &origin_param in actual_origins {
                // A parameter that cannot carry a borrow (a raw or owning pointer) needs no clause.
                let carries = func
                    .locals
                    .get(origin_param.base().0 as usize)
                    .is_some_and(|&t| type_contains_safe_ptr(program, t));
                if carries && !origin_covered(explicit.iter(), origin_param) {
                    return Err(crate::drop::with_first_line(func, format!(
                        "Borrow check error in {}: return value borrows from parameter '{}', which is not permitted by its contract borrows({}); add '{}' to the 'borrows(...)' clause",
                        func.label(),
                        func.param_name(origin_param),
                        explicit
                            .iter()
                            .map(|p| func.param_name(*p))
                            .collect::<Vec<_>>()
                            .join(", "),
                        func.param_name(origin_param)
                    )));
                }
            }
        }
        if let Some(explicit_pf) = &func.param_borrows
            && let Some(actual_pf) = param_flows.get(&func.id)
        {
            for (&dst_param, src_set) in actual_pf {
                for &src_param in src_set {
                    // A source parameter whose type holds no pointer carries no caller-visible loans
                    // (e.g. `&val` of a by-value `i32` copied into `self` through raw pointers).
                    // Raw-pointer parameters are unchecked (`unsafe`) and need no contract either.
                    let param_holds_safe_ref = |p: LocalId| {
                        func.locals
                            .get(p.0 as usize)
                            .is_some_and(|&t| type_contains_safe_ptr(program, t))
                    };
                    if dst_param != src_param
                        && param_holds_safe_ref(src_param)
                        && param_holds_safe_ref(dst_param)
                        && !explicit_pf.contains(&(dst_param, src_param))
                    {
                        let (dst, src) = (func.param_name(dst_param), func.param_name(src_param));
                        return Err(crate::drop::with_first_line(func, format!(
                            "Borrow check error in {}: parameter '{dst}' stores a borrow from parameter '{src}', which its contract does not declare; add 'borrows({dst}: {src})'",
                            func.label()
                        )));
                    }
                }
            }
        }
        check_function(program, func, &effective_summaries, &effective_param_flows)?;
    }
    Ok(())
}

type ParamFlows = BTreeMap<FuncId, BTreeMap<LocalId, BTreeSet<LocalId>>>;
/// A callee's return-borrow summary and parameter-to-parameter flows, as seen at a call site.
type CallContract = (BTreeSet<LocalId>, BTreeMap<LocalId, BTreeSet<LocalId>>);

/// A set of small integers (loan indices) as bits, so copying and joining take a pass over words
/// rather than over elements: a value that gathers many loans is in every copy of the state.
#[derive(Debug, Clone, Default)]
struct LoanSet {
    bits: Vec<u64>,
}

impl LoanSet {
    fn new() -> Self {
        LoanSet::default()
    }

    fn from_one(loan: usize) -> Self {
        let mut set = LoanSet::new();
        set.insert(loan);
        set
    }

    fn insert(&mut self, loan: usize) {
        if self.bits.len() <= loan / 64 {
            self.bits.resize(loan / 64 + 1, 0);
        }
        self.bits[loan / 64] |= 1 << (loan % 64);
    }

    fn iter(&self) -> impl Iterator<Item = usize> + '_ {
        self.bits.iter().enumerate().flat_map(|(i, &word)| {
            std::iter::successors((word != 0).then_some(word), |rest| {
                let next = rest & (rest - 1);
                (next != 0).then_some(next)
            })
            .map(move |rest| i * 64 + rest.trailing_zeros() as usize)
        })
    }

    fn is_empty(&self) -> bool {
        self.bits.iter().all(|&word| word == 0)
    }

    fn contains(&self, loan: &usize) -> bool {
        self.bits.get(loan / 64).is_some_and(|word| word & (1 << (loan % 64)) != 0)
    }

    fn union(&mut self, other: &LoanSet) {
        if self.bits.len() < other.bits.len() {
            self.bits.resize(other.bits.len(), 0);
        }
        for (word, new) in self.bits.iter_mut().zip(&other.bits) {
            *word |= new;
        }
    }
}

impl PartialEq for LoanSet {
    fn eq(&self, other: &LoanSet) -> bool {
        let len = self.bits.len().max(other.bits.len());
        (0..len).all(|i| {
            self.bits.get(i).copied().unwrap_or(0) == other.bits.get(i).copied().unwrap_or(0)
        })
    }
}

impl IntoIterator for LoanSet {
    type Item = usize;
    type IntoIter = std::vec::IntoIter<usize>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter().collect::<Vec<_>>().into_iter()
    }
}

impl Extend<usize> for LoanSet {
    fn extend<I: IntoIterator<Item = usize>>(&mut self, iter: I) {
        for loan in iter {
            self.insert(loan);
        }
    }
}

/// What dataflow state joins.
trait FlowSet: Clone + Default {
    fn is_empty_set(&self) -> bool;
    fn covers(&self, other: &Self) -> bool;
    fn add_all(&mut self, other: &Self);
}

impl FlowSet for BTreeSet<LocalId> {
    fn is_empty_set(&self) -> bool {
        self.is_empty()
    }

    fn covers(&self, other: &Self) -> bool {
        other.is_subset(self)
    }

    fn add_all(&mut self, other: &Self) {
        self.extend(other.iter().copied());
    }
}

impl FlowSet for LoanSet {
    fn is_empty_set(&self) -> bool {
        self.is_empty()
    }

    fn covers(&self, other: &Self) -> bool {
        other.bits.iter().enumerate().all(|(i, new)| {
            new & !self.bits.get(i).copied().unwrap_or(0) == 0
        })
    }

    fn add_all(&mut self, other: &Self) {
        self.union(other);
    }
}

/// Dataflow state: a set per local. The analyses copy their state at every block and join it at
/// every edge, so copies share the sets and a join skips what is shared, which keeps both cheap
/// in a large function.
#[derive(Debug, Clone, PartialEq)]
struct FlowMap<S> {
    /// Sorted by local.
    entries: Vec<(LocalId, Rc<S>)>,
}

impl<S> Default for FlowMap<S> {
    fn default() -> Self {
        FlowMap { entries: Vec::new() }
    }
}

impl<S: FlowSet> FlowMap<S> {
    fn find(&self, local: LocalId) -> Result<usize, usize> {
        self.entries.binary_search_by_key(&local, |e| e.0)
    }

    fn get(&self, local: &LocalId) -> Option<&S> {
        self.find(*local).ok().map(|i| &*self.entries[i].1)
    }

    fn insert(&mut self, local: LocalId, set: S) {
        match self.find(local) {
            Ok(i) => self.entries[i].1 = Rc::new(set),
            Err(i) => self.entries.insert(i, (local, Rc::new(set))),
        }
    }

    fn remove(&mut self, local: &LocalId) {
        if let Ok(i) = self.find(*local) {
            self.entries.remove(i);
        }
    }

    /// The set of `local`, which starts empty; `or_default` keeps the map API's spelling.
    fn entry(&mut self, local: LocalId) -> FlowEntry<'_, S> {
        let i = match self.find(local) {
            Ok(i) => i,
            Err(i) => {
                self.entries.insert(i, (local, Rc::new(S::default())));
                i
            }
        };
        FlowEntry { set: &mut self.entries[i].1 }
    }

    /// Adds everything in `other`, returning whether any set of `self` grew.
    fn join(&mut self, other: &FlowMap<S>) -> bool {
        if self.entries.is_empty() {
            self.entries = other.entries.clone();
            return other.entries.iter().any(|(_, set)| !set.is_empty_set());
        }
        // Both are sorted, so one pass merges them.
        let mut changed = false;
        let mut merged = Vec::with_capacity(self.entries.len().max(other.entries.len()));
        let mut ours = std::mem::take(&mut self.entries).into_iter().peekable();
        let mut theirs = other.entries.iter().peekable();
        loop {
            match (ours.peek(), theirs.peek()) {
                (Some(a), Some(b)) if a.0 == b.0 => {
                    let (local, mut set) = ours.next().unwrap();
                    let (_, new) = theirs.next().unwrap();
                    if !Rc::ptr_eq(&set, new) && !set.covers(new) {
                        Rc::make_mut(&mut set).add_all(new);
                        changed = true;
                    }
                    merged.push((local, set));
                }
                (Some(a), Some(b)) if a.0 < b.0 => merged.push(ours.next().unwrap()),
                (Some(_), None) => merged.push(ours.next().unwrap()),
                (_, Some(_)) => {
                    let (local, new) = theirs.next().unwrap();
                    changed |= !new.is_empty_set();
                    merged.push((*local, new.clone()));
                }
                (None, None) => break,
            }
        }
        self.entries = merged;
        changed
    }
}

struct FlowEntry<'a, S> {
    set: &'a mut Rc<S>,
}

impl<'a, S: Clone> FlowEntry<'a, S> {
    fn or_default(self) -> &'a mut S {
        Rc::make_mut(self.set)
    }
}

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
            type Origins = FlowMap<BTreeSet<LocalId>>;
            let mut origins_in: Vec<Origins> = vec![FlowMap::default(); num_blocks];
            let mut targets_in: Vec<Origins> = vec![FlowMap::default(); num_blocks];
            for i in 1..=func.arg_count {
                let param = LocalId(i as u32);
                origins_in[0].insert(param, BTreeSet::from([param]));
                origins_in[0].insert(param.contents(), BTreeSet::from([param.contents()]));
                targets_in[0].insert(param, BTreeSet::from([param.contents()]));
            }

            // Only a block whose incoming state changed can change anything downstream.
            let mut dirty = vec![true; num_blocks];
            let mut local_changed = true;
            while local_changed {
                local_changed = false;
                for bb in 0..num_blocks {
                    if !std::mem::take(&mut dirty[bb]) {
                        continue;
                    }
                    let mut orig = origins_in[bb].clone();
                    let mut targets = targets_in[bb].clone();
                    for stmt in &func.blocks[bb].statements {
                        match stmt {
                            Statement::StorageLive(l) | Statement::StorageDead(l) => {
                                orig.remove(l);
                                targets.remove(l);
                            }
                            Statement::SetDiscriminant(_, _) | Statement::Line(_) => {}
                            Statement::Assign(dest, rval) => {
                                let mut rhs = BTreeSet::new();
                                let mut rhs_targets = BTreeSet::new();
                                match rval {
                                    Rvalue::Use(op)
                                    | Rvalue::UnaryOp(_, op)
                                    | Rvalue::Cast(op, _)
                                    | Rvalue::Transmute(op, _)
                                    | Rvalue::Union { payload: op, .. } => {
                                        if let Operand::Copy(p) | Operand::Move(p) = op
                                            && place_type_contains_ptr(program, func, p)
                                        {
                                            if p.projections.contains(&Projection::Deref) {
                                                if reads_held_borrow(program, func, p) {
                                                    if let Some(ts) = targets.get(&p.local) {
                                                        for &t in ts {
                                                            if let Some(os) = orig.get(&t) {
                                                                rhs.extend(os.iter().copied());
                                                            }
                                                        }
                                                    } else if let Some(os) = orig.get(&p.local) {
                                                        rhs.extend(contents_of(os));
                                                    }
                                                } else {
                                                    if let Some(os) = orig.get(&p.local) {
                                                        rhs.extend(os.iter().copied());
                                                    }
                                                    if let Some(ts) = targets.get(&p.local) {
                                                        for &t in ts {
                                                            if let Some(os) = orig.get(&t) {
                                                                rhs.extend(os.iter().copied());
                                                            }
                                                        }
                                                    }
                                                }
                                            } else {
                                                if let Some(os) = orig.get(&p.local) {
                                                    rhs.extend(os.iter().copied());
                                                }
                                                if let Some(ts) = targets.get(&p.local) {
                                                    rhs_targets.extend(ts.iter().copied());
                                                }
                                            }
                                        }
                                    }
                                    Rvalue::BinaryOp(_, l, r) => {
                                        for op in [l, r] {
                                            if let Operand::Copy(p) | Operand::Move(p) = op
                                                && place_type_contains_ptr(program, func, p)
                                            {
                                                if let Some(os) = orig.get(&p.local) {
                                                    rhs.extend(os.iter().copied());
                                                }
                                                if !p.projections.contains(&Projection::Deref)
                                                    && let Some(ts) = targets.get(&p.local)
                                                {
                                                    rhs_targets.extend(ts.iter().copied());
                                                }
                                            }
                                        }
                                    }
                                    Rvalue::Ref { place, .. } => {
                                        if place.projections.contains(&Projection::Deref) {
                                            if refs_through_held_borrow(program, func, place) {
                                                if let Some(ts) = targets.get(&place.local) {
                                                    for &t in ts {
                                                        if let Some(os) = orig.get(&t) {
                                                            rhs.extend(os.iter().copied());
                                                        }
                                                    }
                                                } else if let Some(os) = orig.get(&place.local) {
                                                    rhs.extend(contents_of(os));
                                                }
                                            } else {
                                                if let Some(os) = orig.get(&place.local) {
                                                    rhs.extend(os.iter().copied());
                                                }
                                                if let Some(ts) = targets.get(&place.local) {
                                                    for &t in ts {
                                                        if let Some(os) = orig.get(&t.base()) {
                                                            rhs.extend(os.iter().copied());
                                                        }
                                                    }
                                                    rhs_targets.extend(ts.iter().copied());
                                                }
                                            }
                                        } else {
                                            rhs_targets.insert(place.local);
                                            if (place.local.0 as usize) > func.arg_count
                                                || func
                                                    .locals
                                                    .get(place.local.0 as usize)
                                                    .is_some_and(|&t| {
                                                        type_contains_safe_ptr(program, t)
                                                    })
                                            {
                                                if let Some(os) = orig.get(&place.local) {
                                                    rhs.extend(os.iter().copied());
                                                }
                                            }
                                        }
                                    }
                                    Rvalue::Aggregate(_, ops) => {
                                        for op in ops {
                                            if let Operand::Copy(p) | Operand::Move(p) = op
                                                && place_type_contains_ptr(program, func, p)
                                            {
                                                if let Some(os) = orig.get(&p.local) {
                                                    rhs.extend(os.iter().copied());
                                                }
                                                if !p.projections.contains(&Projection::Deref)
                                                    && let Some(ts) = targets.get(&p.local)
                                                {
                                                    rhs_targets.extend(ts.iter().copied());
                                                }
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
                                        targets.remove(&dest.local);
                                    }
                                } else if dest.projections.is_empty() {
                                    if rhs.is_empty() {
                                        orig.remove(&dest.local);
                                    } else {
                                        orig.insert(dest.local, rhs);
                                    }
                                    if rhs_targets.is_empty() {
                                        targets.remove(&dest.local);
                                    } else {
                                        targets.insert(dest.local, rhs_targets);
                                    }
                                } else {
                                    if !rhs.is_empty() {
                                        if dest.projections.contains(&Projection::Deref)
                                            && let Some(owners) = targets.get(&dest.local).cloned()
                                        {
                                            for owner in owners {
                                                orig.entry(owner.base())
                                                    .or_default()
                                                    .extend(rhs.iter().copied());
                                                orig.entry(owner)
                                                    .or_default()
                                                    .extend(rhs.iter().copied());
                                            }
                                        }
                                        orig.entry(dest.local).or_default().extend(rhs);
                                    }
                                    if !rhs_targets.is_empty() {
                                        targets
                                            .entry(dest.local)
                                            .or_default()
                                            .extend(rhs_targets);
                                    }
                                }
                            }
                        }
                    }

                    let mut succs: Vec<(BlockId, Origins, Origins)> = Vec::new();
                    match &func.blocks[bb].terminator {
                        Terminator::Goto { target } | Terminator::Drop { target, .. } => {
                            succs.push((*target, orig, targets));
                        }
                        Terminator::SwitchInt {
                            targets: sw_targets,
                            otherwise,
                            ..
                        } => {
                            for (_, t) in sw_targets {
                                succs.push((*t, orig.clone(), targets.clone()));
                            }
                            succs.push((*otherwise, orig, targets));
                        }
                        Terminator::Call {
                            func: callee_op,
                            args,
                            destination,
                            target,
                        } => {
                            let mut call_origins = BTreeSet::new();
                            // Direct callee summary, or the contract of the function-pointer type
                            // for an indirect call.
                            let callee_contract: Option<CallContract> = match callee_op {
                                Operand::Const(ConstValue::Func(callee_id)) => program
                                    .functions
                                    .iter()
                                    .find(|f| f.id == *callee_id)
                                    .map(|callee_fn| {
                                        let summary: BTreeSet<LocalId> =
                                            if let Some(explicit) = &callee_fn.ret_borrows {
                                                explicit.iter().copied().collect()
                                            } else {
                                                inferred
                                                    .get(callee_id)
                                                    .cloned()
                                                    .unwrap_or_default()
                                            };
                                        let flows = if let Some(explicit_pf) =
                                            &callee_fn.param_borrows
                                        {
                                            let mut m: BTreeMap<LocalId, BTreeSet<LocalId>> =
                                                BTreeMap::new();
                                            for &(dst_p, src_p) in explicit_pf {
                                                m.entry(dst_p).or_default().insert(src_p);
                                            }
                                            m
                                        } else {
                                            param_flows
                                                .get(callee_id)
                                                .cloned()
                                                .unwrap_or_default()
                                        };
                                        (summary, flows)
                                    }),
                                Operand::Copy(p) | Operand::Move(p) => place_type(program, func, p)
                                    .and_then(|t| fn_ptr_contract(program, t))
                                    .map(|c| {
                                        let mut m: BTreeMap<LocalId, BTreeSet<LocalId>> =
                                            BTreeMap::new();
                                        for &(d, s) in &c.flows {
                                            m.entry(d).or_default().insert(s);
                                        }
                                        (c.ret.iter().copied().collect(), m)
                                    }),
                                _ => None,
                            };
                            if let Some((summary, callee_flows)) = callee_contract {
                                for param in summary {
                                    let idx = param.base().0.saturating_sub(1) as usize;
                                    if let Some(Operand::Copy(p) | Operand::Move(p)) = args.get(idx)
                                    {
                                        if param.is_contents() {
                                            if let Some(ts) = targets.get(&p.local) {
                                                for &t in ts {
                                                    if let Some(os) = orig.get(&t) {
                                                        call_origins.extend(os.iter().copied());
                                                    }
                                                }
                                            } else if let Some(os) = orig.get(&p.local) {
                                                call_origins.extend(contents_of(os));
                                            }
                                        } else {
                                            if let Some(os) = orig.get(&p.local) {
                                                call_origins.extend(os.iter().copied());
                                            }
                                            if let Some(ts) = targets.get(&p.local) {
                                                for &t in ts {
                                                    if let Some(os) = orig.get(&t.base()) {
                                                        call_origins.extend(os.iter().copied());
                                                    }
                                                }
                                            }
                                        }
                                    }
                                }
                                for (&dst_param, src_params) in &callee_flows {
                                    let dst_idx = dst_param.0.saturating_sub(1) as usize;
                                    let mut flowed = BTreeSet::new();
                                    for &sp in src_params {
                                        let s_idx = sp.0.saturating_sub(1) as usize;
                                        if let Some(Operand::Copy(p) | Operand::Move(p)) =
                                            args.get(s_idx)
                                        {
                                            if let Some(os) = orig.get(&p.local) {
                                                flowed.extend(os.iter().copied());
                                            }
                                            if let Some(ts) = targets.get(&p.local) {
                                                for &t in ts {
                                                    if let Some(os) = orig.get(&t.base()) {
                                                        flowed.extend(os.iter().copied());
                                                    }
                                                }
                                            }
                                        }
                                    }
                                    if !flowed.is_empty()
                                        && let Some(Operand::Copy(dp) | Operand::Move(dp)) =
                                            args.get(dst_idx)
                                    {
                                        if let Some(owners) = targets.get(&dp.local).cloned() {
                                            for owner in owners {
                                                orig.entry(owner.base())
                                                    .or_default()
                                                    .extend(flowed.iter().copied());
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
                                targets.remove(&destination.local);
                            } else if destination.projections.is_empty() {
                                targets.remove(&destination.local);
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
                            succs.push((*target, orig, targets));
                        }
                        Terminator::Return => {
                            // Only a type that can carry a borrow (a reference, a `*ref T` view,
                            // values behind `*own T`, declared contents) keeps the arguments it was
                            // derived from borrowed. A raw pointer derived from an argument, or a
                            // type wrapping only raw pointers, carries no loan.
                            if type_contains_safe_ptr(program, func.locals[0])
                                && let Some(ret_os) = orig.get(&LocalId(0))
                            {
                                let entry = inferred.entry(func.id).or_default();
                                let before = entry.len();
                                entry.extend(ret_os.iter().copied().filter(|o| {
                                    let b = o.base().0 as usize;
                                    b >= 1 && b <= func.arg_count
                                }));
                                if entry.len() != before {
                                    global_changed = true;
                                }
                            }
                            for i in 1..=func.arg_count {
                                let param = LocalId(i as u32);
                                for key in [param, param.contents()] {
                                    if let Some(p_os) = orig.get(&key) {
                                        for src_p in p_os.iter().map(|o| o.base()) {
                                            let s_idx = src_p.0 as usize;
                                            if src_p != param && s_idx >= 1 && s_idx <= func.arg_count {
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
                        }
                        Terminator::Unreachable => {}
                    }

                    for (succ_bb, edge_orig, edge_targets) in succs {
                        let s_idx = succ_bb.0 as usize;
                        let grew_origins = origins_in[s_idx].join(&edge_orig);
                        let grew_targets = targets_in[s_idx].join(&edge_targets);
                        if grew_origins || grew_targets {
                            dirty[s_idx] = true;
                            local_changed = true;
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
                    return Err(format!(
                        "Cannot deref non-pointer type '{}'",
                        program.type_label(cur_ty)
                    ));
                };
                if (require_mut || is_move) && !*mutable {
                    return Err(format!(
                        "Cannot mutate, move out of, or mutably borrow '{}' through an immutable reference in {}",
                        place, func.label()
                    ));
                }
                cur_ty = *pointee;
            }
            Projection::Field(idx) => match program.types.get(cur_ty.0 as usize) {
                Some(Type::Struct(fields) | Type::Overlay(fields)) => {
                    cur_ty = *fields
                        .get(*idx as usize)
                        .ok_or_else(|| format!(
                            "Field .{idx} out of bounds on '{}'",
                            program.type_label(cur_ty)
                        ))?;
                }
                _ => return Err(format!(
                    "Cannot access field .{idx} on '{}'",
                    program.type_label(cur_ty)
                )),
            },
            Projection::Variant(v_idx) => {
                let Some(Type::Union { variants, .. }) = program.types.get(cur_ty.0 as usize)
                else {
                    return Err(format!(
                        "Cannot access variant .v{v_idx} on '{}'",
                        program.type_label(cur_ty)
                    ));
                };
                cur_ty = *variants
                    .get(*v_idx as usize)
                    .ok_or_else(|| format!(
                        "Variant .v{v_idx} out of bounds on '{}'",
                        program.type_label(cur_ty)
                    ))?;
            }
            Projection::Index(_) => {
                let Some(Type::Array { elem, .. } | Type::Simd { elem, .. }) =
                    program.types.get(cur_ty.0 as usize)
                else {
                    return Err(format!(
                        "Cannot index non-array/simd type '{}'",
                        program.type_label(cur_ty)
                    ));
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

/// Whether values of `ty_id` may carry a borrow: a safe reference, a view pointer (`*ref T`), or
/// an `opaque` that Stage 2 found carries one (`Program::loan_types`: through a view field,
/// borrowing values behind an owning pointer, or declared contents). A raw or owning pointer on
/// its own carries none.
/// Whether the return contract or summary `allowed` covers origin `o`. A parameter covers what it
/// refers to holds (keeping it borrowed keeps that borrowed), but `*p` covers only that.
fn origin_covered<'a>(mut allowed: impl Iterator<Item = &'a LocalId>, o: LocalId) -> bool {
    allowed.any(|&a| a == o || (o.is_contents() && a == o.base()))
}

/// Origins read out of what they refer to: `*p` for each `p`.
fn contents_of(origins: &BTreeSet<LocalId>) -> impl Iterator<Item = LocalId> + '_ {
    origins.iter().map(|o| o.base().contents())
}

/// Whether reading `place` yields a borrow held by what its root refers to, rather than one of
/// its root: the root local carries a borrow (a reference or view), the place dereferences, and
/// the value read carries a borrow (`self.p` for a view field `p`, `*x` for `x: &&T`). An owning
/// or raw pointer read this way carries none. A value read through a raw or owning pointer is
/// one the memory held, as `Vec::pop` moves out; a reference through it does not come here, and
/// still borrows the container, as `Vec::get`'s does.
fn reads_held_borrow(program: &Program, func: &Function, place: &Place) -> bool {
    let root_carries_borrow = func
        .locals
        .get(place.local.0 as usize)
        .is_some_and(|&t| type_contains_safe_ptr(program, t));
    let root_is_raw = func
        .locals
        .get(place.local.0 as usize)
        .is_some_and(|t| program.raw_ptr_types.contains(t));
    let deref_count = place
        .projections
        .iter()
        .filter(|p| matches!(p, Projection::Deref))
        .count();
    (root_carries_borrow || root_is_raw || deref_count >= 2)
        && place.projections.contains(&Projection::Deref)
        && place_type(program, func, place).is_some_and(|t| type_contains_safe_ptr(program, t))
}

/// Whether `&place` points into memory a shared borrow or `*ref` view held by its root refers to:
/// past the first dereference of a borrow-carrying root, it dereferences a shared reference (`&T`)
/// or a `*ref T` / `*ref mut T` view (`&*self.p`), not an owning pointer, raw pointer, or safe
/// `&mut T` reference (since a safe `&mut T` held inside `*p` retains exclusive access unless `p`
/// itself stays borrowed).
fn refs_through_held_borrow(program: &Program, func: &Function, place: &Place) -> bool {
    let Some(mut ty) = func.locals.get(place.local.0 as usize).copied() else {
        return false;
    };
    let mut derefs = 0;
    for proj in &place.projections {
        let Some(cur) = program.types.get(ty.0 as usize) else {
            return false;
        };
        ty = match (proj, cur) {
            (Projection::Deref, Type::Ptr { mutable, pointee }) => {
                if derefs == 0 && !type_contains_safe_ptr(program, ty) {
                    return false;
                }
                if derefs > 0
                    && ((!*mutable && !program.raw_ptr_types.contains(&ty))
                        || program.view_ptr_types.contains(&ty))
                {
                    return true;
                }
                derefs += 1;
                *pointee
            }
            (Projection::Field(i), Type::Struct(fields) | Type::Overlay(fields)) => {
                fields[*i as usize]
            }
            (Projection::Variant(i), Type::Union { variants, .. }) => variants[*i as usize],
            (Projection::Index(_), Type::Array { elem, .. } | Type::Simd { elem, .. }) => *elem,
            _ => return false,
        };
    }
    false
}

fn type_contains_safe_ptr(program: &Program, ty_id: crate::ir::TypeId) -> bool {
    carries_borrow(program, ty_id, &mut Vec::new())
}

fn carries_borrow(
    program: &Program,
    ty_id: crate::ir::TypeId,
    visiting: &mut Vec<crate::ir::TypeId>,
) -> bool {
    if visiting.contains(&ty_id) {
        return false;
    }
    if program.view_ptr_types.contains(&ty_id) || program.loan_types.contains(&ty_id) {
        return true;
    }
    visiting.push(ty_id);
    let carries = match program.types.get(ty_id.0 as usize) {
        Some(Type::Ptr { .. }) => !program.raw_ptr_types.contains(&ty_id),
        Some(
            Type::Struct(fields)
            | Type::Overlay(fields)
            | Type::Union {
                variants: fields, ..
            },
        ) => fields.iter().any(|&f| carries_borrow(program, f, visiting)),
        Some(Type::Array { elem, .. }) => carries_borrow(program, *elem, visiting),
        _ => false,
    };
    visiting.pop();
    carries
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

/// Verifies that every function value stored into a function-pointer type satisfies that type's
/// borrow contract: its return may only borrow from parameters the contract lists, and it may only
/// perform the parameter-to-parameter flows the contract permits. Covers assignments, casts,
/// aggregates (including trait vtables built as globals), union payloads, and call arguments.
fn check_fn_value_contracts(
    program: &Program,
    summaries: &BTreeMap<FuncId, BTreeSet<LocalId>>,
    param_flows: &ParamFlows,
) -> Result<(), String> {
    let check = |fn_id: FuncId, ptr_ty: crate::ir::TypeId| -> Result<(), String> {
        let Some(contract) = fn_ptr_contract(program, ptr_ty) else {
            return Ok(());
        };
        let Some(target) = program.functions.iter().find(|f| f.id == fn_id) else {
            return Ok(()); // extern functions carry no inferred borrows
        };
        let holds_safe = |p: LocalId| {
            target
                .locals
                .get(p.base().0 as usize)
                .is_some_and(|&t| type_contains_safe_ptr(program, t))
        };
        if holds_safe(LocalId(0))
            && let Some(ret) = summaries.get(&fn_id)
        {
            for p in ret {
                if !origin_covered(contract.ret.iter(), *p) {
                    return Err(format!(
                        "Borrow check error: {} is used as a function pointer (or trait method) whose contract does not let the return value borrow from parameter '{}'; add it to the function type's or trait method's 'borrows(...)'",
                        target.label(),
                        p
                    ));
                }
            }
        }
        if let Some(flows) = param_flows.get(&fn_id) {
            for (&dst, srcs) in flows {
                for &src in srcs {
                    if dst != src
                        && holds_safe(dst)
                        && holds_safe(src)
                        && !contract.flows.contains(&(dst, src))
                    {
                        return Err(format!(
                            "Borrow check error: {} stores a borrow from parameter '{}' into parameter '{}', but is used as a function pointer (or trait method) whose contract does not permit it; add 'borrows({}: {})' to the function type or trait method signature",
                            target.label(),
                            src,
                            dst,
                            dst,
                            src
                        ));
                    }
                }
            }
        }
        Ok(())
    };
    let check_operand = |op: &Operand, ty: Option<crate::ir::TypeId>| -> Result<(), String> {
        if let (Operand::Const(ConstValue::Func(id)), Some(ty)) = (op, ty) {
            check(*id, ty)?;
        }
        Ok(())
    };
    fn check_const(
        program: &Program,
        val: &ConstValue,
        ty: crate::ir::TypeId,
        check: &dyn Fn(FuncId, crate::ir::TypeId) -> Result<(), String>,
    ) -> Result<(), String> {
        match (val, program.types.get(ty.0 as usize)) {
            (ConstValue::Func(id), _) => check(*id, ty),
            (ConstValue::Aggregate(items), Some(Type::Struct(fields))) => {
                for (item, &fty) in items.iter().zip(fields) {
                    check_const(program, item, fty, check)?;
                }
                Ok(())
            }
            (ConstValue::Aggregate(items), Some(Type::Array { elem, .. })) => {
                for item in items {
                    check_const(program, item, *elem, check)?;
                }
                Ok(())
            }
            _ => Ok(()),
        }
    }
    for g in &program.globals {
        check_const(program, &g.init, g.ty, &check)?;
    }
    for func in &program.functions {
        for block in &func.blocks {
            for stmt in &block.statements {
                let Statement::Assign(dest, rv) = stmt else {
                    continue;
                };
                match rv {
                    Rvalue::Use(op) => check_operand(op, place_type(program, func, dest))?,
                    Rvalue::Cast(op, ty) => check_operand(op, Some(*ty))?,
                    Rvalue::Aggregate(ty, ops) => match program.types.get(ty.0 as usize) {
                        Some(Type::Struct(fields)) => {
                            for (op, &fty) in ops.iter().zip(fields) {
                                check_operand(op, Some(fty))?;
                            }
                        }
                        Some(Type::Array { elem, .. } | Type::Simd { elem, .. }) => {
                            for op in ops {
                                check_operand(op, Some(*elem))?;
                            }
                        }
                        _ => {}
                    },
                    Rvalue::Union {
                        ty,
                        variant,
                        payload,
                    } => {
                        if let Some(Type::Union { variants, .. }) = program.types.get(ty.0 as usize)
                        {
                            check_operand(payload, variants.get(*variant as usize).copied())?;
                        }
                    }
                    _ => {}
                }
            }
            if let Terminator::Call { func: callee, args, .. } = &block.terminator {
                let param_tys: Option<Vec<crate::ir::TypeId>> = match callee {
                    Operand::Const(ConstValue::Func(id)) => program
                        .functions
                        .iter()
                        .find(|f| f.id == *id)
                        .map(|f| f.locals[1..=f.arg_count].to_vec())
                        .or_else(|| {
                            program
                                .externs
                                .iter()
                                .find(|e| e.id == *id)
                                .map(|e| e.args.clone())
                        }),
                    Operand::Copy(p) | Operand::Move(p) => place_type(program, func, p)
                        .and_then(|t| match program.types.get(t.0 as usize) {
                            Some(Type::FnPtr { args, .. }) => Some(args.clone()),
                            _ => None,
                        }),
                    _ => None,
                };
                if let Some(param_tys) = param_tys {
                    for (op, &pty) in args.iter().zip(&param_tys) {
                        check_operand(op, Some(pty))?;
                    }
                }
            }
        }
    }
    Ok(())
}

/// The type of `place` in `func`, following derefs, fields, variants, and indexing.
fn place_type(program: &Program, func: &Function, place: &Place) -> Option<crate::ir::TypeId> {
    let mut cur_ty = *func.locals.get(place.local.0 as usize)?;
    for proj in &place.projections {
        cur_ty = match (proj, program.types.get(cur_ty.0 as usize)?) {
            (Projection::Deref, Type::Ptr { pointee, .. }) => *pointee,
            (Projection::Field(i), Type::Struct(f) | Type::Overlay(f)) => *f.get(*i as usize)?,
            (Projection::Variant(i), Type::Union { variants, .. }) => *variants.get(*i as usize)?,
            (Projection::Index(_), Type::Array { elem, .. } | Type::Simd { elem, .. }) => *elem,
            _ => return None,
        };
    }
    Some(cur_ty)
}

fn fn_ptr_contract(program: &Program, ty: crate::ir::TypeId) -> Option<&FnContract> {
    program
        .fn_ptr_contracts
        .iter()
        .find(|(t, _)| *t == ty)
        .map(|(_, c)| c)
}

/// Whether storage reachable through a `borrows(dst: src)` destination argument can hold a reference
/// at all. For a pointer argument (`&mut T`) this is whether the pointee `T` contains a pointer, so
/// the contract is vacuous for instantiations such as `swap(i32, ...)` or `Vec(i32)::push`.
fn dst_can_store_ref(program: &Program, func: &Function, dst: &Place) -> bool {
    let mut through = dst.clone();
    through.projections.push(Projection::Deref);
    if place_type_contains_ptr(program, func, &through) {
        return true;
    }
    let mut cur_ty = match func.locals.get(dst.local.0 as usize) {
        Some(&t) => t,
        None => return false,
    };
    for proj in &dst.projections {
        let next = match (proj, program.types.get(cur_ty.0 as usize)) {
            (Projection::Deref, Some(Type::Ptr { pointee, .. })) => *pointee,
            (Projection::Field(i), Some(Type::Struct(f) | Type::Overlay(f))) => {
                match f.get(*i as usize) {
                    Some(&t) => t,
                    None => return true,
                }
            }
            (Projection::Variant(i), Some(Type::Union { variants, .. })) => {
                match variants.get(*i as usize) {
                    Some(&t) => t,
                    None => return true,
                }
            }
            (Projection::Index(_), Some(Type::Array { elem, .. })) => *elem,
            _ => return true,
        };
        cur_ty = next;
    }
    // Not a pointer itself: the destination value holds whatever pointers its type contains.
    !matches!(program.types.get(cur_ty.0 as usize), Some(Type::Ptr { .. }))
        && type_contains_ptr(program, cur_ty)
}

/// Whether `rval` makes a raw pointer of a reference. It keeps no loan alive, which is what such
/// a pointer is for: whoever turns it back into a reference answers for that with `unsafe`.
/// What is written through it still counts as a flow for a function's borrow contract.
fn leaves_borrows_behind(program: &Program, rval: &Rvalue) -> bool {
    let Rvalue::Cast(_, ty) = rval else {
        return false;
    };
    program.raw_ptr_types.contains(ty)
        && !program.own_ptr_types.contains(ty)
        && !program.view_ptr_types.contains(ty)
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

/// The `&mut v` pointer locals of elaborated destructor calls whose dropped type leaves the
/// borrows it holds unread (`Program::dangle_types`). Taking such a pointer is not a use of `v`
/// for liveness, so the borrows `v` holds may end before it is dropped.
fn dangling_drop_ptrs(program: &Program, func: &Function) -> BTreeSet<LocalId> {
    let mut ptrs = BTreeSet::new();
    for block in &func.blocks {
        if let Terminator::Call {
            func: Operand::Const(ConstValue::Func(callee)),
            args,
            ..
        } = &block.terminator
            && program.destructors.iter().any(|(_, f)| f == callee)
            && let [Operand::Move(p) | Operand::Copy(p)] = args.as_slice()
            && p.projections.is_empty()
            && let Some(&ptr_ty) = func.locals.get(p.local.0 as usize)
            && let Some(Type::Ptr { pointee, .. }) = program.types.get(ptr_ty.0 as usize)
            && drop_ignores_borrows(program, *pointee, &mut Vec::new())
        {
            ptrs.insert(p.local);
        }
    }
    ptrs
}

/// Whether dropping a value of `ty` leaves the borrows it holds unread: a type with a `drop` hook
/// qualifies only if Stage 2 listed it in `Program::dangle_types`; any other type qualifies when
/// all its parts do (dropping a pointer reads nothing).
fn drop_ignores_borrows(
    program: &Program,
    ty: crate::ir::TypeId,
    visiting: &mut Vec<crate::ir::TypeId>,
) -> bool {
    if visiting.contains(&ty) {
        return true;
    }
    if program.destructors.iter().any(|(t, _)| *t == ty) {
        return program.dangle_types.contains(&ty);
    }
    visiting.push(ty);
    let ignores = match program.types.get(ty.0 as usize) {
        Some(
            Type::Struct(parts)
            | Type::Union {
                variants: parts, ..
            },
        ) => parts.iter().all(|&p| drop_ignores_borrows(program, p, visiting)),
        Some(Type::Array { elem, .. }) => drop_ignores_borrows(program, *elem, visiting),
        _ => true,
    };
    visiting.pop();
    ignores
}

fn statement_reads_and_def(
    program: &Program,
    func: &Function,
    stmt: &Statement,
    dangling_drops: &BTreeSet<LocalId>,
) -> (BTreeSet<LocalId>, Option<LocalId>) {
    let mut reads = BTreeSet::new();
    let mut def = None;

    match stmt {
        Statement::Line(_) => {}
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
                Rvalue::Use(op)
                | Rvalue::UnaryOp(_, op)
                | Rvalue::Cast(op, _)
                | Rvalue::Transmute(op, _) => {
                    collect_operand_reads(op, &mut reads);
                }
                Rvalue::BinaryOp(_, l, r) => {
                    collect_operand_reads(l, &mut reads);
                    collect_operand_reads(r, &mut reads);
                }
                Rvalue::Ref { place, .. } => {
                    // Taking `&(*_p).0` reads the pointer `_p`, and borrowing a composite/closure
                    // that holds pointers inside its fields keeps that composite live! A drop that
                    // leaves its borrows unread does not.
                    // Only a value the function holds directly may outlive its borrows: dropping
                    // through a pointer (`@drop(r)`) still needs the pointer and what it points at.
                    let dangling_drop = dest.projections.is_empty()
                        && dangling_drops.contains(&dest.local)
                        && !place.projections.contains(&Projection::Deref);
                    if !dangling_drop
                        && (place.projections.contains(&Projection::Deref)
                            || func
                                .locals
                                .get(place.local.0 as usize)
                                .is_some_and(|&t| type_contains_ptr(program, t)))
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

fn terminator_reads_and_def(
    term: &Terminator,
    param_referent_locals: &[LocalId],
) -> (BTreeSet<LocalId>, Option<LocalId>) {
    let mut reads = BTreeSet::new();
    let mut def = None;

    match term {
        Terminator::Goto { .. } | Terminator::Unreachable => {}
        Terminator::Return => {
            reads.insert(LocalId(0));
            reads.extend(param_referent_locals.iter().copied());
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
    let at = std::cell::Cell::new(None);
    check_function_at(program, func, effective_summaries, param_flows, &at)
        .map_err(|e| crate::drop::with_line(func, e, at.get()))
}

fn check_function_at(
    program: &Program,
    func: &Function,
    effective_summaries: &BTreeMap<FuncId, BTreeSet<LocalId>>,
    param_flows: &ParamFlows,
    at: &std::cell::Cell<Option<(usize, usize)>>,
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
    let dangling_drops = dangling_drop_ptrs(program, func);
    let real_local_count = func.locals.len();
    let mut param_referent_locals: Vec<LocalId> = Vec::new();
    let mut param_referent_pairs: Vec<(usize, LocalId)> = Vec::new();
    for i in 1..=func.arg_count {
        if func
            .locals
            .get(i)
            .is_some_and(|&t| type_contains_safe_ptr(program, t))
        {
            let referent_loc = LocalId((real_local_count + i) as u32);
            param_referent_locals.push(referent_loc);
            param_referent_pairs.push((i, referent_loc));
        }
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
            let (t_reads, t_def) =
                terminator_reads_and_def(&block.terminator, &param_referent_locals);
            if let Some(d) = t_def {
                out.remove(&d);
            }
            out.extend(t_reads);

            for stmt in block.statements.iter().rev() {
                let (s_reads, s_def) = statement_reads_and_def(program, func, stmt, &dangling_drops);
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
    type PointsTo = FlowMap<LoanSet>;
    let mut points_to_in: Vec<PointsTo> = vec![FlowMap::default(); num_blocks];
    for &(i, referent_loc) in &param_referent_pairs {
        let contents_loc = LocalId((real_local_count + func.arg_count + i) as u32);
        let l_param = loans.len();
        loans.push(Loan {
            place: Place::new(referent_loc),
            mutable: false,
        });
        let l_contents = loans.len();
        loans.push(Loan {
            place: Place::new(contents_loc),
            mutable: false,
        });
        points_to_in[0].insert(LocalId(i as u32), LoanSet::from_one(l_param));
        points_to_in[0].insert(referent_loc, LoanSet::from_one(l_contents));
    }

    // The locals a store through a pointer holding `ptr_loans` writes: those its loans borrow,
    // less those it holds only because another of them holds a loan of them. `&v` carries the
    // loans `v` holds as well, and a store through it reaches `v`, not what `v` borrows.
    let store_targets = |pt: &PointsTo, ptr_loans: &LoanSet| -> Vec<LocalId> {
        let direct: Vec<usize> = ptr_loans
            .iter()
            .filter(|&l| !loans[l].place.projections.contains(&Projection::Deref))
            .collect();
        let mut out = Vec::new();
        for &l in &direct {
            let target = loans[l].place.local;
            let inherited = direct.iter().any(|&o| {
                loans[o].place.local != target
                    && pt.get(&loans[o].place.local).is_some_and(|ls| ls.contains(&l))
            });
            if !inherited && !out.contains(&target) {
                out.push(target);
            }
        }
        out
    };
    let apply_points_to_stmt =
        |bb_idx: usize, stmt_idx: usize, stmt: &Statement, pt: &mut PointsTo| {
            match stmt {
                Statement::StorageLive(l) | Statement::StorageDead(l) => {
                    pt.remove(l);
                }
                Statement::SetDiscriminant(_, _) | Statement::Line(_) => {}
                Statement::Assign(dest, rval) => {
                    let mut rhs_loans = LoanSet::new();
                    match rval {
                        Rvalue::Use(op)
                        | Rvalue::UnaryOp(_, op)
                        | Rvalue::Cast(op, _)
                        | Rvalue::Transmute(op, _) => {
                            if let Operand::Copy(p) | Operand::Move(p) = op
                                && place_type_contains_ptr(program, func, p)
                                && !leaves_borrows_behind(program, rval)
                                && let Some(ls) = pt.get(&p.local)
                            {
                                if p.projections.contains(&Projection::Deref) {
                                    // A value read through a pointer carries what the pointee
                                    // holds, not the borrow of the pointee itself (moving a `&i32`
                                    // out of `*p` does not keep `*p` borrowed).
                                    for l_id in ls.iter() {
                                        if !loans[l_id].place.projections.contains(&Projection::Deref) {
                                            let pointee = loans[l_id].place.local;
                                            if pointee != p.local
                                                && let Some(held) = pt.get(&pointee)
                                            {
                                                rhs_loans.union(held);
                                            }
                                        }
                                    }
                                } else {
                                    rhs_loans.union(ls);
                                }
                            }
                        }
                        Rvalue::BinaryOp(_, l, r) => {
                            for op in [l, r] {
                                if let Operand::Copy(p) | Operand::Move(p) = op
                                    && place_type_contains_ptr(program, func, p)
                                    && let Some(ls) = pt.get(&p.local)
                                {
                                    rhs_loans.union(ls);
                                }
                            }
                        }
                        Rvalue::Ref { place, .. } => {
                            let loan_id = ref_loan_map[&(bb_idx, stmt_idx)];
                            rhs_loans.insert(loan_id);
                            // If reborrowing through a pointer (`&(*_p)`) or borrowing a composite/closure
                            // that holds loans in its fields, inherit `_p`'s underlying loans too!
                            // However, if `dest` is a temporary `&mut field` synthesized to drop a field
                            // of a type with `may_dangle`, do NOT inherit dead loans held inside `place.local`.
                            let is_dangling_drop_ptr = dest.projections.is_empty()
                                && dangling_drops.contains(&dest.local);
                            if !is_dangling_drop_ptr
                                && let Some(ls) = pt.get(&place.local)
                            {
                                rhs_loans.union(ls);
                            }
                        }
                        Rvalue::Aggregate(_, ops) => {
                            for op in ops {
                                if let Operand::Copy(p) | Operand::Move(p) = op
                                    && place_type_contains_ptr(program, func, p)
                                    && let Some(ls) = pt.get(&p.local)
                                {
                                    rhs_loans.union(ls);
                                }
                            }
                        }
                        Rvalue::Union { payload, .. } => {
                            if let Operand::Copy(p) | Operand::Move(p) = payload
                                && place_type_contains_ptr(program, func, p)
                                && let Some(ls) = pt.get(&p.local)
                            {
                                rhs_loans.union(ls);
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
                            for target_loc in store_targets(pt, &ptr_loans) {
                                pt.entry(target_loc).or_default().union(&rhs_loans);
                            }
                        }
                        pt.entry(dest.local).or_default().extend(rhs_loans);
                    }
                }
            }
        };

    let mut dirty = vec![true; num_blocks];
    let mut pt_changed = true;
    while pt_changed {
        pt_changed = false;
        for bb in 0..num_blocks {
            if !std::mem::take(&mut dirty[bb]) {
                continue;
            }
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
                    let mut arg_loans = LoanSet::new();
                    // Direct calls use the callee's (declared or inferred) summary; calls through a
                    // function pointer use the contract carried by the pointer's type.
                    let ptr_contract = match callee_op {
                        Operand::Copy(p) | Operand::Move(p) => place_type(program, func, p)
                            .and_then(|t| fn_ptr_contract(program, t)),
                        Operand::Const(_) => None,
                    };
                    let ptr_summary: Option<BTreeSet<LocalId>> =
                        ptr_contract.map(|c| c.ret.iter().copied().collect());
                    let ptr_flows: Option<BTreeMap<LocalId, BTreeSet<LocalId>>> =
                        ptr_contract.map(|c| {
                            let mut m: BTreeMap<LocalId, BTreeSet<LocalId>> = BTreeMap::new();
                            for &(d, s) in &c.flows {
                                m.entry(d).or_default().insert(s);
                            }
                            m
                        });
                    let (summary_opt, flows_opt) = match callee_op {
                        Operand::Const(ConstValue::Func(callee_id)) => (
                            effective_summaries.get(callee_id),
                            param_flows.get(callee_id),
                        ),
                        _ => (ptr_summary.as_ref(), ptr_flows.as_ref()),
                    };
                    if let Some(summary) = summary_opt {
                        for param in summary {
                            let idx = param.base().0.saturating_sub(1) as usize;
                            if let Some(Operand::Copy(p) | Operand::Move(p)) = args.get(idx)
                                && let Some(ls) = pt.get(&p.local)
                            {
                                if param.is_contents() {
                                    // `borrows(*p)`: what the argument's referent holds, not a
                                    // borrow of the referent (`it.next()` borrows the sequence
                                    // `it` borrows, not `it`).
                                    for l_id in ls.iter() {
                                        if !loans[l_id].place.projections.contains(&Projection::Deref)
                                            && let Some(held) = pt.get(&loans[l_id].place.local)
                                        {
                                            arg_loans.union(held);
                                        }
                                    }
                                } else {
                                    arg_loans.union(ls);
                                }
                            }
                        }
                        if let Some(flows) = flows_opt {
                            for (&dst_param, src_params) in flows {
                                let dst_idx = dst_param.0.saturating_sub(1) as usize;
                                let mut flowed_loans = LoanSet::new();
                                for &sp in src_params {
                                    let s_idx = sp.0.saturating_sub(1) as usize;
                                    if let Some(Operand::Copy(p) | Operand::Move(p)) =
                                        args.get(s_idx)
                                        && let Some(ls) = pt.get(&p.local)
                                    {
                                        flowed_loans.union(ls);
                                    }
                                }
                                if !flowed_loans.is_empty()
                                    && let Some(Operand::Copy(dp) | Operand::Move(dp)) =
                                        args.get(dst_idx)
                                    // Vacuous flows in generic instantiations (`swap(i32, ..)`) are
                                    // skipped for direct calls; through a pointer or vtable (whose
                                    // `self` is type-erased) the written contract always applies.
                                    && (!matches!(callee_op, Operand::Const(_))
                                        || dst_can_store_ref(program, func, dp))
                                {
                                    if let Some(dst_ptr_loans) = pt.get(&dp.local).cloned() {
                                        for target_loc in store_targets(&pt, &dst_ptr_loans) {
                                            pt.entry(target_loc).or_default().union(&flowed_loans);
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
                                arg_loans.union(ls);
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
                if points_to_in[s_idx].join(&edge_pt) {
                    dirty[s_idx] = true;
                    pt_changed = true;
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
        let (t_reads, t_def) =
            terminator_reads_and_def(&block.terminator, &param_referent_locals);
        if let Some(d) = t_def {
            cur_live.remove(&d);
        }
        cur_live.extend(t_reads);

        for (i, stmt) in block.statements.iter().enumerate().rev() {
            live_after_stmt[i] = cur_live.clone();
            let (s_reads, s_def) = statement_reads_and_def(program, func, stmt, &dangling_drops);
            if let Some(d) = s_def {
                cur_live.remove(&d);
            }
            cur_live.extend(s_reads);
        }

        let mut pt = points_to_in[bb].clone();

        let active_loans_for =
            |pt_map: &PointsTo, live_locals: &BTreeSet<LocalId>| -> LoanSet {
                let mut active = LoanSet::new();
                for &loc in live_locals {
                    if let Some(ls) = pt_map.get(&loc) {
                        active.union(ls);
                    }
                }
                active
            };

        for (stmt_idx, stmt) in block.statements.iter().enumerate() {
            at.set(Some((bb, stmt_idx)));
            // Active loans across this statement are those held by locals that are live AFTER this statement
            // (or used within the statement itself, e.g. when a statement mutates `_1` and also reads a ref `_2` to `_1`!).
            let (s_reads, _) = statement_reads_and_def(program, func, stmt, &dangling_drops);
            let mut live_during = live_after_stmt[stmt_idx].clone();
            live_during.extend(s_reads);
            let active_before = active_loans_for(&pt, &live_during);

            match stmt {
                Statement::Line(_) => {}
                Statement::StorageLive(_) => {}
                Statement::StorageDead(local) => {
                    let active_after = active_loans_for(&pt, &live_after_stmt[stmt_idx]);
                    for loan_id in active_after {
                        let loan = &loans[loan_id];
                        if loan.place.local == *local
                            && !loan.place.projections.contains(&Projection::Deref)
                        {
                            return Err(format!(
                                "Borrow check error in {}: '{}' goes out of scope while still borrowed",
                                func.label(), func.place_label(program, &loan.place)
                            ));
                        }
                    }
                }
                Statement::SetDiscriminant(place, _) => {
                    check_deref_permissions(program, func, place, true, false)?;
                    check_write_conflicts(program, func, place, &active_before, &loans)?;
                }
                Statement::Assign(dest, rval) => {
                    check_deref_permissions(program, func, dest, true, false)?;

                    // 1. Check Rvalue reads, moves, and new borrows
                    match rval {
                        Rvalue::Use(op)
                        | Rvalue::UnaryOp(_, op)
                        | Rvalue::Cast(op, _)
                        | Rvalue::Transmute(op, _) => {
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
                                        func.label(),
                                        func.place_label(program, place),
                                        if *mutable { "mutable" } else { "immutable" },
                                        func.place_label(program, &other.place),
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
                            check_read_conflicts(program, func, place, &active_before, &loans)?;
                        }
                    }

                    // 2. Check LHS destination write conflicts against loans live AFTER this statement
                    let mut pt_after = pt.clone();
                    apply_points_to_stmt(bb, stmt_idx, stmt, &mut pt_after);
                    let active_after = active_loans_for(&pt_after, &live_after_stmt[stmt_idx]);
                    check_write_conflicts(program, func, dest, &active_after, &loans)?;
                }
            }

            apply_points_to_stmt(bb, stmt_idx, stmt, &mut pt);
        }

        // Check Terminator
        let (t_reads, _) =
            terminator_reads_and_def(&block.terminator, &param_referent_locals);
        let mut live_during_term = live_out[bb].clone();
        live_during_term.extend(t_reads);
        let active_term = active_loans_for(&pt, &live_during_term);

        at.set(Some((bb, block.statements.len())));
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
                check_write_conflicts(program, func, destination, &active_after_call, &loans)?;
            }
            Terminator::Drop { place, .. } => {
                let active_after_drop = active_loans_for(&pt, &live_out[bb]);
                check_write_conflicts(program, func, place, &active_after_drop, &loans)?;
            }
            Terminator::Return => {
                // At Return, `_0` cannot hold a loan to any local stack variable!
                // (Returning a reference derived from an incoming pointer argument `_1..=arg_count` via `(*_arg)` is allowed,
                //  whereas returning `&local` where `!loan.place.projections.contains(&Projection::Deref)` is a dangling stack pointer!)
                if let Some(ret_loans) = pt.get(&LocalId(0)) {
                    for loan_id in ret_loans.iter() {
                        let loan = &loans[loan_id];
                        if (loan.place.local.0 as usize) < real_local_count
                            && !loan.place.projections.contains(&Projection::Deref)
                        {
                            return Err(format!(
                                "Borrow check error in {}: cannot return reference to local variable '{}'",
                                func.label(), func.place_label(program, &loan.place)
                            ));
                        }
                    }
                }
                for &(param_idx, referent_loc) in &param_referent_pairs {
                    if let Some(ref_loans) = pt.get(&referent_loc) {
                        for loan_id in ref_loans.iter() {
                            let loan = &loans[loan_id];
                            if (loan.place.local.0 as usize) < real_local_count
                                && !loan.place.projections.contains(&Projection::Deref)
                            {
                                return Err(format!(
                                    "Borrow check error in {}: reference to local variable '{}' escapes through parameter '_{param_idx}'",
                                    func.label(), func.place_label(program, &loan.place)
                                ));
                            }
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
    active_loans: &LoanSet,
    loans: &[Loan],
) -> Result<(), String> {
    match op {
        Operand::Copy(place) => {
            check_deref_permissions(program, func, place, false, false)?;
            check_read_conflicts(program, func, place, active_loans, loans)
        }
        Operand::Move(place) => {
            check_deref_permissions(program, func, place, false, true)?;
            check_write_conflicts(program, func, place, active_loans, loans)
        }
        Operand::Const(_) => Ok(()),
    }
}

/// For an error about `place`: the wider or narrower place `loan` borrows, if not `place` itself.
fn via_loan(program: &Program, func: &Function, place: &Place, loan: &Loan) -> String {
    if *place == loan.place {
        String::new()
    } else {
        format!(" via '{}'", func.place_label(program, &loan.place))
    }
}

fn check_read_conflicts(
    program: &Program,
    func: &Function,
    place: &Place,
    active_loans: &LoanSet,
    loans: &[Loan],
) -> Result<(), String> {
    for loan_id in active_loans.iter() {
        let loan = &loans[loan_id];
        if loan.mutable && places_overlap(place, &loan.place) {
            return Err(format!(
                "Borrow check error in {}: cannot read '{}' because it is mutably borrowed{}",
                func.label(),
                func.place_label(program, place),
                via_loan(program, func, place, loan)
            ));
        }
    }
    Ok(())
}

/// Whether `loan` reaches its target through a `&T` held at `place`. It then borrows what the
/// reference points to, not the reference, which can change. Not so for `&mut T`: a reborrow
/// through one must stop it being moved, as both would be unique.
fn borrows_through_shared(program: &Program, func: &Function, place: &Place, loan: &Loan) -> bool {
    if loan.place.projections.get(place.projections.len()) != Some(&Projection::Deref) {
        return false;
    }
    let ty = place_type(program, func, place);
    ty.is_some_and(|t| matches!(program.types.get(t.0 as usize), Some(Type::Ptr { mutable: false, .. })))
}

fn check_write_conflicts(
    program: &Program,
    func: &Function,
    place: &Place,
    active_loans: &LoanSet,
    loans: &[Loan],
) -> Result<(), String> {
    for loan_id in active_loans.iter() {
        let loan = &loans[loan_id];
        if places_overlap(place, &loan.place) && !borrows_through_shared(program, func, place, loan) {
            return Err(format!(
                "Borrow check error in {}: cannot mutate or move '{}' because it is currently borrowed{}",
                func.label(),
                func.place_label(program, place),
                via_loan(program, func, place, loan)
            ));
        }
    }
    Ok(())
}
