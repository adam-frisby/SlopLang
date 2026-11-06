use std::collections::{BTreeMap, BTreeSet};
use std::rc::Rc;

use crate::ir::{
    BlockId, ConstValue, ExternFunc, FnContract, FuncId, Function, LocalId, Operand, Place,
    Program, Projection, Rvalue, Statement, Terminator, Type, TypeId,
};

#[derive(Debug, Clone, PartialEq, Eq)]
struct Loan {
    place: Place,
    mutable: bool,
}

/// Precomputed per-type and per-function lookup tables for `Program` so dataflow and conflict
/// checks do O(1) lookups instead of linear scans or recursive type walks.
struct BorrowCtx<'a> {
    program: &'a Program,
    has_ptr: Vec<bool>,
    has_safe_ptr: Vec<bool>,
    drop_ignores: Vec<bool>,
    is_raw_ptr: Vec<bool>,
    is_own_ptr: Vec<bool>,
    is_view_ptr: Vec<bool>,
    dtor_fns: BTreeSet<FuncId>,
    func_map: BTreeMap<FuncId, &'a Function>,
    extern_map: BTreeMap<FuncId, &'a ExternFunc>,
    fn_contracts: BTreeMap<TypeId, &'a FnContract>,
}

impl<'a> BorrowCtx<'a> {
    fn new(program: &'a Program) -> Self {
        let num_types = program.types.len();
        let mut is_raw_ptr = vec![false; num_types];
        let mut is_own_ptr = vec![false; num_types];
        let mut is_view_ptr = vec![false; num_types];
        for &t in &program.raw_ptr_types {
            if let Some(slot) = is_raw_ptr.get_mut(t.0 as usize) {
                *slot = true;
            }
        }
        for &t in &program.own_ptr_types {
            if let Some(slot) = is_own_ptr.get_mut(t.0 as usize) {
                *slot = true;
            }
        }
        for &t in &program.view_ptr_types {
            if let Some(slot) = is_view_ptr.get_mut(t.0 as usize) {
                *slot = true;
            }
        }
        let dtor_fns: BTreeSet<FuncId> = program.destructors.iter().map(|&(_, f)| f).collect();
        let func_map: BTreeMap<FuncId, &'a Function> =
            program.functions.iter().map(|f| (f.id, f)).collect();
        let extern_map: BTreeMap<FuncId, &'a ExternFunc> =
            program.externs.iter().map(|e| (e.id, e)).collect();
        let fn_contracts: BTreeMap<TypeId, &'a FnContract> = program
            .fn_ptr_contracts
            .iter()
            .map(|(t, c)| (*t, c))
            .collect();

        let mut has_ptr = vec![false; num_types];
        let mut has_safe_ptr = vec![false; num_types];
        let mut drop_ignores = vec![false; num_types];
        let mut visiting = Vec::new();
        for i in 0..num_types {
            let tid = TypeId(i as u32);
            has_ptr[i] = compute_type_contains_ptr(program, tid);
            visiting.clear();
            has_safe_ptr[i] = compute_carries_borrow(program, tid, &mut visiting);
            visiting.clear();
            drop_ignores[i] = compute_drop_ignores_borrows(program, tid, &mut visiting);
        }

        Self {
            program,
            has_ptr,
            has_safe_ptr,
            drop_ignores,
            is_raw_ptr,
            is_own_ptr,
            is_view_ptr,
            dtor_fns,
            func_map,
            extern_map,
            fn_contracts,
        }
    }

    #[inline]
    fn type_contains_ptr(&self, ty: TypeId) -> bool {
        self.has_ptr.get(ty.0 as usize).copied().unwrap_or(false)
    }

    #[inline]
    fn type_contains_safe_ptr(&self, ty: TypeId) -> bool {
        self.has_safe_ptr.get(ty.0 as usize).copied().unwrap_or(false)
    }

    #[inline]
    fn is_raw_ptr(&self, ty: TypeId) -> bool {
        self.is_raw_ptr.get(ty.0 as usize).copied().unwrap_or(false)
    }
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

/// Collects all `FuncId`s referenced as `ConstValue::Func` inside a `ConstValue`.
fn collect_const_funcs(val: &ConstValue, out: &mut Vec<FuncId>) {
    match val {
        ConstValue::Func(id) => out.push(*id),
        ConstValue::Aggregate(items) => {
            for item in items {
                collect_const_funcs(item, out);
            }
        }
        _ => {}
    }
}

/// Collects all `FuncId`s referenced as `ConstValue::Func` inside an `Operand`.
fn collect_op_funcs(op: &Operand, out: &mut Vec<FuncId>) {
    if let Operand::Const(c) = op {
        collect_const_funcs(c, out);
    }
}

/// Collects all `FuncId`s referenced inside `func`.
fn collect_func_refs(func: &Function, out: &mut Vec<FuncId>) {
    for block in &func.blocks {
        for stmt in &block.statements {
            if let Statement::Assign(_, rval) = stmt {
                match rval {
                    Rvalue::Use(op)
                    | Rvalue::UnaryOp(_, op)
                    | Rvalue::Cast(op, _)
                    | Rvalue::Transmute(op, _)
                    | Rvalue::Union { payload: op, .. } => collect_op_funcs(op, out),
                    Rvalue::BinaryOp(_, l, r)
                    | Rvalue::ArrayType { elem: l, len: r }
                    | Rvalue::SimdType { elem: l, len: r } => {
                        collect_op_funcs(l, out);
                        collect_op_funcs(r, out);
                    }
                    Rvalue::Aggregate(_, ops) | Rvalue::OverlayType(ops) => {
                        for op in ops {
                            collect_op_funcs(op, out);
                        }
                    }
                    Rvalue::UnionType { tag, variants } => {
                        collect_op_funcs(tag, out);
                        for op in variants {
                            collect_op_funcs(op, out);
                        }
                    }
                    Rvalue::PatternType { base, ranges } => {
                        collect_op_funcs(base, out);
                        for (lo, hi) in ranges {
                            collect_op_funcs(lo, out);
                            collect_op_funcs(hi, out);
                        }
                    }
                    Rvalue::Ref { .. } | Rvalue::Discriminant(_) => {}
                }
            }
        }
        if let Terminator::Call {
            func: callee, args, ..
        } = &block.terminator
        {
            collect_op_funcs(callee, out);
            for a in args {
                collect_op_funcs(a, out);
            }
        }
    }
}

/// `check_borrows` for the functions `checked` picks, against what every function borrows.
pub fn check_borrows_where(program: &Program, checked: impl Fn(FuncId) -> bool) -> Result<(), String> {
    let ctx = BorrowCtx::new(program);

    // Compute the set of functions reachable from `checked` functions (and globals) so incremental
    // archetype checks only summarize and validate the relevant call subgraph.
    let mut reachable: BTreeSet<FuncId> = BTreeSet::new();
    let mut worklist: Vec<FuncId> = Vec::new();
    for func in &program.functions {
        if checked(func.id) && reachable.insert(func.id) {
            worklist.push(func.id);
        }
    }
    if reachable.is_empty() {
        return Ok(());
    }
    let mut g_refs = Vec::new();
    for g in &program.globals {
        collect_const_funcs(&g.init, &mut g_refs);
    }
    for id in g_refs {
        if reachable.insert(id) {
            worklist.push(id);
        }
    }
    let mut refs_buf = Vec::new();
    while let Some(fid) = worklist.pop() {
        if let Some(&f) = ctx.func_map.get(&fid) {
            refs_buf.clear();
            collect_func_refs(f, &mut refs_buf);
            for &callee in &refs_buf {
                if reachable.insert(callee) {
                    worklist.push(callee);
                }
            }
        }
    }

    let (inferred_origins, param_flows) = infer_borrow_summaries(&ctx, &reachable);
    let mut effective_summaries: BTreeMap<FuncId, BTreeSet<LocalId>> = BTreeMap::new();
    let mut effective_param_flows: ParamFlows = BTreeMap::new();
    for &fid in &reachable {
        let Some(&func) = ctx.func_map.get(&fid) else {
            continue;
        };
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

    check_fn_value_contracts(&ctx, &reachable, &effective_summaries, &effective_param_flows)?;

    // Each function is checked on its own, so one compile reports what is wrong in each.
    let mut errors: Vec<String> = Vec::new();
    for func in program.functions.iter().filter(|f| checked(f.id)) {
        let checked_one = (|| -> Result<(), String> {
            if let Some(explicit) = &func.ret_borrows
                && let Some(actual_origins) = inferred_origins.get(&func.id)
            {
                for &origin_param in actual_origins {
                    // A parameter that cannot carry a borrow (a raw or owning pointer) needs no clause.
                    let carries = func
                        .locals
                        .get(origin_param.base().0 as usize)
                        .is_some_and(|&t| ctx.type_contains_safe_ptr(t));
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
                                .is_some_and(|&t| ctx.type_contains_safe_ptr(t))
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
            check_function(&ctx, func, &effective_summaries, &effective_param_flows)?;
            Ok(())
        })();
        if let Err(e) = checked_one
            && !errors.contains(&e)
        {
            errors.push(e);
        }
    }
    if errors.is_empty() { Ok(()) } else { Err(errors.join("\nerror: ")) }
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

    fn remove(&mut self, loan: usize) {
        if let Some(word) = self.bits.get_mut(loan / 64) {
            *word &= !(1 << (loan % 64));
        }
    }

    fn subtract(&mut self, other: &LoanSet) {
        for (word, kill) in self.bits.iter_mut().zip(&other.bits) {
            *word &= !*kill;
        }
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

    fn iter_intersect<'a>(&'a self, other: &'a LoanSet) -> impl Iterator<Item = usize> + 'a {
        self.bits
            .iter()
            .zip(&other.bits)
            .enumerate()
            .flat_map(|(i, (&w1, &w2))| {
                let word = w1 & w2;
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

/// Computes, for every reachable function in `program`:
/// 1. Which 1-based parameter locals (`_1..=arg_count`) its return place `_0` may borrow from at `return;`.
/// 2. Which parameter locals may flow into which other mutable parameter locals (`param_flows`, e.g. `stash(dst, x)`).
fn infer_borrow_summaries(
    ctx: &BorrowCtx<'_>,
    reachable: &BTreeSet<FuncId>,
) -> (BTreeMap<FuncId, BTreeSet<LocalId>>, ParamFlows) {
    let program = ctx.program;
    let mut inferred: BTreeMap<FuncId, BTreeSet<LocalId>> = BTreeMap::new();
    let mut param_flows: ParamFlows = BTreeMap::new();

    // Only functions with >= 1 parameter that can either return a safe pointer or flow between >= 2
    // parameters can ever produce non-empty `inferred` or `param_flows` entries.
    let mut active_funcs: Vec<&Function> = Vec::new();
    let mut callers_of: BTreeMap<FuncId, Vec<usize>> = BTreeMap::new();
    for &fid in reachable {
        let Some(&func) = ctx.func_map.get(&fid) else {
            continue;
        };
        inferred.insert(func.id, BTreeSet::new());
        param_flows.insert(func.id, BTreeMap::new());
        if func.blocks.is_empty()
            || func.arg_count == 0
            || (func.arg_count == 1 && !ctx.type_contains_safe_ptr(func.locals[0]))
        {
            continue;
        }
        let idx = active_funcs.len();
        active_funcs.push(func);
        for block in &func.blocks {
            if let Terminator::Call {
                func: Operand::Const(ConstValue::Func(callee_id)),
                ..
            } = &block.terminator
            {
                let list = callers_of.entry(*callee_id).or_default();
                if list.last().copied() != Some(idx) {
                    list.push(idx);
                }
            }
        }
    }

    let mut need_eval = vec![true; active_funcs.len()];
    let mut any_need_eval = !active_funcs.is_empty();
    while any_need_eval {
        any_need_eval = false;
        let current_eval = std::mem::replace(&mut need_eval, vec![false; active_funcs.len()]);
        for (func_idx, &func) in active_funcs.iter().enumerate() {
            if !current_eval[func_idx] {
                continue;
            }
            let num_blocks = func.blocks.len();
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
            let mut func_summary_changed = false;
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
                                            && place_type_contains_ptr(ctx, func, p)
                                        {
                                            if p.projections.contains(&Projection::Deref) {
                                                if reads_held_borrow(ctx, func, p) {
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
                                                && place_type_contains_ptr(ctx, func, p)
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
                                            if refs_through_held_borrow(ctx, func, place) {
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
                                                        ctx.type_contains_safe_ptr(t)
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
                                                && place_type_contains_ptr(ctx, func, p)
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
                                let dest_has_ptr = place_type_contains_ptr(ctx, func, dest);
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
                                Operand::Const(ConstValue::Func(callee_id)) => ctx
                                    .func_map
                                    .get(callee_id)
                                    .map(|&callee_fn| {
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
                                    .and_then(|t| ctx.fn_contracts.get(&t).copied())
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
                                .is_some_and(|&t| ctx.type_contains_ptr(t));
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
                            if ctx.type_contains_safe_ptr(func.locals[0])
                                && let Some(ret_os) = orig.get(&LocalId(0))
                            {
                                let entry = inferred.entry(func.id).or_default();
                                let before = entry.len();
                                entry.extend(ret_os.iter().copied().filter(|o| {
                                    let b = o.base().0 as usize;
                                    b >= 1 && b <= func.arg_count
                                }));
                                if entry.len() != before {
                                    func_summary_changed = true;
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
                                                    func_summary_changed = true;
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
            if func_summary_changed
                && let Some(callers) = callers_of.get(&func.id)
            {
                for &caller_idx in callers {
                    need_eval[caller_idx] = true;
                    any_need_eval = true;
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
fn collect_place_reads(place: &Place, is_lhs_write: bool, out: &mut LoanSet) {
    if !is_lhs_write || place.projections.contains(&Projection::Deref) {
        out.insert(place.local.0 as usize);
    }
    for proj in &place.projections {
        if let Projection::Index(idx_local) = proj {
            out.insert(idx_local.0 as usize);
        }
    }
}

fn collect_operand_reads(op: &Operand, out: &mut LoanSet) {
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
fn reads_held_borrow(ctx: &BorrowCtx<'_>, func: &Function, place: &Place) -> bool {
    let root_carries_borrow = func
        .locals
        .get(place.local.0 as usize)
        .is_some_and(|&t| ctx.type_contains_safe_ptr(t));
    let root_is_raw = func
        .locals
        .get(place.local.0 as usize)
        .is_some_and(|&t| ctx.is_raw_ptr(t));
    let deref_count = place
        .projections
        .iter()
        .filter(|p| matches!(p, Projection::Deref))
        .count();
    (root_carries_borrow || root_is_raw || deref_count >= 2)
        && place.projections.contains(&Projection::Deref)
        && place_type(ctx.program, func, place).is_some_and(|t| ctx.type_contains_safe_ptr(t))
}

/// Whether `&place` points into memory a shared borrow or `*ref` view held by its root refers to:
/// past the first dereference of a borrow-carrying root, it dereferences a shared reference (`&T`)
/// or a `*ref T` / `*ref mut T` view (`&*self.p`), not an owning pointer, raw pointer, or safe
/// `&mut T` reference (since a safe `&mut T` held inside `*p` retains exclusive access unless `p`
/// itself stays borrowed).
fn refs_through_held_borrow(ctx: &BorrowCtx<'_>, func: &Function, place: &Place) -> bool {
    let Some(mut ty) = func.locals.get(place.local.0 as usize).copied() else {
        return false;
    };
    let mut derefs = 0;
    for proj in &place.projections {
        let Some(cur) = ctx.program.types.get(ty.0 as usize) else {
            return false;
        };
        ty = match (proj, cur) {
            (Projection::Deref, Type::Ptr { mutable, pointee }) => {
                if derefs == 0 && !ctx.type_contains_safe_ptr(ty) {
                    return false;
                }
                if derefs > 0
                    && ((!*mutable && !ctx.is_raw_ptr(ty))
                        || ctx.is_view_ptr.get(ty.0 as usize).copied().unwrap_or(false))
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

fn compute_carries_borrow(
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
        ) => fields.iter().any(|&f| compute_carries_borrow(program, f, visiting)),
        Some(Type::Array { elem, .. }) => compute_carries_borrow(program, *elem, visiting),
        _ => false,
    };
    visiting.pop();
    carries
}

fn compute_type_contains_ptr(program: &Program, ty_id: crate::ir::TypeId) -> bool {
    match program.types.get(ty_id.0 as usize) {
        Some(Type::Ptr { .. }) => true,
        Some(
            Type::Struct(fields)
            | Type::Overlay(fields)
            | Type::Union {
                variants: fields, ..
            },
        ) => fields.iter().any(|&f| compute_type_contains_ptr(program, f)),
        Some(Type::Array { elem, .. }) => compute_type_contains_ptr(program, *elem),
        _ => false,
    }
}

/// Verifies that every function value stored into a function-pointer type satisfies that type's
/// borrow contract: its return may only borrow from parameters the contract lists, and it may only
/// perform the parameter-to-parameter flows the contract permits. Covers assignments, casts,
/// aggregates (including trait vtables built as globals), union payloads, and call arguments.
fn check_fn_value_contracts(
    ctx: &BorrowCtx<'_>,
    reachable: &BTreeSet<FuncId>,
    summaries: &BTreeMap<FuncId, BTreeSet<LocalId>>,
    param_flows: &ParamFlows,
) -> Result<(), String> {
    let program = ctx.program;
    let check = |fn_id: FuncId, ptr_ty: crate::ir::TypeId| -> Result<(), String> {
        let Some(&contract) = ctx.fn_contracts.get(&ptr_ty) else {
            return Ok(());
        };
        let Some(&target) = ctx.func_map.get(&fn_id) else {
            return Ok(()); // extern functions carry no inferred borrows
        };
        let holds_safe = |p: LocalId| {
            target
                .locals
                .get(p.base().0 as usize)
                .is_some_and(|&t| ctx.type_contains_safe_ptr(t))
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
    for &fid in reachable {
        let Some(&func) = ctx.func_map.get(&fid) else {
            continue;
        };
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
                let param_tys: Option<&[crate::ir::TypeId]> = match callee {
                    Operand::Const(ConstValue::Func(id)) => ctx
                        .func_map
                        .get(id)
                        .map(|f| &f.locals[1..=f.arg_count])
                        .or_else(|| ctx.extern_map.get(id).map(|e| e.args.as_slice())),
                    Operand::Copy(p) | Operand::Move(p) => place_type(program, func, p)
                        .and_then(|t| match program.types.get(t.0 as usize) {
                            Some(Type::FnPtr { args, .. }) => Some(args.as_slice()),
                            _ => None,
                        }),
                    _ => None,
                };
                if let Some(param_tys) = param_tys {
                    for (op, &pty) in args.iter().zip(param_tys) {
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

/// Whether storage reachable through a `borrows(dst: src)` destination argument can hold a reference
/// at all. For a pointer argument (`&mut T`) this is whether the pointee `T` contains a pointer, so
/// the contract is vacuous for instantiations such as `swap(i32, ...)` or `Vec(i32)::push`.
fn dst_can_store_ref(ctx: &BorrowCtx<'_>, func: &Function, dst: &Place) -> bool {
    let mut through = dst.clone();
    through.projections.push(Projection::Deref);
    if place_type_contains_ptr(ctx, func, &through) {
        return true;
    }
    let mut cur_ty = match func.locals.get(dst.local.0 as usize) {
        Some(&t) => t,
        None => return false,
    };
    for proj in &dst.projections {
        let next = match (proj, ctx.program.types.get(cur_ty.0 as usize)) {
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
    !matches!(ctx.program.types.get(cur_ty.0 as usize), Some(Type::Ptr { .. }))
        && ctx.type_contains_ptr(cur_ty)
}

/// Whether `rval` makes a raw pointer of a reference. It keeps no loan alive, which is what such
/// a pointer is for: whoever turns it back into a reference answers for that with `unsafe`.
/// What is written through it still counts as a flow for a function's borrow contract.
fn leaves_borrows_behind(ctx: &BorrowCtx<'_>, rval: &Rvalue) -> bool {
    let Rvalue::Cast(_, ty) = rval else {
        return false;
    };
    let idx = ty.0 as usize;
    ctx.is_raw_ptr.get(idx).copied().unwrap_or(false)
        && !ctx.is_own_ptr.get(idx).copied().unwrap_or(false)
        && !ctx.is_view_ptr.get(idx).copied().unwrap_or(false)
}

fn place_type_contains_ptr(ctx: &BorrowCtx<'_>, func: &Function, place: &Place) -> bool {
    let Some(&(mut cur_ty)) = func.locals.get(place.local.0 as usize) else {
        return false;
    };
    for proj in &place.projections {
        match proj {
            Projection::Deref => {
                let Some(Type::Ptr { pointee, .. }) = ctx.program.types.get(cur_ty.0 as usize)
                else {
                    return false;
                };
                cur_ty = *pointee;
            }
            Projection::Field(idx) => {
                let Some(Type::Struct(fields) | Type::Overlay(fields)) =
                    ctx.program.types.get(cur_ty.0 as usize)
                else {
                    return false;
                };
                let Some(&fty) = fields.get(*idx as usize) else {
                    return false;
                };
                cur_ty = fty;
            }
            Projection::Variant(idx) => {
                let Some(Type::Union { variants, .. }) = ctx.program.types.get(cur_ty.0 as usize)
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
                    ctx.program.types.get(cur_ty.0 as usize)
                else {
                    return false;
                };
                cur_ty = *elem;
            }
        }
    }
    ctx.type_contains_ptr(cur_ty)
}

/// The `&mut v` pointer locals of elaborated destructor calls whose dropped type leaves the
/// borrows it holds unread (`Program::dangle_types`). Taking such a pointer is not a use of `v`
/// for liveness, so the borrows `v` holds may end before it is dropped.
fn dangling_drop_ptrs(ctx: &BorrowCtx<'_>, func: &Function) -> BTreeSet<LocalId> {
    let mut ptrs = BTreeSet::new();
    for block in &func.blocks {
        if let Terminator::Call {
            func: Operand::Const(ConstValue::Func(callee)),
            args,
            ..
        } = &block.terminator
            && ctx.dtor_fns.contains(callee)
            && let [Operand::Move(p) | Operand::Copy(p)] = args.as_slice()
            && p.projections.is_empty()
            && let Some(&ptr_ty) = func.locals.get(p.local.0 as usize)
            && let Some(Type::Ptr { pointee, .. }) = ctx.program.types.get(ptr_ty.0 as usize)
            && ctx.drop_ignores.get(pointee.0 as usize).copied().unwrap_or(false)
        {
            ptrs.insert(p.local);
        }
    }
    ptrs
}

/// Whether dropping a value of `ty` leaves the borrows it holds unread: a type with a `drop` hook
/// qualifies only if Stage 2 listed it in `Program::dangle_types`; any other type qualifies when
/// all its parts do (dropping a pointer reads nothing).
fn compute_drop_ignores_borrows(
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
        ) => parts
            .iter()
            .all(|&p| compute_drop_ignores_borrows(program, p, visiting)),
        Some(Type::Array { elem, .. }) => compute_drop_ignores_borrows(program, *elem, visiting),
        _ => true,
    };
    visiting.pop();
    ignores
}

fn statement_reads_and_def(
    ctx: &BorrowCtx<'_>,
    func: &Function,
    stmt: &Statement,
    dangling_drops: &BTreeSet<LocalId>,
) -> (LoanSet, Option<LocalId>) {
    let mut reads = LoanSet::new();
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
                                .is_some_and(|&t| ctx.type_contains_ptr(t)))
                    {
                        reads.insert(place.local.0 as usize);
                    }
                    for proj in &place.projections {
                        if let Projection::Index(idx_local) = proj {
                            reads.insert(idx_local.0 as usize);
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
) -> (LoanSet, Option<LocalId>) {
    let mut reads = LoanSet::new();
    let mut def = None;

    match term {
        Terminator::Goto { .. } | Terminator::Unreachable => {}
        Terminator::Return => {
            reads.insert(0);
            for &loc in param_referent_locals {
                reads.insert(loc.0 as usize);
            }
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
    ctx: &BorrowCtx<'_>,
    func: &Function,
    effective_summaries: &BTreeMap<FuncId, BTreeSet<LocalId>>,
    param_flows: &ParamFlows,
) -> Result<(), String> {
    let at = std::cell::Cell::new(None);
    check_function_at(ctx, func, effective_summaries, param_flows, &at)
        .map_err(|e| crate::drop::with_line(func, e, at.get()))
}

fn check_function_at(
    ctx: &BorrowCtx<'_>,
    func: &Function,
    effective_summaries: &BTreeMap<FuncId, BTreeSet<LocalId>>,
    param_flows: &ParamFlows,
    at: &std::cell::Cell<Option<(usize, usize)>>,
) -> Result<(), String> {
    let program = ctx.program;
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
    let dangling_drops = dangling_drop_ptrs(ctx, func);
    let real_local_count = func.locals.len();
    let mut param_referent_locals: Vec<LocalId> = Vec::new();
    let mut param_referent_pairs: Vec<(usize, LocalId)> = Vec::new();
    for i in 1..=func.arg_count {
        if func
            .locals
            .get(i)
            .is_some_and(|&t| ctx.type_contains_safe_ptr(t))
        {
            let referent_loc = LocalId((real_local_count + i) as u32);
            param_referent_locals.push(referent_loc);
            param_referent_pairs.push((i, referent_loc));
        }
    }

    // Precompute per-statement and per-terminator (reads, def) once, and summarize each basic
    // block into `(block_gen, block_kill)` bitsets so the backward liveness fixed-point loop runs
    // in O(words) per block.
    let mut block_stmt_rw: Vec<Vec<(LoanSet, Option<LocalId>)>> = Vec::with_capacity(num_blocks);
    let mut block_term_rw: Vec<(LoanSet, Option<LocalId>)> = Vec::with_capacity(num_blocks);
    let mut block_gen: Vec<LoanSet> = Vec::with_capacity(num_blocks);
    let mut block_kill: Vec<LoanSet> = Vec::with_capacity(num_blocks);

    for bb in 0..num_blocks {
        let block = &func.blocks[bb];
        let mut stmts_rw = Vec::with_capacity(block.statements.len());
        for stmt in &block.statements {
            stmts_rw.push(statement_reads_and_def(ctx, func, stmt, &dangling_drops));
        }
        let (t_reads, t_def) =
            terminator_reads_and_def(&block.terminator, &param_referent_locals);

        let mut b_gen = LoanSet::new();
        let mut kill = LoanSet::new();
        if let Some(d) = t_def {
            b_gen.remove(d.0 as usize);
            kill.insert(d.0 as usize);
        }
        b_gen.union(&t_reads);
        for (s_reads, s_def) in stmts_rw.iter().rev() {
            if let Some(d) = s_def {
                b_gen.remove(d.0 as usize);
                kill.insert(d.0 as usize);
            }
            b_gen.union(s_reads);
        }

        block_stmt_rw.push(stmts_rw);
        block_term_rw.push((t_reads, t_def));
        block_gen.push(b_gen);
        block_kill.push(kill);
    }

    // 1. Backward Liveness Analysis for Locals
    // `live_out[bb]` is the set of locals live at the exit of `bb`.
    // `live_in[bb]` is the set of locals live at the entry of `bb`.
    let mut live_in: Vec<LoanSet> = vec![LoanSet::new(); num_blocks];
    let mut live_out: Vec<LoanSet> = vec![LoanSet::new(); num_blocks];

    let mut changed = true;
    while changed {
        changed = false;
        for bb in (0..num_blocks).rev() {
            let block = &func.blocks[bb];
            let mut out = LoanSet::new();
            match &block.terminator {
                Terminator::Goto { target }
                | Terminator::Call { target, .. }
                | Terminator::Drop { target, .. } => {
                    out.union(&live_in[target.0 as usize]);
                }
                Terminator::SwitchInt {
                    targets, otherwise, ..
                } => {
                    for (_, t) in targets {
                        out.union(&live_in[t.0 as usize]);
                    }
                    out.union(&live_in[otherwise.0 as usize]);
                }
                Terminator::Return | Terminator::Unreachable => {}
            }

            if live_out[bb] != out {
                live_out[bb] = out.clone();
                changed = true;
            }

            out.subtract(&block_kill[bb]);
            out.union(&block_gen[bb]);

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

    // Index loans by their root `place.local` so conflict checks only inspect loans on the same local.
    let max_local = real_local_count + 2 * func.arg_count + 2;
    let mut loans_by_local: Vec<LoanSet> = vec![LoanSet::new(); max_local];
    for (loan_id, loan) in loans.iter().enumerate() {
        let loc = loan.place.local.0 as usize;
        if loc >= loans_by_local.len() {
            loans_by_local.resize(loc + 1, LoanSet::new());
        }
        loans_by_local[loc].insert(loan_id);
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
                                && place_type_contains_ptr(ctx, func, p)
                                && !leaves_borrows_behind(ctx, rval)
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
                                    && place_type_contains_ptr(ctx, func, p)
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
                                    && place_type_contains_ptr(ctx, func, p)
                                    && let Some(ls) = pt.get(&p.local)
                                {
                                    rhs_loans.union(ls);
                                }
                            }
                        }
                        Rvalue::Union { payload, .. } => {
                            if let Operand::Copy(p) | Operand::Move(p) = payload
                                && place_type_contains_ptr(ctx, func, p)
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

                    let dest_has_ptr = place_type_contains_ptr(ctx, func, dest);
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
                            .and_then(|t| ctx.fn_contracts.get(&t).copied()),
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
                                        || dst_can_store_ref(ctx, func, dp))
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
                        .is_some_and(|&t| ctx.type_contains_ptr(t));
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
        let stmts_rw = &block_stmt_rw[bb];
        let (t_reads, t_def) = &block_term_rw[bb];

        // Compute the exact set of live locals AFTER each statement `i` (`live_after_stmt[i]`)
        // and AFTER the terminator (`live_out[bb]`).
        let mut live_after_stmt: Vec<LoanSet> = vec![LoanSet::new(); block.statements.len()];
        let mut cur_live = live_out[bb].clone();
        if let Some(d) = t_def {
            cur_live.remove(d.0 as usize);
        }
        cur_live.union(t_reads);

        for (i, (s_reads, s_def)) in stmts_rw.iter().enumerate().rev() {
            live_after_stmt[i] = cur_live.clone();
            if let Some(d) = s_def {
                cur_live.remove(d.0 as usize);
            }
            cur_live.union(s_reads);
        }

        let mut pt = points_to_in[bb].clone();

        let active_loans_for =
            |pt_map: &PointsTo, live_locals: &LoanSet| -> LoanSet {
                let mut active = LoanSet::new();
                for (loc, ls) in &pt_map.entries {
                    if live_locals.contains(&(loc.0 as usize)) {
                        active.union(ls);
                    }
                }
                active
            };

        for (stmt_idx, stmt) in block.statements.iter().enumerate() {
            at.set(Some((bb, stmt_idx)));
            // Active loans across this statement are those held by locals that are live AFTER this statement
            // (or used within the statement itself, e.g. when a statement mutates `_1` and also reads a ref `_2` to `_1`!).
            let (s_reads, _) = &stmts_rw[stmt_idx];

            match stmt {
                Statement::Line(_) => {}
                Statement::StorageLive(l) => {
                    pt.remove(l);
                }
                Statement::StorageDead(local) => {
                    if let Some(local_loans) = loans_by_local.get(local.0 as usize)
                        && !local_loans.is_empty()
                    {
                        let active_after = active_loans_for(&pt, &live_after_stmt[stmt_idx]);
                        for loan_id in active_after.iter_intersect(local_loans) {
                            let loan = &loans[loan_id];
                            if !loan.place.projections.contains(&Projection::Deref) {
                                return Err(format!(
                                    "Borrow check error in {}: '{}' goes out of scope while still borrowed",
                                    func.label(), func.place_label(program, &loan.place)
                                ));
                            }
                        }
                    }
                    pt.remove(local);
                }
                Statement::SetDiscriminant(place, _) => {
                    let mut live_during = live_after_stmt[stmt_idx].clone();
                    live_during.union(s_reads);
                    let active_before = active_loans_for(&pt, &live_during);
                    check_deref_permissions(program, func, place, true, false)?;
                    check_write_conflicts(
                        program,
                        func,
                        place,
                        &active_before,
                        &loans,
                        &loans_by_local,
                    )?;
                }
                Statement::Assign(dest, rval) => {
                    check_deref_permissions(program, func, dest, true, false)?;

                    let mut live_during = live_after_stmt[stmt_idx].clone();
                    live_during.union(s_reads);
                    let active_before = active_loans_for(&pt, &live_during);

                    // 1. Check Rvalue reads and moves before updating `pt`
                    let mut ref_reborrow_loans: Option<LoanSet> = None;
                    match rval {
                        Rvalue::Use(op)
                        | Rvalue::UnaryOp(_, op)
                        | Rvalue::Cast(op, _)
                        | Rvalue::Transmute(op, _) => {
                            check_operand_borrows(
                                program,
                                func,
                                op,
                                &active_before,
                                &loans,
                                &loans_by_local,
                            )?;
                        }
                        Rvalue::BinaryOp(_, l, r) => {
                            check_operand_borrows(
                                program,
                                func,
                                l,
                                &active_before,
                                &loans,
                                &loans_by_local,
                            )?;
                            check_operand_borrows(
                                program,
                                func,
                                r,
                                &active_before,
                                &loans,
                                &loans_by_local,
                            )?;
                        }
                        Rvalue::Ref { mutable, place } => {
                            check_deref_permissions(program, func, place, *mutable, false)?;
                            if place.projections.contains(&Projection::Deref) {
                                ref_reborrow_loans = pt.get(&place.local).cloned();
                            }
                        }
                        Rvalue::Aggregate(_, ops) | Rvalue::OverlayType(ops) => {
                            for op in ops {
                                check_operand_borrows(
                                    program,
                                    func,
                                    op,
                                    &active_before,
                                    &loans,
                                    &loans_by_local,
                                )?;
                            }
                        }
                        Rvalue::ArrayType { elem, len } | Rvalue::SimdType { elem, len } => {
                            check_operand_borrows(
                                program,
                                func,
                                elem,
                                &active_before,
                                &loans,
                                &loans_by_local,
                            )?;
                            check_operand_borrows(
                                program,
                                func,
                                len,
                                &active_before,
                                &loans,
                                &loans_by_local,
                            )?;
                        }
                        Rvalue::UnionType { tag, variants } => {
                            check_operand_borrows(
                                program,
                                func,
                                tag,
                                &active_before,
                                &loans,
                                &loans_by_local,
                            )?;
                            for op in variants {
                                check_operand_borrows(
                                    program,
                                    func,
                                    op,
                                    &active_before,
                                    &loans,
                                    &loans_by_local,
                                )?;
                            }
                        }
                        Rvalue::PatternType { base, ranges } => {
                            check_operand_borrows(
                                program,
                                func,
                                base,
                                &active_before,
                                &loans,
                                &loans_by_local,
                            )?;
                            for (lo, hi) in ranges {
                                check_operand_borrows(
                                    program,
                                    func,
                                    lo,
                                    &active_before,
                                    &loans,
                                    &loans_by_local,
                                )?;
                                check_operand_borrows(
                                    program,
                                    func,
                                    hi,
                                    &active_before,
                                    &loans,
                                    &loans_by_local,
                                )?;
                            }
                        }
                        Rvalue::Union { payload, .. } => {
                            check_operand_borrows(
                                program,
                                func,
                                payload,
                                &active_before,
                                &loans,
                                &loans_by_local,
                            )?;
                        }
                        Rvalue::Discriminant(place) => {
                            check_deref_permissions(program, func, place, false, false)?;
                            check_read_conflicts(
                                program,
                                func,
                                place,
                                &active_before,
                                &loans,
                                &loans_by_local,
                            )?;
                        }
                    }

                    // Advance `pt` once in-place across this statement
                    apply_points_to_stmt(bb, stmt_idx, stmt, &mut pt);
                    let active_after = active_loans_for(&pt, &live_after_stmt[stmt_idx]);

                    // If this was an `Rvalue::Ref`, check conflicts with all other loans live after the statement
                    if let Rvalue::Ref { mutable, place } = rval
                        && let Some(local_loans) = loans_by_local.get(place.local.0 as usize)
                        && !local_loans.is_empty()
                    {
                        let new_loan_id = ref_loan_map[&(bb, stmt_idx)];
                        for other_id in active_after.iter_intersect(local_loans) {
                            if other_id == new_loan_id {
                                continue;
                            }
                            // If `new_loan` is a reborrow of `other_id` (e.g. `_3 = &mut (*_2)` where `_2` holds `other_id`),
                            // reborrowing from `_2` is allowed as long as `_2` itself isn't accessed while `_3` is live!
                            if ref_reborrow_loans
                                .as_ref()
                                .is_some_and(|ls| ls.contains(&other_id))
                            {
                                continue;
                            }
                            let other = &loans[other_id];
                            if (*mutable || other.mutable) && places_overlap(place, &other.place) {
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

                    // 2. Check LHS destination write conflicts against loans live AFTER this statement
                    check_write_conflicts(
                        program,
                        func,
                        dest,
                        &active_after,
                        &loans,
                        &loans_by_local,
                    )?;
                }
            }
        }

        // Check Terminator
        let mut live_during_term = live_out[bb].clone();
        live_during_term.union(t_reads);
        let active_term = active_loans_for(&pt, &live_during_term);

        at.set(Some((bb, block.statements.len())));
        match &block.terminator {
            Terminator::Goto { .. } | Terminator::Unreachable => {}
            Terminator::SwitchInt { discr, .. } => {
                check_operand_borrows(
                    program,
                    func,
                    discr,
                    &active_term,
                    &loans,
                    &loans_by_local,
                )?;
            }
            Terminator::Call {
                func: callee,
                args,
                destination,
                ..
            } => {
                check_operand_borrows(
                    program,
                    func,
                    callee,
                    &active_term,
                    &loans,
                    &loans_by_local,
                )?;
                for a in args {
                    check_operand_borrows(
                        program,
                        func,
                        a,
                        &active_term,
                        &loans,
                        &loans_by_local,
                    )?;
                }
                check_deref_permissions(program, func, destination, true, false)?;
                let active_after_call = active_loans_for(&pt, &live_out[bb]);
                check_write_conflicts(
                    program,
                    func,
                    destination,
                    &active_after_call,
                    &loans,
                    &loans_by_local,
                )?;
            }
            Terminator::Drop { place, .. } => {
                let active_after_drop = active_loans_for(&pt, &live_out[bb]);
                check_write_conflicts(
                    program,
                    func,
                    place,
                    &active_after_drop,
                    &loans,
                    &loans_by_local,
                )?;
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
    loans_by_local: &[LoanSet],
) -> Result<(), String> {
    match op {
        Operand::Copy(place) => {
            check_deref_permissions(program, func, place, false, false)?;
            check_read_conflicts(program, func, place, active_loans, loans, loans_by_local)
        }
        Operand::Move(place) => {
            check_deref_permissions(program, func, place, false, true)?;
            check_write_conflicts(program, func, place, active_loans, loans, loans_by_local)
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
    loans_by_local: &[LoanSet],
) -> Result<(), String> {
    let Some(local_loans) = loans_by_local.get(place.local.0 as usize) else {
        return Ok(());
    };
    if local_loans.is_empty() {
        return Ok(());
    }
    for loan_id in active_loans.iter_intersect(local_loans) {
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
    loans_by_local: &[LoanSet],
) -> Result<(), String> {
    let Some(local_loans) = loans_by_local.get(place.local.0 as usize) else {
        return Ok(());
    };
    if local_loans.is_empty() {
        return Ok(());
    }
    for loan_id in active_loans.iter_intersect(local_loans) {
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
