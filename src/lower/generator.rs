//! Generators as resume functions over a heap frame.
//!
//! A generator `fn f(params) -> gen T { body }` is lowered as two functions: its constructor,
//! whose body is `@gen_start` (a frame of a size not yet known, and a placeholder call
//! `slir.gen.start.<body>` taking the frame's memory and the arguments), and its body, an
//! ordinary function `(out: &mut ?T, params) -> void` in which `yield e` is `*out = e` and then
//! `if slir.gen.suspend() { return; }`. Both are checked as they are, so the borrow checker sees
//! what a yielded value borrows flow into `*out`, and dropping a suspended generator runs the
//! `return` at its suspension point, which drops what is live there as any `return` does.
//!
//! Once checked, [`Compiler::lower_generators`] makes the body a resume function
//! `(frame: *mut u8, out: *mut ?T, abandon: bool) -> bool` (whether the body has returned).
//! The frame holds a `u32` state, the suspension point last left (0 before the body starts),
//! then each local that must outlive a call of the resume function: the parameters, what is
//! live where the body resumes, and what has its address taken (a reference to it may be). Any
//! other local stays a local of the resume function. The entry switches on the state, a suspension point
//! stores its number and returns, and resuming there gives its `slir.gen.suspend()` the
//! `abandon` flag. The constructor's placeholder becomes the code that stores the arguments in
//! the frame and runs the body to the point every body starts at, and `Gen` holds the rest.

use super::*;

/// The state of a frame whose body has returned.
const GEN_DONE: i128 = u32::MAX as i128;

impl Compiler {
    /// Makes every checked generator body a resume function and fills in its constructor; see
    /// the module documentation.
    pub(super) fn lower_generators(&mut self) -> Result<(), String> {
        let starts: Vec<(FuncId, FuncId)> = self
            .program
            .externs
            .iter()
            .filter_map(|e| {
                let body = e.symbol.strip_prefix(crate::ir::GEN_START_PREFIX)?;
                Some((e.id, FuncId(body.parse().ok()?)))
            })
            .collect();
        let mut done: Vec<FuncId> = Vec::new();
        for (start, body) in starts {
            let callers: Vec<usize> = self
                .program
                .functions
                .iter()
                .enumerate()
                .filter(|(_, f)| f.blocks.iter().any(|b| calls(&b.terminator, start)))
                .map(|(i, _)| i)
                .collect();
            if callers.is_empty() {
                continue;
            }
            let Some(body_idx) = self.program.functions.iter().position(|f| f.id == body) else {
                continue;
            };
            let gen_ty = self.program.externs.iter().find(|e| e.id == start).map(|e| e.ret).unwrap();
            let fields = self.composites.get(&gen_ty).map(|c| c.fields.clone()).unwrap_or_default();
            let names: Vec<&str> = fields.iter().map(|(n, ..)| n.as_str()).collect();
            if names != ["frame", "resume", "done"] {
                return Err(format!("'{}' is not std's 'Gen'", self.type_display_name(gen_ty)));
            }
            let resume_ty = fields[1].1;
            let Type::FnPtr { args: resume_args, .. } = self.program.types[resume_ty.0 as usize].clone() else {
                return Err("'Gen::resume' is not a function pointer".to_string());
            };
            let frame_layout = if done.contains(&body) {
                None
            } else {
                Some(self.make_resume_function(body_idx, &resume_args)?)
            };
            let frame = match frame_layout {
                Some(l) => l,
                None => self.generator_frames[&body].clone(),
            };
            if !done.contains(&body) {
                done.push(body);
                self.generator_frames.insert(body, frame.clone());
            }
            for idx in callers {
                self.fill_constructor(idx, start, body, gen_ty, &frame, &resume_args)?;
            }
        }
        Ok(())
    }

    /// Refuses compile-time evaluation from `root` that can start a generator: a generator's
    /// body becomes a resume function only once it is borrow checked, with the whole program.
    pub(super) fn refuse_comptime_generators(&self, root: FuncId) -> Result<(), String> {
        let starts: Vec<FuncId> = self
            .program
            .externs
            .iter()
            .filter(|e| e.symbol.starts_with(crate::ir::GEN_START_PREFIX))
            .map(|e| e.id)
            .collect();
        if starts.is_empty() {
            return Ok(());
        }
        let mut seen = vec![root];
        let mut queue = vec![root];
        while let Some(id) = queue.pop() {
            let Some(f) = self.program.functions.iter().find(|f| f.id == id) else { continue };
            let mut callees = Vec::new();
            for b in &f.blocks {
                for s in &b.statements {
                    if let Statement::Assign(_, rv) = s {
                        for o in crate::drop::rvalue_operands(rv) {
                            if let Operand::Const(ConstValue::Func(g)) = o {
                                callees.push(*g);
                            }
                        }
                    }
                }
                if let Terminator::Call { func: Operand::Const(ConstValue::Func(g)), args, .. } = &b.terminator {
                    callees.push(*g);
                    for a in args {
                        if let Operand::Const(ConstValue::Func(h)) = a {
                            callees.push(*h);
                        }
                    }
                }
            }
            if callees.iter().any(|g| starts.contains(g)) {
                return Err(format!(
                    "Compile-time evaluation would start a generator, in '{}', which cannot run at compile time yet; compute the value when the program runs",
                    f.debug_name.clone().unwrap_or_default()
                ));
            }
            for g in callees {
                if !seen.contains(&g) {
                    seen.push(g);
                    queue.push(g);
                }
            }
        }
        Ok(())
    }

    /// Rewrites the body at `idx` as its resume function, returning its frame.
    fn make_resume_function(&mut self, idx: usize, resume_args: &[TypeId]) -> Result<Frame, String> {
        let body = self.program.functions[idx].clone();
        let suspend = self.program.externs.iter().find(|e| e.symbol == crate::ir::GEN_SUSPEND).map(|e| e.id);
        let u32_ty = self.intern_type(Type::Int { signed: false, bits: 32 });
        let bool_ty = self.intern_type(Type::Bool);
        let kept = kept_in_frame(&body, suspend);
        // Field 0 is the state; the kept locals follow, and the others are the resume
        // function's own, after its arguments and the typed frame pointer.
        let mut field_tys = vec![u32_ty];
        let mut slots = vec![Slot::Ret, Slot::Out];
        let mut own_locals = vec![bool_ty, resume_args[0], resume_args[1], resume_args[2], FP_TY_PLACEHOLDER];
        for (l, &ty) in body.locals.iter().enumerate().skip(2) {
            if kept[l] {
                slots.push(Slot::Field(field_tys.len() as u32));
                field_tys.push(ty);
            } else {
                slots.push(Slot::Local(LocalId(own_locals.len() as u32)));
                own_locals.push(ty);
            }
        }
        let param_fields: Vec<u32> = (2..=body.arg_count)
            .map(|l| match slots[l] {
                Slot::Field(f) => f,
                _ => unreachable!("parameters are kept"),
            })
            .collect();
        let frame_ty = self.alloc_distinct_type(Type::Struct(field_tys));
        let (size, align) = self.program.type_size_align(frame_ty)?;
        if align > 16 {
            return Err(format!(
                "A local of generator '{}' needs alignment {align}, more than a frame's 16",
                body.debug_name.clone().unwrap_or_default()
            ));
        }
        let fp_ty = self.intern_raw_ptr_type(true, frame_ty);
        own_locals[FP.0 as usize] = fp_ty;
        let mut out = Rewriter { locals: own_locals, body_locals: body.locals.clone(), slots };
        let state = Place { local: FP, projections: vec![Projection::Deref, Projection::Field(0)] };
        // bb0 dispatches; the body's blocks follow, one later; then a block resuming each
        // suspension point, and one for a state that cannot be.
        let shift = |b: BlockId| BlockId(b.0 + 1);
        let mut blocks = vec![BasicBlock { statements: Vec::new(), terminator: Terminator::Unreachable }];
        let mut resumes: Vec<(i128, BlockId)> = vec![(0, BlockId(1))];
        let mut extra: Vec<BasicBlock> = Vec::new();
        let first_extra = body.blocks.len() as u32 + 1;
        for block in &body.blocks {
            let mut statements = Vec::new();
            for s in &block.statements {
                out.statement(s, &mut statements);
            }
            let terminator = match &block.terminator {
                Terminator::Call { func: Operand::Const(ConstValue::Func(f)), destination, target, .. }
                    if Some(*f) == suspend =>
                {
                    let point = resumes.len() as i128;
                    statements.push(Statement::Assign(state.clone(), Rvalue::Use(Operand::Const(ConstValue::I64(point)))));
                    statements.push(Statement::Assign(Place::new(LocalId(0)), Rvalue::Use(Operand::Const(ConstValue::Bool(false)))));
                    let mut resume = Vec::new();
                    let dest = out.place(destination, &mut resume);
                    resume.push(Statement::Assign(dest, Rvalue::Use(Operand::Copy(Place::new(ABANDON)))));
                    let at = BlockId(first_extra + extra.len() as u32);
                    extra.push(BasicBlock { statements: resume, terminator: Terminator::Goto { target: shift(*target) } });
                    resumes.push((point, at));
                    Terminator::Return
                }
                Terminator::Return => {
                    statements.push(Statement::Assign(state.clone(), Rvalue::Use(Operand::Const(ConstValue::I64(GEN_DONE)))));
                    statements.push(Statement::Assign(Place::new(LocalId(0)), Rvalue::Use(Operand::Const(ConstValue::Bool(true)))));
                    Terminator::Return
                }
                Terminator::Goto { target } => Terminator::Goto { target: shift(*target) },
                Terminator::SwitchInt { discr, targets, otherwise } => Terminator::SwitchInt {
                    discr: out.operand(discr, &mut statements),
                    targets: targets.iter().map(|(v, b)| (*v, shift(*b))).collect(),
                    otherwise: shift(*otherwise),
                },
                Terminator::Call { func, args, destination, target } => Terminator::Call {
                    func: out.operand(func, &mut statements),
                    args: args.iter().map(|a| out.operand(a, &mut statements)).collect(),
                    destination: out.place(destination, &mut statements),
                    target: shift(*target),
                },
                Terminator::Drop { place, target } => Terminator::Drop {
                    place: out.place(place, &mut statements),
                    target: shift(*target),
                },
                Terminator::Unreachable => Terminator::Unreachable,
            };
            blocks.push(BasicBlock { statements, terminator });
        }
        blocks.extend(extra);
        let unreachable = BlockId(blocks.len() as u32);
        blocks.push(BasicBlock { statements: Vec::new(), terminator: Terminator::Unreachable });
        blocks[0] = BasicBlock {
            statements: vec![Statement::Assign(Place::new(FP), Rvalue::Cast(Operand::Copy(Place::new(FRAME)), fp_ty))],
            terminator: Terminator::SwitchInt { discr: Operand::Copy(state), targets: resumes, otherwise: unreachable },
        };
        let f = &mut self.program.functions[idx];
        f.arg_count = 3;
        f.ret_borrows = None;
        f.param_borrows = None;
        f.linear_self = None;
        f.param_names = vec!["frame".to_string(), "out".to_string(), "abandon".to_string()];
        f.local_names = Vec::new();
        f.locals = out.locals;
        f.blocks = blocks;
        Ok(Frame { ty: frame_ty, size, param_fields })
    }

    /// Replaces the placeholder in the constructor at `idx` with the code that stores the
    /// arguments in the frame, runs the body to where it starts, and makes the `Gen`.
    #[allow(clippy::too_many_arguments)]
    fn fill_constructor(
        &mut self,
        idx: usize,
        start: FuncId,
        body: FuncId,
        gen_ty: TypeId,
        frame: &Frame,
        resume_args: &[TypeId],
    ) -> Result<(), String> {
        let size = frame.size;
        let fp_ty = self.intern_raw_ptr_type(true, frame.ty);
        let bool_ty = self.intern_type(Type::Bool);
        let usize_ty = self.intern_type(Type::Int { signed: false, bits: 64 });
        let f = &mut self.program.functions[idx];
        for block in &mut f.blocks {
            for s in &mut block.statements {
                if let Statement::Assign(_, Rvalue::Use(Operand::Const(ConstValue::I64(v)))) = s
                    && *v == crate::ir::GEN_FRAME_SIZE_MARKER
                {
                    *v = size.max(1) as i128;
                }
            }
        }
        let new_local = |f: &mut Function, ty: TypeId| {
            f.locals.push(ty);
            LocalId(f.locals.len() as u32 - 1)
        };
        let fp = new_local(f, fp_ty);
        let null_out = new_local(f, resume_args[1]);
        let started = new_local(f, bool_ty);
        let zero = new_local(f, usize_ty);
        for bi in 0..f.blocks.len() {
            let Terminator::Call { func, args, destination, target } = f.blocks[bi].terminator.clone() else {
                continue;
            };
            if func != Operand::Const(ConstValue::Func(start)) {
                continue;
            }
            let raw = args[0].clone();
            let field = |i: u32| Place { local: fp, projections: vec![Projection::Deref, Projection::Field(i)] };
            let stmts = &mut f.blocks[bi].statements;
            stmts.push(Statement::Assign(Place::new(fp), Rvalue::Cast(raw.clone(), fp_ty)));
            stmts.push(Statement::Assign(field(0), Rvalue::Use(Operand::Const(ConstValue::I64(0)))));
            for (a, &f) in args[1..].iter().zip(&frame.param_fields) {
                stmts.push(Statement::Assign(field(f), Rvalue::Use(a.clone())));
            }
            stmts.push(Statement::Assign(Place::new(zero), Rvalue::Use(Operand::Const(ConstValue::I64(0)))));
            stmts.push(Statement::Assign(
                Place::new(null_out),
                Rvalue::Cast(Operand::Copy(Place::new(zero)), resume_args[1]),
            ));
            let made = BlockId(f.blocks.len() as u32);
            f.blocks[bi].terminator = Terminator::Call {
                func: Operand::Const(ConstValue::Func(body)),
                args: vec![raw.clone(), Operand::Copy(Place::new(null_out)), Operand::Const(ConstValue::Bool(false))],
                destination: Place::new(started),
                target: made,
            };
            f.blocks.push(BasicBlock {
                statements: vec![Statement::Assign(
                    destination,
                    Rvalue::Aggregate(
                        gen_ty,
                        vec![raw, Operand::Const(ConstValue::Func(body)), Operand::Const(ConstValue::Bool(false))],
                    ),
                )],
                terminator: Terminator::Goto { target },
            });
        }
        Ok(())
    }
}

/// The resume function's frame pointer as it is passed, its slot, its abandon flag, and the
/// frame pointer typed.
const FRAME: LocalId = LocalId(1);
const OUT: LocalId = LocalId(2);
const ABANDON: LocalId = LocalId(3);
const FP: LocalId = LocalId(4);

fn calls(t: &Terminator, f: FuncId) -> bool {
    matches!(t, Terminator::Call { func: Operand::Const(ConstValue::Func(g)), .. } if *g == f)
}

/// A generator body's frame: its type, its size, and the field of each parameter.
#[derive(Clone)]
pub(super) struct Frame {
    ty: TypeId,
    size: u64,
    param_fields: Vec<u32>,
}

/// Where a body's local is in its resume function.
#[derive(Clone, Copy)]
enum Slot {
    /// `_0`, of type `void`: a local of its own.
    Ret,
    /// `_1`, the slot: the resume function's `out`.
    Out,
    Field(u32),
    Local(LocalId),
}

/// Stands for the typed frame pointer's type until the frame's type exists.
const FP_TY_PLACEHOLDER: TypeId = TypeId(0);

/// Which of `body`'s locals the frame keeps: the parameters, what is live where it resumes after
/// a suspension point (other than the flag the resume sets), and what has its address taken.
fn kept_in_frame(body: &Function, suspend: Option<FuncId>) -> Vec<bool> {
    let n = body.locals.len();
    let mut kept = vec![false; n];
    for k in kept.iter_mut().take(body.arg_count + 1).skip(2) {
        *k = true;
    }
    for b in &body.blocks {
        for s in &b.statements {
            if let Statement::Assign(_, Rvalue::Ref { place, .. }) = s {
                kept[place.local.0 as usize] = true;
            }
        }
    }
    let live_in = liveness(body);
    for b in &body.blocks {
        if let Terminator::Call { func: Operand::Const(ConstValue::Func(f)), destination, target, .. } = &b.terminator
            && Some(*f) == suspend
        {
            for &l in &live_in[target.0 as usize] {
                if !(destination.projections.is_empty() && destination.local.0 == l) {
                    kept[l as usize] = true;
                }
            }
        }
    }
    kept[0] = false;
    kept[1] = false;
    kept
}

/// The locals live at the start of each block of `f`: read on some path before being written
/// whole.
fn liveness(f: &Function) -> Vec<std::collections::BTreeSet<u32>> {
    use std::collections::BTreeSet;
    let n = f.blocks.len();
    let mut live_in: Vec<BTreeSet<u32>> = vec![BTreeSet::new(); n];
    let mut changed = true;
    while changed {
        changed = false;
        for b in (0..n).rev() {
            let block = &f.blocks[b];
            let mut live: BTreeSet<u32> = BTreeSet::new();
            for s in successors(&block.terminator) {
                live.extend(live_in[s.0 as usize].iter().copied());
            }
            let (uses, def) = terminator_effect(&block.terminator);
            if let Some(d) = def {
                live.remove(&d);
            }
            live.extend(uses);
            for s in block.statements.iter().rev() {
                let (uses, def) = statement_effect(s);
                if let Some(d) = def {
                    live.remove(&d);
                }
                live.extend(uses);
            }
            if live != live_in[b] {
                live_in[b] = live;
                changed = true;
            }
        }
    }
    live_in
}

fn successors(t: &Terminator) -> Vec<BlockId> {
    match t {
        Terminator::Goto { target } | Terminator::Call { target, .. } | Terminator::Drop { target, .. } => vec![*target],
        Terminator::SwitchInt { targets, otherwise, .. } => {
            targets.iter().map(|(_, b)| *b).chain(std::iter::once(*otherwise)).collect()
        }
        Terminator::Return | Terminator::Unreachable => Vec::new(),
    }
}

fn place_uses(p: &Place, out: &mut Vec<u32>) {
    out.push(p.local.0);
    for proj in &p.projections {
        if let Projection::Index(l) = proj {
            out.push(l.0);
        }
    }
}

fn operand_uses(o: &Operand, out: &mut Vec<u32>) {
    if let Operand::Copy(p) | Operand::Move(p) = o {
        place_uses(p, out);
    }
}

/// What writing `p` defines whole (a bare local), and what it reads (a path's base and indices).
fn written(p: &Place, uses: &mut Vec<u32>) -> Option<u32> {
    if p.projections.is_empty() {
        Some(p.local.0)
    } else {
        place_uses(p, uses);
        None
    }
}

fn statement_effect(s: &Statement) -> (Vec<u32>, Option<u32>) {
    let mut uses = Vec::new();
    let def = match s {
        Statement::Assign(p, rv) => {
            match rv {
                Rvalue::Ref { place, .. } | Rvalue::Discriminant(place) => place_uses(place, &mut uses),
                _ => {
                    for o in crate::drop::rvalue_operands(rv) {
                        operand_uses(o, &mut uses);
                    }
                }
            }
            written(p, &mut uses)
        }
        Statement::SetDiscriminant(p, _) => {
            place_uses(p, &mut uses);
            None
        }
        Statement::StorageLive(_) | Statement::StorageDead(_) | Statement::Line(_) => None,
    };
    (uses, def)
}

fn terminator_effect(t: &Terminator) -> (Vec<u32>, Option<u32>) {
    let mut uses = Vec::new();
    let def = match t {
        Terminator::SwitchInt { discr, .. } => {
            operand_uses(discr, &mut uses);
            None
        }
        Terminator::Call { func, args, destination, .. } => {
            operand_uses(func, &mut uses);
            for a in args {
                operand_uses(a, &mut uses);
            }
            written(destination, &mut uses)
        }
        Terminator::Drop { place, .. } => {
            place_uses(place, &mut uses);
            None
        }
        Terminator::Goto { .. } | Terminator::Return | Terminator::Unreachable => None,
    };
    (uses, def)
}

/// Moves a body's places into its resume function, as `slots` says.
struct Rewriter {
    locals: Vec<TypeId>,
    body_locals: Vec<TypeId>,
    slots: Vec<Slot>,
}

impl Rewriter {
    fn temp(&mut self, ty: TypeId) -> LocalId {
        self.locals.push(ty);
        LocalId(self.locals.len() as u32 - 1)
    }

    fn base(&mut self, l: LocalId) -> Place {
        match self.slots[l.0 as usize] {
            Slot::Ret => {
                let t = self.temp(self.body_locals[0]);
                Place::new(t)
            }
            Slot::Out => Place::new(OUT),
            Slot::Field(f) => Place { local: FP, projections: vec![Projection::Deref, Projection::Field(f)] },
            Slot::Local(m) => Place::new(m),
        }
    }

    fn place(&mut self, p: &Place, pre: &mut Vec<Statement>) -> Place {
        let mut out = self.base(p.local);
        for proj in &p.projections {
            out.projections.push(match proj {
                // An index must be a local: copy it out of the frame first.
                Projection::Index(l) => match self.slots[l.0 as usize] {
                    Slot::Local(m) => Projection::Index(m),
                    _ => {
                        let ty = self.body_locals[l.0 as usize];
                        let at = self.base(*l);
                        let t = self.temp(ty);
                        pre.push(Statement::Assign(Place::new(t), Rvalue::Use(Operand::Copy(at))));
                        Projection::Index(t)
                    }
                },
                other => other.clone(),
            });
        }
        out
    }

    fn operand(&mut self, o: &Operand, pre: &mut Vec<Statement>) -> Operand {
        match o {
            Operand::Copy(p) => Operand::Copy(self.place(p, pre)),
            Operand::Move(p) => Operand::Move(self.place(p, pre)),
            Operand::Const(c) => Operand::Const(c.clone()),
        }
    }

    fn statement(&mut self, s: &Statement, out: &mut Vec<Statement>) {
        match s {
            Statement::Assign(p, rv) => {
                let rv = self.rvalue(rv, out);
                let p = self.place(p, out);
                out.push(Statement::Assign(p, rv));
            }
            Statement::SetDiscriminant(p, v) => {
                let p = self.place(p, out);
                out.push(Statement::SetDiscriminant(p, *v));
            }
            // Frame fields live as long as the frame.
            Statement::StorageLive(l) => {
                if let Slot::Local(m) = self.slots[l.0 as usize] {
                    out.push(Statement::StorageLive(m));
                }
            }
            Statement::StorageDead(l) => {
                if let Slot::Local(m) = self.slots[l.0 as usize] {
                    out.push(Statement::StorageDead(m));
                }
            }
            Statement::Line(pos) => out.push(Statement::Line(pos.clone())),
        }
    }

    fn rvalue(&mut self, rv: &Rvalue, pre: &mut Vec<Statement>) -> Rvalue {
        let mut op = |o: &Operand, pre: &mut Vec<Statement>| self.operand(o, pre);
        match rv {
            Rvalue::Use(o) => Rvalue::Use(op(o, pre)),
            Rvalue::UnaryOp(u, o) => Rvalue::UnaryOp(*u, op(o, pre)),
            Rvalue::BinaryOp(b, x, y) => {
                let x = op(x, pre);
                Rvalue::BinaryOp(*b, x, op(y, pre))
            }
            Rvalue::Cast(o, t) => Rvalue::Cast(op(o, pre), *t),
            Rvalue::Transmute(o, t) => Rvalue::Transmute(op(o, pre), *t),
            Rvalue::Aggregate(t, ops) => Rvalue::Aggregate(*t, ops.iter().map(|o| op(o, pre)).collect()),
            Rvalue::Union { ty, variant, payload } => {
                Rvalue::Union { ty: *ty, variant: *variant, payload: op(payload, pre) }
            }
            Rvalue::ArrayType { elem, len } => {
                let elem = op(elem, pre);
                Rvalue::ArrayType { elem, len: op(len, pre) }
            }
            Rvalue::SimdType { elem, len } => {
                let elem = op(elem, pre);
                Rvalue::SimdType { elem, len: op(len, pre) }
            }
            Rvalue::OverlayType(ops) => Rvalue::OverlayType(ops.iter().map(|o| op(o, pre)).collect()),
            Rvalue::UnionType { tag, variants } => {
                let tag = op(tag, pre);
                Rvalue::UnionType { tag, variants: variants.iter().map(|o| op(o, pre)).collect() }
            }
            Rvalue::PatternType { base, ranges } => {
                let base = op(base, pre);
                Rvalue::PatternType {
                    base,
                    ranges: ranges.iter().map(|(a, b)| (op(a, pre), op(b, pre))).collect(),
                }
            }
            Rvalue::Ref { mutable, place } => Rvalue::Ref { mutable: *mutable, place: self.place(place, pre) },
            Rvalue::Discriminant(p) => Rvalue::Discriminant(self.place(p, pre)),
        }
    }
}
