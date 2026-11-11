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
//! `(frame: *mut u8, out: *mut ?T, abandon: bool) -> bool` (whether the body has returned):
//! every local but the slot is a field of the frame, after a `u32` state, the suspension point
//! last left (0 before the body starts). The entry switches on the state, a suspension point
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
            let (frame_ty, size) = match frame_layout {
                Some(l) => l,
                None => self.frame_of(body),
            };
            if !done.contains(&body) {
                done.push(body);
                self.generator_frames.insert(body, (frame_ty, size));
            }
            for idx in callers {
                self.fill_constructor(idx, start, body, gen_ty, frame_ty, size, &resume_args)?;
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

    fn frame_of(&self, body: FuncId) -> (TypeId, u64) {
        self.generator_frames[&body]
    }

    /// Rewrites the body at `idx` as its resume function, returning its frame's type and size.
    fn make_resume_function(&mut self, idx: usize, resume_args: &[TypeId]) -> Result<(TypeId, u64), String> {
        let body = self.program.functions[idx].clone();
        let suspend = self.program.externs.iter().find(|e| e.symbol == crate::ir::GEN_SUSPEND).map(|e| e.id);
        let u32_ty = self.intern_type(Type::Int { signed: false, bits: 32 });
        let bool_ty = self.intern_type(Type::Bool);
        // Field 0 is the state, and local `l` (other than `_0` and the slot `_1`) is field `l - 1`.
        let mut field_tys = vec![u32_ty];
        field_tys.extend(body.locals.iter().skip(2).copied());
        let frame_ty = self.alloc_distinct_type(Type::Struct(field_tys));
        let (size, align) = self.program.type_size_align(frame_ty)?;
        if align > 16 {
            return Err(format!(
                "A local of generator '{}' needs alignment {align}, more than a frame's 16",
                body.debug_name.clone().unwrap_or_default()
            ));
        }
        let fp_ty = self.intern_raw_ptr_type(true, frame_ty);
        let mut out = Rewriter {
            locals: vec![bool_ty, resume_args[0], resume_args[1], resume_args[2], fp_ty],
            body_locals: body.locals.clone(),
        };
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
        Ok((frame_ty, size))
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
        frame_ty: TypeId,
        size: u64,
        resume_args: &[TypeId],
    ) -> Result<(), String> {
        let fp_ty = self.intern_raw_ptr_type(true, frame_ty);
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
            // The body's parameters are its locals `_2..`, so fields `1..`.
            for (i, a) in args[1..].iter().enumerate() {
                stmts.push(Statement::Assign(field(i as u32 + 1), Rvalue::Use(a.clone())));
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

/// Moves a body's places into its frame: local `_1` (the slot) is the resume function's `out`,
/// `_0` a local of its own, and every other local a field of `*FP`.
struct Rewriter {
    locals: Vec<TypeId>,
    body_locals: Vec<TypeId>,
}

impl Rewriter {
    fn temp(&mut self, ty: TypeId) -> LocalId {
        self.locals.push(ty);
        LocalId(self.locals.len() as u32 - 1)
    }

    fn base(&mut self, l: LocalId) -> Place {
        match l.0 {
            0 => {
                let t = self.temp(self.body_locals[0]);
                Place::new(t)
            }
            1 => Place::new(OUT),
            n => Place { local: FP, projections: vec![Projection::Deref, Projection::Field(n - 1)] },
        }
    }

    fn place(&mut self, p: &Place, pre: &mut Vec<Statement>) -> Place {
        let mut out = self.base(p.local);
        for proj in &p.projections {
            out.projections.push(match proj {
                // An index must be a local: copy it out of the frame first.
                Projection::Index(l) => {
                    let ty = self.body_locals[l.0 as usize];
                    let at = self.base(*l);
                    let t = self.temp(ty);
                    pre.push(Statement::Assign(Place::new(t), Rvalue::Use(Operand::Copy(at))));
                    Projection::Index(t)
                }
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
            Statement::StorageLive(_) | Statement::StorageDead(_) => {}
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
