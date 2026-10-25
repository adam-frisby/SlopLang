use crate::ir::{
    BinOp, BlockId, ConstValue, FuncId, Function, GlobalId, LocalId, Operand, Place, Program,
    Projection, Rvalue, Statement, Terminator, Type, TypeId, UnOp,
};

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PtrTarget {
    Local { frame: usize, local: LocalId },
    Global(GlobalId),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ResolvedProj {
    Field(u32),
    Variant(u32),
    Index(usize),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Value {
    Uninit,
    Void,
    Bool(bool),
    Int(i64),
    Float(u64), // IEEE 754 bits
    Type(TypeId),
    Func(FuncId),
    Str(String),
    Array(Vec<Value>),
    Struct {
        ty: TypeId,
        fields: Vec<Value>,
    },
    Union {
        ty: TypeId,
        active_field: Option<u32>,
        val: Box<Value>,
    },
    Tagged {
        ty: TypeId,
        variant: u32,
        payload: Box<Value>,
    },
    Ptr {
        target: PtrTarget,
        projections: Vec<ResolvedProj>,
    },
}

impl Value {
    pub fn from_f64(v: f64) -> Self {
        Self::Float(v.to_bits())
    }

    pub fn as_f64(&self) -> Option<f64> {
        if let Self::Float(bits) = self {
            Some(f64::from_bits(*bits))
        } else {
            None
        }
    }

    pub fn to_const(&self) -> Result<ConstValue, String> {
        match self {
            Value::Void => Ok(ConstValue::Void),
            Value::Bool(b) => Ok(ConstValue::Bool(*b)),
            Value::Int(n) => Ok(ConstValue::I64(*n)),
            Value::Float(bits) => Ok(ConstValue::F64(*bits)),
            Value::Type(id) => Ok(ConstValue::Type(*id)),
            Value::Func(id) => Ok(ConstValue::Func(*id)),
            Value::Str(s) => Ok(ConstValue::Str(s.clone())),
            _ => Err(format!(
                "Cannot convert runtime/composite value {self:?} to immediate ConstValue"
            )),
        }
    }
}

struct Frame {
    func_id: FuncId,
    locals: Vec<Value>,
    block: BlockId,
    /// When this frame returns, where in the caller frame should `_0` be written, and which block to jump to?
    caller_return: Option<(Place, BlockId)>,
}

pub struct Vm<'a> {
    program: &'a mut Program,
    globals: Vec<Value>,
    frames: Vec<Frame>,
}

impl<'a> Vm<'a> {
    pub fn new(program: &'a mut Program) -> Self {
        let globals = program
            .globals
            .iter()
            .map(|g| Self::const_to_val(&g.init))
            .collect();
        Self {
            program,
            globals,
            frames: Vec::new(),
        }
    }

    fn const_to_val(cv: &ConstValue) -> Value {
        match cv {
            ConstValue::Void => Value::Void,
            ConstValue::Bool(b) => Value::Bool(*b),
            ConstValue::I64(n) => Value::Int(*n),
            ConstValue::F64(bits) => Value::Float(*bits),
            ConstValue::Type(id) => Value::Type(*id),
            ConstValue::Func(id) => Value::Func(*id),
            ConstValue::Global(id) => Value::Ptr {
                target: PtrTarget::Global(*id),
                projections: Vec::new(),
            },
            ConstValue::Str(s) => Value::Str(s.clone()),
        }
    }

    /// Evaluates `func_id(args)` at compile-time (or runtime interpretation),
    /// allowing Zig-style `comptime` functions to compute both values and new types in `Program`.
    pub fn eval(
        program: &'a mut Program,
        func_id: FuncId,
        args: Vec<Value>,
    ) -> Result<Value, String> {
        let mut vm = Self::new(program);
        vm.call_root(func_id, args)
    }

    fn get_function(&self, id: FuncId) -> Result<Function, String> {
        self.program
            .functions
            .iter()
            .find(|f| f.id == id)
            .cloned()
            .ok_or_else(|| format!("Undefined function {id}"))
    }

    fn call_root(&mut self, func_id: FuncId, args: Vec<Value>) -> Result<Value, String> {
        let func = self.get_function(func_id)?;
        if args.len() != func.arg_count {
            return Err(format!(
                "Function {} expected {} arguments, got {}",
                func_id,
                func.arg_count,
                args.len()
            ));
        }

        let mut locals = vec![Value::Uninit; func.locals.len()];
        for (i, arg) in args.into_iter().enumerate() {
            locals[i + 1] = arg;
        }

        self.frames.push(Frame {
            func_id,
            locals,
            block: BlockId(0),
            caller_return: None,
        });

        loop {
            let current_frame_idx = self.frames.len() - 1;
            let func_id = self.frames[current_frame_idx].func_id;
            let block_id = self.frames[current_frame_idx].block;
            let func = self.get_function(func_id)?;

            let block = func
                .blocks
                .get(block_id.0 as usize)
                .ok_or_else(|| format!("Invalid block {block_id} in {func_id}"))?;

            for stmt in &block.statements {
                self.exec_statement(&func, stmt)?;
            }

            match &block.terminator {
                Terminator::Goto { target } => {
                    self.frames[current_frame_idx].block = *target;
                }
                Terminator::SwitchInt {
                    discr,
                    targets,
                    otherwise,
                } => {
                    let val = self.eval_operand(discr)?;
                    let switch_val = match val {
                        Value::Int(n) => n,
                        Value::Bool(b) => i64::from(b),
                        Value::Type(ty) => i64::from(ty.0),
                        _ => {
                            return Err(format!(
                                "switchInt expected integer/bool/type, got {val:?}"
                            ))
                        }
                    };
                    let next_block = targets
                        .iter()
                        .find(|(v, _)| *v == switch_val)
                        .map(|(_, b)| *b)
                        .unwrap_or(*otherwise);
                    self.frames[current_frame_idx].block = next_block;
                }
                Terminator::Call {
                    func: callee_op,
                    args: call_args,
                    destination,
                    target,
                } => {
                    let callee_val = self.eval_operand(callee_op)?;
                    let Value::Func(callee_id) = callee_val else {
                        return Err(format!("Expected function in call, found {callee_val:?}"));
                    };
                    let mut evaluated_args = Vec::with_capacity(call_args.len());
                    for arg_op in call_args {
                        evaluated_args.push(self.eval_operand(arg_op)?);
                    }

                    let callee_func = self.get_function(callee_id)?;
                    if evaluated_args.len() != callee_func.arg_count {
                        return Err(format!(
                            "Function {} expected {} args, got {}",
                            callee_id,
                            callee_func.arg_count,
                            evaluated_args.len()
                        ));
                    }

                    let mut new_locals = vec![Value::Uninit; callee_func.locals.len()];
                    for (i, arg_val) in evaluated_args.into_iter().enumerate() {
                        new_locals[i + 1] = arg_val;
                    }

                    self.frames.push(Frame {
                        func_id: callee_id,
                        locals: new_locals,
                        block: BlockId(0),
                        caller_return: Some((destination.clone(), *target)),
                    });
                }
                Terminator::Drop { place, target } => {
                    // If unelaborated in VM, check if the place has an initialized value and a registered destructor
                    let ty_id = self.place_type(&func, place)?;
                    let (ptr_target, projs) = self.resolve_place(place)?;
                    let is_init = self
                        .read_resolved(&ptr_target, &projs)
                        .is_ok();
                    if is_init
                        && let Some((_, dtor_fn)) =
                            self.program.destructors.iter().find(|(t, _)| *t == ty_id)
                    {
                        let dtor_id = *dtor_fn;
                        let dtor_func = self.get_function(dtor_id)?;
                        let ptr_val = Value::Ptr {
                            target: ptr_target,
                            projections: projs,
                        };
                        let mut new_locals = vec![Value::Uninit; dtor_func.locals.len()];
                        if dtor_func.arg_count == 1 {
                            new_locals[1] = ptr_val;
                        }
                        self.frames.push(Frame {
                            func_id: dtor_id,
                            locals: new_locals,
                            block: BlockId(0),
                            caller_return: Some((Place::new(LocalId(0)), *target)),
                        });
                    } else {
                        self.frames[current_frame_idx].block = *target;
                    }
                }
                Terminator::Return => {
                    let finished = self.frames.pop().unwrap();
                    let ret_val = finished.locals.into_iter().next().unwrap_or(Value::Void);
                    if matches!(ret_val, Value::Uninit) {
                        return Err(format!(
                            "Function {} returned uninitialized _0",
                            finished.func_id
                        ));
                    }
                    if let Some((dest_place, next_block)) = finished.caller_return {
                        // Note: for Drop calls where destination is synthetic, only write if non-Unit or valid
                        let _ = self.write_place(&dest_place, ret_val);
                        let caller_idx = self.frames.len() - 1;
                        self.frames[caller_idx].block = next_block;
                    } else {
                        return Ok(ret_val);
                    }
                }
                Terminator::Unreachable => {
                    return Err(format!("Reached 'unreachable' terminator in {func_id}"));
                }
            }
        }
    }

    fn exec_statement(&mut self, func: &Function, stmt: &Statement) -> Result<(), String> {
        match stmt {
            Statement::StorageLive(local) => {
                let frame_idx = self.frames.len() - 1;
                if let Some(&ty_id) = func.locals.get(local.0 as usize) {
                    let init_val = match self.program.types.get(ty_id.0 as usize) {
                        Some(Type::Array { len, .. }) => {
                            Value::Array(vec![Value::Uninit; *len as usize])
                        }
                        Some(Type::Struct(fields)) => Value::Struct {
                            ty: ty_id,
                            fields: vec![Value::Uninit; fields.len()],
                        },
                        Some(Type::Union(_)) => Value::Union {
                            ty: ty_id,
                            active_field: None,
                            val: Box::new(Value::Uninit),
                        },
                        Some(Type::Tagged { .. }) => Value::Tagged {
                            ty: ty_id,
                            variant: 0,
                            payload: Box::new(Value::Uninit),
                        },
                        _ => Value::Uninit,
                    };
                    self.frames[frame_idx].locals[local.0 as usize] = init_val;
                }
                Ok(())
            }
            Statement::StorageDead(local) => {
                let frame_idx = self.frames.len() - 1;
                self.frames[frame_idx].locals[local.0 as usize] = Value::Uninit;
                Ok(())
            }
            Statement::SetDiscriminant(place, variant) => {
                let ty_id = self.place_type(func, place)?;
                let (target, projs) = self.resolve_place(place)?;
                let cur = self.read_resolved(&target, &projs).unwrap_or(Value::Tagged {
                    ty: ty_id,
                    variant: *variant,
                    payload: Box::new(Value::Uninit),
                });
                let new_val = match cur {
                    Value::Tagged { ty, payload, .. } => Value::Tagged {
                        ty,
                        variant: *variant,
                        payload,
                    },
                    _ => Value::Tagged {
                        ty: ty_id,
                        variant: *variant,
                        payload: Box::new(Value::Uninit),
                    },
                };
                self.write_resolved(&target, &projs, new_val)
            }
            Statement::Assign(dest, rvalue) => {
                let dest_ty = self.place_type(func, dest)?;
                let val = self.eval_rvalue(func, rvalue, dest_ty)?;
                self.write_place(dest, val)
            }
        }
    }

    fn place_type(&self, func: &Function, place: &Place) -> Result<TypeId, String> {
        let mut cur_ty = *func
            .locals
            .get(place.local.0 as usize)
            .ok_or_else(|| format!("Undefined local {} in {}", place.local, func.id))?;
        for proj in &place.projections {
            match proj {
                Projection::Deref => {
                    let Some(Type::Ptr { pointee, .. }) = self.program.types.get(cur_ty.0 as usize)
                    else {
                        return Err(format!("Cannot deref non-pointer type {cur_ty}"));
                    };
                    cur_ty = *pointee;
                }
                Projection::Field(idx) => match self.program.types.get(cur_ty.0 as usize) {
                    Some(Type::Struct(fields) | Type::Union(fields)) => {
                        cur_ty = *fields
                            .get(*idx as usize)
                            .ok_or_else(|| format!("Field .{idx} out of bounds on {cur_ty}"))?;
                    }
                    _ => {
                        return Err(format!(
                            "Cannot access field on non-struct/union type {cur_ty}"
                        ))
                    }
                },
                Projection::Variant(v_idx) => {
                    let Some(Type::Tagged { variants, .. }) =
                        self.program.types.get(cur_ty.0 as usize)
                    else {
                        return Err(format!(
                            "Cannot access variant .v{v_idx} on non-tagged type {cur_ty}"
                        ));
                    };
                    cur_ty = *variants
                        .get(*v_idx as usize)
                        .ok_or_else(|| format!("Variant .v{v_idx} out of bounds on {cur_ty}"))?;
                }
                Projection::Index(_) => {
                    let Some(Type::Array { elem, .. }) = self.program.types.get(cur_ty.0 as usize)
                    else {
                        return Err(format!("Cannot index non-array type {cur_ty}"));
                    };
                    cur_ty = *elem;
                }
            }
        }
        Ok(cur_ty)
    }

    /// Resolves any `Projection::Deref` indirections in `place` to a concrete `(PtrTarget, Vec<ResolvedProj>)`.
    fn resolve_place(&self, place: &Place) -> Result<(PtrTarget, Vec<ResolvedProj>), String> {
        let caller_frame = self.frames.len() - 1;
        let mut cur_target = PtrTarget::Local {
            frame: caller_frame,
            local: place.local,
        };
        let mut cur_projs: Vec<ResolvedProj> = Vec::new();

        for proj in &place.projections {
            match proj {
                Projection::Deref => {
                    let ptr_val = self.read_resolved(&cur_target, &cur_projs)?;
                    let Value::Ptr {
                        target,
                        projections,
                    } = ptr_val
                    else {
                        return Err(format!("Cannot dereference non-pointer value {ptr_val:?}"));
                    };
                    cur_target = target;
                    cur_projs = projections;
                }
                Projection::Field(idx) => {
                    cur_projs.push(ResolvedProj::Field(*idx));
                }
                Projection::Variant(v_idx) => {
                    cur_projs.push(ResolvedProj::Variant(*v_idx));
                }
                Projection::Index(idx_local) => {
                    let idx_val = self.read_resolved(
                        &PtrTarget::Local {
                            frame: caller_frame,
                            local: *idx_local,
                        },
                        &[],
                    )?;
                    let Value::Int(i) = idx_val else {
                        return Err(format!("Array index must be integer, got {idx_val:?}"));
                    };
                    if i < 0 {
                        return Err(format!("Negative array index {i}"));
                    }
                    cur_projs.push(ResolvedProj::Index(i as usize));
                }
            }
        }

        Ok((cur_target, cur_projs))
    }

    fn read_resolved(
        &self,
        target: &PtrTarget,
        projs: &[ResolvedProj],
    ) -> Result<Value, String> {
        let mut cur = match target {
            PtrTarget::Local { frame, local } => self.frames[*frame]
                .locals
                .get(local.0 as usize)
                .ok_or_else(|| format!("Undefined {local}"))?,
            PtrTarget::Global(gl_id) => self
                .globals
                .get(gl_id.0 as usize)
                .ok_or_else(|| format!("Undefined {gl_id}"))?,
        };

        for proj in projs {
            match proj {
                ResolvedProj::Field(idx) => match cur {
                    Value::Struct { fields, .. } => {
                        cur = fields
                            .get(*idx as usize)
                            .ok_or_else(|| format!("Field .{idx} out of bounds"))?;
                    }
                    Value::Union {
                        active_field, val, ..
                    } => {
                        if *active_field != Some(*idx) {
                            return Err(format!(
                                "Union read of inactive field .{idx} (active: {active_field:?})"
                            ));
                        }
                        cur = val;
                    }
                    _ => return Err(format!("Cannot access field .{idx} on {cur:?}")),
                },
                ResolvedProj::Variant(v_idx) => {
                    let Value::Tagged {
                        variant, payload, ..
                    } = cur
                    else {
                        return Err(format!("Cannot access variant .v{v_idx} on {cur:?}"));
                    };
                    if *variant != *v_idx {
                        return Err(format!(
                            "Tagged union read of inactive variant .v{v_idx} (active: v{variant})"
                        ));
                    }
                    cur = payload;
                }
                ResolvedProj::Index(idx) => {
                    let Value::Array(elems) = cur else {
                        return Err(format!("Cannot index non-array value {cur:?}"));
                    };
                    cur = elems
                        .get(*idx)
                        .ok_or_else(|| format!("Array index {idx} out of bounds (len {})", elems.len()))?;
                }
            }
        }

        if matches!(cur, Value::Uninit) {
            return Err(format!("Read of uninitialized or moved place {target:?}"));
        }
        Ok(cur.clone())
    }

    fn write_resolved(
        &mut self,
        target: &PtrTarget,
        projs: &[ResolvedProj],
        new_val: Value,
    ) -> Result<(), String> {
        let mut cur = match target {
            PtrTarget::Local { frame, local } => self.frames[*frame]
                .locals
                .get_mut(local.0 as usize)
                .ok_or_else(|| format!("Undefined {local}"))?,
            PtrTarget::Global(gl_id) => self
                .globals
                .get_mut(gl_id.0 as usize)
                .ok_or_else(|| format!("Undefined {gl_id}"))?,
        };

        for proj in projs {
            match proj {
                ResolvedProj::Field(idx) => match cur {
                    Value::Struct { fields, .. } => {
                        cur = fields
                            .get_mut(*idx as usize)
                            .ok_or_else(|| format!("Field .{idx} out of bounds"))?;
                    }
                    Value::Union {
                        active_field, val, ..
                    } => {
                        *active_field = Some(*idx);
                        cur = val;
                    }
                    _ => return Err(format!("Cannot write field .{idx} on {cur:?}")),
                },
                ResolvedProj::Variant(v_idx) => {
                    let Value::Tagged {
                        variant, payload, ..
                    } = cur
                    else {
                        return Err(format!("Cannot write variant .v{v_idx} on {cur:?}"));
                    };
                    *variant = *v_idx;
                    cur = payload;
                }
                ResolvedProj::Index(idx) => {
                    let Value::Array(elems) = cur else {
                        return Err(format!("Cannot index non-array value {cur:?}"));
                    };
                    let len = elems.len();
                    cur = elems
                        .get_mut(*idx)
                        .ok_or_else(|| format!("Array index {idx} out of bounds (len {len})"))?;
                }
            }
        }

        *cur = new_val;
        Ok(())
    }

    fn read_place(&mut self, place: &Place, is_move: bool) -> Result<Value, String> {
        let (target, projs) = self.resolve_place(place)?;
        let val = self.read_resolved(&target, &projs)?;
        if is_move {
            self.write_resolved(&target, &projs, Value::Uninit)?;
        }
        Ok(val)
    }

    fn write_place(&mut self, place: &Place, val: Value) -> Result<(), String> {
        let (target, projs) = self.resolve_place(place)?;
        self.write_resolved(&target, &projs, val)
    }

    fn eval_operand(&mut self, op: &Operand) -> Result<Value, String> {
        match op {
            Operand::Copy(place) => self.read_place(place, false),
            Operand::Move(place) => self.read_place(place, true),
            Operand::Const(cv) => Ok(Self::const_to_val(cv)),
        }
    }

    fn operand_is_unsigned(&self, func: &Function, op: &Operand) -> Result<bool, String> {
        match op {
            Operand::Copy(place) | Operand::Move(place) => {
                let ty_id = self.place_type(func, place)?;
                Ok(self
                    .program
                    .types
                    .get(ty_id.0 as usize)
                    .is_some_and(Type::is_unsigned))
            }
            Operand::Const(_) => Ok(false),
        }
    }

    fn eval_rvalue(
        &mut self,
        func: &Function,
        rvalue: &Rvalue,
        dest_ty: TypeId,
    ) -> Result<Value, String> {
        match rvalue {
            Rvalue::Use(op) => self.eval_operand(op),
            Rvalue::UnaryOp(unop, op) => {
                let val = self.eval_operand(op)?;
                match (unop, val) {
                    (UnOp::Neg, Value::Int(n)) => Ok(Value::Int(n.wrapping_neg())),
                    (UnOp::Neg, Value::Float(bits)) => {
                        Ok(Value::from_f64(-f64::from_bits(bits)))
                    }
                    (UnOp::Not, Value::Int(n)) => Ok(Value::Int(!n)),
                    (UnOp::Not, Value::Bool(b)) => Ok(Value::Bool(!b)),
                    (u, v) => Err(format!("Unsupported unary op {u} on {v:?}")),
                }
            }
            Rvalue::BinaryOp(binop, lhs, rhs) => {
                let unsigned =
                    self.operand_is_unsigned(func, lhs)? || self.operand_is_unsigned(func, rhs)?;
                let l_val = self.eval_operand(lhs)?;
                let r_val = self.eval_operand(rhs)?;

                match (l_val, r_val) {
                    (Value::Int(a), Value::Int(b)) => Ok(match (binop, unsigned) {
                        (BinOp::Add, _) => Value::Int(a.wrapping_add(b)),
                        (BinOp::Sub, _) => Value::Int(a.wrapping_sub(b)),
                        (BinOp::Mul, _) => Value::Int(a.wrapping_mul(b)),
                        (BinOp::Div, false) => Value::Int(a / b),
                        (BinOp::Div, true) => Value::Int(((a as u64) / (b as u64)) as i64),
                        (BinOp::Rem, false) => Value::Int(a % b),
                        (BinOp::Rem, true) => Value::Int(((a as u64) % (b as u64)) as i64),
                        (BinOp::BitAnd, _) => Value::Int(a & b),
                        (BinOp::BitOr, _) => Value::Int(a | b),
                        (BinOp::BitXor, _) => Value::Int(a ^ b),
                        (BinOp::Shl, _) => Value::Int(a.wrapping_shl(b as u32)),
                        (BinOp::Shr, false) => Value::Int(a.wrapping_shr(b as u32)),
                        (BinOp::Shr, true) => Value::Int(((a as u64).wrapping_shr(b as u32)) as i64),
                        (BinOp::Eq, _) => Value::Bool(a == b),
                        (BinOp::Ne, _) => Value::Bool(a != b),
                        (BinOp::Lt, false) => Value::Bool(a < b),
                        (BinOp::Lt, true) => Value::Bool((a as u64) < (b as u64)),
                        (BinOp::Le, false) => Value::Bool(a <= b),
                        (BinOp::Le, true) => Value::Bool((a as u64) <= (b as u64)),
                        (BinOp::Gt, false) => Value::Bool(a > b),
                        (BinOp::Gt, true) => Value::Bool((a as u64) > (b as u64)),
                        (BinOp::Ge, false) => Value::Bool(a >= b),
                        (BinOp::Ge, true) => Value::Bool((a as u64) >= (b as u64)),
                    }),
                    (Value::Float(ab), Value::Float(bb)) => {
                        let a = f64::from_bits(ab);
                        let b = f64::from_bits(bb);
                        match binop {
                            BinOp::Add => Ok(Value::from_f64(a + b)),
                            BinOp::Sub => Ok(Value::from_f64(a - b)),
                            BinOp::Mul => Ok(Value::from_f64(a * b)),
                            BinOp::Div => Ok(Value::from_f64(a / b)),
                            BinOp::Rem => Ok(Value::from_f64(a % b)),
                            BinOp::Eq => Ok(Value::Bool(a == b)),
                            BinOp::Ne => Ok(Value::Bool(a != b)),
                            BinOp::Lt => Ok(Value::Bool(a < b)),
                            BinOp::Le => Ok(Value::Bool(a <= b)),
                            BinOp::Gt => Ok(Value::Bool(a > b)),
                            BinOp::Ge => Ok(Value::Bool(a >= b)),
                            _ => Err(format!("Unsupported BinOp {binop} on float")),
                        }
                    }
                    (Value::Bool(a), Value::Bool(b)) => match binop {
                        BinOp::BitAnd => Ok(Value::Bool(a & b)),
                        BinOp::BitOr => Ok(Value::Bool(a | b)),
                        BinOp::BitXor => Ok(Value::Bool(a ^ b)),
                        BinOp::Eq => Ok(Value::Bool(a == b)),
                        BinOp::Ne => Ok(Value::Bool(a != b)),
                        _ => Err(format!("Unsupported BinOp {binop} on bool")),
                    },
                    (Value::Type(a), Value::Type(b)) => match binop {
                        BinOp::Eq => Ok(Value::Bool(a == b)),
                        BinOp::Ne => Ok(Value::Bool(a != b)),
                        _ => Err(format!("Unsupported BinOp {binop} on type")),
                    },
                    (l, r) => Err(format!("Invalid operands for {binop}: {l:?} and {r:?}")),
                }
            }
            Rvalue::Cast(op, target_ty_id) => {
                let val = self.eval_operand(op)?;
                let dst_ty = self
                    .program
                    .types
                    .get(target_ty_id.0 as usize)
                    .ok_or_else(|| format!("Undefined {target_ty_id}"))?;
                match (val, dst_ty) {
                    (Value::Int(n), Type::F32 | Type::F64) => Ok(Value::from_f64(n as f64)),
                    (Value::Float(bits), Type::I8 | Type::I16 | Type::I32 | Type::I64) => {
                        Ok(Value::Int(f64::from_bits(bits) as i64))
                    }
                    (Value::Float(bits), Type::U8 | Type::U16 | Type::U32 | Type::U64) => {
                        Ok(Value::Int((f64::from_bits(bits) as u64) as i64))
                    }
                    (Value::Float(bits), Type::F32) => {
                        Ok(Value::from_f64(f64::from_bits(bits) as f32 as f64))
                    }
                    (Value::Float(bits), Type::F64) => Ok(Value::Float(bits)),
                    (Value::Bool(b), _) => Ok(Value::Int(i64::from(b))),
                    (Value::Int(n), Type::Bool) => Ok(Value::Bool(n != 0)),
                    (Value::Int(n), _) => Ok(Value::Int(n)),
                    (v, t) => Err(format!("Cannot cast {v:?} to {t}")),
                }
            }
            Rvalue::Ref { mutable, place } => {
                // Zig-style comptime: if the destination has type `type` (`MetaType`) and `place` holds a `Value::Type`,
                // `&place` / `&mut place` constructs a pointer TYPE `&T` / `&mut T`!
                if matches!(
                    self.program.types.get(dest_ty.0 as usize),
                    Some(Type::MetaType)
                ) {
                    let val = self.read_place(place, false)?;
                    if let Value::Type(pointee) = val {
                        let ptr_ty = self.program.intern_type(Type::Ptr {
                            mutable: *mutable,
                            pointee,
                        });
                        return Ok(Value::Type(ptr_ty));
                    }
                }
                let (target, projections) = self.resolve_place(place)?;
                Ok(Value::Ptr {
                    target,
                    projections,
                })
            }
            Rvalue::Aggregate(agg_ty, ops) => {
                let mut vals = Vec::with_capacity(ops.len());
                for op in ops {
                    vals.push(self.eval_operand(op)?);
                }

                // Zig-style comptime: if `agg_ty` is `Type::MetaType` (`type`), aggregating `Value::Type`s
                // constructs and interns a new `Type::Struct(...)` in `Program`!
                match self.program.types.get(agg_ty.0 as usize) {
                    Some(Type::MetaType) => {
                        let mut field_types = Vec::with_capacity(vals.len());
                        for v in vals {
                            let Value::Type(ft) = v else {
                                return Err(format!(
                                    "Comptime struct type aggregate expected type operands, got {v:?}"
                                ));
                            };
                            field_types.push(ft);
                        }
                        let new_struct_ty = self.program.intern_type(Type::Struct(field_types));
                        Ok(Value::Type(new_struct_ty))
                    }
                    Some(Type::Array { .. }) => Ok(Value::Array(vals)),
                    _ => Ok(Value::Struct {
                        ty: *agg_ty,
                        fields: vals,
                    }),
                }
            }
            Rvalue::Tagged {
                ty,
                variant,
                payload,
            } => {
                let p_val = self.eval_operand(payload)?;
                Ok(Value::Tagged {
                    ty: *ty,
                    variant: *variant,
                    payload: Box::new(p_val),
                })
            }
            Rvalue::Discriminant(place) => {
                let val = self.read_place(place, false)?;
                let Value::Tagged { variant, .. } = val else {
                    return Err(format!("Cannot read discriminant of non-tagged value {val:?}"));
                };
                Ok(Value::Int(i64::from(variant)))
            }
            Rvalue::ArrayType { elem, len } => {
                let elem_val = self.eval_operand(elem)?;
                let len_val = self.eval_operand(len)?;
                let Value::Type(elem_ty) = elem_val else {
                    return Err(format!(
                        "Comptime array type constructor expected type for element, got {elem_val:?}"
                    ));
                };
                let Value::Int(n) = len_val else {
                    return Err(format!(
                        "Comptime array type constructor expected integer for length, got {len_val:?}"
                    ));
                };
                if n < 0 {
                    return Err(format!("Comptime array length cannot be negative ({n})"));
                }
                let arr_ty = self.program.intern_type(Type::Array {
                    elem: elem_ty,
                    len: n as u64,
                });
                Ok(Value::Type(arr_ty))
            }
            Rvalue::UnionType(ops) => {
                let mut field_types = Vec::with_capacity(ops.len());
                for op in ops {
                    let v = self.eval_operand(op)?;
                    let Value::Type(ft) = v else {
                        return Err(format!(
                            "Comptime union type constructor expected type operands, got {v:?}"
                        ));
                    };
                    field_types.push(ft);
                }
                let union_ty = self.program.intern_type(Type::Union(field_types));
                Ok(Value::Type(union_ty))
            }
            Rvalue::TaggedType { tag, variants } => {
                let tag_val = self.eval_operand(tag)?;
                let Value::Type(tag_ty) = tag_val else {
                    return Err(format!(
                        "Comptime tagged type constructor expected type for tag, got {tag_val:?}"
                    ));
                };
                let mut var_types = Vec::with_capacity(variants.len());
                for op in variants {
                    let v = self.eval_operand(op)?;
                    let Value::Type(vt) = v else {
                        return Err(format!(
                            "Comptime tagged type constructor expected type operands for variants, got {v:?}"
                        ));
                    };
                    var_types.push(vt);
                }
                let tagged_ty = self.program.intern_type(Type::Tagged {
                    tag: tag_ty,
                    variants: var_types,
                });
                Ok(Value::Type(tagged_ty))
            }
        }
    }
}

