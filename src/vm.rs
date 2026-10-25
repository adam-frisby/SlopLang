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
    Int(i128),
    Float(u64), // IEEE 754 bits
    Type(TypeId),
    Func(FuncId),
    Str(String),
    Array(Vec<Value>),
    Struct {
        ty: TypeId,
        fields: Vec<Value>,
    },
    Overlay {
        ty: TypeId,
        active_field: Option<u32>,
        val: Box<Value>,
    },
    Union {
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
                        Value::Bool(b) => i128::from(b),
                        Value::Type(ty) => i128::from(ty.0),
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
                        Some(Type::Array { len, .. } | Type::Simd { len, .. }) => {
                            Value::Array(vec![Value::Uninit; *len as usize])
                        }
                        Some(Type::Struct(fields)) => Value::Struct {
                            ty: ty_id,
                            fields: vec![Value::Uninit; fields.len()],
                        },
                        Some(Type::Overlay(_)) => Value::Overlay {
                            ty: ty_id,
                            active_field: None,
                            val: Box::new(Value::Uninit),
                        },
                        Some(Type::Union { .. }) => Value::Union {
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
                let cur = self.read_resolved(&target, &projs).unwrap_or(Value::Union {
                    ty: ty_id,
                    variant: *variant,
                    payload: Box::new(Value::Uninit),
                });
                let new_val = match cur {
                    Value::Union { ty, payload, .. } => Value::Union {
                        ty,
                        variant: *variant,
                        payload,
                    },
                    _ => Value::Union {
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
                self.validate_pattern_value(dest_ty, &val)?;
                self.write_place(dest, val)
            }
        }
    }

    fn validate_pattern_value(&self, ty_id: TypeId, val: &Value) -> Result<(), String> {
        let Value::Int(n) = val else {
            return Ok(());
        };
        match self.program.types.get(ty_id.0 as usize) {
            Some(Type::Rune) => {
                if !((0..=0xD7FF).contains(n) || (0xE000..=0x10FFFF).contains(n)) {
                    return Err(format!(
                        "Value {n} (0x{n:X}) is not a valid Unicode scalar value for 'rune'"
                    ));
                }
                Ok(())
            }
            Some(Type::Pattern { ranges, .. }) => {
                if !ranges.iter().any(|(lo, hi)| (*lo..=*hi).contains(n)) {
                    return Err(format!(
                        "Value {n} is outside valid pattern ranges for type {}",
                        self.program.types[ty_id.0 as usize]
                    ));
                }
                Ok(())
            }
            _ => Ok(()),
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
                    Some(Type::Struct(fields) | Type::Overlay(fields)) => {
                        cur_ty = *fields
                            .get(*idx as usize)
                            .ok_or_else(|| format!("Field .{idx} out of bounds on {cur_ty}"))?;
                    }
                    _ => {
                        return Err(format!(
                            "Cannot access field on non-struct/overlay type {cur_ty}"
                        ))
                    }
                },
                Projection::Variant(v_idx) => {
                    let Some(Type::Union { variants, .. }) =
                        self.program.types.get(cur_ty.0 as usize)
                    else {
                        return Err(format!(
                            "Cannot access variant .v{v_idx} on non-union type {cur_ty}"
                        ));
                    };
                    cur_ty = *variants
                        .get(*v_idx as usize)
                        .ok_or_else(|| format!("Variant .v{v_idx} out of bounds on {cur_ty}"))?;
                }
                Projection::Index(_) => {
                    let Some(Type::Array { elem, .. } | Type::Simd { elem, .. }) =
                        self.program.types.get(cur_ty.0 as usize)
                    else {
                        return Err(format!("Cannot index non-array/simd type {cur_ty}"));
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
                    Value::Overlay {
                        active_field, val, ..
                    } => {
                        if *active_field != Some(*idx) {
                            return Err(format!(
                                "Overlay read of inactive field .{idx} (active: {active_field:?})"
                            ));
                        }
                        cur = val;
                    }
                    _ => return Err(format!("Cannot access field .{idx} on {cur:?}")),
                },
                ResolvedProj::Variant(v_idx) => {
                    let Value::Union {
                        variant, payload, ..
                    } = cur
                    else {
                        return Err(format!("Cannot access variant .v{v_idx} on {cur:?}"));
                    };
                    if *variant != *v_idx {
                        return Err(format!(
                            "Union read of inactive variant .v{v_idx} (active: v{variant})"
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
                    Value::Overlay {
                        active_field, val, ..
                    } => {
                        *active_field = Some(*idx);
                        cur = val;
                    }
                    _ => return Err(format!("Cannot write field .{idx} on {cur:?}")),
                },
                ResolvedProj::Variant(v_idx) => {
                    let Value::Union {
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

    fn operand_type(&self, func: &Function, op: &Operand) -> Result<Option<TypeId>, String> {
        match op {
            Operand::Copy(place) | Operand::Move(place) => Ok(Some(self.place_type(func, place)?)),
            Operand::Const(_) => Ok(None),
        }
    }

    fn int_type_bounds(ty: &Type) -> (i128, i128, u32, bool) {
        match ty {
            Type::Int {
                signed: true,
                bits: b,
            } => {
                let bits = u32::from(*b);
                if bits >= 128 {
                    (i128::MIN, i128::MAX, bits, false)
                } else {
                    let min = -(1i128 << (bits - 1));
                    let max = (1i128 << (bits - 1)) - 1;
                    (min, max, bits, false)
                }
            }
            Type::Int {
                signed: false,
                bits: b,
            } => {
                let bits = u32::from(*b);
                if bits >= 128 {
                    (0, i128::MAX, bits, true)
                } else {
                    let max = (1i128 << bits) - 1;
                    (0, max, bits, true)
                }
            }
            Type::Rune => (0, 0x10FFFF, 32, true),
            Type::Pattern { .. } => (i64::MIN as i128, i64::MAX as i128, 64, false),
            _ => (i64::MIN as i128, i64::MAX as i128, 64, false),
        }
    }

    fn wrap_int_to_bits(val: i128, bits: u32, unsigned: bool) -> i128 {
        if bits >= 128 {
            return val;
        }
        let mask: u128 = (1u128 << bits) - 1;
        let raw = (val as u128) & mask;
        if unsigned {
            raw as i128
        } else {
            let sign_bit = 1u128 << (bits - 1);
            if (raw & sign_bit) != 0 {
                (raw | !mask) as i128
            } else {
                raw as i128
            }
        }
    }

    fn eval_scalar_binop(
        inferred_ty: &Type,
        binop: BinOp,
        l_val: Value,
        r_val: Value,
    ) -> Result<Value, String> {
        let (min_val, max_val, bits, unsigned) = Self::int_type_bounds(inferred_ty);
        match (l_val, r_val) {
            (Value::Int(a), Value::Int(b)) => {
                if unsigned && bits >= 128 {
                    let au = a as u128;
                    let bu = b as u128;
                    return match binop {
                        BinOp::Add
                        | BinOp::Sub
                        | BinOp::Mul
                        | BinOp::AddUnchecked
                        | BinOp::SubUnchecked
                        | BinOp::MulUnchecked => {
                            let res = match binop {
                                BinOp::Add | BinOp::AddUnchecked => au.checked_add(bu),
                                BinOp::Sub | BinOp::SubUnchecked => au.checked_sub(bu),
                                BinOp::Mul | BinOp::MulUnchecked => au.checked_mul(bu),
                                _ => unreachable!(),
                            };
                            let Some(v) = res else {
                                return Err(format!(
                                    "Integer overflow in '{binop}({au}, {bu})' for type {inferred_ty}"
                                ));
                            };
                            Ok(Value::Int(v as i128))
                        }
                        BinOp::AddWrap => Ok(Value::Int(au.wrapping_add(bu) as i128)),
                        BinOp::SubWrap => Ok(Value::Int(au.wrapping_sub(bu) as i128)),
                        BinOp::MulWrap => Ok(Value::Int(au.wrapping_mul(bu) as i128)),
                        BinOp::AddSat => Ok(Value::Int(au.saturating_add(bu) as i128)),
                        BinOp::SubSat => Ok(Value::Int(au.saturating_sub(bu) as i128)),
                        BinOp::MulSat => Ok(Value::Int(au.saturating_mul(bu) as i128)),
                        BinOp::Div => {
                            if bu == 0 {
                                return Err("Division by zero".to_string());
                            }
                            Ok(Value::Int((au / bu) as i128))
                        }
                        BinOp::Rem => {
                            if bu == 0 {
                                return Err("Remainder by zero".to_string());
                            }
                            Ok(Value::Int((au % bu) as i128))
                        }
                        BinOp::BitAnd => Ok(Value::Int(a & b)),
                        BinOp::BitOr => Ok(Value::Int(a | b)),
                        BinOp::BitXor => Ok(Value::Int(a ^ b)),
                        BinOp::Shl => Ok(Value::Int((au.wrapping_shl(bu as u32)) as i128)),
                        BinOp::Shr => Ok(Value::Int((au.wrapping_shr(bu as u32)) as i128)),
                        BinOp::Eq => Ok(Value::Bool(au == bu)),
                        BinOp::Ne => Ok(Value::Bool(au != bu)),
                        BinOp::Lt => Ok(Value::Bool(au < bu)),
                        BinOp::Le => Ok(Value::Bool(au <= bu)),
                        BinOp::Gt => Ok(Value::Bool(au > bu)),
                        BinOp::Ge => Ok(Value::Bool(au >= bu)),
                    };
                }

                let a128 = if unsigned {
                    (a as u128 & ((1u128 << bits) - 1)) as i128
                } else {
                    a
                };
                let b128 = if unsigned {
                    (b as u128 & ((1u128 << bits) - 1)) as i128
                } else {
                    b
                };
                match binop {
                    BinOp::Add
                    | BinOp::Sub
                    | BinOp::Mul
                    | BinOp::AddUnchecked
                    | BinOp::SubUnchecked
                    | BinOp::MulUnchecked => {
                        let res = match binop {
                            BinOp::Add | BinOp::AddUnchecked => a128.checked_add(b128),
                            BinOp::Sub | BinOp::SubUnchecked => a128.checked_sub(b128),
                            BinOp::Mul | BinOp::MulUnchecked => a128.checked_mul(b128),
                            _ => unreachable!(),
                        };
                        let Some(v) = res else {
                            return Err(format!(
                                "Integer overflow in '{binop}({a128}, {b128})' for type {inferred_ty}"
                            ));
                        };
                        if v < min_val || v > max_val {
                            return Err(format!(
                                "Integer overflow in '{binop}({a128}, {b128})' = {v} (out of range {min_val}..={max_val} for {inferred_ty})"
                            ));
                        }
                        Ok(Value::Int(v))
                    }
                    BinOp::AddWrap | BinOp::SubWrap | BinOp::MulWrap => {
                        let res = match binop {
                            BinOp::AddWrap => a128.wrapping_add(b128),
                            BinOp::SubWrap => a128.wrapping_sub(b128),
                            BinOp::MulWrap => a128.wrapping_mul(b128),
                            _ => unreachable!(),
                        };
                        Ok(Value::Int(Self::wrap_int_to_bits(res, bits, unsigned)))
                    }
                    BinOp::AddSat | BinOp::SubSat | BinOp::MulSat => {
                        let clamped = match binop {
                            BinOp::AddSat => a128
                                .checked_add(b128)
                                .map(|v| v.clamp(min_val, max_val))
                                .unwrap_or(if b128 < 0 { min_val } else { max_val }),
                            BinOp::SubSat => a128
                                .checked_sub(b128)
                                .map(|v| v.clamp(min_val, max_val))
                                .unwrap_or(if b128 < 0 { max_val } else { min_val }),
                            BinOp::MulSat => a128
                                .checked_mul(b128)
                                .map(|v| v.clamp(min_val, max_val))
                                .unwrap_or(if (a128 < 0) ^ (b128 < 0) {
                                    min_val
                                } else {
                                    max_val
                                }),
                            _ => unreachable!(),
                        };
                        Ok(Value::Int(clamped))
                    }
                    BinOp::Div => {
                        if b128 == 0 {
                            return Err("Division by zero".to_string());
                        }
                        Ok(Value::Int(a128 / b128))
                    }
                    BinOp::Rem => {
                        if b128 == 0 {
                            return Err("Remainder by zero".to_string());
                        }
                        Ok(Value::Int(a128 % b128))
                    }
                    BinOp::BitAnd => Ok(Value::Int(a128 & b128)),
                    BinOp::BitOr => Ok(Value::Int(a128 | b128)),
                    BinOp::BitXor => Ok(Value::Int(a128 ^ b128)),
                    BinOp::Shl => Ok(Value::Int(a128.wrapping_shl(b128 as u32))),
                    BinOp::Shr => Ok(Value::Int(if unsigned {
                        ((a128 as u128).wrapping_shr(b128 as u32)) as i128
                    } else {
                        a128.wrapping_shr(b128 as u32)
                    })),
                    BinOp::Eq => Ok(Value::Bool(a128 == b128)),
                    BinOp::Ne => Ok(Value::Bool(a128 != b128)),
                    BinOp::Lt => Ok(Value::Bool(a128 < b128)),
                    BinOp::Le => Ok(Value::Bool(a128 <= b128)),
                    BinOp::Gt => Ok(Value::Bool(a128 > b128)),
                    BinOp::Ge => Ok(Value::Bool(a128 >= b128)),
                }
            }
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
                    (u, Value::Array(elems)) => {
                        let mut out = Vec::with_capacity(elems.len());
                        for e in elems {
                            let v = match (u, e) {
                                (UnOp::Neg, Value::Int(n)) => Value::Int(n.wrapping_neg()),
                                (UnOp::Neg, Value::Float(bits)) => {
                                    Value::from_f64(-f64::from_bits(bits))
                                }
                                (UnOp::Not, Value::Int(n)) => Value::Int(!n),
                                (UnOp::Not, Value::Bool(b)) => Value::Bool(!b),
                                (u, v) => {
                                    return Err(format!("Unsupported SIMD unary op {u} on {v:?}"))
                                }
                            };
                            out.push(v);
                        }
                        Ok(Value::Array(out))
                    }
                    (u, v) => Err(format!("Unsupported unary op {u} on {v:?}")),
                }
            }
            Rvalue::BinaryOp(binop, lhs, rhs) => {
                let inferred_ty_id = self
                    .operand_type(func, lhs)?
                    .or(self.operand_type(func, rhs)?)
                    .unwrap_or(dest_ty);
                let inferred_ty = self
                    .program
                    .types
                    .get(inferred_ty_id.0 as usize)
                    .cloned()
                    .unwrap_or(Type::Int {
                        signed: true,
                        bits: 64,
                    });
                let l_val = self.eval_operand(lhs)?;
                let r_val = self.eval_operand(rhs)?;

                if let (Value::Array(l_elems), Value::Array(r_elems)) = (&l_val, &r_val) {
                    if l_elems.len() != r_elems.len() {
                        return Err(format!(
                            "SIMD vector lane length mismatch: {} vs {}",
                            l_elems.len(),
                            r_elems.len()
                        ));
                    }
                    let elem_ty = match &inferred_ty {
                        Type::Simd { elem, .. } | Type::Array { elem, .. } => self
                            .program
                            .types
                            .get(elem.0 as usize)
                            .cloned()
                            .unwrap_or(Type::Int {
                                signed: true,
                                bits: 64,
                            }),
                        other => other.clone(),
                    };
                    let mut out = Vec::with_capacity(l_elems.len());
                    for (le, re) in l_elems.iter().cloned().zip(r_elems.iter().cloned()) {
                        out.push(Self::eval_scalar_binop(&elem_ty, *binop, le, re)?);
                    }
                    return Ok(Value::Array(out));
                }

                Self::eval_scalar_binop(&inferred_ty, *binop, l_val, r_val)
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
                    (Value::Float(bits), Type::Int { signed: true, .. }) => {
                        Ok(Value::Int(f64::from_bits(bits) as i128))
                    }
                    (Value::Float(bits), Type::Rune | Type::Int { signed: false, .. }) => {
                        Ok(Value::Int((f64::from_bits(bits) as u128) as i128))
                    }
                    (Value::Float(bits), Type::F32) => {
                        Ok(Value::from_f64(f64::from_bits(bits) as f32 as f64))
                    }
                    (Value::Float(bits), Type::F64) => Ok(Value::Float(bits)),
                    (Value::Bool(b), _) => Ok(Value::Int(i128::from(b))),
                    (Value::Int(n), Type::Bool) => Ok(Value::Bool(n != 0)),
                    (Value::Int(n), _) => Ok(Value::Int(n)),
                    (Value::Ptr { target, projections }, Type::Ptr { .. }) => {
                        Ok(Value::Ptr { target, projections })
                    }
                    (Value::Ptr { .. }, Type::Int { .. }) => Ok(Value::Int(1)),
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
                    Some(Type::Simd { len, .. }) => {
                        if vals.len() == 1 && *len > 1 {
                            Ok(Value::Array(vec![vals[0].clone(); *len as usize]))
                        } else {
                            Ok(Value::Array(vals))
                        }
                    }
                    _ => Ok(Value::Struct {
                        ty: *agg_ty,
                        fields: vals,
                    }),
                }
            }
            Rvalue::Union {
                ty,
                variant,
                payload,
            } => {
                let p_val = self.eval_operand(payload)?;
                Ok(Value::Union {
                    ty: *ty,
                    variant: *variant,
                    payload: Box::new(p_val),
                })
            }
            Rvalue::Discriminant(place) => {
                let val = self.read_place(place, false)?;
                let Value::Union { variant, .. } = val else {
                    return Err(format!("Cannot read discriminant of non-union value {val:?}"));
                };
                Ok(Value::Int(i128::from(variant)))
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
            Rvalue::SimdType { elem, len } => {
                let elem_val = self.eval_operand(elem)?;
                let len_val = self.eval_operand(len)?;
                let Value::Type(elem_ty) = elem_val else {
                    return Err(format!(
                        "Comptime SIMD type constructor expected type for element, got {elem_val:?}"
                    ));
                };
                let Value::Int(n) = len_val else {
                    return Err(format!(
                        "Comptime SIMD type constructor expected integer for lane count, got {len_val:?}"
                    ));
                };
                if n <= 0 {
                    return Err(format!("Comptime SIMD lane count must be positive ({n})"));
                }
                let simd_ty = self.program.intern_type(Type::Simd {
                    elem: elem_ty,
                    len: n as u64,
                });
                Ok(Value::Type(simd_ty))
            }
            Rvalue::OverlayType(ops) => {
                let mut field_types = Vec::with_capacity(ops.len());
                for op in ops {
                    let v = self.eval_operand(op)?;
                    let Value::Type(ft) = v else {
                        return Err(format!(
                            "Comptime overlay type constructor expected type operands, got {v:?}"
                        ));
                    };
                    field_types.push(ft);
                }
                let overlay_ty = self.program.intern_type(Type::Overlay(field_types));
                Ok(Value::Type(overlay_ty))
            }
            Rvalue::UnionType { tag, variants } => {
                let tag_val = self.eval_operand(tag)?;
                let Value::Type(tag_ty) = tag_val else {
                    return Err(format!(
                        "Comptime union type constructor expected type for tag, got {tag_val:?}"
                    ));
                };
                let mut var_types = Vec::with_capacity(variants.len());
                for op in variants {
                    let v = self.eval_operand(op)?;
                    let Value::Type(vt) = v else {
                        return Err(format!(
                            "Comptime union type constructor expected type operands for variants, got {v:?}"
                        ));
                    };
                    var_types.push(vt);
                }
                let union_ty = self.program.intern_type(Type::Union {
                    tag: tag_ty,
                    variants: var_types,
                });
                Ok(Value::Type(union_ty))
            }
            Rvalue::PatternType { base, ranges } => {
                let base_val = self.eval_operand(base)?;
                let Value::Type(base_ty) = base_val else {
                    return Err(format!(
                        "Comptime pattern type constructor expected base integer type, got {base_val:?}"
                    ));
                };
                let mut eval_ranges = Vec::with_capacity(ranges.len());
                for (lo_op, hi_op) in ranges {
                    let lo_val = self.eval_operand(lo_op)?;
                    let hi_val = self.eval_operand(hi_op)?;
                    let (Value::Int(lo), Value::Int(hi)) = (lo_val, hi_val) else {
                        return Err(
                            "Comptime pattern type constructor expected integer range bounds"
                                .to_string(),
                        );
                    };
                    if lo > hi {
                        return Err(format!(
                            "Invalid pattern range {lo}..={hi}: lower bound exceeds upper bound"
                        ));
                    }
                    eval_ranges.push((lo, hi));
                }
                let pat_ty = self.program.intern_type(Type::Pattern {
                    base: base_ty,
                    ranges: eval_ranges,
                });
                Ok(Value::Type(pat_ty))
            }
        }
    }
}

