use crate::ir::{
    BinOp, BlockId, ConstValue, FuncId, Function, GlobalId, LocalId, Operand, Place, Program,
    Projection, Rvalue, Statement, Terminator, Type, TypeId, UnOp,
};
use crate::wide::Wide;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PtrTarget {
    Local { frame: usize, local: LocalId },
    Global(GlobalId),
    Str(String),
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
    /// An integer that does not fit in `i128` (values of `u128`..`u512` / `i129`..`i512` types).
    Wide(Box<crate::wide::Wide>),
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
    /// An integer value in canonical form: `Int` when it fits in `i128`, otherwise `Wide`.
    pub fn from_wide(v: crate::wide::Wide) -> Self {
        match v.to_i128() {
            Some(n) => Value::Int(n),
            None => Value::Wide(Box::new(v)),
        }
    }

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
            Value::Array(elems) | Value::Struct { fields: elems, .. } => {
                let mut cvs = Vec::with_capacity(elems.len());
                for e in elems {
                    cvs.push(e.to_const()?);
                }
                Ok(ConstValue::Aggregate(cvs))
            }
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
    steps: usize,
    max_steps: usize,
}

impl<'a> Vm<'a> {
    pub fn new(program: &'a mut Program) -> Self {
        let globals = program
            .globals
            .iter()
            .map(|g| Self::const_to_val_typed(&g.init, g.ty, &program.types))
            .collect();
        Self {
            program,
            globals,
            frames: Vec::new(),
            steps: 0,
            max_steps: 1_000_000,
        }
    }

    pub fn set_max_steps(&mut self, max_steps: usize) {
        self.max_steps = max_steps;
    }

    pub fn eval_call(&mut self, func_id: FuncId, args: Vec<Value>) -> Result<Value, String> {
        self.call_root(func_id, args)
    }

    pub fn read_ptr_value(
        &self,
        target: &PtrTarget,
        projs: &[ResolvedProj],
    ) -> Result<Value, String> {
        self.read_resolved(target, projs)
    }

    fn const_to_val_typed(cv: &ConstValue, ty_id: TypeId, types: &[Type]) -> Value {
        if let ConstValue::Aggregate(items) = cv {
            match types.get(ty_id.0 as usize) {
                Some(Type::Struct(ftys)) => {
                    let fields = items
                        .iter()
                        .enumerate()
                        .map(|(i, item)| {
                            let fty = ftys.get(i).copied().unwrap_or(ty_id);
                            Self::const_to_val_typed(item, fty, types)
                        })
                        .collect();
                    return Value::Struct { ty: ty_id, fields };
                }
                Some(Type::Array { elem, .. }) => {
                    let elems = items
                        .iter()
                        .map(|item| Self::const_to_val_typed(item, *elem, types))
                        .collect();
                    return Value::Array(elems);
                }
                _ => {}
            }
        }
        Self::const_to_val(cv)
    }

    fn const_to_val(cv: &ConstValue) -> Value {
        match cv {
            ConstValue::Void => Value::Void,
            ConstValue::Bool(b) => Value::Bool(*b),
            ConstValue::I64(n) => Value::Int(*n),
            ConstValue::Wide(w) => Value::Wide(w.clone()),
            ConstValue::F64(bits) => Value::Float(*bits),
            ConstValue::Type(id) => Value::Type(*id),
            ConstValue::Func(id) => Value::Func(*id),
            ConstValue::Global(id) => Value::Ptr {
                target: PtrTarget::Global(*id),
                projections: Vec::new(),
            },
            ConstValue::Str(s) => Value::Str(s.clone()),
            ConstValue::Aggregate(items) => {
                Value::Array(items.iter().map(Self::const_to_val).collect())
            }
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
                self.steps += 1;
                if self.steps > self.max_steps {
                    return Err(format!(
                        "Comptime VM sandbox violation: evaluation exceeded step limit of {}",
                        self.max_steps
                    ));
                }
                self.exec_statement(&func, stmt)?;
            }
            self.steps += 1;
            if self.steps > self.max_steps {
                return Err(format!(
                    "Comptime VM sandbox violation: evaluation exceeded step limit of {}",
                    self.max_steps
                ));
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
                            ));
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

                    if let Some(ext) = self.program.externs.iter().find(|e| e.id == callee_id) {
                        return Err(format!(
                            "Comptime VM sandbox violation: cannot call extern function '{}' during comptime evaluation",
                            ext.symbol
                        ));
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
                    let is_init = self.read_resolved(&ptr_target, &projs).is_ok();
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
                let mut val = self.eval_rvalue(func, rvalue, dest_ty)?;
                if matches!(val, Value::Void) {
                    val = Self::uninit_value_for_type(self.program, dest_ty);
                }
                self.validate_pattern_value(dest_ty, &val)?;
                self.write_place(dest, val)
            }
        }
    }

    fn uninit_value_for_type(program: &Program, ty_id: TypeId) -> Value {
        match program.types.get(ty_id.0 as usize) {
            Some(Type::Overlay(_)) => Value::Overlay {
                ty: ty_id,
                active_field: Some(0),
                val: Box::new(Value::Void),
            },
            Some(Type::Array { elem, len } | Type::Simd { elem, len }) => Value::Array(vec![
                Self::uninit_value_for_type(program, *elem);
                *len as usize
            ]),
            _ => Value::Void,
        }
    }

    fn validate_pattern_value(&self, ty_id: TypeId, val: &Value) -> Result<(), String> {
        if let (Value::Wide(w), Some(Type::Pattern { ranges, .. })) =
            (val, self.program.types.get(ty_id.0 as usize))
            && !crate::ir::pattern_contains(ranges, w)
        {
            return Err(format!(
                "Value {w} is outside valid pattern ranges for type {}",
                self.program.type_label(ty_id)
            ));
        }
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
                if !crate::ir::pattern_contains(ranges, &Wide::from_i128(*n)) {
                    return Err(format!(
                        "Value {n} is outside valid pattern ranges for type {}",
                        self.program.type_label(ty_id)
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
                        return Err(format!(
                            "Cannot deref non-pointer type '{}'",
                            self.program.type_label(cur_ty)
                        ));
                    };
                    cur_ty = *pointee;
                }
                Projection::Field(idx) => match self.program.types.get(cur_ty.0 as usize) {
                    Some(Type::Struct(fields) | Type::Overlay(fields)) => {
                        cur_ty = *fields
                            .get(*idx as usize)
                            .ok_or_else(|| format!(
                                "Field .{idx} out of bounds on '{}'",
                                self.program.type_label(cur_ty)
                            ))?;
                    }
                    _ => {
                        return Err(format!(
                            "Cannot access field on non-struct/overlay type '{}'",
                            self.program.type_label(cur_ty)
                        ));
                    }
                },
                Projection::Variant(v_idx) => {
                    let Some(Type::Union { variants, .. }) =
                        self.program.types.get(cur_ty.0 as usize)
                    else {
                        return Err(format!(
                            "Cannot access variant .v{v_idx} on non-union type '{}'",
                            self.program.type_label(cur_ty)
                        ));
                    };
                    cur_ty = *variants
                        .get(*v_idx as usize)
                        .ok_or_else(|| format!(
                            "Variant .v{v_idx} out of bounds on '{}'",
                            self.program.type_label(cur_ty)
                        ))?;
                }
                Projection::Index(_) => {
                    let Some(Type::Array { elem, .. } | Type::Simd { elem, .. }) =
                        self.program.types.get(cur_ty.0 as usize)
                    else {
                        return Err(format!(
                            "Cannot index non-array/simd type '{}'",
                            self.program.type_label(cur_ty)
                        ));
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
                    match ptr_val {
                        Value::Ptr {
                            target,
                            projections,
                        } => {
                            cur_target = target;
                            cur_projs = projections;
                        }
                        Value::Str(s) => {
                            cur_target = PtrTarget::Str(s);
                            cur_projs = Vec::new();
                        }
                        _ => {
                            return Err(format!(
                                "Cannot dereference non-pointer value {ptr_val:?}"
                            ));
                        }
                    }
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

    fn read_resolved(&self, target: &PtrTarget, projs: &[ResolvedProj]) -> Result<Value, String> {
        if let PtrTarget::Str(s) = target {
            if projs.is_empty() {
                return Ok(Value::Str(s.clone()));
            }
            if let [ResolvedProj::Index(idx)] = projs {
                let b = *s.as_bytes().get(*idx).ok_or_else(|| {
                    format!("String index {idx} out of bounds (len {})", s.len())
                })?;
                return Ok(Value::Int(i128::from(b)));
            }
            return Err(format!("Unsupported projections {projs:?} on string target"));
        }
        let mut cur = match target {
            PtrTarget::Local { frame, local } => self.frames[*frame]
                .locals
                .get(local.0 as usize)
                .ok_or_else(|| format!("Undefined {local}"))?,
            PtrTarget::Global(gl_id) => self
                .globals
                .get(gl_id.0 as usize)
                .ok_or_else(|| format!("Undefined {gl_id}"))?,
            PtrTarget::Str(_) => unreachable!(),
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
                    cur = elems.get(*idx).ok_or_else(|| {
                        format!("Array index {idx} out of bounds (len {})", elems.len())
                    })?;
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
            PtrTarget::Str(_) => {
                return Err("Cannot write to immutable string literal".to_string());
            }
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

    /// Byte offsets of `fields` laid out in order with natural alignment (as `type_size_align`).
    fn field_offsets(&self, fields: &[TypeId]) -> Result<Vec<u64>, String> {
        let mut offset = 0u64;
        let mut out = Vec::with_capacity(fields.len());
        for &f in fields {
            let (fs, fa) = self.program.type_size_align(f)?;
            offset = (offset + fa - 1) & !(fa - 1);
            out.push(offset);
            offset += fs;
        }
        Ok(out)
    }

    /// Byte offset of a tagged union's payload: the tag first, then the payload aligned to the
    /// largest variant alignment.
    fn union_payload_offset(&self, tag: TypeId, variants: &[TypeId]) -> Result<u64, String> {
        let (ts, _) = self.program.type_size_align(tag)?;
        let mut max_align = 1u64;
        for &v in variants {
            max_align = max_align.max(self.program.type_size_align(v)?.1);
        }
        Ok((ts + max_align - 1) & !(max_align - 1))
    }

    /// The in-memory bit pattern of `v` (of type `ty`) as laid out by compiled code, for
    /// `@transmute`. Supports scalars, optionals, unions, structs, arrays, and overlays up to 128
    /// bytes; pointers have no bit pattern in the VM.
    fn value_to_bits(&self, v: &Value, ty: TypeId) -> Result<crate::wide::Wide, String> {
        let (size, _) = self.program.type_size_align(ty)?;
        if size > 128 {
            return Err(format!(
                "'@transmute' of a {size}-byte value is not supported during compile-time evaluation"
            ));
        }
        let int_bits = |v: &Value| -> Result<Wide, String> {
            match v {
                Value::Int(n) => Ok(Wide::from_i128(*n)),
                Value::Wide(w) => Ok(**w),
                Value::Bool(b) => Ok(Wide::from_i128(i128::from(*b))),
                other => Err(format!("Expected an integer value for '@transmute', got {other:?}")),
            }
        };
        let place = |acc: Wide, field: Wide, offset: u64, bytes: u64| {
            acc.bitor(&field.wrap((bytes * 8) as u16, false).shl((offset * 8) as u32))
        };
        let ty_def = self
            .program
            .types
            .get(ty.0 as usize)
            .ok_or_else(|| format!("Undefined type {ty}"))?
            .clone();
        match ty_def {
            Type::Void | Type::Never => Ok(Wide::ZERO),
            Type::Bool | Type::Int { .. } | Type::Rune | Type::Pattern { .. } => {
                Ok(int_bits(v)?.wrap((size * 8) as u16, false))
            }
            Type::F32 => match v {
                Value::Float(b) => Ok(Wide::from_i128(i128::from(
                    (f64::from_bits(*b) as f32).to_bits(),
                ))),
                other => Err(format!("Expected a float value, got {other:?}")),
            },
            Type::F64 => match v {
                Value::Float(b) => Ok(Wide::from_i128(i128::from(*b))),
                other => Err(format!("Expected a float value, got {other:?}")),
            },
            Type::Union { tag, variants } => {
                let Value::Union { variant, payload, .. } = v else {
                    return Err(format!("Expected a union value, got {v:?}"));
                };
                let var_ty = variants[*variant as usize];
                if let Some((payload_ty, null)) = self.program.union_niche(ty) {
                    let (ps, _) = self.program.type_size_align(payload_ty)?;
                    return Ok(if *variant == 0 {
                        Wide::from_i128(null).wrap((ps * 8) as u16, false)
                    } else {
                        self.value_to_bits(payload, payload_ty)?
                    });
                }
                let stored_tag = self
                    .program
                    .union_tag_values(ty)
                    .and_then(|vals| vals.get(*variant as usize).copied())
                    .unwrap_or(i128::from(*variant));
                let (ts, _) = self.program.type_size_align(tag)?;
                let off = self.union_payload_offset(tag, &variants)?;
                let (vs, _) = self.program.type_size_align(var_ty)?;
                let acc = place(Wide::ZERO, Wide::from_i128(stored_tag), 0, ts);
                Ok(place(acc, self.value_to_bits(payload, var_ty)?, off, vs))
            }
            Type::Struct(fields) => {
                let Value::Struct { fields: vals, .. } = v else {
                    return Err(format!("Expected a struct value, got {v:?}"));
                };
                let offsets = self.field_offsets(&fields)?;
                let mut acc = Wide::ZERO;
                for ((fty, off), fv) in fields.iter().zip(offsets).zip(vals) {
                    let (fs, _) = self.program.type_size_align(*fty)?;
                    acc = place(acc, self.value_to_bits(fv, *fty)?, off, fs);
                }
                Ok(acc)
            }
            Type::Array { elem, .. } => {
                let Value::Array(vals) = v else {
                    return Err(format!("Expected an array value, got {v:?}"));
                };
                let (es, _) = self.program.type_size_align(elem)?;
                let mut acc = Wide::ZERO;
                for (i, ev) in vals.iter().enumerate() {
                    acc = place(acc, self.value_to_bits(ev, elem)?, i as u64 * es, es);
                }
                Ok(acc)
            }
            Type::Overlay(fields) => match v {
                Value::Overlay {
                    active_field: Some(f),
                    val,
                    ..
                } => self.value_to_bits(val, fields[*f as usize]),
                _ => Ok(Wide::ZERO),
            },
            other => Err(format!(
                "'@transmute' of {other} values is not supported during compile-time evaluation"
            )),
        }
    }

    /// Decodes a bit pattern produced by `value_to_bits` as a value of type `ty`.
    fn bits_to_value(&self, bits: &crate::wide::Wide, ty: TypeId) -> Result<Value, String> {
        let slice = |offset: u64, bytes: u64| bits.shr((offset * 8) as u32).wrap((bytes * 8) as u16, false);
        let ty_def = self
            .program
            .types
            .get(ty.0 as usize)
            .ok_or_else(|| format!("Undefined type {ty}"))?
            .clone();
        match ty_def {
            Type::Void | Type::Never => Ok(Value::Void),
            Type::Bool => Ok(Value::Bool(!bits.wrap(8, false).is_zero())),
            Type::Int { signed, bits: n } => Ok(Value::from_wide(bits.wrap(n, signed))),
            Type::Rune => Ok(Value::from_wide(bits.wrap(32, false))),
            Type::Pattern { base, .. } => self.bits_to_value(bits, base),
            Type::F32 => {
                let raw = bits.wrap(32, false).to_i128().unwrap_or(0) as u32;
                Ok(Value::from_f64(f64::from(f32::from_bits(raw))))
            }
            Type::F64 => Ok(Value::Float(bits.wrap(64, false).to_i128().unwrap_or(0) as u64)),
            Type::Union { tag, variants } => {
                if let Some((payload_ty, null)) = self.program.union_niche(ty) {
                    let (ps, _) = self.program.type_size_align(payload_ty)?;
                    let raw = slice(0, ps);
                    return Ok(if raw == Wide::from_i128(null).wrap((ps * 8) as u16, false) {
                        Value::Union {
                            ty,
                            variant: 0,
                            payload: Box::new(Value::Void),
                        }
                    } else {
                        Value::Union {
                            ty,
                            variant: 1,
                            payload: Box::new(self.bits_to_value(&raw, payload_ty)?),
                        }
                    });
                }
                let (ts, _) = self.program.type_size_align(tag)?;
                let stored = slice(0, ts);
                let variant = match self.program.union_tag_values(ty) {
                    Some(vals) => vals
                        .iter()
                        .position(|v| Wide::from_i128(*v).wrap((ts * 8) as u16, false) == stored),
                    None => stored.to_i128().map(|i| i as usize),
                }
                .filter(|&i| i < variants.len())
                .ok_or_else(|| format!(
                    "'@transmute' produced an invalid tag {stored} for '{}'",
                    self.program.type_label(ty)
                ))?;
                let var_ty = variants[variant];
                let off = self.union_payload_offset(tag, &variants)?;
                let (vs, _) = self.program.type_size_align(var_ty)?;
                Ok(Value::Union {
                    ty,
                    variant: variant as u32,
                    payload: Box::new(self.bits_to_value(&slice(off, vs), var_ty)?),
                })
            }
            Type::Struct(fields) => {
                let offsets = self.field_offsets(&fields)?;
                let mut vals = Vec::with_capacity(fields.len());
                for (fty, off) in fields.iter().zip(offsets) {
                    let (fs, _) = self.program.type_size_align(*fty)?;
                    vals.push(self.bits_to_value(&slice(off, fs), *fty)?);
                }
                Ok(Value::Struct { ty, fields: vals })
            }
            Type::Array { elem, len } => {
                let (es, _) = self.program.type_size_align(elem)?;
                let mut vals = Vec::with_capacity(len as usize);
                for i in 0..len {
                    vals.push(self.bits_to_value(&slice(i * es, es), elem)?);
                }
                Ok(Value::Array(vals))
            }
            other => Err(format!(
                "'@transmute' to {other} is not supported during compile-time evaluation"
            )),
        }
    }

    /// `(bits, unsigned)` of an integer-like type (`isize`-like `i64` for anything else).
    fn int_width(ty: &Type) -> (u32, bool) {
        match ty {
            Type::Int { signed, bits } => (u32::from(*bits), !signed),
            Type::Rune => (32, true),
            _ => (64, false),
        }
    }

    pub(crate) fn wrap_int_to_bits(val: i128, bits: u32, unsigned: bool) -> i128 {
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

    pub(crate) fn bswap_int(val: i128, bits: u32, unsigned: bool) -> i128 {
        let byte_count = (bits / 8) as usize;
        if byte_count <= 1 {
            return Self::wrap_int_to_bits(val, bits, unsigned);
        }
        let raw = val as u128;
        let mut swapped = 0u128;
        for i in 0..byte_count {
            let b = (raw >> (i * 8)) & 0xFF;
            swapped |= b << ((byte_count - 1 - i) * 8);
        }
        Self::wrap_int_to_bits(swapped as i128, bits, unsigned)
    }

    fn eval_scalar_binop(
        inferred_ty: &Type,
        binop: BinOp,
        l_val: Value,
        r_val: Value,
    ) -> Result<Value, String> {
        // Integers use the exact semantics of compile-time folding (`wide::apply_binop`):
        // overflow, division, and shift-amount errors, wrapping and saturating operators.
        let (bits, unsigned) = Self::int_width(inferred_ty);
        let as_wide = |v: &Value| match v {
            Value::Int(n) => Some(Wide::from_i128(*n)),
            Value::Wide(w) => Some(**w),
            _ => None,
        };
        let (l_val, r_val) = match (as_wide(&l_val), as_wide(&r_val)) {
            (Some(l), Some(r)) => {
                // Older code paths may hold a `u128` as its `i128` bit pattern: normalize.
                let width = u16::try_from(bits).unwrap_or(512);
                let l = l.wrap(width, !unsigned);
                let r = r.wrap(width, !unsigned);
                return match crate::wide::apply_binop(binop, &l, &r, width, !unsigned)
                    .map_err(|e| format!("{e} (for type '{inferred_ty}')"))?
                {
                    crate::wide::BinResult::Bool(b) => Ok(Value::Bool(b)),
                    crate::wide::BinResult::Int(v) => Ok(Value::from_wide(v)),
                };
            }
            _ => (l_val, r_val),
        };
        match (l_val, r_val) {
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
            Rvalue::Use(op) => {
                if let Operand::Const(cv) = op {
                    Ok(Self::const_to_val_typed(cv, dest_ty, &self.program.types))
                } else {
                    self.eval_operand(op)
                }
            }
            Rvalue::UnaryOp(unop, op) => {
                let val = self.eval_operand(op)?;
                let dst_ty = self
                    .program
                    .types
                    .get(dest_ty.0 as usize)
                    .cloned()
                    .unwrap_or(Type::Int {
                        signed: true,
                        bits: 64,
                    });
                let resolved_dst_ty = match &dst_ty {
                    Type::Pattern { base, .. } => self
                        .program
                        .types
                        .get(base.0 as usize)
                        .cloned()
                        .unwrap_or(dst_ty),
                    _ => dst_ty,
                };
                let (bits, unsigned) = Self::int_width(&resolved_dst_ty);
                match (unop, val) {
                    (UnOp::Neg, Value::Int(n)) => Ok(Value::Int(n.wrapping_neg())),
                    (UnOp::Neg, Value::Float(bits)) => Ok(Value::from_f64(-f64::from_bits(bits))),
                    (UnOp::Not, Value::Int(n)) => Ok(Value::Int(!n)),
                    (UnOp::Not, Value::Bool(b)) => Ok(Value::Bool(!b)),
                    (UnOp::Bswap, Value::Int(n)) => {
                        Ok(Value::Int(Self::bswap_int(n, bits, unsigned)))
                    }
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
                                (UnOp::Bswap, Value::Int(n)) => {
                                    Value::Int(Self::bswap_int(n, bits, unsigned))
                                }
                                (u, v) => {
                                    return Err(format!("Unsupported SIMD unary op {u} on {v:?}"));
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
                let l_val = self.eval_operand(lhs)?;
                let r_val = self.eval_operand(rhs)?;

                if matches!(
                    binop,
                    BinOp::AddChecked | BinOp::SubChecked | BinOp::MulChecked
                ) {
                    let payload_ty_id = match self.program.types.get(dest_ty.0 as usize) {
                        Some(Type::Union { variants, .. }) if variants.len() == 2 => variants[1],
                        _ => dest_ty,
                    };
                    let inferred_ty_id = self
                        .operand_type(func, lhs)?
                        .or(self.operand_type(func, rhs)?)
                        .unwrap_or(payload_ty_id);
                    let raw_ty = self
                        .program
                        .types
                        .get(inferred_ty_id.0 as usize)
                        .cloned()
                        .unwrap_or(Type::Int {
                            signed: true,
                            bits: 64,
                        });
                    let inferred_ty = match &raw_ty {
                        Type::Pattern { base, .. } => self
                            .program
                            .types
                            .get(base.0 as usize)
                            .cloned()
                            .unwrap_or(raw_ty),
                        _ => raw_ty,
                    };
                    let checked_op = match binop {
                        BinOp::AddChecked => BinOp::Add,
                        BinOp::SubChecked => BinOp::Sub,
                        BinOp::MulChecked => BinOp::Mul,
                        _ => unreachable!(),
                    };
                    return match Self::eval_scalar_binop(&inferred_ty, checked_op, l_val, r_val) {
                        Ok(val) => Ok(Value::Union {
                            ty: dest_ty,
                            variant: 1,
                            payload: Box::new(val),
                        }),
                        Err(_) => Ok(Value::Union {
                            ty: dest_ty,
                            variant: 0,
                            payload: Box::new(Value::Void),
                        }),
                    };
                }

                let inferred_ty_id = self
                    .operand_type(func, lhs)?
                    .or(self.operand_type(func, rhs)?)
                    .unwrap_or(dest_ty);
                let raw_ty = self
                    .program
                    .types
                    .get(inferred_ty_id.0 as usize)
                    .cloned()
                    .unwrap_or(Type::Int {
                        signed: true,
                        bits: 64,
                    });
                let inferred_ty = match &raw_ty {
                    Type::Pattern { base, .. } => self
                        .program
                        .types
                        .get(base.0 as usize)
                        .cloned()
                        .unwrap_or(raw_ty),
                    _ => raw_ty,
                };

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
            Rvalue::Transmute(op, target_ty_id)
                if self.operand_type(func, op)?.is_some() =>
            {
                // Bitwise reinterpretation with the compiled layout (see `value_to_bits`).
                let src_ty = self.operand_type(func, op)?.expect("checked above");
                let val = self.eval_operand(op)?;
                let bits = self.value_to_bits(&val, src_ty)?;
                self.bits_to_value(&bits, *target_ty_id)
            }
            Rvalue::Cast(op, target_ty_id) | Rvalue::Transmute(op, target_ty_id) => {
                let val = self.eval_operand(op)?;
                let dst_ty = self
                    .program
                    .types
                    .get(target_ty_id.0 as usize)
                    .ok_or_else(|| format!("Undefined type {target_ty_id}"))?;
                let resolved_dst_ty = match dst_ty {
                    Type::Pattern { base, .. } => {
                        self.program.types.get(base.0 as usize).unwrap_or(dst_ty)
                    }
                    other => other,
                };
                match (val, resolved_dst_ty) {
                    (Value::Int(n), Type::F32 | Type::F64) => Ok(Value::from_f64(n as f64)),
                    (Value::Wide(w), Type::F32 | Type::F64) => {
                        Ok(Value::from_f64(w.to_string().parse::<f64>().unwrap_or(0.0)))
                    }
                    // Saturating float-to-int conversion (NaN converts to 0), as in compiled code.
                    (Value::Float(fbits), Type::Int { signed, bits }) => {
                        let f = f64::from_bits(fbits);
                        let truncated = if f.is_nan() {
                            crate::wide::Wide::ZERO
                        } else {
                            // Exact integer part (beyond `i128` for wide targets); values past
                            // the representable range saturate below.
                            let mag = crate::wide::Wide::from_str_radix(
                                &format!("{:.0}", f.trunc().abs()),
                                10,
                            )
                            .unwrap_or(crate::wide::Wide::max_value(1024, false));
                            if f < 0.0 { mag.neg() } else { mag }
                        };
                        Ok(Value::from_wide(
                            truncated
                                .max(crate::wide::Wide::min_value(*bits, *signed))
                                .min(crate::wide::Wide::max_value(*bits, *signed)),
                        ))
                    }
                    (Value::Float(bits), Type::Rune) => {
                        Ok(Value::Int((f64::from_bits(bits) as u32).into()))
                    }
                    (Value::Float(bits), Type::F32) => {
                        Ok(Value::from_f64(f64::from_bits(bits) as f32 as f64))
                    }
                    (Value::Float(bits), Type::F64) => Ok(Value::Float(bits)),
                    (Value::Bool(b), _) => Ok(Value::Int(i128::from(b))),
                    (Value::Int(n), Type::Bool) => Ok(Value::Bool(n != 0)),
                    (Value::Int(n), Type::Int { signed, bits }) => Ok(Value::from_wide(
                        crate::wide::Wide::from_i128(n).wrap(*bits, *signed),
                    )),
                    (Value::Wide(w), Type::Int { signed, bits }) => {
                        Ok(Value::from_wide(w.wrap(*bits, *signed)))
                    }
                    (Value::Wide(w), Type::Bool) => Ok(Value::Bool(!w.is_zero())),
                    (Value::Int(n), _) => Ok(Value::Int(n)),
                    (
                        Value::Ptr {
                            target,
                            projections,
                        },
                        Type::Ptr { .. },
                    ) => Ok(Value::Ptr {
                        target,
                        projections,
                    }),
                    (Value::Str(s), Type::Ptr { .. }) => Ok(Value::Str(s)),
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
                    Some(Type::Array { elem, .. }) => {
                        for v in &mut vals {
                            if matches!(v, Value::Void) {
                                *v = Self::uninit_value_for_type(self.program, *elem);
                            }
                        }
                        Ok(Value::Array(vals))
                    }
                    Some(Type::Int { bits: 256, .. }) => Ok(Value::Array(vals)),
                    Some(Type::Simd { len, .. }) => {
                        if vals.len() == 1 && *len > 1 {
                            Ok(Value::Array(vec![vals[0].clone(); *len as usize]))
                        } else {
                            Ok(Value::Array(vals))
                        }
                    }
                    Some(Type::Struct(ftys)) => {
                        let ftys = ftys.clone();
                        for (v, fty) in vals.iter_mut().zip(ftys) {
                            if matches!(v, Value::Void) {
                                *v = Self::uninit_value_for_type(self.program, fty);
                            }
                        }
                        Ok(Value::Struct {
                            ty: *agg_ty,
                            fields: vals,
                        })
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
                    return Err(format!(
                        "Cannot read discriminant of non-union value {val:?}"
                    ));
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
                    let as_wide = |v: Value| match v {
                        Value::Int(n) => Some(Wide::from_i128(n)),
                        Value::Wide(w) => Some(*w),
                        _ => None,
                    };
                    let (Some(lo), Some(hi)) = (as_wide(lo_val), as_wide(hi_val)) else {
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
