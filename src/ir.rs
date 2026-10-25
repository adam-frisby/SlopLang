use std::fmt;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct TypeId(pub u32);

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct LocalId(pub u32);

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct BlockId(pub u32);

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct FuncId(pub u32);

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct GlobalId(pub u32);

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Type {
    Void,
    Bool,
    Rune,
    I8,
    I16,
    I32,
    I64,
    I128,
    U8,
    U16,
    U32,
    U64,
    U128,
    F32,
    F64,
    MetaType,
    Pattern {
        base: TypeId,
        ranges: Vec<(i128, i128)>,
    },
    Ptr { mutable: bool, pointee: TypeId },
    Array { elem: TypeId, len: u64 },
    Struct(Vec<TypeId>),
    Overlay(Vec<TypeId>),
    Union { tag: TypeId, variants: Vec<TypeId> },
    FnPtr { args: Vec<TypeId>, ret: TypeId },
}

impl Type {
    pub fn is_unsigned(&self) -> bool {
        matches!(
            self,
            Type::Rune | Type::U8 | Type::U16 | Type::U32 | Type::U64 | Type::U128
        )
    }

    pub fn is_float(&self) -> bool {
        matches!(self, Type::F32 | Type::F64)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Projection {
    Deref,
    Field(u32),
    Variant(u32),
    Index(LocalId),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Place {
    pub local: LocalId,
    pub projections: Vec<Projection>,
}

impl Place {
    pub fn new(local: LocalId) -> Self {
        Self {
            local,
            projections: Vec::new(),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ConstValue {
    Void,
    Bool(bool),
    I64(i128),
    F64(u64), // IEEE 754 bits for Eq/Hash
    Type(TypeId),
    Func(FuncId),
    Global(GlobalId),
    Str(String),
}

impl ConstValue {
    pub fn f64_from_val(v: f64) -> Self {
        Self::F64(v.to_bits())
    }

    pub fn as_f64(&self) -> Option<f64> {
        if let Self::F64(bits) = self {
            Some(f64::from_bits(*bits))
        } else {
            None
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Operand {
    Copy(Place),
    Move(Place),
    Const(ConstValue),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UnOp {
    Neg,
    Not,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinOp {
    Add,
    Sub,
    Mul,
    AddWrap,
    SubWrap,
    MulWrap,
    AddSat,
    SubSat,
    MulSat,
    AddUnchecked,
    SubUnchecked,
    MulUnchecked,
    Div,
    Rem,
    BitAnd,
    BitOr,
    BitXor,
    Shl,
    Shr,
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Rvalue {
    Use(Operand),
    UnaryOp(UnOp, Operand),
    BinaryOp(BinOp, Operand, Operand),
    Cast(Operand, TypeId),
    Ref {
        mutable: bool,
        place: Place,
    },
    Aggregate(TypeId, Vec<Operand>),
    Union {
        ty: TypeId,
        variant: u32,
        payload: Operand,
    },
    Discriminant(Place),
    /// Comptime array type constructor: `[<elem>; <len>]`
    ArrayType {
        elem: Operand,
        len: Operand,
    },
    /// Comptime untagged overlay type constructor: `overlay(<op0>, <op1>, ...)`
    OverlayType(Vec<Operand>),
    /// Comptime tagged union type constructor: `union(<tag>, <v0>, <v1>, ...)`
    UnionType {
        tag: Operand,
        variants: Vec<Operand>,
    },
    /// Comptime scalar pattern type constructor: `<base> in <lo>..=<hi> | ...`
    PatternType {
        base: Operand,
        ranges: Vec<(Operand, Operand)>,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Statement {
    Assign(Place, Rvalue),
    SetDiscriminant(Place, u32),
    StorageLive(LocalId),
    StorageDead(LocalId),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Terminator {
    Goto {
        target: BlockId,
    },
    SwitchInt {
        discr: Operand,
        targets: Vec<(i128, BlockId)>,
        otherwise: BlockId,
    },
    Call {
        func: Operand,
        args: Vec<Operand>,
        destination: Place,
        target: BlockId,
    },
    Drop {
        place: Place,
        target: BlockId,
    },
    Return,
    Unreachable,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BasicBlock {
    pub statements: Vec<Statement>,
    pub terminator: Terminator,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ExternFunc {
    pub id: FuncId,
    pub args: Vec<TypeId>,
    pub ret: TypeId,
    pub symbol: String,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Function {
    pub id: FuncId,
    pub export: Option<String>,
    pub arg_count: usize,
    /// Optional explicit borrow contract for the return value `_0`:
    /// - `None`: infer which parameter locals (`_1..=arg_count`) `_0` borrows from.
    /// - `Some(params)`: enforce that `_0` only borrows from the listed parameter locals.
    pub ret_borrows: Option<Vec<LocalId>>,
    pub locals: Vec<TypeId>, // Indexed by LocalId: _0 is return, _1..=arg_count are args
    pub blocks: Vec<BasicBlock>, // Indexed by BlockId: bb0, bb1, ...
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Global {
    pub id: GlobalId,
    pub mutable: bool,
    pub ty: TypeId,
    pub init: ConstValue,
}

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct Program {
    pub types: Vec<Type>,
    pub destructors: Vec<(TypeId, FuncId)>,
    pub globals: Vec<Global>,
    pub externs: Vec<ExternFunc>,
    pub functions: Vec<Function>,
}

impl Program {
    pub fn intern_type(&mut self, ty: Type) -> TypeId {
        if let Some(idx) = self.types.iter().position(|t| *t == ty) {
            TypeId(idx as u32)
        } else {
            let id = TypeId(self.types.len() as u32);
            self.types.push(ty);
            id
        }
    }
}

impl fmt::Display for TypeId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "ty{}", self.0)
    }
}

impl fmt::Display for LocalId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "_{}", self.0)
    }
}

impl fmt::Display for BlockId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "bb{}", self.0)
    }
}

impl fmt::Display for FuncId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "fn{}", self.0)
    }
}

impl fmt::Display for GlobalId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "gl{}", self.0)
    }
}

impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Type::Void => write!(f, "void"),
            Type::Bool => write!(f, "bool"),
            Type::Rune => write!(f, "rune"),
            Type::I8 => write!(f, "i8"),
            Type::I16 => write!(f, "i16"),
            Type::I32 => write!(f, "i32"),
            Type::I64 => write!(f, "i64"),
            Type::I128 => write!(f, "i128"),
            Type::U8 => write!(f, "u8"),
            Type::U16 => write!(f, "u16"),
            Type::U32 => write!(f, "u32"),
            Type::U64 => write!(f, "u64"),
            Type::U128 => write!(f, "u128"),
            Type::F32 => write!(f, "f32"),
            Type::F64 => write!(f, "f64"),
            Type::MetaType => write!(f, "type"),
            Type::Pattern { base, ranges } => {
                write!(f, "{base} in ")?;
                for (i, (lo, hi)) in ranges.iter().enumerate() {
                    if i > 0 {
                        write!(f, " | ")?;
                    }
                    write!(f, "{lo}..={hi}")?;
                }
                Ok(())
            }
            Type::Ptr {
                mutable: false,
                pointee,
            } => write!(f, "&{pointee}"),
            Type::Ptr {
                mutable: true,
                pointee,
            } => write!(f, "&mut {pointee}"),
            Type::Array { elem, len } => write!(f, "[{elem}; {len}]"),
            Type::Struct(fields) => {
                write!(f, "{{ ")?;
                for (i, ty) in fields.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{ty}")?;
                }
                write!(f, " }}")
            }
            Type::Overlay(fields) => {
                write!(f, "overlay {{ ")?;
                for (i, ty) in fields.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{ty}")?;
                }
                write!(f, " }}")
            }
            Type::Union { tag, variants } => {
                write!(f, "union {tag} {{ ")?;
                for (i, ty) in variants.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{ty}")?;
                }
                write!(f, " }}")
            }
            Type::FnPtr { args, ret } => {
                write!(f, "fn(")?;
                for (i, ty) in args.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{ty}")?;
                }
                write!(f, ") -> {ret}")
            }
        }
    }
}

impl fmt::Display for Place {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut s = format!("{}", self.local);
        for proj in &self.projections {
            match proj {
                Projection::Deref => s = format!("(*{s})"),
                Projection::Field(idx) => s = format!("{s}.{idx}"),
                Projection::Variant(idx) => s = format!("{s}.v{idx}"),
                Projection::Index(idx) => s = format!("{s}[{idx}]"),
            }
        }
        write!(f, "{s}")
    }
}

impl fmt::Display for ConstValue {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ConstValue::Void => write!(f, "void"),
            ConstValue::Bool(b) => write!(f, "{b}"),
            ConstValue::I64(n) => write!(f, "{n}"),
            ConstValue::F64(bits) => {
                let val = f64::from_bits(*bits);
                if val.fract() == 0.0 {
                    write!(f, "{val:.1}")
                } else {
                    write!(f, "{val}")
                }
            }
            ConstValue::Type(id) => write!(f, "{id}"),
            ConstValue::Func(id) => write!(f, "{id}"),
            ConstValue::Global(id) => write!(f, "{id}"),
            ConstValue::Str(s) => write!(f, "{s:?}"),
        }
    }
}

impl fmt::Display for Operand {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Operand::Copy(p) => write!(f, "copy {p}"),
            Operand::Move(p) => write!(f, "move {p}"),
            Operand::Const(c) => write!(f, "const {c}"),
        }
    }
}

impl fmt::Display for UnOp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let name = match self {
            UnOp::Neg => "neg",
            UnOp::Not => "not",
        };
        write!(f, "{name}")
    }
}

impl fmt::Display for BinOp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let name = match self {
            BinOp::Add => "add",
            BinOp::Sub => "sub",
            BinOp::Mul => "mul",
            BinOp::AddWrap => "add_wrap",
            BinOp::SubWrap => "sub_wrap",
            BinOp::MulWrap => "mul_wrap",
            BinOp::AddSat => "add_sat",
            BinOp::SubSat => "sub_sat",
            BinOp::MulSat => "mul_sat",
            BinOp::AddUnchecked => "add_unchecked",
            BinOp::SubUnchecked => "sub_unchecked",
            BinOp::MulUnchecked => "mul_unchecked",
            BinOp::Div => "div",
            BinOp::Rem => "rem",
            BinOp::BitAnd => "bitand",
            BinOp::BitOr => "bitor",
            BinOp::BitXor => "bitxor",
            BinOp::Shl => "shl",
            BinOp::Shr => "shr",
            BinOp::Eq => "eq",
            BinOp::Ne => "ne",
            BinOp::Lt => "lt",
            BinOp::Le => "le",
            BinOp::Gt => "gt",
            BinOp::Ge => "ge",
        };
        write!(f, "{name}")
    }
}

impl fmt::Display for Rvalue {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Rvalue::Use(op) => write!(f, "{op}"),
            Rvalue::UnaryOp(op, val) => write!(f, "{op}({val})"),
            Rvalue::BinaryOp(op, lhs, rhs) => write!(f, "{op}({lhs}, {rhs})"),
            Rvalue::Cast(op, ty) => write!(f, "cast({op}, {ty})"),
            Rvalue::Ref {
                mutable: false,
                place,
            } => write!(f, "&{place}"),
            Rvalue::Ref {
                mutable: true,
                place,
            } => write!(f, "&mut {place}"),
            Rvalue::Aggregate(ty, ops) => {
                write!(f, "aggregate {ty}(")?;
                for (i, op) in ops.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{op}")?;
                }
                write!(f, ")")
            }
            Rvalue::Union {
                ty,
                variant,
                payload,
            } => {
                write!(f, "union {ty}(v{variant}, {payload})")
            }
            Rvalue::Discriminant(place) => write!(f, "discriminant({place})"),
            Rvalue::ArrayType { elem, len } => write!(f, "[{elem}; {len}]"),
            Rvalue::OverlayType(ops) => {
                write!(f, "overlay(")?;
                for (i, op) in ops.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{op}")?;
                }
                write!(f, ")")
            }
            Rvalue::UnionType { tag, variants } => {
                write!(f, "union({tag}")?;
                for op in variants {
                    write!(f, ", {op}")?;
                }
                write!(f, ")")
            }
            Rvalue::PatternType { base, ranges } => {
                write!(f, "{base} in ")?;
                for (i, (lo, hi)) in ranges.iter().enumerate() {
                    if i > 0 {
                        write!(f, " | ")?;
                    }
                    write!(f, "{lo}..={hi}")?;
                }
                Ok(())
            }
        }
    }
}

impl fmt::Display for Statement {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Statement::Assign(place, rval) => write!(f, "{place} = {rval};"),
            Statement::SetDiscriminant(place, variant) => {
                write!(f, "discriminant({place}) = v{variant};")
            }
            Statement::StorageLive(local) => write!(f, "StorageLive({local});"),
            Statement::StorageDead(local) => write!(f, "StorageDead({local});"),
        }
    }
}

impl fmt::Display for Terminator {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Terminator::Goto { target } => write!(f, "goto -> {target};"),
            Terminator::SwitchInt {
                discr,
                targets,
                otherwise,
            } => {
                write!(f, "switchInt({discr}) -> [")?;
                for (val, blk) in targets {
                    write!(f, "{val}: {blk}, ")?;
                }
                write!(f, "otherwise: {otherwise}];")
            }
            Terminator::Call {
                func,
                args,
                destination,
                target,
            } => {
                write!(f, "{destination} = call {func}(")?;
                for (i, arg) in args.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{arg}")?;
                }
                write!(f, ") -> {target};")
            }
            Terminator::Drop { place, target } => write!(f, "drop({place}) -> {target};"),
            Terminator::Return => write!(f, "return;"),
            Terminator::Unreachable => write!(f, "unreachable;"),
        }
    }
}

impl fmt::Display for Global {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.mutable {
            write!(f, "global mut {}: {} = const {};", self.id, self.ty, self.init)
        } else {
            write!(f, "global {}: {} = const {};", self.id, self.ty, self.init)
        }
    }
}

impl fmt::Display for ExternFunc {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "extern {}(", self.id)?;
        for (i, arg) in self.args.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            write!(f, "{arg}")?;
        }
        write!(f, ") -> {} = {:?};", self.ret, self.symbol)
    }
}

impl fmt::Display for Function {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.id)?;
        if self.arg_count > 0 {
            write!(f, "({})", self.arg_count)?;
        }
        if let Some(params) = &self.ret_borrows {
            write!(f, " borrows(")?;
            for (i, p) in params.iter().enumerate() {
                if i > 0 {
                    write!(f, ", ")?;
                }
                write!(f, "{p}")?;
            }
            write!(f, ")")?;
        }
        if let Some(sym) = &self.export {
            write!(f, " = {sym:?}")?;
        }
        writeln!(f, " {{")?;
        for (i, ty) in self.locals.iter().enumerate() {
            writeln!(f, "    let _{i}: {ty};")?;
        }
        for (i, blk) in self.blocks.iter().enumerate() {
            writeln!(f, "    bb{i}: {{")?;
            for stmt in &blk.statements {
                writeln!(f, "        {stmt}")?;
            }
            writeln!(f, "        {}", blk.terminator)?;
            writeln!(f, "    }}")?;
        }
        write!(f, "}}")
    }
}

impl fmt::Display for Program {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for (i, ty) in self.types.iter().enumerate() {
            writeln!(f, "ty{i} = {ty};")?;
        }
        if !self.types.is_empty()
            && (!self.destructors.is_empty()
                || !self.globals.is_empty()
                || !self.externs.is_empty()
                || !self.functions.is_empty())
        {
            writeln!(f)?;
        }
        for (ty_id, fn_id) in &self.destructors {
            writeln!(f, "drop {ty_id} = {fn_id};")?;
        }
        if !self.destructors.is_empty()
            && (!self.globals.is_empty()
                || !self.externs.is_empty()
                || !self.functions.is_empty())
        {
            writeln!(f)?;
        }
        for gl in &self.globals {
            writeln!(f, "{gl}")?;
        }
        if !self.globals.is_empty() && (!self.externs.is_empty() || !self.functions.is_empty()) {
            writeln!(f)?;
        }
        for ext in &self.externs {
            writeln!(f, "{ext}")?;
        }
        if !self.externs.is_empty() && !self.functions.is_empty() {
            writeln!(f)?;
        }
        for (i, func) in self.functions.iter().enumerate() {
            if i > 0 {
                writeln!(f)?;
            }
            writeln!(f, "{func}")?;
        }
        Ok(())
    }
}
