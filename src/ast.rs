use crate::ir::{BinOp, UnOp};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Visibility {
    Private,
    PubPkg,
    Pub,
}

#[derive(Debug, Clone, PartialEq)]
pub struct ModuleAst {
    pub imports: Vec<ImportDecl>,
    pub items: Vec<Item>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ImportDecl {
    pub vis: Visibility,
    pub path: Vec<String>,
    pub targets: ImportTargets,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ImportTargets {
    /// `import root::math;` (binds `math` module in scope)
    Module(Option<String>),
    /// `import root::math::{Vec, Point as Pt};`
    Items(Vec<(String, Option<String>)>),
    /// `import root::math::*;`
    Glob,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Item {
    Func(FuncDecl),
    ExternFunc(ExternFuncDecl),
    TypeDecl {
        vis: Visibility,
        name: String,
        ty: TypeExpr,
    },
}

#[derive(Debug, Clone, PartialEq)]
pub struct Param {
    pub is_comptime: bool,
    pub is_mut: bool,
    pub name: String,
    pub ty: TypeExpr,
}

#[derive(Debug, Clone, PartialEq)]
pub struct FuncDecl {
    pub vis: Visibility,
    pub name: String,
    pub params: Vec<Param>,
    pub ret_ty: TypeExpr,
    pub body: Block,
}

#[derive(Debug, Clone, PartialEq)]
pub struct ExternFuncDecl {
    pub vis: Visibility,
    pub name: String,
    pub params: Vec<(String, TypeExpr)>,
    pub ret_ty: TypeExpr,
}

#[derive(Debug, Clone, PartialEq)]
pub struct FieldDecl {
    pub vis: Visibility,
    pub name: String,
    pub ty: TypeExpr,
    pub default_val: Option<Expr>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum TypeConstraint {
    AnyType,       // `type` (rank 1)
    Scalar,        // `scalar` (`number` | `bool` | `rune` | `*T`) (rank 2)
    Callable,      // `callable` (`fn` or `closure`) (rank 2)
    Sequence,      // `sequence` (`array` or `slice`) (rank 2)
    Number,        // `number` (`integer` or `float`) (rank 3)
    FnPtr,         // `fn` (function pointer `fn(...) -> R`) (rank 3)
    Closure,       // `closure` (capturing closure) (rank 3)
    Integer,       // `integer` (`signed` or `unsigned`) (rank 4)
    Signed,        // `signed` (`i1`..`i512`, `isize`) (rank 5)
    Unsigned,      // `unsigned` (`u1`..`u512`, `usize`) (rank 5)
    Float,         // `float` (`f32`, `f64`) (rank 4)
    Aggregate,     // `aggregate` (`record` or `tuple`) (rank 2)
    Record,        // `record` (rank 3)
    Tuple,         // `tuple` (rank 3)
    Discriminated, // `discriminated` (`enum` or `union`) (rank 2)
    Enum,          // `enum` (rank 3)
    Union,         // `union` (including `?T`) (rank 3)
    Struct,        // `struct` (rank 3)
    Linear,        // `linear` (`linear struct` or container with linear field) (rank 4)
    Simd,          // `simd` (`simd[T; N]`) (rank 3)
    Array,         // `array` (`[T; N]`) (rank 3)
    Slice,         // `slice` (`&[T]`, `&mut [T]`) (rank 3)
}

impl TypeConstraint {
    pub fn specificity(self) -> u8 {
        match self {
            TypeConstraint::AnyType => 1,
            TypeConstraint::Scalar
            | TypeConstraint::Callable
            | TypeConstraint::Sequence
            | TypeConstraint::Aggregate
            | TypeConstraint::Discriminated => 2,
            TypeConstraint::Number
            | TypeConstraint::FnPtr
            | TypeConstraint::Closure
            | TypeConstraint::Record
            | TypeConstraint::Tuple
            | TypeConstraint::Enum
            | TypeConstraint::Union
            | TypeConstraint::Struct
            | TypeConstraint::Simd
            | TypeConstraint::Array
            | TypeConstraint::Slice => 3,
            TypeConstraint::Linear | TypeConstraint::Integer | TypeConstraint::Float => 4,
            TypeConstraint::Signed | TypeConstraint::Unsigned => 5,
        }
    }

    pub fn name(self) -> &'static str {
        match self {
            TypeConstraint::AnyType => "type",
            TypeConstraint::Scalar => "scalar",
            TypeConstraint::Callable => "callable",
            TypeConstraint::Sequence => "sequence",
            TypeConstraint::Number => "number",
            TypeConstraint::FnPtr => "fn",
            TypeConstraint::Closure => "closure",
            TypeConstraint::Integer => "integer",
            TypeConstraint::Signed => "signed",
            TypeConstraint::Unsigned => "unsigned",
            TypeConstraint::Float => "float",
            TypeConstraint::Aggregate => "aggregate",
            TypeConstraint::Record => "record",
            TypeConstraint::Tuple => "tuple",
            TypeConstraint::Discriminated => "discriminated",
            TypeConstraint::Enum => "enum",
            TypeConstraint::Union => "union",
            TypeConstraint::Struct => "struct",
            TypeConstraint::Linear => "linear",
            TypeConstraint::Simd => "simd",
            TypeConstraint::Array => "array",
            TypeConstraint::Slice => "slice",
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum TypeExpr {
    Void,
    Never,
    Bool,
    Rune,
    F32,
    F64,
    Isize,
    Usize,
    Int {
        signed: bool,
        bits: u16,
    },
    MetaType,
    Constraint(TypeConstraint),
    SelfType,
    Named(Vec<String>),
    TypeCall {
        path: Vec<String>,
        args: Vec<Expr>,
    },
    Ref {
        mutable: bool,
        inner: Box<TypeExpr>,
    },
    Ptr {
        mutable: bool,
        inner: Box<TypeExpr>,
    },
    Optional(Box<TypeExpr>),
    Slice {
        mutable: bool,
        elem: Box<TypeExpr>,
    },
    StrRef,
    RelRef(Box<TypeExpr>),
    RelSlice(Box<TypeExpr>),
    RelStr,
    Array {
        elem: Box<TypeExpr>,
        len: Box<Expr>,
    },
    Simd {
        elem: Box<TypeExpr>,
        len: Box<Expr>,
    },
    Pattern {
        base: Box<TypeExpr>,
        ranges: Vec<(Expr, Expr)>,
    },
    Tuple(Vec<TypeExpr>),
    FnPtr {
        params: Vec<TypeExpr>,
        ret: Box<TypeExpr>,
    },
    Enum(Vec<(String, Option<i128>)>),
    Record {
        fields: Vec<FieldDecl>,
        methods: Vec<FuncDecl>,
    },
    Struct {
        is_linear: bool,
        fields: Vec<FieldDecl>,
        methods: Vec<FuncDecl>,
        default_hook: Option<Block>,
        clone_hook: Option<(String, Block)>,
        drop_hook: Option<(String, Block)>,
    },
}

impl TypeExpr {
    pub fn as_type_constraint(&self) -> Option<TypeConstraint> {
        match self {
            TypeExpr::MetaType => Some(TypeConstraint::AnyType),
            TypeExpr::Constraint(c) => Some(*c),
            _ => None,
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Block {
    pub stmts: Vec<Stmt>,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Stmt {
    Let {
        mutable: bool,
        name: String,
        ty: Option<TypeExpr>,
        init: Expr,
    },
    Assign {
        target: Expr,
        op: Option<BinOp>,
        value: Expr,
    },
    If {
        cond: Expr,
        then_block: Block,
        else_block: Option<Block>,
    },
    IfLet {
        var_name: String,
        opt_expr: Expr,
        then_block: Block,
        else_block: Option<Block>,
    },
    While {
        cond: Expr,
        body: Block,
    },
    Return(Option<Expr>),
    Unsafe(Block),
    Expr(Expr),
}

#[derive(Debug, Clone, PartialEq)]
pub enum Expr {
    Int(i128),
    Float(u64),
    Bool(bool),
    Rune(char),
    Str(String),
    Null,
    TypeVal(TypeExpr),
    Path(Vec<String>),
    Move(Box<Expr>),
    Unary {
        op: UnOp,
        expr: Box<Expr>,
    },
    Ref {
        mutable: bool,
        expr: Box<Expr>,
    },
    RelRef(Box<Expr>),
    Deref(Box<Expr>),
    Binary {
        op: BinOp,
        lhs: Box<Expr>,
        rhs: Box<Expr>,
    },
    LogicalAnd(Box<Expr>, Box<Expr>),
    LogicalOr(Box<Expr>, Box<Expr>),
    Cast {
        expr: Box<Expr>,
        ty: TypeExpr,
    },
    OrElse {
        opt: Box<Expr>,
        fallback: Box<Expr>,
    },
    Field {
        base: Box<Expr>,
        field: String,
    },
    TupleIndex {
        base: Box<Expr>,
        index: u32,
    },
    Index {
        base: Box<Expr>,
        index: Box<Expr>,
    },
    Slice {
        base: Box<Expr>,
        start: Box<Expr>,
        end: Box<Expr>,
    },
    Call {
        callee: Box<Expr>,
        args: Vec<Expr>,
    },
    MethodCall {
        receiver: Box<Expr>,
        method: String,
        args: Vec<Expr>,
    },
    TupleLit(Vec<Expr>),
    SimdLit {
        ty: TypeExpr,
        elems: Vec<Expr>,
    },
    StructLit {
        ty: TypeExpr,
        fields: Vec<(String, Expr)>,
    },
    IntrinsicDefault(TypeExpr),
    IntrinsicClone(Box<Expr>),
    IntrinsicDrop(Box<Expr>),
    IntrinsicTrap,
    Return(Option<Box<Expr>>),
    Lambda {
        is_move: bool,
        params: Vec<(bool, String, TypeExpr)>,
        ret_ty: TypeExpr,
        body: Block,
    },
    UnsafeBlock(Block),
}

