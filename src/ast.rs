use crate::ir::{BinOp, UnOp};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Visibility {
    Private,
    PubPkg,
    Pub,
    Export,
}

impl Visibility {
    pub fn is_public_or_export(self) -> bool {
        matches!(self, Visibility::Pub | Visibility::Export)
    }

    pub fn is_export(self) -> bool {
        matches!(self, Visibility::Export)
    }
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
    pub is_prelude: bool,
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
    Static(StaticDecl),
    Const(ConstDecl),
    Impl(ImplDecl),
}

/// A module-level trait implementation: `impl Tr for T { ... }` or the generic form
/// `impl(comptime T: Bound) Tr for Pair(T) { ... }`.
#[derive(Debug, Clone, PartialEq)]
pub struct ImplDecl {
    pub comptime_params: Vec<Param>,
    pub trait_expr: TypeExpr,
    pub for_ty: TypeExpr,
    pub methods: Vec<FuncDecl>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct StaticDecl {
    pub vis: Visibility,
    pub mutable: bool,
    pub name: String,
    pub ty: TypeExpr,
    pub init: Expr,
}

#[derive(Debug, Clone, PartialEq)]
pub struct ConstDecl {
    pub vis: Visibility,
    pub name: String,
    pub ty: Option<TypeExpr>,
    pub init: Expr,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Param {
    pub is_comptime: bool,
    pub is_mut: bool,
    pub name: String,
    pub ty: TypeExpr,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum BorrowContractItem {
    /// Return value borrows from parameter `param` (`borrows(a, b)`).
    Return(String),
    /// Mutable parameter `dst` borrows from parameter `src` (`borrows(dst: src)`).
    ParamFlow { dst: String, src: String },
}

#[derive(Debug, Clone, PartialEq)]
pub struct FuncDecl {
    pub vis: Visibility,
    pub name: String,
    pub params: Vec<Param>,
    pub ret_ty: TypeExpr,
    pub borrows: Option<Vec<BorrowContractItem>>,
    pub where_clauses: Vec<WherePredicate>,
    pub body: Block,
    /// For a method declared inside an `impl Tr { ... }` block within a type's own body: the
    /// trait `Tr` it implements. Such methods are not inherent methods of the type.
    pub impl_of: Option<TypeExpr>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct TraitMethodDecl {
    pub name: String,
    pub params: Vec<Param>,
    pub ret_ty: TypeExpr,
    pub borrows: Option<Vec<BorrowContractItem>>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct WherePredicate {
    pub type_param: String,
    pub negated: bool,
    pub constraint: TypeConstraint,
}

#[derive(Debug, Clone, PartialEq)]
pub struct CloneHookDecl {
    pub self_name: String,
    pub where_clauses: Vec<WherePredicate>,
    pub body: Block,
}

#[derive(Debug, Clone, PartialEq)]
pub struct DropHookDecl {
    pub self_name: String,
    pub where_clauses: Vec<WherePredicate>,
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
pub enum StructOwnership {
    Copy,
    Affine,
    Linear,
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
    Aggregate,     // `aggregate` (`struct` or `tuple`) (rank 2)
    Record,        // `struct` (transparent product type) (rank 3)
    Tuple,         // `tuple` (rank 3)
    Discriminated, // `discriminated` (`enum`, `union`, or `error`) (rank 2)
    Enum,          // `enum` (rank 3)
    Union,         // `union` (including `?T` and `E!T`) (rank 3)
    Overlay,       // `overlay` (untagged union `overlay { ... }` or `uninit T`) (rank 3)
    Error,         // `error` (`error { ... }` or `E1 || E2`) (rank 3)
    Struct,        // `opaque` (encapsulated product type) (rank 3)
    Copy,          // `copy` (`opaque(copy)` or copyable transparent/scalar type) (rank 4)
    Affine,        // `affine` (`opaque(affine)` / `opaque` or move-only non-linear type) (rank 4)
    Linear,        // `linear` (`opaque(linear)` or container with linear field) (rank 4)
    Simd,          // `simd` (`simd[T; N]`) (rank 3)
    Array,         // `array` (`[T; N]`) (rank 3)
    Slice,         // `slice` (`&[T]`, `&mut [T]`) (rank 3)
    Send,          // `send` (safe to transfer across threads) (rank 2)
    Sync,          // `sync` (safe to share `&T` across threads) (rank 2)
    Format,        // `format` (transparent type or struct with `format` hook) (rank 2)
    Clone,         // `clone` (copyable type or struct/record supporting `@clone`) (rank 2)
    Default,       // `default` (type supporting `@default(T)`) (rank 2)
    Module,        // `module` (first-class comptime module value) (rank 2)
}

impl TypeConstraint {
    pub fn specificity(self) -> u8 {
        match self {
            TypeConstraint::AnyType => 1,
            TypeConstraint::Scalar
            | TypeConstraint::Callable
            | TypeConstraint::Sequence
            | TypeConstraint::Aggregate
            | TypeConstraint::Discriminated
            | TypeConstraint::Send
            | TypeConstraint::Sync
            | TypeConstraint::Format
            | TypeConstraint::Clone
            | TypeConstraint::Default
            | TypeConstraint::Module => 2,
            TypeConstraint::Number
            | TypeConstraint::FnPtr
            | TypeConstraint::Closure
            | TypeConstraint::Record
            | TypeConstraint::Tuple
            | TypeConstraint::Enum
            | TypeConstraint::Union
            | TypeConstraint::Overlay
            | TypeConstraint::Error
            | TypeConstraint::Struct
            | TypeConstraint::Simd
            | TypeConstraint::Array
            | TypeConstraint::Slice => 3,
            TypeConstraint::Copy
            | TypeConstraint::Affine
            | TypeConstraint::Linear
            | TypeConstraint::Integer
            | TypeConstraint::Float => 4,
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
            TypeConstraint::Record => "struct",
            TypeConstraint::Tuple => "tuple",
            TypeConstraint::Discriminated => "discriminated",
            TypeConstraint::Enum => "enum",
            TypeConstraint::Union => "union",
            TypeConstraint::Overlay => "overlay",
            TypeConstraint::Error => "error",
            TypeConstraint::Struct => "opaque",
            TypeConstraint::Copy => "copy",
            TypeConstraint::Affine => "affine",
            TypeConstraint::Linear => "linear",
            TypeConstraint::Simd => "simd",
            TypeConstraint::Array => "array",
            TypeConstraint::Slice => "slice",
            TypeConstraint::Send => "send",
            TypeConstraint::Sync => "sync",
            TypeConstraint::Format => "format",
            TypeConstraint::Clone => "clone",
            TypeConstraint::Default => "default",
            TypeConstraint::Module => "module",
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum CIntKind {
    CChar,
    CSChar,
    CUChar,
    CShort,
    CUShort,
    CInt,
    CUInt,
    CLong,
    CULong,
    CLongLong,
    CULongLong,
}

impl CIntKind {
    pub fn from_ident(s: &str) -> Option<Self> {
        match s {
            "c_char" => Some(Self::CChar),
            "c_schar" => Some(Self::CSChar),
            "c_uchar" => Some(Self::CUChar),
            "c_short" => Some(Self::CShort),
            "c_ushort" => Some(Self::CUShort),
            "c_int" => Some(Self::CInt),
            "c_uint" => Some(Self::CUInt),
            "c_long" => Some(Self::CLong),
            "c_ulong" => Some(Self::CULong),
            "c_longlong" => Some(Self::CLongLong),
            "c_ulonglong" => Some(Self::CULongLong),
            _ => None,
        }
    }

    pub fn name(self) -> &'static str {
        match self {
            Self::CChar => "c_char",
            Self::CSChar => "c_schar",
            Self::CUChar => "c_uchar",
            Self::CShort => "c_short",
            Self::CUShort => "c_ushort",
            Self::CInt => "c_int",
            Self::CUInt => "c_uint",
            Self::CLong => "c_long",
            Self::CULong => "c_ulong",
            Self::CLongLong => "c_longlong",
            Self::CULongLong => "c_ulonglong",
        }
    }

    pub fn c_header_name(self) -> &'static str {
        match self {
            Self::CChar => "char",
            Self::CSChar => "signed char",
            Self::CUChar => "unsigned char",
            Self::CShort => "short",
            Self::CUShort => "unsigned short",
            Self::CInt => "int",
            Self::CUInt => "unsigned int",
            Self::CLong => "long",
            Self::CULong => "unsigned long",
            Self::CLongLong => "long long",
            Self::CULongLong => "unsigned long long",
        }
    }

    pub fn signed_and_bits(self) -> (bool, u16) {
        match self {
            Self::CChar | Self::CSChar => (true, 8),
            Self::CUChar => (false, 8),
            Self::CShort => (true, 16),
            Self::CUShort => (false, 16),
            Self::CInt => (true, 32),
            Self::CUInt => (false, 32),
            Self::CLong | Self::CLongLong => (true, 64),
            Self::CULong | Self::CULongLong => (false, 64),
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum TypeExpr {
    Void,
    Opaque,
    OpaqueDef {
        methods: Vec<FuncDecl>,
    },
    OpaqueNewtype {
        underlying: Box<TypeExpr>,
        methods: Vec<FuncDecl>,
    },
    OpaqueTrait(Box<TypeExpr>),
    Never,
    Bool,
    Rune,
    F32,
    F64,
    Isize,
    Usize,
    CInt(CIntKind),
    Int {
        signed: bool,
        bits: u16,
    },
    ComputedInt {
        signed: Box<Expr>,
        bits: Box<Expr>,
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
    Uninit(Box<TypeExpr>),
    Overlay(Vec<(String, TypeExpr)>),
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
    Map {
        key: Box<TypeExpr>,
        val: Box<TypeExpr>,
    },
    TypeIndex {
        path: Vec<String>,
        index: Box<Expr>,
    },
    Pattern {
        base: Box<TypeExpr>,
        ranges: Vec<(Expr, Expr)>,
    },
    Tuple(Vec<TypeExpr>),
    FnPtr {
        params: Vec<TypeExpr>,
        ret: Box<TypeExpr>,
        /// Positional borrow contract (`borrows(_2)`, `borrows(_1: _2)`); `None` uses elision.
        borrows: Option<Vec<BorrowContractItem>>,
    },
    Enum {
        backing: Option<Box<TypeExpr>>,
        variants: Vec<(String, Option<i128>)>,
    },
    Union(Vec<(String, Option<TypeExpr>)>),
    Error(Vec<(String, Option<TypeExpr>)>),
    ErrorSetUnion(Vec<TypeExpr>),
    Result {
        err: Box<TypeExpr>,
        ok: Box<TypeExpr>,
    },
    Record {
        is_packed: bool,
        fields: Vec<FieldDecl>,
        methods: Vec<FuncDecl>,
    },
    Struct {
        is_packed: bool,
        ownership: StructOwnership,
        is_sync: bool,
        /// `comptime` type parameters owned by this `opaque` (`opaque(owns T)`); an instantiation
        /// is linear if any owned type argument is linear.
        owns: Vec<String>,
        fields: Vec<FieldDecl>,
        consts: Vec<ConstDecl>,
        statics: Vec<StaticDecl>,
        methods: Vec<FuncDecl>,
        default_hook: Option<Block>,
        clone_hooks: Vec<CloneHookDecl>,
        drop_hooks: Vec<DropHookDecl>,
        format_hook: Option<(String, String, Option<String>, Block)>,
    },
    Trait(Vec<TraitMethodDecl>),
    TraitBounds(Vec<TypeExpr>),
}

#[derive(Debug, Clone, PartialEq)]
pub enum MatchPat {
    Wildcard,
    Int(i128),
    CatchAllBind {
        is_move: bool,
        name: String,
    },
    Variant {
        path: Vec<String>,
        binding: Option<(bool, String)>,
    },
}

#[derive(Debug, Clone, PartialEq)]
pub enum FmtSegment {
    Lit(String),
    Interp { expr: Expr, spec: String },
}

impl TypeExpr {
    pub fn as_type_constraint(&self) -> Option<TypeConstraint> {
        match self {
            TypeExpr::MetaType => Some(TypeConstraint::AnyType),
            TypeExpr::Opaque => Some(TypeConstraint::Struct),
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
    Match {
        scrutinee: Expr,
        arms: Vec<(MatchPat, Expr)>,
    },
    Return(Option<Expr>),
    Unsafe(Block),
    Expr(Expr),
}

#[derive(Debug, Clone, PartialEq)]
pub enum SelectOp {
    Recv { bind: Option<String>, source: Expr },
    /// `ch.send(value) [else |unsent| handler]`: when another arm wins, `handler` receives the
    /// unsent value; without a handler the unsent value is dropped (rejected if it is linear).
    Send {
        channel: Expr,
        value: Expr,
        unsent: Option<(String, Box<Expr>)>,
    },
    Default,
}

#[derive(Debug, Clone, PartialEq)]
pub struct SelectArm {
    pub op: SelectOp,
    pub body: Expr,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Expr {
    Int(i128),
    Float(u64),
    Bool(bool),
    Rune(char),
    Str(String),
    Null,
    Uninit(Option<Box<Expr>>),
    TypeVal(TypeExpr),
    Path(Vec<String>),
    Move(Box<Expr>),
    Try(Box<Expr>),
    Unary {
        op: UnOp,
        expr: Box<Expr>,
    },
    Ref {
        mutable: bool,
        expr: Box<Expr>,
    },
    RawPtr {
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
    Catch {
        expr: Box<Expr>,
        err_binding: Option<String>,
        fallback: Box<Expr>,
    },
    Match {
        scrutinee: Box<Expr>,
        arms: Vec<(MatchPat, Expr)>,
    },
    Select {
        arms: Vec<SelectArm>,
    },
    If {
        cond: Box<Expr>,
        then_block: Block,
        else_block: Option<Block>,
    },
    Block(Block),
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
    SliceLit {
        mutable: bool,
        elems: Vec<Expr>,
    },
    MapLit(Vec<(Expr, Expr)>),
    SimdLit {
        ty: TypeExpr,
        elems: Vec<Expr>,
    },
    StructLit {
        ty: TypeExpr,
        fields: Vec<(String, Expr)>,
    },
    IntrinsicInvert(Box<Expr>),
    IntrinsicDeclarations(Box<Expr>),
    IntrinsicAlloc {
        ty: TypeExpr,
        len: Box<Expr>,
    },
    IntrinsicRealloc {
        ty: TypeExpr,
        ptr: Box<Expr>,
        len: Box<Expr>,
    },
    IntrinsicDealloc(Box<Expr>),
    IntrinsicMemcpy {
        dest: Box<Expr>,
        src: Box<Expr>,
        len: Box<Expr>,
    },
    IntrinsicMemmove {
        dest: Box<Expr>,
        src: Box<Expr>,
        len: Box<Expr>,
    },
    IntrinsicTransmute {
        dst_ty: TypeExpr,
        src: Box<Expr>,
    },
    IntrinsicBswap(Box<Expr>),
    IntrinsicArithUnchecked {
        op: BinOp,
        lhs: Box<Expr>,
        rhs: Box<Expr>,
    },
    IntrinsicForget(Box<Expr>),
    /// `@c_abi(f)`: pointer to the C-ABI wrapper of `export fn f`, for handing to C as a callback.
    IntrinsicCAbi(Box<Expr>),
    IntrinsicDefault(TypeExpr),
    IntrinsicClone(Box<Expr>),
    IntrinsicDrop(Box<Expr>),
    IntrinsicFormat {
        formatter: Box<Expr>,
        value: Box<Expr>,
        spec: Option<String>,
    },
    IntrinsicTrap,
    FormatStr(Vec<FmtSegment>),
    Return(Option<Box<Expr>>),
    Lambda {
        is_move: bool,
        params: Vec<(bool, String, TypeExpr)>,
        ret_ty: TypeExpr,
        body: Block,
    },
    UnsafeBlock(Block),
}
