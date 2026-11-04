use crate::ir::{BinOp, Pos, UnOp};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Visibility {
    /// Visible inside the declaring block (a method or field of a type) or module (an item).
    Private,
    /// `pub(mod)`: a method visible to its whole defining module.
    PubMod,
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
    /// `type Name = T` (a new nominal type: `T` is a struct, opaque, enum, union, error, or
    /// overlay declaration) or, with `alias`, `alias Name = T` (another name for `T`).
    TypeDecl {
        vis: Visibility,
        name: String,
        ty: TypeExpr,
        alias: bool,
    },
    Static(StaticDecl),
    Const(ConstDecl),
    Impl(ImplDecl),
}

/// A module-level trait implementation: `impl Tr for T { ... }` or the generic form
/// `impl[T: Bound] Tr for Pair[T] { ... }`.
#[derive(Debug, Clone, PartialEq)]
pub struct ImplDecl {
    /// `unsafe impl`, as a trait declared `unsafe trait` requires.
    pub is_unsafe: bool,
    pub comptime_params: Vec<Param>,
    pub trait_expr: TypeExpr,
    pub for_ty: TypeExpr,
    pub methods: Vec<FuncDecl>,
    /// `const Name: T = value;`: what the impl gives for the trait's associated items.
    pub consts: Vec<ConstDecl>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct StaticDecl {
    pub vis: Visibility,
    /// `thread_local static mut`: each thread has its own copy, starting at `init`.
    pub thread_local: bool,
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
    /// In a type or an impl: a compile-time field, known by its name inside its type.
    pub field: bool,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Param {
    pub is_comptime: bool,
    pub is_mut: bool,
    pub name: String,
    pub ty: TypeExpr,
    /// The default of a comptime parameter (`[S: Hasher = Fnv]`).
    pub default: Option<Expr>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum BorrowContractItem {
    /// Return value borrows from parameter `name` (`borrows(a, b)`), or, with `contents`, only
    /// what the value `name` refers to holds (`borrows(*self)`): an iterator's items borrow the
    /// sequence the iterator borrows, not the iterator.
    Return { name: String, contents: bool },
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
    /// Declared `unsafe fn`: callers must be inside `unsafe { ... }` and uphold its documented
    /// preconditions. The body itself is not an `unsafe` block.
    pub is_unsafe: bool,
    /// For a method declared inside an `impl Tr { ... }` block within a type's own body: the
    /// trait `Tr` it implements. Such methods are not inherent methods of the type.
    pub impl_of: Option<TypeExpr>,
    /// For such a method: whether its block is `unsafe impl Tr { ... }`.
    pub is_unsafe_impl: bool,
}

/// A sequentially consistent atomic operation (`@atomic_load`, `@atomic_add`, ...). Every
/// operation but `store` yields the value the integer held before it.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum AtomicOp {
    Load,
    Store,
    Swap,
    /// `@atomic_cas(p, expected, new)`: stores `new` if the value is `expected`.
    Cas,
    Add,
    Sub,
    And,
    Or,
    Xor,
    /// Relaxed forms, for a counter that orders nothing: they are atomic, but other memory is
    /// not synchronized by them.
    LoadRelaxed,
    AddRelaxed,
    SubRelaxed,
}

impl AtomicOp {
    pub const ALL: [AtomicOp; 12] = [
        AtomicOp::Load,
        AtomicOp::Store,
        AtomicOp::Swap,
        AtomicOp::Cas,
        AtomicOp::Add,
        AtomicOp::Sub,
        AtomicOp::And,
        AtomicOp::Or,
        AtomicOp::Xor,
        AtomicOp::LoadRelaxed,
        AtomicOp::AddRelaxed,
        AtomicOp::SubRelaxed,
    ];

    pub fn name(self) -> &'static str {
        match self {
            AtomicOp::Load => "load",
            AtomicOp::Store => "store",
            AtomicOp::Swap => "swap",
            AtomicOp::Cas => "cas",
            AtomicOp::Add => "add",
            AtomicOp::Sub => "sub",
            AtomicOp::And => "and",
            AtomicOp::Or => "or",
            AtomicOp::Xor => "xor",
            AtomicOp::LoadRelaxed => "load_relaxed",
            AtomicOp::AddRelaxed => "add_relaxed",
            AtomicOp::SubRelaxed => "sub_relaxed",
        }
    }

    pub fn from_name(name: &str) -> Option<Self> {
        Self::ALL.into_iter().find(|op| op.name() == name)
    }

    /// The number of value arguments after the pointer.
    pub fn value_args(self) -> usize {
        match self {
            AtomicOp::Load | AtomicOp::LoadRelaxed => 0,
            AtomicOp::Cas => 2,
            _ => 1,
        }
    }
}

/// What an unchecked pointer holds. All three dereference only in `unsafe` and support pointer
/// arithmetic; they differ in what a type containing them is (see DESIGN.md, "Pointer Kinds").
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum PtrKind {
    /// `*const T` / `*mut T`: holds nothing; carries no borrow and confers no ownership.
    Raw,
    /// `*own T`: owns the `T` values it points to (a container holding one is linear if `T` is,
    /// carries `T`'s borrows, and is `send` / `sync` as `T` is). Only `opaque` fields may hold one.
    Own,
    /// `*ref T` / `*ref mut T`: a view of borrowed data, carrying the borrow it was made from
    /// like `&T` / `&mut T`, but unchecked for aliasing.
    View,
}

#[derive(Debug, Clone, PartialEq)]
pub struct TraitMethodDecl {
    pub name: String,
    pub params: Vec<Param>,
    pub ret_ty: TypeExpr,
    pub borrows: Option<Vec<BorrowContractItem>>,
    /// Declared `unsafe fn`: implementations must be `unsafe fn` too.
    pub is_unsafe: bool,
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
    /// `unsafe impl drop(may_dangle T)`: the hook only drops, moves, or frees the `T` values the
    /// type holds and never otherwise reads them, so borrows inside them may have ended by the
    /// time the value is dropped.
    pub may_dangle: Vec<String>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct ExternFuncDecl {
    pub vis: Visibility,
    pub name: String,
    pub params: Vec<(String, TypeExpr)>,
    pub ret_ty: TypeExpr,
    /// Declared `safe extern fn`: callable without `unsafe`, asserting the C function has no
    /// preconditions. Any other `extern fn` is an `unsafe fn`.
    pub is_safe: bool,
}

#[derive(Debug, Clone, PartialEq)]
pub struct FieldDecl {
    pub vis: Visibility,
    pub name: String,
    pub ty: TypeExpr,
    pub default_val: Option<Expr>,
    /// Declared `cell name: T` (only in an `opaque`): the field may be written through a shared
    /// reference to its value, which makes the `opaque` not `sync` unless it declares `unsafe sync`.
    pub is_cell: bool,
}

/// Thread-safety declarations on an `opaque`, overriding what its contents imply:
/// `opaque(unsafe send)` / `opaque(unsafe sync)` assert a trait the compiler cannot verify (raw
/// pointers are exempt from the field check), and `opaque(!send)` / `opaque(!sync)` withhold one.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct ThreadDecl {
    pub unsafe_send: bool,
    pub unsafe_sync: bool,
    pub not_send: bool,
    pub not_sync: bool,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum OpaqueOwnership {
    Default,
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
    Struct,        // `struct` (transparent product type) (rank 3)
    Tuple,         // `tuple` (rank 3)
    Discriminated, // `discriminated` (`enum`, `union`, or `error`) (rank 2)
    Enum,          // `enum` (rank 3)
    Union,         // `union` (including `?T` and `E!T`) (rank 3)
    Overlay,       // `overlay` (untagged union `overlay { ... }` or `uninit T`) (rank 3)
    Error,         // `error` (`error { ... }` or `E1 || E2`) (rank 3)
    Opaque,        // `opaque` (encapsulated product type) (rank 3)
    Copy,          // `copy` (`opaque(copy)` or copyable transparent/scalar type) (rank 4)
    Affine,        // `affine` (`opaque(affine)` / `opaque` or move-only non-linear type) (rank 4)
    Linear,        // `linear` (`opaque(linear)` or container with linear field) (rank 4)
    Recursive,     // `recursive` (can own another of itself) (rank 4)
    Unchecked,     // `unchecked` (any type, used as anything: duck typing, checked where used) (rank 1)
    Simd,          // `simd` (`simd[T; N]`) (rank 3)
    Array,         // `array` (`[T; N]`) (rank 3)
    Slice,         // `slice` (`&[T]`, `&mut [T]`) (rank 3)
    Send,          // `send` (safe to transfer across threads) (rank 2)
    Sync,          // `sync` (safe to share `&T` across threads) (rank 2)
    Format,        // `format` (transparent type or opaque with `format` hook) (rank 2)
    Clone,         // `clone` (copyable type or opaque/struct supporting `@clone`) (rank 2)
    Default,       // `default` (type supporting `@default(T)`) (rank 2)
    Module,        // `module` (first-class comptime module value) (rank 2)
}

impl TypeConstraint {
    pub fn specificity(self) -> u8 {
        match self {
            TypeConstraint::AnyType | TypeConstraint::Unchecked => 1,
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
            | TypeConstraint::Struct
            | TypeConstraint::Tuple
            | TypeConstraint::Enum
            | TypeConstraint::Union
            | TypeConstraint::Overlay
            | TypeConstraint::Error
            | TypeConstraint::Opaque
            | TypeConstraint::Simd
            | TypeConstraint::Array
            | TypeConstraint::Slice => 3,
            TypeConstraint::Copy
            | TypeConstraint::Affine
            | TypeConstraint::Linear
            | TypeConstraint::Recursive
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
            TypeConstraint::Struct => "struct",
            TypeConstraint::Tuple => "tuple",
            TypeConstraint::Discriminated => "discriminated",
            TypeConstraint::Enum => "enum",
            TypeConstraint::Union => "union",
            TypeConstraint::Overlay => "overlay",
            TypeConstraint::Error => "error",
            TypeConstraint::Opaque => "opaque",
            TypeConstraint::Copy => "copy",
            TypeConstraint::Affine => "affine",
            TypeConstraint::Linear => "linear",
            TypeConstraint::Recursive => "recursive",
            TypeConstraint::Unchecked => "unchecked",
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

/// The body of an `opaque { ... }` type expression.
#[derive(Debug, Clone, PartialEq)]
pub struct OpaqueBody {
    pub is_packed: bool,
    pub ownership: OpaqueOwnership,
    pub threads: ThreadDecl,
    /// `comptime` type parameters owned by this `opaque` (`opaque(owns T)`); an instantiation
    /// is linear if any owned type argument is linear.
    pub owns: Vec<String>,
    /// `comptime` type parameters this `opaque` borrows without a visible `*ref T` field
    /// (`opaque(borrows T)`); its values then carry borrows like `&T`.
    pub borrows: Vec<String>,
    pub fields: Vec<FieldDecl>,
    pub consts: Vec<ConstDecl>,
    pub statics: Vec<StaticDecl>,
    pub methods: Vec<FuncDecl>,
    pub default_hook: Option<(Vec<WherePredicate>, Block)>,
    pub clone_hooks: Vec<CloneHookDecl>,
    pub drop_hooks: Vec<DropHookDecl>,
    pub format_hook: Option<(String, String, Option<String>, Block)>,
}

/// An associated item a trait asks of its implementations: `const Name: bound;`, a compile-time
/// value (a type, when the bound is a kind of type) that each gives with `const Name: T = value;`.
#[derive(Debug, Clone, PartialEq)]
pub struct AssocItem {
    pub name: String,
    pub bound: TypeExpr,
}

/// How a type comes to meet a trait.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TraitKind {
    /// By an `impl`.
    Nominal,
    /// `unsafe trait`: by an `unsafe impl`, whose author takes on what the trait promises.
    Unsafe,
    /// `trait(structural)`: by having methods of the declared signatures; it takes no `impl`.
    Structural,
}

#[derive(Debug, Clone, PartialEq)]
pub enum TypeExpr {
    Void,
    BareOpaque,
    OpaqueDef {
        methods: Vec<FuncDecl>,
    },
    Distinct {
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
    /// `F[args]`: a type function applied to comptime arguments, or an element of a comptime
    /// list of types (`ts[i]`).
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
        kind: PtrKind,
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
        /// `unsafe fn(...)`: calls through it need an `unsafe` block.
        is_unsafe: bool,
    },
    /// `extern fn(...) -> R`: a function pointer using the C calling convention.
    CFnPtr {
        params: Vec<TypeExpr>,
        ret: Box<TypeExpr>,
        /// `unsafe extern fn(...)`: calls through it need an `unsafe` block.
        is_unsafe: bool,
    },
    Enum {
        backing: Option<Box<TypeExpr>>,
        variants: Vec<(String, Option<i128>)>,
    },
    Union {
        backing: Option<Box<TypeExpr>>,
        variants: Vec<(String, Option<TypeExpr>, Option<i128>)>,
    },
    /// Unified `error` (`error(c_int) { ok Ok = 0, Variant: Payload = 1, ... }`).
    Error {
        backing: Option<Box<TypeExpr>>,
        ok_flag: Option<(String, i128)>,
        variants: Vec<(String, Option<TypeExpr>, Option<i128>)>,
    },
    ErrorSetUnion(Vec<TypeExpr>),
    Result {
        err: Box<TypeExpr>,
        ok: Box<TypeExpr>,
    },
    Struct {
        is_packed: bool,
        fields: Vec<FieldDecl>,
        methods: Vec<FuncDecl>,
    },
    /// `opaque { ... }` (boxed: by far the largest type expression).
    Opaque(Box<OpaqueBody>),
    /// The methods, how a type comes to meet the trait, and the associated items its
    /// implementations give (`const Handle: copy;`).
    Trait(Vec<TraitMethodDecl>, TraitKind, Vec<AssocItem>),
    TraitBounds(Vec<TypeExpr>),
    BackingType(Box<TypeExpr>),
    SynthesizedStruct {
        is_packed: bool,
        fields: Box<Expr>,
    },
    SynthesizedTuple(Box<Expr>),
    SynthesizedEnum {
        backing: Box<TypeExpr>,
        variants: Box<Expr>,
    },
    SynthesizedUnion {
        backing: Option<Box<TypeExpr>>,
        variants: Box<Expr>,
    },
    SynthesizedError(Box<Expr>),
}

impl TypeExpr {
    /// Whether naming this type expression declares a new nominal type (`type Name = ...`)
    /// rather than naming an existing or structural one (`alias Name = ...`).
    pub fn declares_type(&self) -> bool {
        matches!(
            self,
            TypeExpr::Struct { .. }
                | TypeExpr::Opaque(_)
                | TypeExpr::OpaqueDef { .. }
                | TypeExpr::Distinct { .. }
                | TypeExpr::BareOpaque
                | TypeExpr::Enum { .. }
                | TypeExpr::Union { .. }
                | TypeExpr::Error { .. }
                | TypeExpr::Overlay(_)
                | TypeExpr::Trait(..)
        )
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum MatchPat {
    Wildcard,
    Null,
    Bool(bool),
    Int(i128),
    WideInt(Box<crate::wide::Wide>),
    Float(u64),
    Rune(char),
    Str(String),
    Range {
        lo: Box<MatchPat>,
        hi: Box<MatchPat>,
    },
    CatchAllBind {
        mode: BindMode,
        name: String,
    },
    Variant {
        path: Vec<String>,
        payload: Option<Box<MatchPat>>,
    },
    /// `.Name` / `.Name(pat)`: a variant of the scrutinee's own type.
    DotVariant {
        name: String,
        payload: Option<Box<MatchPat>>,
    },
    /// `Point { x: p1, y, .. }` or `{ x: p1, y, .. }`.
    Struct {
        path: Option<Vec<String>>,
        fields: Vec<(String, MatchPat)>,
        rest: bool,
    },
    /// `{ p1, p2 }`, `(p1, p2)`, `[p1, p2]`, `{ p1, .., p2 }`, `[first, .., last]`.
    Seq {
        elems: Vec<MatchPat>,
        rest: Option<usize>,
        bracketed: bool,
    },
    /// `p1 | p2 | ...`
    Or(Vec<MatchPat>),
    /// `Maybe[i32]::Some(v)` or `Pair[i32] { first, .. }`: `pat`, whose path is relative to the
    /// generic type `ty` (a `Variant` path of just the variant, a `Struct` path that is empty).
    TypeQualified {
        ty: TypeExpr,
        pat: Box<MatchPat>,
    },
}

impl MatchPat {
    /// Whether a `TypeQualified` pattern is anywhere in this one.
    pub fn has_type_qualified(&self) -> bool {
        match self {
            MatchPat::TypeQualified { .. } => true,
            MatchPat::Variant { payload, .. } | MatchPat::DotVariant { payload, .. } => {
                payload.as_deref().is_some_and(MatchPat::has_type_qualified)
            }
            MatchPat::Struct { fields, .. } => fields.iter().any(|(_, p)| p.has_type_qualified()),
            MatchPat::Seq { elems, .. } | MatchPat::Or(elems) => {
                elems.iter().any(MatchPat::has_type_qualified)
            }
            _ => false,
        }
    }

    /// Collects identifier names bound by this pattern so closure capture analysis does not
    /// mistake pattern bindings inside an arm for outer local captures.
    pub fn collect_bound_names(&self, out: &mut std::collections::HashSet<String>) {
        match self {
            MatchPat::Wildcard
            | MatchPat::Null
            | MatchPat::Bool(_)
            | MatchPat::Int(_)
            | MatchPat::WideInt(_)
            | MatchPat::Float(_)
            | MatchPat::Rune(_)
            | MatchPat::Str(_)
            | MatchPat::Range { .. } => {}
            MatchPat::CatchAllBind { name, .. } => {
                if name != "_" {
                    out.insert(name.clone());
                }
            }
            MatchPat::Variant { payload, .. } | MatchPat::DotVariant { payload, .. } => {
                if let Some(p) = payload {
                    p.collect_bound_names(out);
                }
            }
            MatchPat::Struct { fields, .. } => {
                for (_, fp) in fields {
                    fp.collect_bound_names(out);
                }
            }
            MatchPat::Seq { elems, .. } | MatchPat::Or(elems) => {
                for ep in elems {
                    ep.collect_bound_names(out);
                }
            }
            MatchPat::TypeQualified { pat, .. } => pat.collect_bound_names(out),
        }
    }

    /// Collects any `ref` / `ref mut` binding mode used anywhere in this pattern (`Some(true)` if
    /// any binding is `ref mut`, `Some(false)` if only shared `ref` bindings appear).
    pub fn ref_bind_mode(&self) -> Option<bool> {
        let mut acc = None;
        self.visit_ref_modes(&mut acc);
        acc
    }

    fn visit_ref_modes(&self, acc: &mut Option<bool>) {
        match self {
            MatchPat::CatchAllBind {
                mode: BindMode::Ref { mutable },
                ..
            } => {
                *acc = Some(acc.unwrap_or(false) || *mutable);
            }
            MatchPat::Variant { payload, .. } | MatchPat::DotVariant { payload, .. } => {
                if let Some(p) = payload {
                    p.visit_ref_modes(acc);
                }
            }
            MatchPat::Struct { fields, .. } => {
                for (_, fp) in fields {
                    fp.visit_ref_modes(acc);
                }
            }
            MatchPat::Seq { elems, .. } | MatchPat::Or(elems) => {
                for ep in elems {
                    ep.visit_ref_modes(acc);
                }
            }
            _ => {}
        }
    }
}

/// What a `for` loop iterates over.
#[derive(Debug, Clone, PartialEq)]
pub enum ForIter {
    /// `start..end` or `start..=end` over integers.
    Range {
        start: Box<Expr>,
        end: Box<Expr>,
        inclusive: bool,
    },
    /// An array, a slice, or an iterator (a value with `next(self: &mut Self) -> ?T`).
    Expr(Box<Expr>),
}

/// How a `match` arm binds a variant payload: `V(x)` copies or moves (`Default`), `V(move x)`
/// moves explicitly, and `V(ref x)` / `V(ref mut x)` borrows it from the matched value.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BindMode {
    Default,
    Move,
    Ref { mutable: bool },
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
            TypeExpr::BareOpaque => Some(TypeConstraint::Opaque),
            TypeExpr::Constraint(c) => Some(*c),
            _ => None,
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Block {
    pub stmts: Vec<Stmt>,
    /// Where each statement starts and then where the closing brace is, when parsed from source.
    pub lines: Vec<Pos>,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Stmt {
    Let {
        mutable: bool,
        name: String,
        ty: Option<TypeExpr>,
        init: Expr,
    },
    /// `let mut name: ty;`: a variable with no value yet. Assigning it, or each of its fields,
    /// initializes it; until then it is treated like a value moved out of.
    LetDeferred {
        name: String,
        ty: TypeExpr,
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
    /// `while let v = opt_expr { ... }`: re-evaluates `opt_expr` each iteration and runs the body
    /// with `v` bound to the payload until it yields `null`.
    WhileLet {
        var_name: String,
        opt_expr: Expr,
        body: Block,
    },
    Match {
        scrutinee: Expr,
        arms: Vec<(MatchPat, Expr)>,
    },
    ComptimeFor {
        var_name: String,
        idx_name: Option<String>,
        iterable: Expr,
        body: Block,
    },
    /// `let { a, b } = e;` (a tuple) or `let P { x, y: py, .. } = e;` (a struct): binds fields
    /// (`(field, binding)`; tuple fields are `"0"`, `"1"`, ...) by copying or moving them out of
    /// `e`. `rest` (`..`) allows unnamed fields, which are dropped with the destructured value.
    LetDestructure {
        mutable: bool,
        ty: Option<Vec<String>>,
        /// The arguments of a generic `ty`: `let Pair[i32] { first, second } = p;`.
        ty_args: Vec<Expr>,
        fields: Vec<(String, String)>,
        rest: bool,
        init: Expr,
    },
    /// `for x in iter { ... }`, with `for ref x` / `for ref mut x` borrowing array or slice
    /// elements and `for (x, i) in arr` also binding the index.
    For {
        var_name: String,
        mode: BindMode,
        idx_name: Option<String>,
        iter: ForIter,
        body: Block,
    },
    /// `label: while ...` / `label: for ...`: names a loop for `break label` / `continue label`.
    Labeled {
        label: String,
        stmt: Box<Stmt>,
    },
    Return(Option<Expr>),
    Unsafe(Block),
    /// `nosuspend { ... }`: nothing in the block may wait (see `Compiler::check_nosuspend`).
    NoSuspend(Block),
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
    /// An integer literal that does not fit in `i128`.
    WideInt(Box<crate::wide::Wide>),
    Float(u64),
    Bool(bool),
    Rune(char),
    Str(String),
    Null,
    Uninit(Option<Box<Expr>>),
    /// `Maybe[i32]::None` or `Guard[u8]::LIMIT`: a member of a generic type, other than a call.
    TypeMember {
        ty: TypeExpr,
        name: String,
    },
    TypeVal(TypeExpr),
    Path(Vec<String>),
    Move(Box<Expr>),
    Try(Box<Expr>),
    /// `async f(x)` / `async(e) f(x)`: starts the call as a task, on the executor `e` if given.
    /// `bound` once its arguments are in locals.
    Async {
        call: Box<Expr>,
        bound: bool,
        executor: Option<Box<Expr>>,
    },
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
    /// `f(args)`, or `f[ct_args](args)` with explicit comptime arguments. Without `ct_args`, a
    /// generic callee's comptime arguments are inferred from `args`.
    Call {
        callee: Box<Expr>,
        ct_args: Option<Vec<Expr>>,
        args: Vec<Expr>,
    },
    /// `recv.method(args)`, or `recv.method[ct_args](args)` with explicit comptime arguments.
    MethodCall {
        receiver: Box<Expr>,
        method: String,
        ct_args: Option<Vec<Expr>>,
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
    /// `{ x: 1, y: 2 }`: a struct literal of the expected type, or the structural anonymous
    /// struct of its fields when none is expected.
    RecordLit(Vec<(String, Expr)>),
    IntrinsicInvert(Box<Expr>),
    IntrinsicDeclarations(Box<Expr>),
    IntrinsicTypeName(Box<TypeExpr>),
    IntrinsicSatisfies {
        ty: Box<TypeExpr>,
        bound: Box<TypeExpr>,
    },
    IntrinsicFields(Box<TypeExpr>),
    IntrinsicLeaves(Box<TypeExpr>),
    IntrinsicHasField {
        ty: Box<TypeExpr>,
        name: Box<Expr>,
    },
    /// `@has_method(T, "name")`: whether `x.name(...)` names a method of `T` (its own `pub`
    /// method, or one a trait it implements gives it).
    IntrinsicHasMethod {
        ty: Box<TypeExpr>,
        name: Box<Expr>,
    },
    IntrinsicVariants(Box<TypeExpr>),
    IntrinsicEntries(Box<Expr>),
    IntrinsicFnInfo(Box<TypeExpr>),
    IntrinsicField {
        base: Box<Expr>,
        field: Box<Expr>,
    },
    IntrinsicVariant {
        base: Box<Expr>,
        variant: Box<Expr>,
    },
    IntrinsicMakeUnion {
        ty: Box<TypeExpr>,
        variant: Box<Expr>,
        payload: Option<Box<Expr>>,
    },
    IntrinsicMap {
        key_ty: Box<TypeExpr>,
        val_ty: Box<TypeExpr>,
        entries: Box<Expr>,
    },
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
    /// `@raw_alloc(bytes)`: `bytes` from the program's allocator, or null.
    IntrinsicRawAlloc(Box<Expr>),
    /// `@atomic_<op>(ptr, values...)`: a sequentially consistent atomic operation on the integer
    /// behind a raw pointer.
    IntrinsicAtomic {
        op: AtomicOp,
        args: Vec<Expr>,
    },
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
    /// `@size_of(T)` (`align: false`) or `@align_of(T)` (`align: true`): a `usize` constant.
    IntrinsicLayout {
        ty: TypeExpr,
        align: bool,
    },
    IntrinsicClone(Box<Expr>),
    IntrinsicDrop(Box<Expr>),
    IntrinsicFormat {
        formatter: Box<Expr>,
        value: Box<Expr>,
        spec: Option<String>,
    },
    IntrinsicTrap,
    /// `@compile_error(parts...)`: fails compilation with the parts, evaluated at compile time.
    IntrinsicCompileError(Vec<Expr>),
    FormatStr(Vec<FmtSegment>),
    Return(Option<Box<Expr>>),
    /// `break` / `break label`: leaves the innermost loop, or the loop labelled `label`
    /// (type `never`).
    Break(Option<String>),
    /// `continue` / `continue label`: jumps to the next iteration of the innermost loop, or of
    /// the loop labelled `label` (type `never`).
    Continue(Option<String>),
    /// `.Name` / `.Name(payload)`: a variant of the expected enum, union, or error type.
    DotVariant {
        name: String,
        payload: Option<Box<Expr>>,
    },
    Lambda {
        is_move: bool,
        params: Vec<(bool, String, TypeExpr)>,
        ret_ty: TypeExpr,
        body: Block,
    },
    UnsafeBlock(Block),
}
