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

#[derive(Debug, Clone, PartialEq)]
pub enum TypeExpr {
    Void,
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
    Record {
        fields: Vec<FieldDecl>,
        methods: Vec<FuncDecl>,
    },
    Struct {
        fields: Vec<FieldDecl>,
        methods: Vec<FuncDecl>,
        default_hook: Option<Block>,
        clone_hook: Option<(String, Block)>,
        drop_hook: Option<(String, Block)>,
    },
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
    UnsafeBlock(Block),
}

