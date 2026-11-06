mod archetype;
mod call;
mod comptime;
mod infer;
mod export;
mod expr;
mod stmt;
mod typefn;
mod types;

use crate::fasthash::FastMap as HashMap;

use crate::ast::{
    AssocItem, AtomicOp, BindMode, Block, BorrowContractItem, CIntKind, CloneHookDecl, ConstDecl,
    DropHookDecl, Expr, ExternFuncDecl, FieldDecl, FmtSegment, ForIter, FuncDecl, ImportDecl,
    ImportTargets, Item, MatchPat, ModuleAst, OpaqueBody, OpaqueOwnership, PtrKind, SelectArm,
    SelectOp, StaticDecl, Stmt, ThreadDecl, TraitKind, TraitMethodDecl, TypeConstraint, TypeExpr,
    Visibility, WherePredicate,
};
use crate::borrowck::check_borrows_where;
use crate::drop::elaborate_drops_of;
use crate::frontend::SurfaceParser;
use crate::ir::{
    BasicBlock, BinOp, BlockId, ConstValue, ExternFunc, FnContract, FuncId, Function, Global,
    GlobalId,
    LocalId, Operand, Place, Program, Projection, Rvalue, Statement, Terminator, Type, TypeId,
    UnOp,
};
use crate::wide::Wide;
use comptime::{const_to_wide, int_const};
use infer::TypeVar;
use typefn::HostThunk;

/// The side table describing a compiler-tracked type (see `Compiler::type_kind`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum TypeKind {
    UniversalOpaque,
    Slice,
    Map,
    Closure,
    Distinct,
    CInt,
    RawPtr,
    Composite,
    Trait,
    TraitObj,
    Enum,
    Union,
    Uninit,
    Overlay,
    Error,
    Result,
}

/// The start of the name of a statement's temporary in its scope.
const STATEMENT_TEMP: &str = "__temp";

/// Where `allocator_call` puts the program's allocator, so `__allocator::alloc` names its methods.
const ALLOCATOR_ENV: &str = "__allocator";

/// What a build does with `test` blocks.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum TestBuild {
    /// Leaves them out: an ordinary build.
    None,
    /// Compiles each as a public function (see `Compiler::compile_tests`).
    All,
    /// As `All`, with a `main` that runs this one.
    Entry(usize),
}

/// A `test` block of a package compiled with `Compiler::compile_tests`.
#[derive(Debug, Clone)]
pub struct TestCase {
    pub module: String,
    pub name: String,
    /// The function its body became.
    pub func: FuncId,
}

/// Stack size of the compiler thread (see `Compiler::compile_package_compiler`).
const COMPILER_STACK_BYTES: usize = 512 << 20;
/// The C functions in which a thread waits for something else: what `nosuspend` forbids along
/// with a fiber parking.
const WAITING_EXTERNS: &[&str] = &[
    "pthread_mutex_lock",
    "pthread_cond_wait",
    "pthread_cond_timedwait",
    "pthread_join",
    "usleep",
    "nanosleep",
    "sleep",
    "poll",
    "epoll_wait",
];
/// How deeply types may nest while being built, which ends `G[T]` naming `G[*const T]`.
const MAX_TYPE_NESTING: usize = 256;

/// Identity of an anonymous struct or overlay: `(is_overlay, is_packed, ordered fields)`.
type AnonRecordKey = (bool, bool, Vec<(String, TypeId)>);

/// An associated constant: `(value, type, compile-time value, visibility, explicitly typed)`.
type AssociatedConst = (ConstValue, TypeId, ComptimeVal, Visibility, bool);

/// Identity of a synthesized union: `(tag enum, ordered variants)`.
type UnionKey = (Option<TypeId>, Vec<(String, TypeId)>);

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
struct ErrorLeafKey {
    def_module: String,
    error_name: String,
    variant_name: String,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct ErrorLeafInfo {
    key: ErrorLeafKey,
    payload_ty: TypeId,
}

#[derive(Debug, Clone)]
struct ErrorTypeInfo {
    name: String,
    leaves: Vec<ErrorLeafInfo>,
    /// Leaf keys in declaration order (with embedded errors expanded in their own declaration order).
    decl_order: Vec<ErrorLeafKey>,
    /// Whether any variant carries a non-`void` payload.
    has_payloads: bool,
    /// Whether this error embeds another error type (or was formed by `E1 || E2`).
    has_embedded: bool,
    /// Explicit C backing integer type (`error(Int)`), if specified.
    c_backing: Option<TypeId>,
    /// Reserved success sentinel `(name, value)` for `error` (default `("Ok", 0)`).
    ok_flag: (String, i128),
}

#[derive(Debug, Clone, PartialEq)]
struct UnionTypeInfo {
    name: String,
    variants: Vec<(String, TypeId)>,
    c_backing: Option<TypeId>,
    tag_values: Vec<i128>,
}

#[derive(Debug, Clone)]
struct OverlayTypeInfo {
    name: String,
    fields: Vec<(String, TypeId)>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct ResultTypeInfo {
    ok_ty: TypeId,
    err_ty: TypeId,
}

#[derive(Debug, Clone)]
pub enum ComptimeVal {
    Null,
    Type(TypeId),
    Int(i128),
    Bool(bool),
    Str(String),
    Module(String),
    Map(u32),
    List(Vec<ComptimeVal>, Option<TypeId>),
    Record(Vec<(String, ComptimeVal)>),
    Tuple(Vec<ComptimeVal>),
    ConstExpr(String, Expr),
}

impl PartialEq for ComptimeVal {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (ComptimeVal::Null, ComptimeVal::Null) => true,
            (ComptimeVal::Type(a), ComptimeVal::Type(b)) => a == b,
            (ComptimeVal::Int(a), ComptimeVal::Int(b)) => a == b,
            (ComptimeVal::Bool(a), ComptimeVal::Bool(b)) => a == b,
            (ComptimeVal::Str(a), ComptimeVal::Str(b)) => a == b,
            (ComptimeVal::Module(a), ComptimeVal::Module(b)) => a == b,
            (ComptimeVal::Map(a), ComptimeVal::Map(b)) => a == b,
            (ComptimeVal::List(a, ta), ComptimeVal::List(b, tb)) => a == b && ta == tb,
            (ComptimeVal::Record(a), ComptimeVal::Record(b)) => a == b,
            (ComptimeVal::Tuple(a), ComptimeVal::Tuple(b)) => a == b,
            (ComptimeVal::ConstExpr(ka, _), ComptimeVal::ConstExpr(kb, _)) => ka == kb,
            _ => false,
        }
    }
}

impl Eq for ComptimeVal {}

impl std::hash::Hash for ComptimeVal {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        std::mem::discriminant(self).hash(state);
        match self {
            ComptimeVal::Null => {}
            ComptimeVal::Type(t) => t.hash(state),
            ComptimeVal::Int(n) => n.hash(state),
            ComptimeVal::Bool(b) => b.hash(state),
            ComptimeVal::Str(s) => s.hash(state),
            ComptimeVal::Module(m) => m.hash(state),
            ComptimeVal::Map(id) => id.hash(state),
            ComptimeVal::List(items, ty) => {
                items.hash(state);
                ty.hash(state);
            }
            ComptimeVal::Record(fields) => fields.hash(state),
            ComptimeVal::Tuple(items) => items.hash(state),
            ComptimeVal::ConstExpr(k, _) => k.hash(state),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(super) enum MapKey {
    Type(TypeId),
    Int(i128),
    Bool(bool),
    Str(String),
    Module(String),
}

#[derive(Debug, Clone)]
pub(super) struct MapEntry {
    pub key: MapKey,
    pub key_const: ConstValue,
    pub key_comptime: ComptimeVal,
    pub val_const: ConstValue,
    pub val_comptime: ComptimeVal,
}

#[derive(Debug, Clone)]
pub(super) struct MapInstance {
    pub map_ty: TypeId,
    pub entries: Vec<MapEntry>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) struct MapTypeInfo {
    pub key_ty: TypeId,
    pub val_ty: TypeId,
}

#[derive(Debug, Clone, Copy)]
pub(super) struct PhfTableInfo {
    pub global_id: GlobalId,
    pub table_len: usize,
    pub seed: u64,
    pub entry_ty: TypeId,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EvaluatedDependency {
    pub name: String,
    pub url: String,
    pub sha256: [u64; 4],
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EvaluatedPackage {
    pub name: String,
    pub version: (u32, u32, u32),
    pub root: String,
    pub no_std: bool,
    pub deps: Vec<EvaluatedDependency>,
    pub system_libs: Vec<String>,
}

#[derive(Debug, Clone)]
struct TraitInfo {
    name: String,
    def_module: String,
    comptime_env: HashMap<String, ComptimeVal>,
    methods: Vec<TraitMethodDecl>,
    /// `unsafe trait`: its implementations make promises the compiler cannot check.
    /// `trait(structural)`: met by methods alone, with no implementation.
    kind: TraitKind,
    /// The associated items each implementation gives (`const Handle: copy;`).
    assoc: Vec<AssocItem>,
}

#[derive(Debug, Clone)]
struct TraitObjInfo {
    trait_ty: TypeId,
    mutable: bool,
    data_ptr_ty: TypeId,
    vtable_ty: TypeId,
    vtable_ptr_ty: TypeId,
    method_fn_ptr_tys: Vec<TypeId>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum RelFieldKind {
    Elem(TypeId),
    Slice(TypeId),
    Str,
}

/// What an `opaque` holds without a visible field: `opaque(owns T)` (values of `T`, as if behind
/// a `*own T`) and `opaque(borrows T)` (a borrow of `T`, as if behind a `*ref T`).
#[derive(Debug, Clone, Default)]
struct DeclaredContents {
    owns: Vec<TypeId>,
    borrows: Vec<TypeId>,
}

#[derive(Debug, Clone)]
struct CompositeInfo {
    name: String,
    is_opaque: bool,
    is_packed: bool,
    total_bits: u16,
    packed_offsets: Vec<(u16, u16)>,
    ownership: OpaqueOwnership,
    /// `opaque(unsafe send, unsafe sync, !send, !sync)` declarations.
    threads: ThreadDecl,
    /// Indices of `cell` fields, which may be written through a shared reference.
    cell_fields: Vec<usize>,
    has_format_hook: bool,
    def_module: String,
    comptime_env: HashMap<String, ComptimeVal>,
    fields: Vec<(String, TypeId, Visibility, Option<Expr>)>,
    rel_fields: HashMap<u32, RelFieldKind>,
    consts: HashMap<String, (Visibility, ConstDecl)>,
    statics: HashMap<String, (Visibility, StaticDecl)>,
    /// Shared, as every method call reads it.
    methods: std::sync::Arc<HashMap<String, (Visibility, FuncDecl)>>,
    method_fn_ids: HashMap<String, FuncId>,
    default_fn: Option<FuncId>,
    clone_fn: Option<FuncId>,
    drop_fn: Option<FuncId>,
    format_fn: Option<(FuncId, bool)>,
    /// Contents declared with `opaque(owns T)` / `opaque(borrows T)`.
    declared: DeclaredContents,
    /// Type arguments the selected `drop` hook declares `may_dangle`.
    may_dangle: Vec<TypeId>,
}

#[derive(Debug, Clone)]
enum ResolvedItem {
    Module(String),
    Type(String, String),
    Func(String, String),
    ExternFunc(String, String),
    Static(String, String),
    Const(String, String),
}

#[derive(Debug, Clone)]
struct ClosureInfo {
    call_fn_id: FuncId,
    is_move: bool,
    env_mut: bool,
    env_by_val: bool,
    param_tys: Vec<TypeId>,
    ret_ty: TypeId,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct SliceInfo {
    mutable: bool,
    elem: TypeId,
    ptr_ty: TypeId,
    is_str: bool,
}

#[derive(Clone)]
struct PendingFunc {
    func_id: FuncId,
    module_path: String,
    owner_ty: Option<TypeId>,
    decl: FuncDecl,
    comptime_env: HashMap<String, ComptimeVal>,
    closure_captures: Vec<(String, TypeId, bool)>,
}

/// A type-function call put off because an argument has no definition yet.
#[derive(Clone)]
struct DeferredType {
    id: TypeId,
    mod_path: String,
    fname: String,
    args: Vec<ComptimeVal>,
}

#[derive(Debug, Clone)]
struct DistinctTypeInfo {
    name: String,
    def_module: String,
    underlying: TypeId,
    comptime_env: HashMap<String, ComptimeVal>,
    methods: HashMap<String, (Visibility, FuncDecl)>,
    method_fn_ids: HashMap<String, FuncId>,
}

#[derive(Debug, Clone)]
struct OpaqueRetBound {
    bound_mod: String,
    owner_ty: Option<TypeId>,
    env: HashMap<String, ComptimeVal>,
    bound_expr: TypeExpr,
}

#[derive(Debug, Clone)]
pub enum ExportRetKind {
    Direct(TypeId),
    OptionalPtr {
        opt_ty: TypeId,
        raw_ptr_ty: TypeId,
    },
    OptionalVal {
        opt_ty: TypeId,
        val_ty: TypeId,
        out_ptr_ty: TypeId,
    },
    ResultVal {
        res_ty: TypeId,
        err_ty: TypeId,
        ok_ty: TypeId,
        out_val_ptr_ty: Option<TypeId>,
        out_err_ptr_ty: Option<TypeId>,
    },
}

#[allow(dead_code)]
#[derive(Debug, Clone)]
struct CAbiParamInfo {
    name: String,
    inner_ty: TypeId,
    c_abi_ty: TypeId,
    is_nullable_raw_ptr: Option<(TypeId, TypeId)>,
}

#[allow(dead_code)]
#[derive(Debug, Clone)]
struct CAbiExportWrapperInfo {
    c_abi_fn_id: FuncId,
    export_symbol: String,
    user_params: Vec<CAbiParamInfo>,
    c_abi_param_tys: Vec<TypeId>,
    c_abi_ret_ty: TypeId,
    ret_kind: ExportRetKind,
}

#[derive(Debug, Clone)]
pub struct ExportedTypeMeta {
    pub name: String,
    pub ty_id: TypeId,
}

#[derive(Debug, Clone)]
pub struct ExportedFuncMeta {
    pub symbol: String,
    pub params: Vec<(String, TypeId)>,
    pub ret_kind: ExportRetKind,
}

#[derive(Clone)]
pub struct Compiler {
    modules: HashMap<String, ModuleAst>,
    pub program: Program,
    composites: HashMap<TypeId, std::sync::Arc<CompositeInfo>>,
    enums: HashMap<TypeId, (String, Vec<(String, i128)>)>,
    unions: HashMap<TypeId, UnionTypeInfo>,
    overlays: HashMap<TypeId, OverlayTypeInfo>,
    uninit_types: HashMap<TypeId, TypeId>,
    memoized_uninit: HashMap<TypeId, TypeId>,
    errors: HashMap<TypeId, ErrorTypeInfo>,
    memoized_anon_records: HashMap<AnonRecordKey, TypeId>,
    memoized_c_fn_ptrs: HashMap<(Vec<TypeId>, TypeId, bool), TypeId>,
    /// Functions declared `unsafe fn`: calling one requires an `unsafe` block.
    unsafe_fns: crate::fasthash::FastSet<FuncId>,
    /// `(module, name)` of each `safe extern fn` declaration. Every other `extern fn` is unsafe to
    /// call; safety belongs to the declaration, so modules may declare one C symbol differently.
    safe_externs: crate::fasthash::FastSet<(String, String)>,
    /// Function-pointer types declared `unsafe fn(...)` / `unsafe extern fn(...)`.
    unsafe_fn_ptr_types: crate::fasthash::FastSet<TypeId>,
    /// The structural instance of each interned type shape (see `intern_type`).
    structural_types: HashMap<Type, TypeId>,
    /// C enum value of each leaf (by leaf index) of every `export error`.
    export_error_values: HashMap<TypeId, Vec<i128>>,
    memoized_error_unions: HashMap<Vec<(ErrorLeafKey, TypeId)>, TypeId>,
    results: HashMap<TypeId, ResultTypeInfo>,
    memoized_results: HashMap<(TypeId, TypeId), TypeId>,
    traits: HashMap<TypeId, TraitInfo>,
    trait_objs: HashMap<TypeId, TraitObjInfo>,
    memoized_trait_objs: HashMap<(TypeId, bool), TypeId>,
    memoized_vtables: HashMap<(TypeId, TypeId), (GlobalId, Vec<FuncId>)>,
    closures: HashMap<TypeId, ClosureInfo>,
    slices: HashMap<TypeId, SliceInfo>,
    raw_ptrs: HashMap<TypeId, (bool, TypeId)>,
    /// The kind of each `raw_ptrs` entry that is not a plain raw pointer (`*own T`, `*ref T`).
    ptr_kinds: HashMap<TypeId, PtrKind>,
    maps: HashMap<TypeId, MapTypeInfo>,
    memoized_maps: HashMap<(TypeId, TypeId), TypeId>,
    map_instances: Vec<MapInstance>,
    dense_map_globals: HashMap<u32, (GlobalId, i128, i128)>,
    phf_map_globals: HashMap<u32, PhfTableInfo>,
    c_ints: HashMap<TypeId, CIntKind>,
    memoized_c_ints: HashMap<CIntKind, TypeId>,
    opaque_ty: Option<TypeId>,
    named_opaques: crate::fasthash::FastSet<TypeId>,
    distinct_types: HashMap<TypeId, DistinctTypeInfo>,
    opaque_ret_funcs: HashMap<FuncId, OpaqueRetBound>,
    pub exported_types: Vec<ExportedTypeMeta>,
    exported_type_set: crate::fasthash::FastSet<TypeId>,
    c_abi_func_wrappers: HashMap<FuncId, CAbiExportWrapperInfo>,
    pub exported_funcs: Vec<ExportedFuncMeta>,
    named_types: HashMap<(String, String), TypeId>,
    memoized_type_calls: HashMap<(String, String, Vec<ComptimeVal>), TypeId>,
    /// Types with an id but no definition yet (see `with_reserved_type`), each with the nesting
    /// depth of the outermost unfinished type it needs.
    pending_types: HashMap<TypeId, usize>,
    /// Unfinished types nesting around the one being built.
    type_depth: usize,
    /// The outermost `pending_types` depth reached since the last cycle finished.
    cycle_floor: usize,
    /// The id the next type declaration takes, reserved by `with_reserved_type`.
    reserved_type: Option<TypeId>,
    /// Type-function calls waiting for an argument to be defined, oldest first.
    deferred_types: std::collections::VecDeque<DeferredType>,
    /// Type-function calls that take the id already handed out for them.
    reserved_calls: HashMap<(String, String, Vec<ComptimeVal>), TypeId>,
    /// Types of the cycle `finish_types` is completing, and whether it is running.
    finishing_types: Vec<TypeId>,
    finishing: bool,
    /// Methods of unfinished types, whose bodies wait for those types.
    held_funcs: Vec<PendingFunc>,
    /// The functions whose bodies are being lowered, innermost last.
    lowering_funcs: Vec<FuncId>,
    /// The calls and drops inside `nosuspend` blocks: the function, and the block they end.
    nosuspend_sites: Vec<(FuncId, BlockId)>,
    /// Declarations with no id to reserve, being resolved: naming one again never ends.
    resolving_named: Vec<(String, String)>,
    /// Folding an expression nothing asked to be constant, which must not call anything impure.
    implicit_folding: bool,
    /// The root module's `ProgramAllocator`, once looked up.
    program_allocator: Option<Option<TypeId>>,
    /// Calls in `memoized_type_calls` that returned a type which already existed, such as one of
    /// their arguments: that type is not an instance of the function.
    reused_type_calls: crate::fasthash::FastSet<(String, String, Vec<ComptimeVal>)>,
    memoized_inherent_methods: HashMap<(TypeId, String, Vec<ComptimeVal>), FuncId>,
    resolved_funcs: HashMap<(String, String, Vec<ComptimeVal>), FuncId>,
    resolved_externs: HashMap<(String, String), FuncId>,
    resolved_statics: HashMap<(String, String), (GlobalId, TypeId, bool)>,
    resolved_consts: HashMap<(String, String), (ConstValue, TypeId, ComptimeVal, bool)>,
    associated_statics: HashMap<(TypeId, String), (GlobalId, TypeId, bool, Visibility)>,
    associated_consts: HashMap<(TypeId, String), AssociatedConst>,
    func_sigs: HashMap<FuncId, (Vec<TypeId>, TypeId)>,
    pending_funcs: Vec<PendingFunc>,
    /// Index of the next entry of `pending_funcs` to lower.
    pending_cursor: usize,
    /// Nesting depth of compile-time type-function evaluation (guards runaway recursion).
    comptime_depth: usize,
    /// Non-fatal diagnostics (lints) collected during compilation, deduplicated.
    pub warnings: Vec<String>,
    /// Functions declared `-> T discardable`, whose results a statement may leave unused.
    discardable_fns: crate::fasthash::FastSet<FuncId>,
    /// Function-pointer types keyed by `(args, ret, contract)`; each carries its borrow contract.
    memoized_fn_ptrs: HashMap<(Vec<TypeId>, TypeId, FnContract, bool), TypeId>,
    /// Functions whose body has no private access to its `owner_ty` (module-level `impl` methods).
    no_private_access_fns: crate::fasthash::FastSet<FuncId>,
    /// Closures and lambdas written inside an `unsafe` block: their bodies are inside it too.
    unsafe_closures: crate::fasthash::FastSet<FuncId>,
    /// Set while scheduling a module-level `impl` method so it is lowered without private access.
    schedule_no_private: bool,
    /// `impl Tr { ... }` blocks declared inside a type's own body, keyed by the instantiated type.
    inline_impls: HashMap<TypeId, Vec<InlineImpl>>,
    /// Instantiated trait-implementation methods keyed by `(type, trait, method name)`.
    memoized_impl_methods: HashMap<(TypeId, TypeId, String), FuncId>,
    /// All module-level `impl` items (module path, declaration), collected once on first use.
    module_impls: Option<std::sync::Arc<Vec<(String, crate::ast::ImplDecl)>>>,
    /// The `T::Tag` enum of each union: the linked enum for `union(Enum)`, otherwise synthesized.
    union_tag_enums: HashMap<TypeId, TypeId>,
    /// Expressions currently in the generic fallback of `eval_const_expr_typed` (re-entrancy guard).
    const_eval_fallback: Vec<usize>,
    /// Results of `impl` lookups keyed by `(type, optional trait filter)`.
    trait_impl_cache: HashMap<(TypeId, Option<TypeId>), TraitImpls>,
    /// The `test` blocks a test build compiled: their module, name, and function's name.
    tests: Vec<(String, String, String)>,
    /// Packages the root package depends on, by the name their modules are under (`tls` for
    /// `tls` and `tls::conn`): inside them, `root` means that name.
    dependencies: crate::fasthash::FastSet<String>,
    /// The `(type, trait filter)` collections of impls under way (see `collect_trait_impls`).
    impls_in_progress: crate::fasthash::FastSet<(TypeId, Option<TypeId>)>,
    synthesized_enums: HashMap<(TypeId, Vec<(String, i128)>), TypeId>,
    synthesized_unions: HashMap<UnionKey, TypeId>,
    synthesized_errors: HashMap<Vec<(String, TypeId)>, TypeId>,
    /// The type-building steps of type functions, numbered by their host-function symbols
    /// (see `typefn.rs`).
    host_thunks: Vec<HostThunk>,
    /// Instances of type functions: their name and arguments.
    type_fn_instances: HashMap<FuncId, (String, Vec<ComptimeVal>)>,
}

/// A trait implementation declared inside a type's own body (`impl Tr { ... }`).
#[derive(Debug, Clone)]
struct InlineImpl {
    trait_expr: TypeExpr,
    is_unsafe: bool,
    def_module: String,
    env: HashMap<String, ComptimeVal>,
    methods: Vec<FuncDecl>,
}

/// `(trait, impl)` pairs applying to a type.
type TraitImpls = Vec<(TypeId, ImplMatch)>;

/// The implementation of a trait chosen for a concrete type.
#[derive(Debug, Clone)]
struct ImplMatch {
    def_module: String,
    env: HashMap<String, ComptimeVal>,
    methods: Vec<FuncDecl>,
    /// Inline impls keep the type body's private access; module-level impls do not.
    private_access: bool,
    /// Human-readable location for diagnostics (`impl Hash in 'Point'`, `impl Hash for i32 in 'root'`).
    origin: String,
    /// The associated items a module-level impl gives (an inline impl's are the type's own).
    consts: Vec<ConstDecl>,
}

impl Default for Compiler {
    fn default() -> Self {
        Self::new()
    }
}

impl Compiler {
    pub fn new() -> Self {
        Self {
            modules: HashMap::default(),
            program: Program {
                types: Vec::new(),
                destructors: Vec::new(),
                linear_types: Vec::new(),
                raw_ptr_types: Vec::new(),
                own_ptr_types: Vec::new(),
                view_ptr_types: Vec::new(),
                loan_types: Vec::new(),
                dangle_types: Vec::new(),
                thread_local_globals: Vec::new(),
                c_fn_ptr_types: Vec::new(),
                fn_ptr_contracts: Vec::new(),
                tagged_unions: Vec::new(),
                union_tag_values: Vec::new(),
                type_names: Vec::new(),
                field_names: Vec::new(),
                globals: Vec::new(),
                externs: Vec::new(),
                functions: Vec::new(),
            },
            composites: HashMap::default(),
            enums: HashMap::default(),
            unions: HashMap::default(),
            overlays: HashMap::default(),
            uninit_types: HashMap::default(),
            memoized_uninit: HashMap::default(),
            errors: HashMap::default(),
            structural_types: HashMap::default(),
            memoized_anon_records: HashMap::default(),
            memoized_c_fn_ptrs: HashMap::default(),
            unsafe_fns: crate::fasthash::FastSet::default(),
            safe_externs: crate::fasthash::FastSet::default(),
            unsafe_fn_ptr_types: crate::fasthash::FastSet::default(),
            export_error_values: HashMap::default(),
            memoized_error_unions: HashMap::default(),
            results: HashMap::default(),
            memoized_results: HashMap::default(),
            traits: HashMap::default(),
            trait_objs: HashMap::default(),
            memoized_trait_objs: HashMap::default(),
            memoized_vtables: HashMap::default(),
            closures: HashMap::default(),
            slices: HashMap::default(),
            raw_ptrs: HashMap::default(),
            ptr_kinds: HashMap::default(),
            maps: HashMap::default(),
            memoized_maps: HashMap::default(),
            map_instances: Vec::new(),
            dense_map_globals: HashMap::default(),
            phf_map_globals: HashMap::default(),
            c_ints: HashMap::default(),
            memoized_c_ints: HashMap::default(),
            opaque_ty: None,
            named_opaques: crate::fasthash::FastSet::default(),
            distinct_types: HashMap::default(),
            opaque_ret_funcs: HashMap::default(),
            exported_types: Vec::new(),
            exported_type_set: crate::fasthash::FastSet::default(),
            c_abi_func_wrappers: HashMap::default(),
            exported_funcs: Vec::new(),
            named_types: HashMap::default(),
            memoized_type_calls: HashMap::default(),
            pending_types: HashMap::default(),
            type_depth: 0,
            cycle_floor: usize::MAX,
            reserved_type: None,
            deferred_types: std::collections::VecDeque::new(),
            reserved_calls: HashMap::default(),
            finishing_types: Vec::new(),
            finishing: false,
            held_funcs: Vec::new(),
            lowering_funcs: Vec::new(),
            nosuspend_sites: Vec::new(),
            resolving_named: Vec::new(),
            reused_type_calls: crate::fasthash::FastSet::default(),
            implicit_folding: false,
            program_allocator: None,
            memoized_inherent_methods: HashMap::default(),
            resolved_funcs: HashMap::default(),
            resolved_externs: HashMap::default(),
            resolved_statics: HashMap::default(),
            resolved_consts: HashMap::default(),
            associated_statics: HashMap::default(),
            associated_consts: HashMap::default(),
            func_sigs: HashMap::default(),
            pending_funcs: Vec::new(),
            pending_cursor: 0,
            comptime_depth: 0,
            warnings: Vec::new(),
            discardable_fns: crate::fasthash::FastSet::default(),
            memoized_fn_ptrs: HashMap::default(),
            no_private_access_fns: crate::fasthash::FastSet::default(),
            unsafe_closures: crate::fasthash::FastSet::default(),
            schedule_no_private: false,
            inline_impls: HashMap::default(),
            memoized_impl_methods: HashMap::default(),
            module_impls: None,
            trait_impl_cache: HashMap::default(),
            tests: Vec::new(),
            dependencies: crate::fasthash::FastSet::default(),
            impls_in_progress: crate::fasthash::FastSet::default(),
            union_tag_enums: HashMap::default(),
            const_eval_fallback: Vec::new(),
            synthesized_enums: HashMap::default(),
            synthesized_unions: HashMap::default(),
            synthesized_errors: HashMap::default(),
            host_thunks: Vec::new(),
            type_fn_instances: HashMap::default(),
        }
    }

    /// Compiles a single root module from source in hosted (`std`) mode, runs Stage 3 move/drop
    /// elaboration and NLL borrow checking, and returns the verified Stage 3 `Program`.
    pub fn compile_source(src: &str) -> Result<Program, String> {
        Self::compile_package(&[("root", src)])
    }

    /// Compiles a single root module from source and also returns the generated C compatible `.h` header
    /// for all `export` types and functions.
    pub fn compile_source_with_c_header(src: &str) -> Result<(Program, String), String> {
        Self::compile_package_with_c_header(&[("root", src)])
    }

    /// Compiles a single root module from source in freestanding (`no_std` / `core`-only) mode,
    /// runs Stage 3 move/drop elaboration and NLL borrow checking, and returns the verified Stage 3 `Program`.
    pub fn compile_source_no_std(src: &str) -> Result<Program, String> {
        Self::compile_package_no_std(&[("root", src)])
    }

    /// Loads a package from disk: every `.slop` file under `<dir>/src` becomes a module named after
    /// its path (`src/main.slop` or `src/lib.slop` is `root`, `src/net/http.slop` is
    /// `root::net::http`). Returns `(module_path, source)` pairs in a deterministic order.
    pub fn load_package_dir(dir: &std::path::Path) -> Result<Vec<(String, String)>, String> {
        fn walk(
            src_root: &std::path::Path,
            cur: &std::path::Path,
            out: &mut Vec<(String, String)>,
        ) -> Result<(), String> {
            let mut entries: Vec<_> = std::fs::read_dir(cur)
                .map_err(|e| format!("Cannot read directory '{}': {e}", cur.display()))?
                .filter_map(Result::ok)
                .map(|e| e.path())
                .collect();
            entries.sort();
            for path in entries {
                if path.is_dir() {
                    walk(src_root, &path, out)?;
                } else if path.extension().is_some_and(|x| x == "slop") {
                    let rel = path.strip_prefix(src_root).map_err(|e| e.to_string())?;
                    let mut segments: Vec<String> = rel
                        .with_extension("")
                        .components()
                        .map(|c| c.as_os_str().to_string_lossy().into_owned())
                        .collect();
                    if segments.len() == 1 && matches!(segments[0].as_str(), "main" | "lib") {
                        segments.clear();
                    }
                    let module = std::iter::once("root".to_string())
                        .chain(segments)
                        .collect::<Vec<_>>()
                        .join("::");
                    if out.iter().any(|(m, _)| *m == module) {
                        return Err(format!(
                            "Module '{module}' is defined by more than one file (both 'main.slop' and 'lib.slop'?)"
                        ));
                    }
                    let source = std::fs::read_to_string(&path)
                        .map_err(|e| format!("Cannot read '{}': {e}", path.display()))?;
                    out.push((module, source));
                }
            }
            Ok(())
        }
        let src_root = dir.join("src");
        let mut out = Vec::new();
        walk(&src_root, &src_root, &mut out)?;
        if !out.iter().any(|(m, _)| m == "root") {
            return Err(format!(
                "Package '{}' has no 'src/main.slop' or 'src/lib.slop'",
                dir.display()
            ));
        }
        Ok(out)
    }

    /// Compiles the package rooted at `dir` (see `load_package_dir`) in hosted (`std`) mode.
    pub fn compile_package_dir(dir: &std::path::Path) -> Result<Program, String> {
        let modules = Self::load_package_dir(dir)?;
        let refs: Vec<(&str, &str)> = modules
            .iter()
            .map(|(m, s)| (m.as_str(), s.as_str()))
            .collect();
        Self::compile_package(&refs)
    }

    /// Compiles a multi-module package (`[(module_path, source_code), ...]`) in hosted (`std`) mode,
    /// enforcing module & `struct`-block visibility, specializing `comptime` types/functions,
    /// and running Stage 3 drop elaboration and NLL borrow checking.
    pub fn compile_package(sources: &[(&str, &str)]) -> Result<Program, String> {
        Self::compile_package_with_mode(sources, false)
    }

    /// Compiles a multi-module package in hosted (`std`) mode and returns both the verified Stage 3 `Program`
    /// and the generated C compatible `.h` header for all `export` types and functions.
    pub fn compile_package_with_c_header(
        sources: &[(&str, &str)],
    ) -> Result<(Program, String), String> {
        let compiler = Self::compile_package_compiler(sources, false)?;
        let header = compiler.generate_c_header();
        Ok((compiler.program, header))
    }

    /// Compiles a multi-module package in hosted (`std`) mode and returns the verified Stage 3 `Program`
    /// together with any non-fatal warnings (lints) produced during compilation.
    pub fn compile_package_with_warnings(
        sources: &[(&str, &str)],
    ) -> Result<(Program, Vec<String>), String> {
        Self::compile_package_with_warnings_in(sources, false)
    }

    /// `compile_package_with_warnings`, freestanding (`core` only) when `no_std`.
    pub fn compile_package_with_warnings_in(
        sources: &[(&str, &str)],
        no_std: bool,
    ) -> Result<(Program, Vec<String>), String> {
        let compiler = Self::compile_package_compiler(sources, no_std)?;
        Ok((compiler.program, compiler.warnings))
    }

    /// What `slop check` looks at: the package compiled with its `test` blocks (as `slop test`
    /// compiles it), its warnings, and how many tests it has. It needs no `main`.
    pub fn check_package(
        sources: &[(&str, &str)],
        no_std: bool,
    ) -> Result<(Program, Vec<String>, usize), String> {
        let (program, cases, warnings) = Self::compile_tests_warned(sources, no_std)?;
        Ok((program, warnings, cases.len()))
    }

    /// Compiles a multi-module package (`[(module_path, source_code), ...]`) in freestanding (`no_std` / `core`-only) mode.
    pub fn compile_package_no_std(sources: &[(&str, &str)]) -> Result<Program, String> {
        Self::compile_package_with_mode(sources, true)
    }

    fn compile_package_with_mode(
        sources: &[(&str, &str)],
        no_std: bool,
    ) -> Result<Program, String> {
        Ok(Self::compile_package_compiler(sources, no_std)?.program)
    }

    /// Compiles a package with its `test` blocks, as public functions, and lists them.
    pub fn compile_tests(sources: &[(&str, &str)]) -> Result<(Program, Vec<TestCase>), String> {
        Self::compile_tests_in(sources, false)
    }

    /// `compile_tests`, freestanding (`core` only) when `no_std`.
    pub fn compile_tests_in(sources: &[(&str, &str)], no_std: bool) -> Result<(Program, Vec<TestCase>), String> {
        Self::compile_tests_warned(sources, no_std).map(|(program, cases, _)| (program, cases))
    }

    /// `compile_tests_in`, with the compiler's warnings.
    pub fn compile_tests_warned(
        sources: &[(&str, &str)],
        no_std: bool,
    ) -> Result<(Program, Vec<TestCase>, Vec<String>), String> {
        let compiler = Self::compile_package_compiler_for(sources, no_std, TestBuild::All)?;
        let cases = compiler
            .tests
            .iter()
            .map(|(module, name, func)| {
                let debug = format!("{module}::{func}");
                let id = compiler
                    .program
                    .functions
                    .iter()
                    .find(|f| f.debug_name.as_deref() == Some(debug.as_str()))
                    .map(|f| f.id)
                    .ok_or_else(|| format!("test '{name}' was not compiled"))?;
                Ok(TestCase { module: module.clone(), name: name.clone(), func: id })
            })
            .collect::<Result<_, String>>()?;
        Ok((compiler.program, cases, compiler.warnings))
    }

    /// Compiles a package whose `main` runs its `index`th test (in `compile_tests` order) and
    /// returns 0, for running it natively. The package's own `main`, if any, is kept under
    /// another name.
    pub fn compile_test_entry(sources: &[(&str, &str)], index: usize) -> Result<Program, String> {
        Self::compile_test_entry_in(sources, index, false)
    }

    /// `compile_test_entry`, freestanding when `no_std`.
    pub fn compile_test_entry_in(sources: &[(&str, &str)], index: usize, no_std: bool) -> Result<Program, String> {
        Ok(Self::compile_package_compiler_for(sources, no_std, TestBuild::Entry(index))?.program)
    }

    /// A user module outside `root` (and outside `std` and `core`) is a dependency's, under its
    /// package's name: its own `import root::x` means `import tls::x` for package `tls`, as the
    /// package was written to be the root of its own build.
    fn mount_dependencies(&mut self, sources: &[(&str, &str)]) {
        for &(path, _) in sources {
            let first = path.split("::").next().unwrap_or(path);
            if matches!(first, "root" | "std" | "core") {
                continue;
            }
            self.dependencies.insert(first.to_string());
            if let Some(module) = self.modules.get_mut(path) {
                for imp in &mut module.imports {
                    if imp.path.first().map(String::as_str) == Some("root") {
                        imp.path[0] = first.to_string();
                    }
                }
            }
        }
    }

    /// Leaves the `test` blocks out of an ordinary build, and a dependency's out of any build. A
    /// test build makes each of the root package's a public
    /// function `__slop_test_N` of its module, numbered across the package in module order; for
    /// `Entry(n)` it also gives the root a `main` that runs test `n` and returns 0, keeping the
    /// package's own as `__user_main`.
    fn prepare_tests(&mut self, build: TestBuild) {
        let mut paths: Vec<String> = self.modules.keys().cloned().collect();
        paths.sort();
        for path in paths {
            let module = self.modules.get_mut(&path).unwrap();
            let items = std::mem::take(&mut module.items);
            for item in items {
                let Item::Test { name, body } = item else {
                    module.items.push(item);
                    continue;
                };
                // A dependency's tests are its own build's, not this one's.
                if build == TestBuild::None || !(path == "root" || path.starts_with("root::")) {
                    continue;
                }
                // `__slop_`, so that reflection (`@declarations`) leaves it out.
                let func = format!("__slop_test_{}", self.tests.len());
                module.items.push(Item::Func(FuncDecl {
                    vis: Visibility::Pub,
                    name: func.clone(),
                    params: Vec::new(),
                    ret_ty: TypeExpr::Void,
                    borrows: None,
                    where_clauses: Vec::new(),
                    body,
                    is_unsafe: false,
                    impl_of: None,
                    is_unsafe_impl: false,
                    discardable: false,
                }));
                self.tests.push((path.clone(), name, func));
            }
        }
        let TestBuild::Entry(index) = build else {
            return;
        };
        let Some((module, _, func)) = self.tests.get(index).cloned() else {
            return;
        };
        let Some(root) = self.modules.get_mut("root") else {
            return;
        };
        for item in &mut root.items {
            if let Item::Func(f) = item
                && f.name == "main"
            {
                f.name = "__user_main".to_string();
            }
        }
        let mut path: Vec<String> = module.split("::").map(str::to_string).collect();
        path.push(func);
        root.items.push(Item::Func(FuncDecl {
            vis: Visibility::Pub,
            name: "main".to_string(),
            params: Vec::new(),
            ret_ty: TypeExpr::Int { signed: true, bits: 32 },
            borrows: None,
            where_clauses: Vec::new(),
            body: Block {
                stmts: vec![
                    Stmt::Expr(Expr::Call { callee: Box::new(Expr::Path(path)), ct_args: None, args: Vec::new(), at: crate::ast::At::default() }),
                    Stmt::Return(Some(Expr::Int(0))),
                ],
                lines: Vec::new(),
            },
            is_unsafe: false,
            impl_of: None,
            is_unsafe_impl: false,
            discardable: false,
        }));
    }

    /// Checks every generic in std against its bounds (see `check_generic_bodies`), which
    /// compiling a program skips, std being the same for every program.
    pub fn check_std_generics() -> Result<(), String> {
        let mut compiler =
            Self::compile_package_compiler(&[("root", "pub fn main() -> i32 { return 0; }")], false)?;
        compiler.check_generic_bodies(true)
    }

    fn compile_package_compiler(
        sources: &[(&str, &str)],
        no_std: bool,
    ) -> Result<Self, String> {
        Self::compile_package_compiler_for(sources, no_std, TestBuild::None)
    }

    fn compile_package_compiler_for(
        sources: &[(&str, &str)],
        no_std: bool,
        tests: TestBuild,
    ) -> Result<Self, String> {
        thread_local! {
            static ON_COMPILER_STACK: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
        }
        if ON_COMPILER_STACK.get() {
            return Self::compile_package_compiler_on_stack(sources, no_std, tests);
        }
        // Compile-time evaluation recurses through the compiler (a type function calling a
        // type function nests evaluation, lowering, and the VM): give it a stack deep enough
        // for the evaluation limits (`comptime_depth`) to be what stops runaway recursion.
        std::thread::scope(|scope| {
            std::thread::Builder::new()
                .stack_size(COMPILER_STACK_BYTES)
                .spawn_scoped(scope, || {
                    ON_COMPILER_STACK.set(true);
                    let res = Self::compile_package_compiler_on_stack(sources, no_std, tests);
                    ON_COMPILER_STACK.set(false);
                    res
                })
                .map_err(|e| format!("Cannot start the compiler thread: {e}"))?
                .join()
                .unwrap_or_else(|panic| std::panic::resume_unwind(panic))
        })
    }

    fn compile_package_compiler_on_stack(
        sources: &[(&str, &str)],
        no_std: bool,
        tests: TestBuild,
    ) -> Result<Self, String> {
        static PARSED_CORE_MODULES: std::sync::LazyLock<Vec<(String, ModuleAst)>> =
            std::sync::LazyLock::new(|| {
                crate::stdlib::CORE_MODULES
                    .iter()
                    .map(|&(mod_path, src)| {
                        let ast = SurfaceParser::parse_module(src)
                            .unwrap_or_else(|e| panic!("In bundled module '{mod_path}': {e}"));
                        (mod_path.to_string(), ast)
                    })
                    .collect()
            });
        static PARSED_STD_MODULES: std::sync::LazyLock<Vec<(String, ModuleAst)>> =
            std::sync::LazyLock::new(|| {
                crate::stdlib::STD_MODULES
                    .iter()
                    .map(|&(mod_path, src)| {
                        let ast = SurfaceParser::parse_module(src)
                            .unwrap_or_else(|e| panic!("In bundled module '{mod_path}': {e}"));
                        (mod_path.to_string(), ast)
                    })
                    .collect()
            });

        let mut compiler = Self::new();

        // 1. Load bundled `core` modules (always available) and `std` modules (when `!no_std`)
        for (mod_path, ast) in PARSED_CORE_MODULES.iter() {
            compiler.modules.insert(mod_path.clone(), ast.clone());
        }
        if !no_std {
            for (mod_path, ast) in PARSED_STD_MODULES.iter() {
                compiler.modules.insert(mod_path.clone(), ast.clone());
            }
        }

        // 2. Load user package modules (allowing explicit overrides of any module path)
        for &(mod_path, src) in sources {
            let ast = SurfaceParser::parse_module(src)
                .map_err(|e| format!("In module '{mod_path}': {e}"))?;
            compiler.modules.insert(mod_path.to_string(), ast);
        }
        compiler.prepare_tests(tests);
        compiler.mount_dependencies(sources);

        // The root module's `ProgramExecutor` is what `std::thread` defaults to.
        let has_executor = compiler.modules.get("root").is_some_and(|m| {
            m.items.iter().any(|i| matches!(i, Item::TypeDecl { name, alias: true, .. } if name == "ProgramExecutor"))
        });
        if has_executor
            && let Some(thread) = compiler.modules.get_mut("std::thread")
        {
            for item in &mut thread.items {
                if let Item::TypeDecl { name, ty, .. } = item
                    && name == "DefaultExecutor"
                {
                    *ty = TypeExpr::Named(["root", "ProgramExecutor"].map(str::to_string).to_vec());
                }
            }
        }

        // 2b. Resolve `super::...` import paths against each importing module's parent
        for (mod_path, ast) in &mut compiler.modules {
            for imp in &mut ast.imports {
                if imp.path.first().map(String::as_str) != Some("super") {
                    continue;
                }
                let mut base: Vec<String> = mod_path.split("::").map(str::to_string).collect();
                let mut rest = imp.path.as_slice();
                while rest.first().map(String::as_str) == Some("super") {
                    if base.len() <= 1 {
                        return Err(format!(
                            "In module '{mod_path}': 'super' in import '{}' goes above the package root",
                            imp.path.join("::")
                        ));
                    }
                    base.pop();
                    rest = &rest[1..];
                }
                // `import super;` binds the parent module as `super` (`super::helper()`).
                if rest.is_empty() && imp.targets == ImportTargets::Module(None) {
                    imp.targets = ImportTargets::Module(Some("super".to_string()));
                }
                base.extend(rest.iter().cloned());
                imp.path = base;
            }
        }

        // 3. Inject implicit prelude import (`std::prelude::*` or `core::prelude::*`) into non-stdlib modules
        let prelude_root = if no_std { "core" } else { "std" };
        for (mod_path, ast) in &mut compiler.modules {
            if !crate::stdlib::is_stdlib_module(mod_path) {
                ast.imports.push(ImportDecl {
                    vis: Visibility::Private,
                    path: vec![prelude_root.to_string(), "prelude".to_string()],
                    targets: ImportTargets::Glob,
                    is_prelude: true,
                });
            }
        }

        compiler.compile_all()?;
        compiler.check_nosuspend()?;
        // A function the move checker refused is not borrow checked, but the others are, so
        // one compile reports both kinds of error.
        let failed = crate::drop::elaborate_drops_reporting(&mut compiler.program, 0);
        let borrows = check_borrows_where(&compiler.program, |id| !failed.iter().any(|(f, _)| *f == id));
        let mut errors: Vec<String> = Vec::new();
        for e in failed.into_iter().map(|(_, e)| e).chain(borrows.err()) {
            if !errors.contains(&e) {
                errors.push(e);
            }
        }
        if !errors.is_empty() {
            return Err(errors.join("\nerror: "));
        }
        compiler.check_types_at_run_time()?;
        compiler.check_generic_bodies(false)?;
        Ok(compiler)
    }

    /// Refuses a program whose run-time code calls a function that holds `type` values, which
    /// exist only at compile time: `mk(i32)` outside a `const`, say. Such a function is run only
    /// by the compiler; the VM could run it later as well, but nothing compiled could. Run-time
    /// code is what `main`, an exported function, a test, or a destructor reaches.
    fn check_types_at_run_time(&self) -> Result<(), String> {
        let program = &self.program;
        let by_id: HashMap<FuncId, &Function> = program.functions.iter().map(|f| (f.id, f)).collect();
        let holds_types = |f: &Function| {
            f.locals.iter().any(|t| matches!(program.types.get(t.0 as usize), Some(Type::MetaType)))
        };
        let mut queue: Vec<(FuncId, Option<FuncId>)> = program
            .functions
            .iter()
            .filter(|f| f.export.is_some())
            .map(|f| f.id)
            .chain(program.destructors.iter().map(|&(_, f)| f))
            .chain(self.tests.iter().filter_map(|(module, _, func)| {
                let debug = format!("{module}::{func}");
                program.functions.iter().find(|f| f.debug_name.as_deref() == Some(debug.as_str())).map(|f| f.id)
            }))
            .map(|f| (f, None))
            .collect();
        let mut seen = crate::fasthash::FastSet::default();
        let mut seen_globals = crate::fasthash::FastSet::default();
        while let Some((id, from)) = queue.pop() {
            if !seen.insert(id) {
                continue;
            }
            let Some(func) = by_id.get(&id) else { continue };
            if holds_types(func) {
                let name = func.debug_name.as_deref().unwrap_or("a function");
                let how = match from.and_then(|f| by_id.get(&f)).and_then(|f| f.debug_name.as_deref()) {
                    Some(caller) => format!("is called at run time, by '{caller}'"),
                    None => "runs at run time".to_string(),
                };
                return Err(format!(
                    "'{name}' {how}, but it handles 'type' values, which exist only at compile time (pass a type as a comptime argument, '[T: type]', or use it in a 'const')"
                ));
            }
            let mut consts: Vec<&ConstValue> = Vec::new();
            for block in &func.blocks {
                for stmt in &block.statements {
                    if let Statement::Assign(_, rv) = stmt {
                        consts.extend(crate::drop::rvalue_operands(rv).into_iter().filter_map(op_const));
                    }
                }
                if let Terminator::Call { func: callee, args, .. } = &block.terminator {
                    consts.extend(std::iter::once(callee).chain(args).filter_map(op_const));
                }
            }
            while let Some(c) = consts.pop() {
                match c {
                    ConstValue::Func(f) => queue.push((*f, Some(id))),
                    ConstValue::Aggregate(items) => consts.extend(items),
                    ConstValue::Global(g) => {
                        if seen_globals.insert(*g)
                            && let Some(global) = program.globals.iter().find(|x| x.id == *g)
                        {
                            consts.push(&global.init);
                        }
                    }
                    _ => {}
                }
            }
        }
        Ok(())
    }

    /// The type named by the root module's `alias ProgramAllocator`, which replaces the default
    /// allocator behind `@alloc`, `@realloc`, and `@dealloc` for the whole program.
    fn program_allocator(&mut self) -> Result<Option<TypeId>, String> {
        if let Some(known) = self.program_allocator {
            return Ok(known);
        }
        let found = matches!(self.find_item_in_module("root", "root", "ProgramAllocator"), Ok(Some(_)));
        let allocator = if found {
            let name = TypeExpr::Named(vec!["ProgramAllocator".to_string()]);
            let ty = self.resolve_type_expr("root", None, &HashMap::default(), &name)?;
            let mut env = HashMap::default();
            env.insert("__candidate".to_string(), ComptimeVal::Type(ty));
            let implements = self.eval_satisfies_intrinsic(
                "std::mem",
                None,
                &env,
                &TypeExpr::Named(vec!["__candidate".to_string()]),
                &TypeExpr::Named(vec!["GlobalAllocator".to_string()]),
            );
            if !matches!(implements, Ok(true)) {
                return Err(format!(
                    "'ProgramAllocator' needs a type implementing 'GlobalAllocator', found '{}'",
                    self.type_display_name(ty)
                ));
            }
            Some(ty)
        } else {
            None
        };
        self.program_allocator = Some(allocator);
        Ok(allocator)
    }

    /// The composite `ty`, to change while it is being built.
    fn composite_mut(&mut self, ty: TypeId) -> &mut CompositeInfo {
        std::sync::Arc::make_mut(self.composites.get_mut(&ty).expect("composite was just added"))
    }

    fn warn(&mut self, msg: String) {
        if !self.warnings.contains(&msg) {
            self.warnings.push(msg);
        }
    }

    /// Which side table describes `tid`, if any: the single classification behind nominal
    /// interning, diagnostics, and C names. Checked in priority order for types registered in
    /// more than one table.
    pub(super) fn type_kind(&self, tid: TypeId) -> Option<TypeKind> {
        Some(if self.opaque_ty == Some(tid) {
            TypeKind::UniversalOpaque
        } else if self.slices.contains_key(&tid) {
            TypeKind::Slice
        } else if self.maps.contains_key(&tid) {
            TypeKind::Map
        } else if self.closures.contains_key(&tid) {
            TypeKind::Closure
        } else if self.distinct_types.contains_key(&tid) {
            TypeKind::Distinct
        } else if self.c_ints.contains_key(&tid) {
            TypeKind::CInt
        } else if self.raw_ptrs.contains_key(&tid) {
            TypeKind::RawPtr
        } else if self.composites.contains_key(&tid) || self.named_opaques.contains(&tid) {
            TypeKind::Composite
        } else if self.traits.contains_key(&tid) {
            TypeKind::Trait
        } else if self.trait_objs.contains_key(&tid) {
            TypeKind::TraitObj
        } else if self.enums.contains_key(&tid) {
            TypeKind::Enum
        } else if self.unions.contains_key(&tid) {
            TypeKind::Union
        } else if self.uninit_types.contains_key(&tid) {
            TypeKind::Uninit
        } else if self.overlays.contains_key(&tid) {
            TypeKind::Overlay
        } else if self.errors.contains_key(&tid) {
            TypeKind::Error
        } else if self.results.contains_key(&tid) {
            TypeKind::Result
        } else {
            return None;
        })
    }

    /// Whether `tid` is a nominal type (a side-table type or a fn pointer), which structural
    /// interning must never return.
    fn is_nominal_type(&self, tid: TypeId) -> bool {
        self.type_kind(tid).is_some()
            || matches!(self.program.types[tid.0 as usize], Type::FnPtr { .. })
    }

    /// The structural type equal to `ty`, created on first use. A cached entry that has since been
    /// registered as nominal is replaced by a fresh structural type.
    fn intern_type(&mut self, ty: Type) -> TypeId {
        if let Some(&tid) = self.structural_types.get(&ty)
            && !self.is_nominal_type(tid)
        {
            return tid;
        }
        let id = TypeId(self.program.types.len() as u32);
        self.program.types.push(ty.clone());
        self.structural_types.insert(ty, id);
        id
    }

    fn alloc_distinct_type(&mut self, ty: Type) -> TypeId {
        let id = TypeId(self.program.types.len() as u32);
        self.program.types.push(ty);
        id
    }

    fn intern_c_int_type(&mut self, kind: CIntKind) -> TypeId {
        if let Some(&tid) = self.memoized_c_ints.get(&kind) {
            return tid;
        }
        let (signed, bits) = kind.signed_and_bits();
        let tid = self.alloc_distinct_type(Type::Int { signed, bits });
        self.c_ints.insert(tid, kind);
        self.memoized_c_ints.insert(kind, tid);
        tid
    }

    fn intern_opaque_type(&mut self) -> TypeId {
        if let Some(tid) = self.opaque_ty {
            return tid;
        }
        let tid = self.alloc_distinct_type(Type::Int {
            signed: false,
            bits: 8,
        });
        self.opaque_ty = Some(tid);
        tid
    }

    fn is_opaque_type(&self, ty_id: TypeId) -> bool {
        self.opaque_ty == Some(ty_id) || self.named_opaques.contains(&ty_id)
    }

    fn is_universal_opaque_type(&self, ty_id: TypeId) -> bool {
        self.opaque_ty == Some(ty_id)
    }

    pub(super) fn intern_uninit_type(&mut self, inner_ty: TypeId) -> Result<TypeId, String> {
        if self.is_opaque_type(inner_ty) {
            return Err(format!(
                "Unsized type '{}' cannot be used in 'uninit {}'",
                self.type_display_name(inner_ty),
                self.type_display_name(inner_ty)
            ));
        }
        if let Some(tr) = self.traits.get(&inner_ty) {
            return Err(format!(
                "Trait '{}' is an unsized meta-type constraint and cannot be used in 'uninit {}'",
                tr.name, tr.name
            ));
        }
        if let Some(&existing) = self.memoized_uninit.get(&inner_ty) {
            return Ok(existing);
        }
        let void_ty = self.intern_type(Type::Void);
        let tid = self.alloc_distinct_type(Type::Overlay(vec![void_ty, inner_ty]));
        self.uninit_types.insert(tid, inner_ty);
        self.memoized_uninit.insert(inner_ty, tid);
        Ok(tid)
    }

    pub(super) fn is_uninit_compatible_type(&self, ty_id: TypeId) -> bool {
        if self.uninit_types.contains_key(&ty_id) {
            return true;
        }
        match &self.program.types[ty_id.0 as usize] {
            Type::Overlay(fields) => fields
                .first()
                .is_some_and(|&f0| matches!(self.program.types[f0.0 as usize], Type::Void)),
            Type::Array { elem, .. } => self.is_uninit_compatible_type(*elem),
            _ => false,
        }
    }

    /// Interns a function-pointer type carrying `contract`. Types that differ only in their borrow
    /// contract (or in being `unsafe fn`) are distinct; contracts are canonicalized so equal
    /// contracts share one `TypeId`.
    fn intern_fn_ptr_type(
        &mut self,
        args: Vec<TypeId>,
        ret: TypeId,
        contract: FnContract,
        is_unsafe: bool,
    ) -> TypeId {
        let mut contract = contract;
        contract.ret.sort();
        contract.ret.dedup();
        contract.flows.sort();
        contract.flows.dedup();
        let key = (args.clone(), ret, contract.clone(), is_unsafe);
        if let Some(&tid) = self.memoized_fn_ptrs.get(&key) {
            return tid;
        }
        let tid = self.alloc_distinct_type(Type::FnPtr { args, ret });
        self.program.fn_ptr_contracts.push((tid, contract));
        if is_unsafe {
            self.unsafe_fn_ptr_types.insert(tid);
        }
        self.memoized_fn_ptrs.insert(key, tid);
        tid
    }

    /// The contract a function value gets when its own contract is not yet known (private functions
    /// are inferred later): the return may borrow from every reference-carrying parameter, and no
    /// parameter-to-parameter flows are permitted. Stage 3c checks the function against it.
    fn default_fn_contract(&self, args: &[TypeId], ret: TypeId) -> FnContract {
        let ret_list = if self.type_contains_safe_ref(ret) {
            args.iter()
                .enumerate()
                .filter(|(_, t)| self.type_contains_safe_ref(**t))
                .map(|(i, _)| LocalId((i + 1) as u32))
                .collect()
        } else {
            Vec::new()
        };
        FnContract {
            ret: ret_list,
            flows: Vec::new(),
        }
    }

    /// The function-pointer type of a function value (`let f = helper;`, non-capturing lambdas).
    /// The C-calling-convention function pointer type `extern fn(args) -> ret`: distinct from the
    /// SlopLang `fn(args) -> ret`, so the two never convert into each other.
    pub(super) fn intern_c_fn_ptr_type(
        &mut self,
        args: Vec<TypeId>,
        ret: TypeId,
        is_unsafe: bool,
    ) -> TypeId {
        let key = (args.clone(), ret, is_unsafe);
        if let Some(&t) = self.memoized_c_fn_ptrs.get(&key) {
            return t;
        }
        let t = self.alloc_distinct_type(Type::FnPtr { args, ret });
        self.program.c_fn_ptr_types.push(t);
        if is_unsafe {
            self.unsafe_fn_ptr_types.insert(t);
        }
        self.memoized_c_fn_ptrs.insert(key, t);
        t
    }

    fn fn_value_ptr_type(&mut self, args: Vec<TypeId>, ret: TypeId, is_unsafe: bool) -> TypeId {
        let contract = self.default_fn_contract(&args, ret);
        self.intern_fn_ptr_type(args, ret, contract, is_unsafe)
    }

    /// The function-pointer type a function value gets when named (`let f = helper;`): an
    /// `extern fn` uses the C convention, and an `unsafe fn` gives an `unsafe` pointer type.
    pub(super) fn named_fn_ptr_type(&mut self, fn_id: FuncId) -> TypeId {
        let (args, ret) = self.func_sigs[&fn_id].clone();
        if self.program.externs.iter().any(|e| e.id == fn_id) {
            // The declaration is not known here, so a C function value is conservatively unsafe.
            self.intern_c_fn_ptr_type(args, ret, true)
        } else {
            let is_unsafe = self.unsafe_fns.contains(&fn_id);
            self.fn_value_ptr_type(args, ret, is_unsafe)
        }
    }

    pub(super) fn fn_ptr_contract(&self, ty: TypeId) -> Option<&FnContract> {
        self.program
            .fn_ptr_contracts
            .iter()
            .find(|(t, _)| *t == ty)
            .map(|(_, c)| c)
    }

    fn intern_raw_ptr_type(&mut self, mutable: bool, pointee: TypeId) -> TypeId {
        self.intern_kind_ptr_type(PtrKind::Raw, mutable, pointee)
    }

    /// Interns an unchecked pointer type of `kind`. All kinds share the raw-pointer rules
    /// (`unsafe` dereference, arithmetic, nullability) and differ in what they confer on a type
    /// that contains them.
    pub(super) fn intern_kind_ptr_type(
        &mut self,
        kind: PtrKind,
        mutable: bool,
        pointee: TypeId,
    ) -> TypeId {
        if let Some((&tid, _)) = self.raw_ptrs.iter().find(|(t, (m, p))| {
            *m == mutable && *p == pointee && self.ptr_kind(**t) == Some(kind)
        }) {
            return tid;
        }
        let tid = self.alloc_distinct_type(Type::Ptr { mutable, pointee });
        self.raw_ptrs.insert(tid, (mutable, pointee));
        self.program.raw_ptr_types.push(tid);
        match kind {
            PtrKind::Raw => {}
            PtrKind::Own => self.program.own_ptr_types.push(tid),
            PtrKind::View => self.program.view_ptr_types.push(tid),
        }
        if kind != PtrKind::Raw {
            self.ptr_kinds.insert(tid, kind);
        }
        tid
    }

    /// The kind of an unchecked pointer type, or `None` for any other type.
    pub(super) fn ptr_kind(&self, ty: TypeId) -> Option<PtrKind> {
        self.raw_ptrs
            .contains_key(&ty)
            .then(|| self.ptr_kinds.get(&ty).copied().unwrap_or(PtrKind::Raw))
    }

    fn intern_slice_type(&mut self, mutable: bool, elem: TypeId) -> TypeId {
        if let Some((&tid, _)) = self
            .slices
            .iter()
            .find(|(_, info)| info.mutable == mutable && info.elem == elem && !info.is_str)
        {
            return tid;
        }
        let arr0_ty = self.intern_type(Type::Array { elem, len: 0 });
        let ptr_ty = self.intern_type(Type::Ptr {
            mutable,
            pointee: arr0_ty,
        });
        let usize_ty = self.intern_type(Type::Int {
            signed: false,
            bits: 64,
        });
        let slice_ty = self.alloc_distinct_type(Type::Struct(vec![ptr_ty, usize_ty]));
        self.slices.insert(
            slice_ty,
            SliceInfo {
                mutable,
                elem,
                ptr_ty,
                is_str: false,
            },
        );
        slice_ty
    }

    fn intern_str_type(&mut self) -> TypeId {
        if let Some((&tid, _)) = self.slices.iter().find(|(_, info)| info.is_str) {
            return tid;
        }
        let u8_id = self.intern_type(Type::Int {
            signed: false,
            bits: 8,
        });
        let arr0_ty = self.intern_type(Type::Array {
            elem: u8_id,
            len: 0,
        });
        let ptr_ty = self.intern_type(Type::Ptr {
            mutable: false,
            pointee: arr0_ty,
        });
        let usize_ty = self.intern_type(Type::Int {
            signed: false,
            bits: 64,
        });
        let str_ty = self.alloc_distinct_type(Type::Struct(vec![ptr_ty, usize_ty]));
        self.slices.insert(
            str_ty,
            SliceInfo {
                mutable: false,
                elem: u8_id,
                ptr_ty,
                is_str: true,
            },
        );
        str_ty
    }

    fn compile_all(&mut self) -> Result<(), String> {
        let mod_names: Vec<String> = self
            .modules
            .keys()
            .filter(|m| !crate::stdlib::is_stdlib_module(m))
            .cloned()
            .collect();

        // 1. Register extern functions in user modules (stdlib externs are registered on demand)
        for mod_path in &mod_names {
            let items = self.modules[mod_path].items.clone();
            for item in items {
                if let Item::ExternFunc(ext) = item {
                    self.register_extern(mod_path, &ext)?;
                }
            }
        }

        // 2. Register concrete top-level types (`struct`, `opaque`, `type`) in user modules
        for mod_path in &mod_names {
            let items = self.modules[mod_path].items.clone();
            for item in items {
                if let Item::TypeDecl { name, .. } = item {
                    let _ = self.resolve_named_type(mod_path, &name)?;
                }
            }
        }

        // 2b. Register top-level `const`/`comptime` and `static`/`static mut` declarations in user modules
        for mod_path in &mod_names {
            let items = self.modules[mod_path].items.clone();
            for item in items {
                match item {
                    Item::Const(cdecl) => {
                        let _ = self.resolve_top_const(mod_path, &cdecl.name)?;
                    }
                    Item::Static(sdecl) => {
                        let _ = self.resolve_top_static(mod_path, &sdecl.name)?;
                    }
                    _ => {}
                }
            }
        }

        // 3. Register non-comptime top-level functions in user modules
        for mod_path in &mod_names {
            let items = self.modules[mod_path].items.clone();
            for item in items {
                if let Item::Func(fdecl) = item {
                    if fdecl.vis.is_export() && fdecl.params.iter().any(|p| p.is_comptime) {
                        return Err(format!(
                            "Exported function '{}' cannot have 'comptime' parameters; 'export fn' requires a concrete C ABI signature",
                            fdecl.name
                        ));
                    }
                    if !fdecl.params.iter().any(|p| p.is_comptime)
                        && fdecl.ret_ty != TypeExpr::MetaType
                    {
                        let _ = self.instantiate_specific_func_decl(mod_path, &fdecl, &[])?;
                    }
                }
            }
        }

        // 4. Process worklist of all pending functions and methods until empty
        self.lower_pending_funcs_collecting()?;

        Ok(())
    }

    /// Lowers every queued function body not yet lowered. Re-entrant: compile-time evaluation
    /// lowers its callees through this as well, and the shared cursor keeps each body lowered once.
    fn lower_pending_funcs(&mut self) -> Result<(), String> {
        while self.pending_cursor < self.pending_funcs.len() {
            let pending = self.pending_funcs[self.pending_cursor].clone();
            self.pending_cursor += 1;
            if !self.body_missing(pending.func_id) {
                continue;
            }
            if self.must_hold(&pending) {
                self.held_funcs.push(pending);
                continue;
            }
            self.lower_function_body(pending)?;
        }
        Ok(())
    }

    /// `lower_pending_funcs`, going on past a function whose body is refused, so one compile
    /// reports what is wrong in each (up to `MAX_ERRORS`). A call is checked against the
    /// callee's signature, not its body, so one bad body does not make its callers' fail.
    /// Compile-time evaluation within a body still stops at the first error, as it needs what
    /// it calls.
    fn lower_pending_funcs_collecting(&mut self) -> Result<(), String> {
        const MAX_ERRORS: usize = 20;
        let mut errors: Vec<String> = Vec::new();
        let mut failures = 0;
        while self.pending_cursor < self.pending_funcs.len() {
            let pending = self.pending_funcs[self.pending_cursor].clone();
            self.pending_cursor += 1;
            if !self.body_missing(pending.func_id) {
                continue;
            }
            if self.must_hold(&pending) {
                self.held_funcs.push(pending);
                continue;
            }
            if let Err(e) = self.lower_function_body(pending) {
                failures += 1;
                if !errors.contains(&e) {
                    errors.push(e);
                }
                // Every failure counts, repeated ones too: a type that cannot be built is given
                // up and fails again in each function that names it.
                if failures >= MAX_ERRORS {
                    break;
                }
            }
        }
        if errors.is_empty() {
            return Ok(());
        }
        // `slop` writes `error: ` before the whole; each further one gets its own.
        Err(errors.join("\nerror: "))
    }

    /// Whether the body of `func` waits for the types being built, which any function can
    /// name. A destructor of a finished type is run by compile-time code that drops a value.
    fn must_hold(&self, func: &PendingFunc) -> bool {
        self.types_are_unfinished()
            && (func.owner_ty.is_none_or(|t| self.type_is_unfinished(t))
                || !self.program.destructors.iter().any(|(_, f)| *f == func.func_id))
    }

    /// Rejects a `nosuspend` block that can wait: one that reaches, through the calls and drops
    /// it makes, a point where a fiber parks (`std::sync::switch_fiber`) or a thread blocks in C
    /// (`WAITING_EXTERNS`). A call through a function value may reach anything, so it counts too.
    fn check_nosuspend(&self) -> Result<(), String> {
        let mut known: HashMap<FuncId, Option<Vec<String>>> = HashMap::default();
        for &(func_id, block) in &self.nosuspend_sites {
            let Some(func) = self.program.functions.iter().find(|f| f.id == func_id) else {
                continue;
            };
            let name = func.debug_name.clone().unwrap_or_else(|| func_id.to_string());
            let waits = match &func.blocks[block.0 as usize].terminator {
                Terminator::Call { func: Operand::Const(ConstValue::Func(callee)), .. } => {
                    self.wait_path(*callee, &mut known, &mut Vec::new())
                }
                Terminator::Call { .. } => Some(vec!["a call through a function value".to_string()]),
                Terminator::Drop { place, .. } => {
                    let ty = crate::drop::place_type(&self.program, func, place)?;
                    self.drop_wait_path(ty, &mut known)
                }
                _ => None,
            };
            if let Some(path) = waits {
                return Err(format!(
                    "'nosuspend' block in {name} can wait: {}",
                    path.join(" -> ")
                ));
            }
        }
        Ok(())
    }

    /// How dropping a `ty` can wait, if it can: through a destructor of it or of a part.
    fn drop_wait_path(
        &self,
        ty: TypeId,
        known: &mut HashMap<FuncId, Option<Vec<String>>>,
    ) -> Option<Vec<String>> {
        let mut parts = vec![ty];
        let mut seen = Vec::new();
        while let Some(t) = parts.pop() {
            if seen.contains(&t) {
                continue;
            }
            seen.push(t);
            if let Some((_, dtor)) = self.program.destructors.iter().find(|(d, _)| *d == t)
                && let Some(path) = self.wait_path(*dtor, known, &mut Vec::new())
            {
                return Some(path);
            }
            match &self.program.types[t.0 as usize] {
                Type::Struct(fields) => parts.extend(fields),
                Type::Union { variants, .. } => parts.extend(variants),
                Type::Array { elem, .. } => parts.push(*elem),
                _ => {}
            }
        }
        None
    }

    /// The calls by which `f` can wait, ending where it does, if it can.
    fn wait_path(
        &self,
        f: FuncId,
        known: &mut HashMap<FuncId, Option<Vec<String>>>,
        visiting: &mut Vec<FuncId>,
    ) -> Option<Vec<String>> {
        if let Some(found) = known.get(&f) {
            return found.clone();
        }
        if visiting.contains(&f) {
            return None;
        }
        if let Some(ext) = self.program.externs.iter().find(|e| e.id == f) {
            let waits = WAITING_EXTERNS.contains(&ext.symbol.as_str());
            return waits.then(|| vec![ext.symbol.clone()]);
        }
        let func = self.program.functions.iter().find(|g| g.id == f)?;
        let name = func.debug_name.clone().unwrap_or_else(|| f.to_string());
        if name == "std::sync::switch_fiber" {
            return Some(vec![name]);
        }
        visiting.push(f);
        let mut found = None;
        for block in &func.blocks {
            let tail = match &block.terminator {
                Terminator::Call { func: Operand::Const(ConstValue::Func(callee)), .. } => {
                    self.wait_path(*callee, known, visiting)
                }
                Terminator::Call { .. } => Some(vec!["a call through a function value".to_string()]),
                Terminator::Drop { place, .. } => crate::drop::place_type(&self.program, func, place)
                    .ok()
                    .and_then(|ty| self.drop_wait_path(ty, known)),
                _ => None,
            };
            if let Some(tail) = tail {
                found = Some(std::iter::once(name.clone()).chain(tail).collect());
                break;
            }
        }
        visiting.pop();
        known.insert(f, found.clone());
        found
    }

    /// Lowers what compile-time code `root` needs, and only that: the functions it reaches
    /// through calls, function values (closures and vtables are built from them), and drops. The
    /// rest of the queue waits, so that lowering one function does not, through compile-time code
    /// inside it, lower another that needs the first.
    fn lower_for_comptime(&mut self, root: FuncId) -> Result<(), String> {
        let mut seen = vec![root];
        let mut work = vec![root];
        while let Some(f) = work.pop() {
            if self.body_missing(f) {
                if self.lowering_funcs.contains(&f) {
                    let name = self
                        .program
                        .functions
                        .iter()
                        .find(|g| g.id == f)
                        .and_then(|g| g.debug_name.clone())
                        .unwrap_or_else(|| f.to_string());
                    return Err(format!(
                        "'{name}' is needed at compile time while it is itself being compiled"
                    ));
                }
                let entry = match self.held_funcs.iter().position(|p| p.func_id == f) {
                    Some(at) => Some(self.held_funcs.remove(at)),
                    None => self.pending_funcs[self.pending_cursor..]
                        .iter()
                        .find(|p| p.func_id == f)
                        .cloned(),
                };
                if let Some(entry) = entry {
                    self.lower_function_body(entry)?;
                }
            }
            let Some(body) = self.program.functions.iter().find(|g| g.id == f) else {
                continue;
            };
            let mut reached = Vec::new();
            for block in &body.blocks {
                for statement in &block.statements {
                    let Statement::Assign(_, rvalue) = statement else {
                        continue;
                    };
                    let operands: Vec<&Operand> = match rvalue {
                        Rvalue::Use(op) | Rvalue::Cast(op, _) => vec![op],
                        Rvalue::Aggregate(_, ops) => ops.iter().collect(),
                        _ => Vec::new(),
                    };
                    for op in operands {
                        if let Operand::Const(c) = op {
                            Self::funcs_in_const(c, &mut reached);
                        }
                    }
                }
                match &block.terminator {
                    Terminator::Call { func, args, .. } => {
                        for operand in std::iter::once(func).chain(args) {
                            if let Operand::Const(c) = operand {
                                Self::funcs_in_const(c, &mut reached);
                            }
                        }
                    }
                    Terminator::Drop { .. } => {
                        reached.extend(self.program.destructors.iter().map(|(_, d)| *d));
                    }
                    _ => {}
                }
            }
            for g in reached {
                if !seen.contains(&g) {
                    seen.push(g);
                    work.push(g);
                }
            }
        }
        Ok(())
    }

    /// The functions a constant names, as a function value or inside an aggregate.
    fn funcs_in_const(c: &ConstValue, out: &mut Vec<FuncId>) {
        match c {
            ConstValue::Func(f) => out.push(*f),
            ConstValue::Aggregate(items) => {
                for item in items {
                    Self::funcs_in_const(item, out);
                }
            }
            _ => {}
        }
    }

    /// Whether `f` is a function whose body has not been lowered.
    fn body_missing(&self, f: FuncId) -> bool {
        self.program.functions.iter().any(|g| g.id == f && g.blocks.is_empty())
    }

    fn register_extern(&mut self, mod_path: &str, ext: &ExternFuncDecl) -> Result<FuncId, String> {
        let key = (mod_path.to_string(), ext.name.clone());
        if let Some(&id) = self.resolved_externs.get(&key) {
            return Ok(id);
        }
        let env = HashMap::default();
        let mut arg_tys = Vec::new();
        for (pname, pty) in &ext.params {
            let p_id = self.resolve_type_expr(mod_path, None, &env, pty)?;
            self.reject_owned_across_ffi(
                p_id,
                &format!("parameter '{pname}' of extern function '{}'", ext.name),
            )?;
            if self.is_opaque_type(p_id) {
                return Err(format!(
                    "Unsized type 'opaque' cannot be passed by value in parameter '{}' of extern function '{}'; use '*const opaque', '*mut opaque', '&opaque', or '&mut opaque'",
                    pname, ext.name
                ));
            }
            arg_tys.push(p_id);
        }
        let ret_ty = self.resolve_type_expr(mod_path, None, &env, &ext.ret_ty)?;
        self.reject_owned_across_ffi(
            ret_ty,
            &format!("the return type of extern function '{}'", ext.name),
        )?;
        if self.is_opaque_type(ret_ty) {
            return Err(format!(
                "Unsized type 'opaque' cannot be returned by value from extern function '{}'; use '*const opaque', '*mut opaque', '&opaque', or '&mut opaque'",
                ext.name
            ));
        }
        if let Some(existing) = self.program.externs.iter().find(|e| e.symbol == ext.name) {
            let fn_id = existing.id;
            if ext.is_safe {
                self.safe_externs.insert(key.clone());
            }
            self.resolved_externs.insert(key, fn_id);
            return Ok(fn_id);
        }
        let fn_id = FuncId((self.program.externs.len() + self.program.functions.len()) as u32);
        self.program.externs.push(ExternFunc {
            id: fn_id,
            args: arg_tys.clone(),
            ret: ret_ty,
            symbol: ext.name.clone(),
        });
        if ext.is_safe {
            self.safe_externs.insert(key.clone());
        }
        self.resolved_externs.insert(key, fn_id);
        self.func_sigs.insert(fn_id, (arg_tys, ret_ty));
        Ok(fn_id)
    }

    fn get_or_register_extern(&mut self, mod_path: &str, name: &str) -> Result<FuncId, String> {
        let key = (mod_path.to_string(), name.to_string());
        if let Some(&id) = self.resolved_externs.get(&key) {
            return Ok(id);
        }
        let Some((def_mod, _, item, _)) = self.find_item_in_module(mod_path, mod_path, name)?
        else {
            return Err(format!(
                "Extern function '{name}' not found in '{mod_path}'"
            ));
        };
        let Item::ExternFunc(ext) = item else {
            return Err(format!(
                "Extern function '{name}' not found in '{mod_path}'"
            ));
        };
        let ext = ext.clone();
        let fn_id = self.register_extern(&def_mod, &ext)?;
        self.resolved_externs.insert(key, fn_id);
        Ok(fn_id)
    }

    pub(super) fn get_or_register_builtin_extern(
        &mut self,
        symbol: &str,
        args: Vec<TypeId>,
        ret: TypeId,
    ) -> FuncId {
        if let Some(existing) = self.program.externs.iter().find(|e| e.symbol == symbol) {
            return existing.id;
        }
        let fn_id = FuncId((self.program.externs.len() + self.program.functions.len()) as u32);
        self.program.externs.push(ExternFunc {
            id: fn_id,
            args: args.clone(),
            ret,
            symbol: symbol.to_string(),
        });
        self.func_sigs.insert(fn_id, (args, ret));
        fn_id
    }

    pub(super) fn sized_type_layout(
        &self,
        ty_id: TypeId,
        context: &str,
    ) -> Result<(u64, u64), String> {
        if self.is_opaque_type(ty_id) {
            return Err(format!(
                "Cannot use unsized opaque type '{}' in {context}",
                self.type_display_name(ty_id)
            ));
        }
        if let Some(tr) = self.traits.get(&ty_id) {
            return Err(format!(
                "Cannot use unsized trait type '{}' in {context}",
                tr.name
            ));
        }
        self.program.type_size_align(ty_id)
    }

    fn check_item_visibility(
        &self,
        from_mod: &str,
        target_mod: &str,
        item_name: &str,
        vis: Visibility,
    ) -> Result<(), String> {
        if from_mod != target_mod && vis == Visibility::Private {
            return Err(format!(
                "Item '{item_name}' in module '{target_mod}' is private and cannot be accessed from '{from_mod}'"
            ));
        }
        Ok(())
    }

    fn find_item_in_module(
        &self,
        from_mod: &str,
        target_mod: &str,
        name: &str,
    ) -> Result<Option<(String, String, Item, Visibility)>, String> {
        Ok(self
            .find_item_ref_in_module(from_mod, target_mod, name)?
            .map(|(m, n, item, vis)| (m, n, item.clone(), vis)))
    }

    fn find_item_ref_in_module(
        &self,
        from_mod: &str,
        target_mod: &str,
        name: &str,
    ) -> Result<Option<(String, String, &Item, Visibility)>, String> {
        let Some(ast) = self.modules.get(target_mod) else {
            return Err(format!("Undefined module '{target_mod}'"));
        };
        for item in &ast.items {
            match item {
                Item::Func(f) if f.name == name => {
                    self.check_item_visibility(from_mod, target_mod, name, f.vis)?;
                    return Ok(Some((
                        target_mod.to_string(),
                        f.name.clone(),
                        item,
                        f.vis,
                    )));
                }
                Item::ExternFunc(e) if e.name == name => {
                    self.check_item_visibility(from_mod, target_mod, name, e.vis)?;
                    return Ok(Some((
                        target_mod.to_string(),
                        e.name.clone(),
                        item,
                        e.vis,
                    )));
                }
                Item::TypeDecl {
                    vis, name: tname, ..
                } if tname == name => {
                    self.check_item_visibility(from_mod, target_mod, name, *vis)?;
                    return Ok(Some((
                        target_mod.to_string(),
                        tname.clone(),
                        item,
                        *vis,
                    )));
                }
                Item::Static(s) if s.name == name => {
                    self.check_item_visibility(from_mod, target_mod, name, s.vis)?;
                    return Ok(Some((
                        target_mod.to_string(),
                        s.name.clone(),
                        item,
                        s.vis,
                    )));
                }
                Item::Const(c) if c.name == name => {
                    self.check_item_visibility(from_mod, target_mod, name, c.vis)?;
                    return Ok(Some((
                        target_mod.to_string(),
                        c.name.clone(),
                        item,
                        c.vis,
                    )));
                }
                _ => {}
            }
        }
        // Check `pub import` re-exports
        for imp in &ast.imports {
            if imp.vis == Visibility::Private {
                continue;
            }
            let imp_mod = imp.path.join("::");
            match &imp.targets {
                ImportTargets::Items(items) => {
                    for (orig, alias) in items {
                        let bound = alias.as_deref().unwrap_or(orig);
                        if bound == name {
                            return self.find_item_ref_in_module(target_mod, &imp_mod, orig);
                        }
                    }
                }
                ImportTargets::Glob => {
                    if let Some(found) = self.find_item_ref_in_module(target_mod, &imp_mod, name)? {
                        return Ok(Some(found));
                    }
                }
                ImportTargets::Module(alias) => {
                    if !self.modules.contains_key(&imp_mod) && imp.path.len() >= 2 {
                        let parent_mod = imp.path[..imp.path.len() - 1].join("::");
                        let orig = imp.path.last().unwrap();
                        let bound = alias.as_deref().unwrap_or(orig);
                        if bound == name {
                            return self.find_item_ref_in_module(target_mod, &parent_mod, orig);
                        }
                    }
                }
            }
        }
        Ok(None)
    }

    pub(super) fn intern_map_type(&mut self, key_ty: TypeId, val_ty: TypeId) -> TypeId {
        if let Some(&tid) = self.memoized_maps.get(&(key_ty, val_ty)) {
            return tid;
        }
        let tid = self.alloc_distinct_type(Type::Int {
            signed: false,
            bits: 8,
        });
        self.maps.insert(tid, MapTypeInfo { key_ty, val_ty });
        self.memoized_maps.insert((key_ty, val_ty), tid);
        tid
    }

    pub(super) fn expand_module_path(
        &self,
        env: &HashMap<String, ComptimeVal>,
        path: &[String],
    ) -> Vec<String> {
        if !path.is_empty()
            && let Some(ComptimeVal::Module(m)) = env.get(&path[0])
        {
            let mut out: Vec<String> = m.split("::").map(String::from).collect();
            out.extend_from_slice(&path[1..]);
            return out;
        }
        path.to_vec()
    }

    /// `F[T]` parses as an index; when `F` names a function rather than a comptime value, it is
    /// the type-function call `F[T]`.
    pub(super) fn index_as_type_call(
        &self,
        mod_path: &str,
        env: &HashMap<String, ComptimeVal>,
        expr: &Expr,
    ) -> Option<Expr> {
        let Expr::Index { base, index } = expr else {
            return None;
        };
        let Expr::Path(path) = base.as_ref() else {
            return None;
        };
        if env
            .get(&path[0])
            .is_some_and(|v| !matches!(v, ComptimeVal::Module(_)))
        {
            return None;
        }
        let expanded = self.expand_module_path(env, path);
        matches!(
            self.resolve_path(mod_path, &expanded),
            Ok(ResolvedItem::Func(..))
        )
        .then(|| {
            Expr::TypeVal(TypeExpr::TypeCall {
                path: path.clone(),
                args: vec![(**index).clone()],
            })
        })
    }

    fn resolve_path(&self, cur_mod: &str, path: &[String]) -> Result<ResolvedItem, String> {
        // In a dependency's module, `root::x` is that package's `x`.
        let package = cur_mod.split("::").next().unwrap_or(cur_mod);
        if path.len() >= 2 && path[0] == "root" && self.dependencies.contains(package) {
            let mut mapped = path.to_vec();
            mapped[0] = package.to_string();
            return self.resolve_path(cur_mod, &mapped);
        }
        let item_to_resolved = |def_mod: String, orig_name: String, item: &Item| match item {
            Item::Func(_) => ResolvedItem::Func(def_mod, orig_name),
            Item::ExternFunc(_) => ResolvedItem::ExternFunc(def_mod, orig_name),
            Item::TypeDecl { .. } => ResolvedItem::Type(def_mod, orig_name),
            Item::Static(_) => ResolvedItem::Static(def_mod, orig_name),
            Item::Const(_) => ResolvedItem::Const(def_mod, orig_name),
            Item::Impl(_) | Item::Test { .. } => unreachable!("'impl' and 'test' blocks are not named module items"),
        };
        if path.len() == 1 {
            let name = &path[0];
            // 1. Local module item
            if let Some((def_mod, orig_name, item, _)) =
                self.find_item_ref_in_module(cur_mod, cur_mod, name)?
            {
                return Ok(item_to_resolved(def_mod, orig_name, item));
            }
            // 2. Imported item or module (explicit imports checked before prelude imports)
            let ast = &self.modules[cur_mod];
            for check_prelude in [false, true] {
                for imp in &ast.imports {
                    if imp.is_prelude != check_prelude {
                        continue;
                    }
                    let target_mod = imp.path.join("::");
                    match &imp.targets {
                        ImportTargets::Module(alias) => {
                            let orig = imp.path.last().map(String::as_str).unwrap_or("");
                            let bound = alias.as_deref().unwrap_or(orig);
                            if bound == name {
                                if self.modules.contains_key(&target_mod) {
                                    return Ok(ResolvedItem::Module(target_mod));
                                } else if imp.path.len() >= 2 {
                                    let parent_mod = imp.path[..imp.path.len() - 1].join("::");
                                    let Some((def_mod, orig_name, item, _)) =
                                        self.find_item_ref_in_module(cur_mod, &parent_mod, orig)?
                                    else {
                                        return Err(format!(
                                            "Item '{orig}' not found in module '{parent_mod}'"
                                        ));
                                    };
                                    return Ok(item_to_resolved(def_mod, orig_name, item));
                                }
                            }
                        }
                        ImportTargets::Items(list) => {
                            for (orig, alias) in list {
                                let bound = alias.as_deref().unwrap_or(orig);
                                if bound == name {
                                    let Some((def_mod, orig_name, item, _)) =
                                        self.find_item_ref_in_module(cur_mod, &target_mod, orig)?
                                    else {
                                        return Err(format!(
                                            "Item '{orig}' not found in module '{target_mod}'"
                                        ));
                                    };
                                    return Ok(item_to_resolved(def_mod, orig_name, item));
                                }
                            }
                        }
                        ImportTargets::Glob => {
                            if let Some((def_mod, orig_name, item, _)) =
                                self.find_item_ref_in_module(cur_mod, &target_mod, name)?
                            {
                                return Ok(item_to_resolved(def_mod, orig_name, item));
                            }
                        }
                    }
                }
            }
            Err(format!("Undefined symbol '{name}' in module '{cur_mod}'"))
        } else {
            // Multi-segment path: `mod::item`, `root::sub::item`, or `Type::NestedType`
            let item_name = path.last().unwrap();
            let prefix = &path[..path.len() - 1];
            let prefix_joined = prefix.join("::");
            let target_mod = if self.modules.contains_key(&prefix_joined) {
                prefix_joined
            } else {
                match self.resolve_path(cur_mod, prefix) {
                    Ok(ResolvedItem::Module(m)) => m,
                    Ok(ResolvedItem::Const(def_mod, cname)) => {
                        if let Some((_, _, ComptimeVal::Module(m), _)) =
                            self.resolved_consts.get(&(def_mod, cname))
                        {
                            m.clone()
                        } else {
                            prefix_joined
                        }
                    }
                    Ok(ResolvedItem::Type(def_mod, tname)) => {
                        let nested_name = format!("{tname}::{item_name}");
                        if let Some((dmod, oname, item, _)) =
                            self.find_item_ref_in_module(cur_mod, &def_mod, &nested_name)?
                        {
                            return Ok(item_to_resolved(dmod, oname, item));
                        }
                        prefix_joined
                    }
                    _ => prefix_joined,
                }
            };
            let Some((def_mod, orig_name, item, _)) =
                self.find_item_ref_in_module(cur_mod, &target_mod, item_name)?
            else {
                return Err(format!(
                    "Item '{item_name}' not found in module '{target_mod}'"
                ));
            };
            Ok(item_to_resolved(def_mod, orig_name, item))
        }
    }

    /// Evaluates a pure `comptime` `package.slop` manifest (`pub fn package[target: Target]() -> Package`)
    /// inside the sandboxed Stage 3 VM (`Vm::eval`).
    pub fn evaluate_package_manifest(
        manifest_src: &str,
        target_os: &str,
        target_arch: &str,
    ) -> Result<EvaluatedPackage, String> {
        Self::evaluate_package_manifest_for(manifest_src, target_os, target_arch, "Debug")
    }

    /// `evaluate_package_manifest` for a build in `optimize` mode (`Debug`, `ReleaseSafe`,
    /// `ReleaseFast`, or `ReleaseSmall`).
    pub fn evaluate_package_manifest_for(
        manifest_src: &str,
        target_os: &str,
        target_arch: &str,
        optimize: &str,
    ) -> Result<EvaluatedPackage, String> {
        let wrapper_src = format!(
            "{manifest_src}\n\npub fn __slop_eval_package_manifest() -> std::build::Package {{\n    return package[std::build::Target {{\n        os: std::build::Target::Os::{target_os},\n        arch: std::build::Target::Arch::{target_arch},\n        optimize: std::build::OptimizeMode::{optimize},\n    }}]();\n}}\n"
        );
        let mut compiler = Self::compile_package_compiler(&[("root", &wrapper_src)], false)?;
        let fn_id = compiler
            .resolved_funcs
            .get(&(
                "root".to_string(),
                "__slop_eval_package_manifest".to_string(),
                Vec::new(),
            ))
            .copied()
            .ok_or_else(|| "Manifest evaluation wrapper not found".to_string())?;
        let mut vm = crate::vm::Vm::new(&mut compiler.program);
        let pkg_val = vm.eval_call(fn_id, Vec::new())?;
        let crate::vm::Value::Struct { fields, .. } = pkg_val else {
            return Err(format!(
                "Expected Package struct from package(), got {pkg_val:?}"
            ));
        };
        if fields.len() != 6 {
            return Err(format!(
                "Expected 6 fields in std::build::Package, got {}",
                fields.len()
            ));
        }
        let extract_str = |v: &crate::vm::Value| -> Result<String, String> {
            match v {
                crate::vm::Value::Str(s) => Ok(s.clone()),
                crate::vm::Value::Struct { fields, .. } if !fields.is_empty() => {
                    if let crate::vm::Value::Str(s) = &fields[0] {
                        Ok(s.clone())
                    } else {
                        Err(format!("Expected &str field, got {v:?}"))
                    }
                }
                _ => Err(format!("Expected &str, got {v:?}")),
            }
        };
        let name = extract_str(&fields[0])?;
        let version = match &fields[1] {
            crate::vm::Value::Struct { fields: vf, .. } if vf.len() == 3 => {
                let (
                    crate::vm::Value::Int(maj),
                    crate::vm::Value::Int(min),
                    crate::vm::Value::Int(pat),
                ) = (&vf[0], &vf[1], &vf[2])
                else {
                    return Err(format!(
                        "Expected (u32, u32, u32) version tuple, got {:?}",
                        fields[1]
                    ));
                };
                (*maj as u32, *min as u32, *pat as u32)
            }
            other => {
                return Err(format!(
                    "Expected (u32, u32, u32) version tuple, got {other:?}"
                ));
            }
        };
        let root = extract_str(&fields[2])?;
        let crate::vm::Value::Bool(no_std) = fields[3] else {
            return Err(format!("Expected bool for no_std, got {:?}", fields[3]));
        };
        let extract_slice_elems = |v: &crate::vm::Value| -> Result<Vec<crate::vm::Value>, String> {
            let crate::vm::Value::Struct { fields: sf, .. } = v else {
                return Err(format!("Expected slice struct, got {v:?}"));
            };
            let crate::vm::Value::Int(len) = sf[1] else {
                return Err(format!("Expected slice length, got {:?}", sf[1]));
            };
            if len == 0 {
                return Ok(Vec::new());
            }
            let crate::vm::Value::Ptr {
                target,
                projections,
                ..
            } = &sf[0]
            else {
                return Err(format!("Expected slice pointer, got {:?}", sf[0]));
            };
            let arr_val = vm.read_ptr_value(target, projections)?;
            let crate::vm::Value::Array(elems) = arr_val else {
                return Err(format!("Expected array backing slice, got {arr_val:?}"));
            };
            Ok(elems.into_iter().take(len as usize).collect())
        };
        let dep_vals = extract_slice_elems(&fields[4])?;
        let mut deps = Vec::with_capacity(dep_vals.len());
        for dv in dep_vals {
            let crate::vm::Value::Struct { fields: df, .. } = dv else {
                return Err(format!("Expected Dependency struct, got {dv:?}"));
            };
            let dep_name = extract_str(&df[0])?;
            let dep_url = extract_str(&df[1])?;
            let sha256 = match &df[2] {
                crate::vm::Value::Wide(w) => {
                    let words = w.low_words(4);
                    [words[0], words[1], words[2], words[3]]
                }
                crate::vm::Value::Int(n) => {
                    let u = *n as u128;
                    [u as u64, (u >> 64) as u64, 0, 0]
                }
                crate::vm::Value::Array(words) if words.len() == 4 => {
                    let mut out = [0u64; 4];
                    for (i, w) in words.iter().enumerate() {
                        let crate::vm::Value::Int(n) = w else {
                            return Err(format!("Expected integer word in u256, got {w:?}"));
                        };
                        out[i] = *n as u64;
                    }
                    out
                }
                crate::vm::Value::Struct { fields: words, .. } if words.len() == 4 => {
                    let mut out = [0u64; 4];
                    for (i, w) in words.iter().enumerate() {
                        let crate::vm::Value::Int(n) = w else {
                            return Err(format!("Expected integer word in u256, got {w:?}"));
                        };
                        out[i] = *n as u64;
                    }
                    out
                }
                other => return Err(format!("Expected u256 digest in Dependency, got {other:?}")),
            };
            deps.push(EvaluatedDependency {
                name: dep_name,
                url: dep_url,
                sha256,
            });
        }
        let lib_vals = extract_slice_elems(&fields[5])?;
        let mut system_libs = Vec::with_capacity(lib_vals.len());
        for lv in lib_vals {
            system_libs.push(extract_str(&lv)?);
        }
        Ok(EvaluatedPackage {
            name,
            version,
            root,
            no_std,
            deps,
            system_libs,
        })
    }

    fn lower_function_body(&mut self, pending: PendingFunc) -> Result<(), String> {
        self.lowering_funcs.push(pending.func_id);
        let lowered = self.lower_function_body_in_context(pending);
        self.lowering_funcs.pop();
        lowered
    }

    fn lower_function_body_in_context(&mut self, pending: PendingFunc) -> Result<(), String> {
        // Diagnostic name, including the comptime arguments of a generic instantiation:
        // `Vec[Tx]::push`, `root::ignore[T = Tx]`.
        let mut debug_name = match pending.owner_ty {
            Some(owner) => {
                let base = pending
                    .decl
                    .name
                    .split_once("::")
                    .map_or(pending.decl.name.as_str(), |(_, rest)| rest);
                format!("{}::{}", self.type_instance_label(owner), base)
            }
            None if pending.decl.name.contains("::") => pending.decl.name.clone(),
            None => format!("{}::{}", pending.module_path, pending.decl.name),
        };
        let ct_args: Vec<String> = pending
            .decl
            .params
            .iter()
            .filter(|p| p.is_comptime)
            .filter_map(|p| {
                pending
                    .comptime_env
                    .get(&p.name)
                    .map(|v| format!("{} = {}", p.name, self.comptime_val_label(v)))
            })
            .collect();
        if !ct_args.is_empty() {
            debug_name.push_str(&format!("[{}]", ct_args.join(", ")));
        }
        let is_instantiation = !ct_args.is_empty()
            || pending
                .owner_ty
                .is_some_and(|o| self.memoized_type_calls.values().any(|t| *t == o));
        let mut param_names: Vec<String> = Vec::new();
        if !pending.closure_captures.is_empty() {
            param_names.push("__env".to_string());
        }
        param_names.extend(
            pending
                .decl
                .params
                .iter()
                .filter(|p| !p.is_comptime)
                .map(|p| p.name.clone()),
        );
        let linear_owner = pending.owner_ty.is_some_and(|o| self.is_linear_type(o));
        if let Some(func) = self
            .program
            .functions
            .iter_mut()
            .find(|f| f.id == pending.func_id)
        {
            if func.debug_name.is_none() {
                func.debug_name = Some(debug_name.clone());
            }
            func.param_names = param_names;
            func.linear_owner = linear_owner;
        }
        // A literal binding defaulted before its first typed use can be lowered again with the
        // type that use wanted (see `FuncLowerer::learn_type_hint`).
        let mut hints: Vec<Option<TypeId>> = Vec::new();
        let mut attempt = 0;
        let res = loop {
            let mut lowerer = FuncLowerer::new(self, pending.clone());
            lowerer.type_var_hints = hints.clone();
            let res = lowerer.lower();
            let learned = std::mem::take(&mut lowerer.learned_type_hints);
            attempt += 1;
            let mut changed = false;
            if res.is_err() && attempt < 4 {
                for (k, ty) in learned {
                    if hints.len() <= k {
                        hints.resize(k + 1, None);
                    }
                    if hints[k].is_none() {
                        hints[k] = Some(ty);
                        changed = true;
                    }
                }
            }
            if !changed {
                break res;
            }
        };
        res.map_err(|e| {
            if is_instantiation && !e.contains(&format!("in instantiation of {debug_name}")) {
                format!("{e}\n  in instantiation of {debug_name}")
            } else {
                e
            }
        })
    }

    /// `Vec[i32]` for an instantiated type function, otherwise the type's display name.
    fn type_instance_label(&self, ty: TypeId) -> String {
        // A tuple's display name already says everything about it.
        if self.type_satisfies_constraint(ty, TypeConstraint::Tuple) {
            return self.type_display_name(ty);
        }
        let mut keys: Vec<&(String, String, Vec<ComptimeVal>)> = self
            .memoized_type_calls
            .iter()
            .filter(|(k, t)| **t == ty && !self.reused_type_calls.contains(*k))
            .map(|(k, _)| k)
            .collect();
        keys.sort_by_cached_key(|k| (k.0.clone(), k.1.clone(), format!("{:?}", k.2)));
        match keys.first() {
            Some((_, fname, args)) => {
                // The default allocator is what `Vec[i32]` already says.
                let shown = match args.last() {
                    Some(ComptimeVal::Type(t)) if self.type_display_name(*t) == "Global" => &args[..args.len() - 1],
                    _ => &args[..],
                };
                let args: Vec<String> = shown.iter().map(|a| self.comptime_val_label(a)).collect();
                format!("{fname}[{}]", args.join(", "))
            }
            None => self.type_display_name(ty),
        }
    }

    fn comptime_val_label(&self, v: &ComptimeVal) -> String {
        match v {
            ComptimeVal::Null => "null".to_string(),
            ComptimeVal::Type(t) => self.type_instance_label(*t),
            ComptimeVal::Int(n) => n.to_string(),
            ComptimeVal::Bool(b) => b.to_string(),
            ComptimeVal::Str(s) => format!("{s:?}"),
            ComptimeVal::Module(m) => m.clone(),
            ComptimeVal::Map(id) => format!("<map {id}>"),
            ComptimeVal::List(items, _) => {
                let elems: Vec<String> = items.iter().map(|i| self.comptime_val_label(i)).collect();
                format!("[{}]", elems.join(", "))
            }
            ComptimeVal::Record(fields) => {
                let items: Vec<String> = fields
                    .iter()
                    .filter(|(k, _)| !k.starts_with("__ty:"))
                    .map(|(k, v)| format!("{k}: {}", self.comptime_val_label(v)))
                    .collect();
                format!(".{{ {} }}", items.join(", "))
            }
            ComptimeVal::Tuple(items) => {
                let elems: Vec<String> = items.iter().map(|i| self.comptime_val_label(i)).collect();
                format!("({})", elems.join(", "))
            }
            ComptimeVal::ConstExpr(k, _) => k.clone(),
        }
    }
}

/// What an index is checked against before `Projection::Index` is applied.
pub(super) enum IndexBound {
    /// A slice's runtime `len` field.
    Dynamic(Place),
    /// A fixed-length array or SIMD vector.
    Static(u64),
    /// No check (`[T; 0]` flexible arrays reached through raw pointers).
    Unchecked,
}

#[derive(Clone)]
struct ScopeVar {
    name: String,
    local: LocalId,
    ty: TypeId,
    opaque_bound: Option<OpaqueRetBound>,
    /// Declared `mut`: the binding's own memory may be assigned or borrowed `&mut`.
    mutable: bool,
}

/// A function body under construction: its locals, blocks, and the block being filled. Used by
/// source lowering (`FuncLowerer`) and by compiler-synthesized functions (C-ABI export wrappers).
#[derive(Clone)]
struct BodyBuilder {
    locals: Vec<TypeId>,
    blocks: Vec<BasicBlock>,
    terminated: Vec<bool>,
    cur_block: BlockId,
}

impl BodyBuilder {
    /// A body with `locals` (return slot and parameters first) and an empty entry block.
    fn new(locals: Vec<TypeId>) -> Self {
        Self {
            locals,
            blocks: vec![BasicBlock {
                statements: Vec::new(),
                terminator: Terminator::Unreachable,
            }],
            terminated: vec![false],
            cur_block: BlockId(0),
        }
    }

    fn new_block(&mut self) -> BlockId {
        let id = BlockId(self.blocks.len() as u32);
        self.blocks.push(BasicBlock {
            statements: Vec::new(),
            terminator: Terminator::Unreachable,
        });
        self.terminated.push(false);
        id
    }

    fn alloc_temp(&mut self, ty: TypeId) -> LocalId {
        let id = LocalId(self.locals.len() as u32);
        self.locals.push(ty);
        id
    }

    fn emit(&mut self, stmt: Statement) {
        self.blocks[self.cur_block.0 as usize].statements.push(stmt);
    }

    fn terminate(&mut self, term: Terminator) {
        self.blocks[self.cur_block.0 as usize].terminator = term;
        self.terminated[self.cur_block.0 as usize] = true;
    }

    fn is_terminated(&self) -> bool {
        self.terminated[self.cur_block.0 as usize]
    }
}

struct FuncLowerer<'a> {
    compiler: &'a mut Compiler,
    /// False for module-level `impl Tr for T` methods: `Self` resolves to `T`, but `T`'s private
    /// members stay inaccessible.
    private_access: bool,
    func_id: FuncId,
    mod_path: String,
    owner_ty: Option<TypeId>,
    decl: FuncDecl,
    comptime_env: HashMap<String, ComptimeVal>,
    closure_captures: Vec<(String, TypeId, bool)>,
    body: BodyBuilder,
    /// For an instance of a type function: its name and arguments (see `typefn.rs`).
    type_fn: Option<(String, Vec<ComptimeVal>)>,
    /// Locals holding the task's context instance from before each enclosing stateful `with`.
    scopes: Vec<Vec<ScopeVar>>,
    inferred_opaque_ret: Option<TypeId>,
    last_call_opaque_bound: Option<OpaqueRetBound>,
    /// The type the call being lowered is expected to give, for inferring its comptime
    /// arguments where its arguments leave them open (taken by `lower_call`).
    call_expected: Option<TypeId>,
    /// A field access's base that was lowered to see whether the field is packed, and was not:
    /// the base expression's address and its place, for `lower_place` to take rather than lower
    /// (and so evaluate) the base again.
    lowered_base: Option<(*const Expr, Place, TypeId)>,
    unsafe_depth: usize,
    /// Inside `nosuspend { ... }`, which records the calls it makes.
    nosuspend_depth: usize,
    raw_addr_of_depth: usize,
    static_locals: HashMap<LocalId, (String, bool)>,
    /// Enclosing loops, innermost last: `break` / `continue` targets and the scope depth to unwind to.
    loops: Vec<LoopCtx>,
    /// Set when `x.method()` matched only traits that are not in scope, to explain a failed lookup.
    out_of_scope_trait_hint: Option<String>,
    /// Writes found by closure capture analysis that may modify a captured binding itself:
    /// `(root variable, whether the written place is the bare variable)`. Places reached through
    /// an explicit `*` are left out.
    capture_binding_writes: std::cell::RefCell<Vec<(String, bool)>>,
    /// Captures the closure being analysed uses by value, which spends its environment, with
    /// the method called on them if that depends on the method.
    capture_moves: std::cell::RefCell<Vec<(String, Option<String>)>>,
    /// The label of the loop statement being lowered (taken by the loop it labels).
    pending_loop_label: Option<String>,
    /// Names of the variables of popped scopes (see `Function::local_names`).
    local_names: Vec<(LocalId, String)>,
    /// Types learned for type variables by a previous attempt at this function, by creation
    /// index (see `learn_type_hint`).
    type_var_hints: Vec<Option<TypeId>>,
    /// Hints learned by this attempt: `(type variable index, type)`.
    learned_type_hints: Vec<(usize, TypeId)>,
    /// Type variables of unannotated literal `let`s (see `infer.rs`).
    type_vars: Vec<TypeVar>,
    /// Whether the expression being lowered may leave a type variable unresolved (its consumer
    /// is arithmetic, a `let`, an assignment, or a cast; see `FuncLowerer::lower_expr`).
    allow_type_var: bool,
    /// The source position the last `Statement::Line` gave: a statement's, or a call's within
    /// it while the call is lowered.
    line: Option<crate::ir::Pos>,
    /// The function the last call lowered called directly, if it did.
    last_call: Option<FuncId>,
}

#[derive(Clone)]
struct LoopCtx {
    continue_bb: BlockId,
    break_bb: BlockId,
    scope_depth: usize,
    /// How many stateful contexts were active at the loop, for leaving those entered since.
    /// The loop's label (`outer: while ...`), for `break outer` / `continue outer`.
    label: Option<String>,
}

fn op_const(op: &Operand) -> Option<&ConstValue> {
    match op {
        Operand::Const(c) => Some(c),
        _ => None,
    }
}
