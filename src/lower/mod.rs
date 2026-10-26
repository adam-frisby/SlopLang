mod call;
mod comptime;
mod export;
mod expr;
mod stmt;
mod types;

use std::collections::HashMap;

use crate::ast::{
    BindMode, Block, BorrowContractItem, CIntKind, CloneHookDecl, ConstDecl, DropHookDecl, Expr,
    ExternFuncDecl, FieldDecl, FmtSegment, FuncDecl, ImportDecl, ImportTargets, Item, MatchPat,
    ModuleAst, SelectArm, SelectOp, StaticDecl, Stmt, StructOwnership, TraitMethodDecl,
    TypeConstraint, TypeExpr, Visibility, WherePredicate,
};
use crate::borrowck::check_borrows;
use crate::drop::elaborate_drops;
use crate::frontend::SurfaceParser;
use crate::ir::{
    BasicBlock, BinOp, BlockId, ConstValue, ExternFunc, FnContract, FuncId, Function, Global,
    GlobalId,
    LocalId, Operand, Place, Program, Projection, Rvalue, Statement, Terminator, Type, TypeId,
    UnOp,
};

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
}

#[derive(Debug, Clone)]
struct UnionTypeInfo {
    name: String,
    variants: Vec<(String, TypeId)>,
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
    Type(TypeId),
    Int(i128),
    Bool(bool),
    Str(String),
    Module(String),
    Map(u32),
    ConstExpr(String, Expr),
}

impl PartialEq for ComptimeVal {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (ComptimeVal::Type(a), ComptimeVal::Type(b)) => a == b,
            (ComptimeVal::Int(a), ComptimeVal::Int(b)) => a == b,
            (ComptimeVal::Bool(a), ComptimeVal::Bool(b)) => a == b,
            (ComptimeVal::Str(a), ComptimeVal::Str(b)) => a == b,
            (ComptimeVal::Module(a), ComptimeVal::Module(b)) => a == b,
            (ComptimeVal::Map(a), ComptimeVal::Map(b)) => a == b,
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
            ComptimeVal::Type(t) => t.hash(state),
            ComptimeVal::Int(n) => n.hash(state),
            ComptimeVal::Bool(b) => b.hash(state),
            ComptimeVal::Str(s) => s.hash(state),
            ComptimeVal::Module(m) => m.hash(state),
            ComptimeVal::Map(id) => id.hash(state),
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

#[derive(Debug, Clone)]
struct CompositeInfo {
    name: String,
    is_struct: bool,
    is_packed: bool,
    total_bits: u16,
    packed_offsets: Vec<(u16, u16)>,
    ownership: StructOwnership,
    is_sync: bool,
    has_format_hook: bool,
    def_module: String,
    comptime_env: HashMap<String, ComptimeVal>,
    fields: Vec<(String, TypeId, Visibility, Option<Expr>)>,
    rel_fields: HashMap<u32, RelFieldKind>,
    consts: HashMap<String, (Visibility, ConstDecl)>,
    statics: HashMap<String, (Visibility, StaticDecl)>,
    methods: HashMap<String, (Visibility, FuncDecl)>,
    method_fn_ids: HashMap<String, FuncId>,
    default_fn: Option<FuncId>,
    clone_fn: Option<FuncId>,
    drop_fn: Option<FuncId>,
    format_fn: Option<(FuncId, bool)>,
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

#[derive(Debug, Clone)]
struct OpaqueNewtypeInfo {
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
        out_err_ptr_ty: TypeId,
        ok_ty: TypeId,
        out_val_ptr_ty: Option<TypeId>,
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

pub struct Compiler {
    modules: HashMap<String, ModuleAst>,
    pub program: Program,
    composites: HashMap<TypeId, CompositeInfo>,
    enums: HashMap<TypeId, (String, Vec<(String, i128)>)>,
    unions: HashMap<TypeId, UnionTypeInfo>,
    overlays: HashMap<TypeId, OverlayTypeInfo>,
    uninit_types: HashMap<TypeId, TypeId>,
    memoized_uninit: HashMap<TypeId, TypeId>,
    errors: HashMap<TypeId, ErrorTypeInfo>,
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
    maps: HashMap<TypeId, MapTypeInfo>,
    memoized_maps: HashMap<(TypeId, TypeId), TypeId>,
    map_instances: Vec<MapInstance>,
    dense_map_globals: HashMap<u32, (GlobalId, i128, i128)>,
    phf_map_globals: HashMap<u32, PhfTableInfo>,
    c_ints: HashMap<TypeId, CIntKind>,
    memoized_c_ints: HashMap<CIntKind, TypeId>,
    opaque_ty: Option<TypeId>,
    named_opaques: std::collections::HashSet<TypeId>,
    opaque_newtypes: HashMap<TypeId, OpaqueNewtypeInfo>,
    opaque_ret_funcs: HashMap<FuncId, OpaqueRetBound>,
    pub exported_types: Vec<ExportedTypeMeta>,
    exported_type_set: std::collections::HashSet<TypeId>,
    c_abi_func_wrappers: HashMap<FuncId, CAbiExportWrapperInfo>,
    pub exported_funcs: Vec<ExportedFuncMeta>,
    named_types: HashMap<(String, String), TypeId>,
    memoized_type_calls: HashMap<(String, String, Vec<ComptimeVal>), TypeId>,
    memoized_inherent_methods: HashMap<(TypeId, String, Vec<ComptimeVal>), FuncId>,
    resolved_funcs: HashMap<(String, String, Vec<ComptimeVal>), FuncId>,
    resolved_externs: HashMap<(String, String), FuncId>,
    resolved_statics: HashMap<(String, String), (GlobalId, TypeId, bool)>,
    resolved_consts: HashMap<(String, String), (ConstValue, TypeId, ComptimeVal, bool)>,
    associated_statics: HashMap<(TypeId, String), (GlobalId, TypeId, bool, Visibility)>,
    associated_consts:
        HashMap<(TypeId, String), (ConstValue, TypeId, ComptimeVal, Visibility, bool)>,
    func_sigs: HashMap<FuncId, (Vec<TypeId>, TypeId)>,
    pending_funcs: Vec<PendingFunc>,
    /// Index of the next entry of `pending_funcs` to lower.
    pending_cursor: usize,
    /// Nesting depth of compile-time type-function evaluation (guards runaway recursion).
    comptime_depth: usize,
    /// Non-fatal diagnostics (lints) collected during compilation, deduplicated.
    pub warnings: Vec<String>,
    /// Function-pointer types keyed by `(args, ret, contract)`; each carries its borrow contract.
    memoized_fn_ptrs: HashMap<(Vec<TypeId>, TypeId, FnContract), TypeId>,
    /// Functions whose body has no private access to its `owner_ty` (module-level `impl` methods).
    no_private_access_fns: std::collections::HashSet<FuncId>,
    /// Set while scheduling a module-level `impl` method so it is lowered without private access.
    schedule_no_private: bool,
    /// `impl Tr { ... }` blocks declared inside a type's own body, keyed by the instantiated type.
    inline_impls: HashMap<TypeId, Vec<InlineImpl>>,
    /// Instantiated trait-implementation methods keyed by `(type, trait, method name)`.
    memoized_impl_methods: HashMap<(TypeId, TypeId, String), FuncId>,
    /// All module-level `impl` items (module path, declaration), collected once on first use.
    module_impls: Option<Vec<(String, crate::ast::ImplDecl)>>,
    /// The `T::Tag` enum of each union: the linked enum for `union(Enum)`, otherwise synthesized.
    union_tag_enums: HashMap<TypeId, TypeId>,
    /// Expressions currently in the generic fallback of `eval_const_expr_typed` (re-entrancy guard).
    const_eval_fallback: Vec<usize>,
    /// Results of `impl` lookups keyed by `(type, optional trait filter)`.
    trait_impl_cache: HashMap<(TypeId, Option<TypeId>), TraitImpls>,
}

/// A trait implementation declared inside a type's own body (`impl Tr { ... }`).
#[derive(Debug, Clone)]
struct InlineImpl {
    trait_expr: TypeExpr,
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
}

impl Default for Compiler {
    fn default() -> Self {
        Self::new()
    }
}

impl Compiler {
    pub fn new() -> Self {
        Self {
            modules: HashMap::new(),
            program: Program {
                types: Vec::new(),
                destructors: Vec::new(),
                linear_types: Vec::new(),
                raw_ptr_types: Vec::new(),
                fn_ptr_contracts: Vec::new(),
                tagged_unions: Vec::new(),
                union_tag_values: Vec::new(),
                type_names: Vec::new(),
                globals: Vec::new(),
                externs: Vec::new(),
                functions: Vec::new(),
            },
            composites: HashMap::new(),
            enums: HashMap::new(),
            unions: HashMap::new(),
            overlays: HashMap::new(),
            uninit_types: HashMap::new(),
            memoized_uninit: HashMap::new(),
            errors: HashMap::new(),
            memoized_error_unions: HashMap::new(),
            results: HashMap::new(),
            memoized_results: HashMap::new(),
            traits: HashMap::new(),
            trait_objs: HashMap::new(),
            memoized_trait_objs: HashMap::new(),
            memoized_vtables: HashMap::new(),
            closures: HashMap::new(),
            slices: HashMap::new(),
            raw_ptrs: HashMap::new(),
            maps: HashMap::new(),
            memoized_maps: HashMap::new(),
            map_instances: Vec::new(),
            dense_map_globals: HashMap::new(),
            phf_map_globals: HashMap::new(),
            c_ints: HashMap::new(),
            memoized_c_ints: HashMap::new(),
            opaque_ty: None,
            named_opaques: std::collections::HashSet::new(),
            opaque_newtypes: HashMap::new(),
            opaque_ret_funcs: HashMap::new(),
            exported_types: Vec::new(),
            exported_type_set: std::collections::HashSet::new(),
            c_abi_func_wrappers: HashMap::new(),
            exported_funcs: Vec::new(),
            named_types: HashMap::new(),
            memoized_type_calls: HashMap::new(),
            memoized_inherent_methods: HashMap::new(),
            resolved_funcs: HashMap::new(),
            resolved_externs: HashMap::new(),
            resolved_statics: HashMap::new(),
            resolved_consts: HashMap::new(),
            associated_statics: HashMap::new(),
            associated_consts: HashMap::new(),
            func_sigs: HashMap::new(),
            pending_funcs: Vec::new(),
            pending_cursor: 0,
            comptime_depth: 0,
            warnings: Vec::new(),
            memoized_fn_ptrs: HashMap::new(),
            no_private_access_fns: std::collections::HashSet::new(),
            schedule_no_private: false,
            inline_impls: HashMap::new(),
            memoized_impl_methods: HashMap::new(),
            module_impls: None,
            trait_impl_cache: HashMap::new(),
            union_tag_enums: HashMap::new(),
            const_eval_fallback: Vec::new(),
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

    /// Loads a package from disk: every `.lrrr` file under `<dir>/src` becomes a module named after
    /// its path (`src/main.lrrr` or `src/lib.lrrr` is `root`, `src/net/http.lrrr` is
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
                } else if path.extension().is_some_and(|x| x == "lrrr") {
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
                            "Module '{module}' is defined by more than one file (both 'main.lrrr' and 'lib.lrrr'?)"
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
                "Package '{}' has no 'src/main.lrrr' or 'src/lib.lrrr'",
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
        let compiler = Self::compile_package_compiler(sources, false)?;
        Ok((compiler.program, compiler.warnings))
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

    fn compile_package_compiler(sources: &[(&str, &str)], no_std: bool) -> Result<Self, String> {
        let mut compiler = Self::new();

        // 1. Load bundled `core` modules (always available) and `std` modules (when `!no_std`)
        for &(mod_path, src) in crate::stdlib::CORE_MODULES {
            let ast = SurfaceParser::parse_module(src)
                .map_err(|e| format!("In bundled module '{mod_path}': {e}"))?;
            compiler.modules.insert(mod_path.to_string(), ast);
        }
        if !no_std {
            for &(mod_path, src) in crate::stdlib::STD_MODULES {
                let ast = SurfaceParser::parse_module(src)
                    .map_err(|e| format!("In bundled module '{mod_path}': {e}"))?;
                compiler.modules.insert(mod_path.to_string(), ast);
            }
        }

        // 2. Load user package modules (allowing explicit overrides of any module path)
        for &(mod_path, src) in sources {
            let ast = SurfaceParser::parse_module(src)
                .map_err(|e| format!("In module '{mod_path}': {e}"))?;
            compiler.modules.insert(mod_path.to_string(), ast);
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
        elaborate_drops(&mut compiler.program)?;
        check_borrows(&compiler.program)?;
        Ok(compiler)
    }

    fn warn(&mut self, msg: String) {
        if !self.warnings.contains(&msg) {
            self.warnings.push(msg);
        }
    }

    fn intern_type(&mut self, ty: Type) -> TypeId {
        if let Some(idx) = self.program.types.iter().enumerate().find_map(|(i, t)| {
            let tid = TypeId(i as u32);
            (*t == ty
                && !self.composites.contains_key(&tid)
                && !self.enums.contains_key(&tid)
                && !self.unions.contains_key(&tid)
                && !self.overlays.contains_key(&tid)
                && !self.uninit_types.contains_key(&tid)
                && !self.errors.contains_key(&tid)
                && !self.results.contains_key(&tid)
                && !self.traits.contains_key(&tid)
                && !self.trait_objs.contains_key(&tid)
                && !self.closures.contains_key(&tid)
                && !self.slices.contains_key(&tid)
                && !self.raw_ptrs.contains_key(&tid)
                && !self.maps.contains_key(&tid)
                && !self.c_ints.contains_key(&tid)
                && !self.named_opaques.contains(&tid)
                && !self.opaque_newtypes.contains_key(&tid)
                && !matches!(t, Type::FnPtr { .. })
                && self.opaque_ty != Some(tid))
            .then_some(i)
        }) {
            TypeId(idx as u32)
        } else {
            let id = TypeId(self.program.types.len() as u32);
            self.program.types.push(ty);
            id
        }
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
    /// contract are distinct; contracts are canonicalized so equal contracts share one `TypeId`.
    fn intern_fn_ptr_type(&mut self, args: Vec<TypeId>, ret: TypeId, contract: FnContract) -> TypeId {
        let mut contract = contract;
        contract.ret.sort();
        contract.ret.dedup();
        contract.flows.sort();
        contract.flows.dedup();
        let key = (args.clone(), ret, contract.clone());
        if let Some(&tid) = self.memoized_fn_ptrs.get(&key) {
            return tid;
        }
        let tid = self.alloc_distinct_type(Type::FnPtr { args, ret });
        self.program.fn_ptr_contracts.push((tid, contract));
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
    fn fn_value_ptr_type(&mut self, args: Vec<TypeId>, ret: TypeId) -> TypeId {
        let contract = self.default_fn_contract(&args, ret);
        self.intern_fn_ptr_type(args, ret, contract)
    }

    pub(super) fn fn_ptr_contract(&self, ty: TypeId) -> Option<&FnContract> {
        self.program
            .fn_ptr_contracts
            .iter()
            .find(|(t, _)| *t == ty)
            .map(|(_, c)| c)
    }

    fn intern_raw_ptr_type(&mut self, mutable: bool, pointee: TypeId) -> TypeId {
        if let Some((&tid, _)) = self
            .raw_ptrs
            .iter()
            .find(|(_, (m, p))| *m == mutable && *p == pointee)
        {
            return tid;
        }
        let tid = self.alloc_distinct_type(Type::Ptr { mutable, pointee });
        self.raw_ptrs.insert(tid, (mutable, pointee));
        self.program.raw_ptr_types.push(tid);
        tid
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

        // 2. Register concrete top-level types (`record`, `struct`, `type`) in user modules
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
        self.lower_pending_funcs()?;

        Ok(())
    }

    /// Lowers every queued function body not yet lowered. Re-entrant: compile-time evaluation
    /// lowers its callees through this as well, and the shared cursor keeps each body lowered once.
    fn lower_pending_funcs(&mut self) -> Result<(), String> {
        while self.pending_cursor < self.pending_funcs.len() {
            let pending = self.pending_funcs[self.pending_cursor].clone();
            self.pending_cursor += 1;
            self.lower_function_body(pending)?;
        }
        Ok(())
    }

    fn register_extern(&mut self, mod_path: &str, ext: &ExternFuncDecl) -> Result<FuncId, String> {
        let key = (mod_path.to_string(), ext.name.clone());
        if let Some(&id) = self.resolved_externs.get(&key) {
            return Ok(id);
        }
        let env = HashMap::new();
        let mut arg_tys = Vec::new();
        for (pname, pty) in &ext.params {
            let p_id = self.resolve_type_expr(mod_path, None, &env, pty)?;
            if self.is_opaque_type(p_id) {
                return Err(format!(
                    "Unsized type 'opaque' cannot be passed by value in parameter '{}' of extern function '{}'; use '*const opaque', '*mut opaque', '&opaque', or '&mut opaque'",
                    pname, ext.name
                ));
            }
            arg_tys.push(p_id);
        }
        let ret_ty = self.resolve_type_expr(mod_path, None, &env, &ext.ret_ty)?;
        if self.is_opaque_type(ret_ty) {
            return Err(format!(
                "Unsized type 'opaque' cannot be returned by value from extern function '{}'; use '*const opaque', '*mut opaque', '&opaque', or '&mut opaque'",
                ext.name
            ));
        }
        if let Some(existing) = self.program.externs.iter().find(|e| e.symbol == ext.name) {
            let fn_id = existing.id;
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
        self.resolved_externs.insert(key, fn_id);
        self.func_sigs.insert(fn_id, (arg_tys, ret_ty));
        Ok(fn_id)
    }

    fn get_or_register_extern(&mut self, mod_path: &str, name: &str) -> Result<FuncId, String> {
        let key = (mod_path.to_string(), name.to_string());
        if let Some(&id) = self.resolved_externs.get(&key) {
            return Ok(id);
        }
        let Some((def_mod, _, Item::ExternFunc(ext), _)) =
            self.find_item_in_module(mod_path, mod_path, name)?
        else {
            return Err(format!(
                "Extern function '{name}' not found in '{mod_path}'"
            ));
        };
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
                        item.clone(),
                        f.vis,
                    )));
                }
                Item::ExternFunc(e) if e.name == name => {
                    self.check_item_visibility(from_mod, target_mod, name, e.vis)?;
                    return Ok(Some((
                        target_mod.to_string(),
                        e.name.clone(),
                        item.clone(),
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
                        item.clone(),
                        *vis,
                    )));
                }
                Item::Static(s) if s.name == name => {
                    self.check_item_visibility(from_mod, target_mod, name, s.vis)?;
                    return Ok(Some((
                        target_mod.to_string(),
                        s.name.clone(),
                        item.clone(),
                        s.vis,
                    )));
                }
                Item::Const(c) if c.name == name => {
                    self.check_item_visibility(from_mod, target_mod, name, c.vis)?;
                    return Ok(Some((
                        target_mod.to_string(),
                        c.name.clone(),
                        item.clone(),
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
                            return self.find_item_in_module(target_mod, &imp_mod, orig);
                        }
                    }
                }
                ImportTargets::Glob => {
                    if let Some(found) = self.find_item_in_module(target_mod, &imp_mod, name)? {
                        return Ok(Some(found));
                    }
                }
                ImportTargets::Module(alias) => {
                    if !self.modules.contains_key(&imp_mod) && imp.path.len() >= 2 {
                        let parent_mod = imp.path[..imp.path.len() - 1].join("::");
                        let orig = imp.path.last().unwrap();
                        let bound = alias.as_deref().unwrap_or(orig);
                        if bound == name {
                            return self.find_item_in_module(target_mod, &parent_mod, orig);
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

    fn resolve_path(&self, cur_mod: &str, path: &[String]) -> Result<ResolvedItem, String> {
        let item_to_resolved = |def_mod: String, orig_name: String, item: Item| match item {
            Item::Func(_) => ResolvedItem::Func(def_mod, orig_name),
            Item::ExternFunc(_) => ResolvedItem::ExternFunc(def_mod, orig_name),
            Item::TypeDecl { .. } => ResolvedItem::Type(def_mod, orig_name),
            Item::Static(_) => ResolvedItem::Static(def_mod, orig_name),
            Item::Const(_) => ResolvedItem::Const(def_mod, orig_name),
            Item::Impl(_) => unreachable!("'impl' blocks are not named module items"),
        };
        if path.len() == 1 {
            let name = &path[0];
            // 1. Local module item
            if let Some((def_mod, orig_name, item, _)) =
                self.find_item_in_module(cur_mod, cur_mod, name)?
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
                                        self.find_item_in_module(cur_mod, &parent_mod, orig)?
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
                                        self.find_item_in_module(cur_mod, &target_mod, orig)?
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
                                self.find_item_in_module(cur_mod, &target_mod, name)?
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
                            self.find_item_in_module(cur_mod, &def_mod, &nested_name)?
                        {
                            return Ok(item_to_resolved(dmod, oname, item));
                        }
                        prefix_joined
                    }
                    _ => prefix_joined,
                }
            };
            let Some((def_mod, orig_name, item, _)) =
                self.find_item_in_module(cur_mod, &target_mod, item_name)?
            else {
                return Err(format!(
                    "Item '{item_name}' not found in module '{target_mod}'"
                ));
            };
            Ok(item_to_resolved(def_mod, orig_name, item))
        }
    }

    /// Evaluates a pure `comptime` `package.lrrr` manifest (`pub fn package(comptime target: Target) -> Package`)
    /// inside the sandboxed Stage 3 VM (`Vm::eval`).
    pub fn evaluate_package_manifest(
        manifest_src: &str,
        target_os: &str,
        target_arch: &str,
    ) -> Result<EvaluatedPackage, String> {
        let wrapper_src = format!(
            "{manifest_src}\n\npub fn __lrrr_eval_package_manifest() -> std::build::Package {{\n    return package(std::build::Target {{\n        os: std::build::Target::Os::{target_os},\n        arch: std::build::Target::Arch::{target_arch},\n        optimize: std::build::OptimizeMode::Debug,\n    }});\n}}\n"
        );
        let mut compiler = Self::compile_package_compiler(&[("root", &wrapper_src)], false)?;
        let fn_id = compiler
            .resolved_funcs
            .get(&(
                "root".to_string(),
                "__lrrr_eval_package_manifest".to_string(),
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
        // Diagnostic name, including the comptime arguments of a generic instantiation:
        // `Vec(Tx)::push`, `root::ignore(T = Tx)`.
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
            debug_name.push_str(&format!("({})", ct_args.join(", ")));
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
        }
        let mut lowerer = FuncLowerer::new(self, pending);
        lowerer.lower().map_err(|e| {
            if is_instantiation && !e.contains(&format!("in instantiation of {debug_name}")) {
                format!("{e}\n  in instantiation of {debug_name}")
            } else {
                e
            }
        })
    }

    /// `Vec(i32)` for an instantiated type function, otherwise the type's display name.
    fn type_instance_label(&self, ty: TypeId) -> String {
        let mut keys: Vec<&(String, String, Vec<ComptimeVal>)> = self
            .memoized_type_calls
            .iter()
            .filter(|(_, t)| **t == ty)
            .map(|(k, _)| k)
            .collect();
        keys.sort_by(|a, b| (&a.0, &a.1).cmp(&(&b.0, &b.1)));
        match keys.first() {
            Some((_, fname, args)) => {
                let args: Vec<String> = args.iter().map(|a| self.comptime_val_label(a)).collect();
                format!("{fname}({})", args.join(", "))
            }
            None => self.type_display_name(ty),
        }
    }

    fn comptime_val_label(&self, v: &ComptimeVal) -> String {
        match v {
            ComptimeVal::Type(t) => self.type_instance_label(*t),
            ComptimeVal::Int(n) => n.to_string(),
            ComptimeVal::Bool(b) => b.to_string(),
            ComptimeVal::Str(s) => format!("{s:?}"),
            ComptimeVal::Module(m) => m.clone(),
            ComptimeVal::Map(id) => format!("<map {id}>"),
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
    locals: Vec<TypeId>,
    blocks: Vec<BasicBlock>,
    terminated: Vec<bool>,
    cur_block: BlockId,
    scopes: Vec<Vec<ScopeVar>>,
    inferred_opaque_ret: Option<TypeId>,
    last_call_opaque_bound: Option<OpaqueRetBound>,
    unsafe_depth: usize,
    raw_addr_of_depth: usize,
    static_locals: HashMap<LocalId, (String, bool)>,
    /// Enclosing loops, innermost last: `break` / `continue` targets and the scope depth to unwind to.
    loops: Vec<LoopCtx>,
    /// Set when `x.method()` matched only traits that are not in scope, to explain a failed lookup.
    out_of_scope_trait_hint: Option<String>,
}

#[derive(Clone, Copy)]
struct LoopCtx {
    continue_bb: BlockId,
    break_bb: BlockId,
    scope_depth: usize,
}
