mod call;
mod comptime;
mod export;
mod expr;
mod stmt;
mod types;

use std::collections::HashMap;

use crate::ast::{
    Block, BorrowContractItem, CIntKind, CloneHookDecl, ConstDecl, DropHookDecl, Expr,
    ExternFuncDecl, FieldDecl, FmtSegment, FuncDecl, ImportDecl, ImportTargets, Item, MatchPat,
    ModuleAst, StaticDecl, Stmt, StructOwnership, TraitMethodDecl, TypeConstraint, TypeExpr,
    Visibility, WherePredicate,
};
use crate::borrowck::check_borrows;
use crate::drop::elaborate_drops;
use crate::frontend::SurfaceParser;
use crate::ir::{
    BasicBlock, BinOp, BlockId, ConstValue, ExternFunc, FuncId, Function, Global, GlobalId,
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
    ConstExpr(String, Expr),
}

impl PartialEq for ComptimeVal {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (ComptimeVal::Type(a), ComptimeVal::Type(b)) => a == b,
            (ComptimeVal::Int(a), ComptimeVal::Int(b)) => a == b,
            (ComptimeVal::Bool(a), ComptimeVal::Bool(b)) => a == b,
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
            ComptimeVal::ConstExpr(k, _) => k.hash(state),
        }
    }
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
                globals: Vec::new(),
                externs: Vec::new(),
                functions: Vec::new(),
            },
            composites: HashMap::new(),
            enums: HashMap::new(),
            unions: HashMap::new(),
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

    fn intern_type(&mut self, ty: Type) -> TypeId {
        if let Some(idx) = self.program.types.iter().enumerate().find_map(|(i, t)| {
            let tid = TypeId(i as u32);
            (*t == ty
                && !self.composites.contains_key(&tid)
                && !self.enums.contains_key(&tid)
                && !self.unions.contains_key(&tid)
                && !self.errors.contains_key(&tid)
                && !self.results.contains_key(&tid)
                && !self.traits.contains_key(&tid)
                && !self.trait_objs.contains_key(&tid)
                && !self.closures.contains_key(&tid)
                && !self.slices.contains_key(&tid)
                && !self.raw_ptrs.contains_key(&tid)
                && !self.c_ints.contains_key(&tid)
                && !self.named_opaques.contains(&tid)
                && !self.opaque_newtypes.contains_key(&tid)
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
        let mut idx = 0;
        while idx < self.pending_funcs.len() {
            let pending = self.pending_funcs[idx].clone();
            idx += 1;
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

    fn resolve_path(&self, cur_mod: &str, path: &[String]) -> Result<ResolvedItem, String> {
        let item_to_resolved = |def_mod: String, orig_name: String, item: Item| match item {
            Item::Func(_) => ResolvedItem::Func(def_mod, orig_name),
            Item::ExternFunc(_) => ResolvedItem::ExternFunc(def_mod, orig_name),
            Item::TypeDecl { .. } => ResolvedItem::Type(def_mod, orig_name),
            Item::Static(_) => ResolvedItem::Static(def_mod, orig_name),
            Item::Const(_) => ResolvedItem::Const(def_mod, orig_name),
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
            // Multi-segment path: `mod::item` or `root::sub::item`
            let item_name = path.last().unwrap();
            let prefix = &path[..path.len() - 1];
            let target_mod = if prefix.len() == 1 {
                match self.resolve_path(cur_mod, prefix) {
                    Ok(ResolvedItem::Module(m)) => m,
                    _ => prefix.join("::"),
                }
            } else {
                prefix.join("::")
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

    fn lower_function_body(&mut self, pending: PendingFunc) -> Result<(), String> {
        let mut lowerer = FuncLowerer::new(self, pending);
        lowerer.lower()
    }
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
}
