use std::collections::HashMap;

use crate::ast::{
    Block, BorrowContractItem, CIntKind, CloneHookDecl, DropHookDecl, Expr, ExternFuncDecl,
    FieldDecl, FmtSegment, FuncDecl, ImportDecl, ImportTargets, Item, MatchPat, ModuleAst, Stmt,
    StructOwnership, TraitMethodDecl, TypeConstraint, TypeExpr, Visibility, WherePredicate,
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

    fn compile_package_with_mode(sources: &[(&str, &str)], no_std: bool) -> Result<Program, String> {
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

    pub fn c_type_name(&self, ty_id: TypeId) -> String {
        if let Some(ck) = self.c_ints.get(&ty_id) {
            return ck.c_header_name().to_string();
        }
        if let Some(nt) = self.opaque_newtypes.get(&ty_id) {
            return nt.name.clone();
        }
        if self.named_opaques.contains(&ty_id) {
            return self.composites[&ty_id].name.clone();
        }
        if let Some(comp) = self.composites.get(&ty_id) {
            return comp.name.clone();
        }
        if let Some((ename, _)) = self.enums.get(&ty_id) {
            return ename.clone();
        }
        if let Some(err_info) = self.errors.get(&ty_id) {
            return err_info.name.clone();
        }
        if self.is_universal_opaque_type(ty_id) {
            return "void".to_string();
        }
        if let Some((mutable, pointee, _)) = self.as_nullable_raw_ptr(ty_id) {
            let pt = self.c_type_name(pointee);
            return if mutable {
                format!("{pt}*")
            } else {
                format!("const {pt}*")
            };
        }
        if let Some(&(mutable, pointee)) = self.raw_ptrs.get(&ty_id) {
            let pt = self.c_type_name(pointee);
            return if mutable {
                format!("{pt}*")
            } else {
                format!("const {pt}*")
            };
        }
        match &self.program.types[ty_id.0 as usize] {
            Type::Void | Type::Never => "void".to_string(),
            Type::Bool => "bool".to_string(),
            Type::F32 => "float".to_string(),
            Type::F64 => "double".to_string(),
            Type::Rune => "uint32_t".to_string(),
            Type::Int { signed: true, bits: 8 } => "int8_t".to_string(),
            Type::Int { signed: false, bits: 8 } => "uint8_t".to_string(),
            Type::Int { signed: true, bits: 16 } => "int16_t".to_string(),
            Type::Int { signed: false, bits: 16 } => "uint16_t".to_string(),
            Type::Int { signed: true, bits: 32 } => "int32_t".to_string(),
            Type::Int { signed: false, bits: 32 } => "uint32_t".to_string(),
            Type::Int { signed: true, bits: 64 } => "int64_t".to_string(),
            Type::Int { signed: false, bits: 64 } => "uint64_t".to_string(),
            other => format!("/* {} */ void", other),
        }
    }

    pub fn c_decl(&self, ty_id: TypeId, ident: &str) -> String {
        let mut cur = ty_id;
        let mut dims = String::new();
        while let Type::Array { elem, len } = self.program.types[cur.0 as usize] {
            dims.push_str(&format!("[{len}]"));
            cur = elem;
        }
        format!("{} {}{}", self.c_type_name(cur), ident, dims)
    }

    pub fn generate_c_header(&self) -> String {
        use std::fmt::Write as _;
        let mut out = String::new();
        writeln!(out, "#ifndef LRRR_EXPORT_H").unwrap();
        writeln!(out, "#define LRRR_EXPORT_H").unwrap();
        writeln!(out).unwrap();
        writeln!(out, "#include <stdint.h>").unwrap();
        writeln!(out, "#include <stddef.h>").unwrap();
        writeln!(out, "#include <stdbool.h>").unwrap();
        writeln!(out).unwrap();
        writeln!(out, "#ifdef __cplusplus").unwrap();
        writeln!(out, "extern \"C\" {{").unwrap();
        writeln!(out, "#endif").unwrap();
        writeln!(out).unwrap();

        // 1. Forward declarations for exported opaque types, opaque structs, and records
        let mut emitted_forwards = false;
        for meta in &self.exported_types {
            if self.named_opaques.contains(&meta.ty_id)
                || self.composites.contains_key(&meta.ty_id)
            {
                writeln!(out, "typedef struct {0} {0};", meta.name).unwrap();
                emitted_forwards = true;
            }
        }
        if emitted_forwards {
            writeln!(out).unwrap();
        }

        // 2. Concrete type definitions for exported enums, errors, newtypes/aliases, and records
        for meta in &self.exported_types {
            let tid = meta.ty_id;
            if let Some((_, variants)) = self.enums.get(&tid) {
                writeln!(out, "typedef enum {} {{", meta.name).unwrap();
                for (vname, val) in variants {
                    writeln!(out, "    {}_{} = {},", meta.name, vname, val).unwrap();
                }
                writeln!(out, "}} {};\n", meta.name).unwrap();
            } else if let Some(err_info) = self.errors.get(&tid) {
                writeln!(out, "typedef enum {} {{", meta.name).unwrap();
                for (idx, leaf) in err_info.leaves.iter().enumerate() {
                    if leaf.key.error_name == meta.name {
                        writeln!(out, "    {}_{} = {},", meta.name, leaf.key.variant_name, idx)
                            .unwrap();
                    } else {
                        writeln!(
                            out,
                            "    {}_{}_{} = {},",
                            meta.name, leaf.key.error_name, leaf.key.variant_name, idx
                        )
                        .unwrap();
                    }
                }
                writeln!(out, "}} {};\n", meta.name).unwrap();
            } else if let Some(nt) = self.opaque_newtypes.get(&tid) {
                writeln!(
                    out,
                    "typedef {} {};\n",
                    self.c_type_name(nt.underlying),
                    meta.name
                )
                .unwrap();
            } else if let Some(comp) = self.composites.get(&tid) {
                if !comp.is_struct {
                    writeln!(out, "struct {} {{", meta.name).unwrap();
                    for (fname, fty, _, _) in &comp.fields {
                        writeln!(out, "    {};", self.c_decl(*fty, fname)).unwrap();
                    }
                    writeln!(out, "}};\n").unwrap();
                }
            } else if !self.named_opaques.contains(&tid) {
                writeln!(out, "typedef {} {};\n", self.c_type_name(tid), meta.name).unwrap();
            }
        }

        // 3. Function prototypes for exported functions
        for fmeta in &self.exported_funcs {
            let mut c_params: Vec<String> = fmeta
                .params
                .iter()
                .map(|(pname, pty)| self.c_decl(*pty, pname))
                .collect();
            let ret_c = match &fmeta.ret_kind {
                ExportRetKind::Direct(ret_ty) => self.c_type_name(*ret_ty),
                ExportRetKind::OptionalPtr { raw_ptr_ty, .. } => self.c_type_name(*raw_ptr_ty),
                ExportRetKind::OptionalVal { val_ty, .. } => {
                    c_params.push(format!("/* out */ {}* out_val", self.c_type_name(*val_ty)));
                    "bool".to_string()
                }
                ExportRetKind::ResultVal { err_ty, ok_ty, .. } => {
                    c_params.push(format!("/* out */ {}* out_err", self.c_type_name(*err_ty)));
                    if !matches!(self.program.types[ok_ty.0 as usize], Type::Void) {
                        c_params.push(format!("/* out */ {}* out_val", self.c_type_name(*ok_ty)));
                    }
                    "bool".to_string()
                }
            };
            let params_str = if c_params.is_empty() {
                "void".to_string()
            } else {
                c_params.join(", ")
            };
            writeln!(out, "{} {}({});", ret_c, fmeta.symbol, params_str).unwrap();
        }

        writeln!(out).unwrap();
        writeln!(out, "#ifdef __cplusplus").unwrap();
        writeln!(out, "}}").unwrap();
        writeln!(out, "#endif").unwrap();
        writeln!(out).unwrap();
        writeln!(out, "#endif /* LRRR_EXPORT_H */").unwrap();
        out
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
            return Err(format!("Extern function '{name}' not found in '{mod_path}'"));
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
                    vis,
                    name: tname,
                    ..
                } if tname == name => {
                    self.check_item_visibility(from_mod, target_mod, name, *vis)?;
                    return Ok(Some((
                        target_mod.to_string(),
                        tname.clone(),
                        item.clone(),
                        *vis,
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
        if path.len() == 1 {
            let name = &path[0];
            // 1. Local module item
            if let Some((def_mod, orig_name, item, _)) =
                self.find_item_in_module(cur_mod, cur_mod, name)?
            {
                return Ok(match item {
                    Item::Func(_) => ResolvedItem::Func(def_mod, orig_name),
                    Item::ExternFunc(_) => ResolvedItem::ExternFunc(def_mod, orig_name),
                    Item::TypeDecl { .. } => ResolvedItem::Type(def_mod, orig_name),
                });
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
                                    return Ok(match item {
                                        Item::Func(_) => ResolvedItem::Func(def_mod, orig_name),
                                        Item::ExternFunc(_) => {
                                            ResolvedItem::ExternFunc(def_mod, orig_name)
                                        }
                                        Item::TypeDecl { .. } => {
                                            ResolvedItem::Type(def_mod, orig_name)
                                        }
                                    });
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
                                    return Ok(match item {
                                        Item::Func(_) => ResolvedItem::Func(def_mod, orig_name),
                                        Item::ExternFunc(_) => {
                                            ResolvedItem::ExternFunc(def_mod, orig_name)
                                        }
                                        Item::TypeDecl { .. } => {
                                            ResolvedItem::Type(def_mod, orig_name)
                                        }
                                    });
                                }
                            }
                        }
                        ImportTargets::Glob => {
                            if let Some((def_mod, orig_name, item, _)) =
                                self.find_item_in_module(cur_mod, &target_mod, name)?
                            {
                                return Ok(match item {
                                    Item::Func(_) => ResolvedItem::Func(def_mod, orig_name),
                                    Item::ExternFunc(_) => {
                                        ResolvedItem::ExternFunc(def_mod, orig_name)
                                    }
                                    Item::TypeDecl { .. } => {
                                        ResolvedItem::Type(def_mod, orig_name)
                                    }
                                });
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
            Ok(match item {
                Item::Func(_) => ResolvedItem::Func(def_mod, orig_name),
                Item::ExternFunc(_) => ResolvedItem::ExternFunc(def_mod, orig_name),
                Item::TypeDecl { .. } => ResolvedItem::Type(def_mod, orig_name),
            })
        }
    }

    fn is_linear_type(&self, ty_id: TypeId) -> bool {
        if self.program.linear_types.iter().any(|(t, _)| *t == ty_id) {
            return true;
        }
        if self.slices.contains_key(&ty_id) {
            return false;
        }
        match &self.program.types[ty_id.0 as usize] {
            Type::Struct(fields) => fields.iter().any(|&f| self.is_linear_type(f)),
            Type::Array { elem, len } => *len > 0 && self.is_linear_type(*elem),
            Type::Union { variants, .. } => variants.iter().any(|&v| self.is_linear_type(v)),
            _ => false,
        }
    }

    fn is_copy_type(&self, ty_id: TypeId) -> bool {
        if self.is_opaque_type(ty_id) || self.is_linear_type(ty_id) {
            return false;
        }
        if self.program.destructors.iter().any(|(t, _)| *t == ty_id) {
            return false;
        }
        if let Some(comp) = self.composites.get(&ty_id)
            && comp.is_struct
        {
            return comp.ownership == StructOwnership::Copy;
        }
        if let Some(slice_info) = self.slices.get(&ty_id) {
            return !slice_info.mutable;
        }
        if let Some(tobj_info) = self.trait_objs.get(&ty_id) {
            return !tobj_info.mutable;
        }
        match &self.program.types[ty_id.0 as usize] {
            Type::Ptr { mutable: true, .. } => self.raw_ptrs.contains_key(&ty_id),
            Type::Struct(fields) => fields.iter().all(|&f| self.is_copy_type(f)),
            Type::Array { elem, .. } => self.is_copy_type(*elem),
            Type::Union { variants, .. } => variants.iter().all(|&v| self.is_copy_type(v)),
            _ => true,
        }
    }

    fn is_send_type(&self, ty_id: TypeId) -> bool {
        if self.is_opaque_type(ty_id) || self.raw_ptrs.contains_key(&ty_id) {
            return false;
        }
        if let Some(&slice_info) = self.slices.get(&ty_id) {
            return if slice_info.mutable {
                self.is_send_type(slice_info.elem)
            } else {
                self.is_sync_type(slice_info.elem)
            };
        }
        if let Some(comp) = self.composites.get(&ty_id) {
            if comp.is_struct && comp.is_sync {
                return comp
                    .fields
                    .iter()
                    .all(|(_, f_ty, _, _)| self.raw_ptrs.contains_key(f_ty) || self.is_send_type(*f_ty));
            }
        }
        match &self.program.types[ty_id.0 as usize] {
            Type::Ptr { mutable, pointee } => {
                if *mutable {
                    self.is_send_type(*pointee)
                } else {
                    self.is_sync_type(*pointee)
                }
            }
            Type::Struct(fields) => fields.iter().all(|&f| self.is_send_type(f)),
            Type::Array { elem, .. } => self.is_send_type(*elem),
            Type::Union { variants, .. } => variants.iter().all(|&v| self.is_send_type(v)),
            Type::Pattern { base, .. } => self.is_send_type(*base),
            _ => true,
        }
    }

    fn is_sync_type(&self, ty_id: TypeId) -> bool {
        if self.is_opaque_type(ty_id) || self.raw_ptrs.contains_key(&ty_id) {
            return false;
        }
        if let Some(&slice_info) = self.slices.get(&ty_id) {
            return self.is_sync_type(slice_info.elem);
        }
        if let Some(comp) = self.composites.get(&ty_id) {
            if comp.is_struct && comp.is_sync {
                return comp
                    .fields
                    .iter()
                    .all(|(_, f_ty, _, _)| self.raw_ptrs.contains_key(f_ty) || self.is_send_type(*f_ty));
            }
        }
        match &self.program.types[ty_id.0 as usize] {
            Type::Ptr { pointee, .. } => self.is_sync_type(*pointee),
            Type::Struct(fields) => fields.iter().all(|&f| self.is_sync_type(f)),
            Type::Array { elem, .. } => self.is_sync_type(*elem),
            Type::Union { variants, .. } => variants.iter().all(|&v| self.is_sync_type(v)),
            Type::Pattern { base, .. } => self.is_sync_type(*base),
            _ => true,
        }
    }

    fn is_format_type(&self, ty_id: TypeId) -> bool {
        if self.is_opaque_type(ty_id)
            || self.raw_ptrs.contains_key(&ty_id)
            || self.closures.contains_key(&ty_id)
        {
            return false;
        }
        if let Some(&slice_info) = self.slices.get(&ty_id) {
            return slice_info.is_str || self.is_format_type(slice_info.elem);
        }
        if let Some(comp) = self.composites.get(&ty_id) {
            return if comp.is_struct {
                comp.has_format_hook
            } else {
                comp.fields
                    .iter()
                    .all(|(_, f_ty, _, _)| self.is_format_type(*f_ty))
            };
        }
        if self.enums.contains_key(&ty_id) {
            return true;
        }
        match &self.program.types[ty_id.0 as usize] {
            Type::Void | Type::Int { .. } | Type::F32 | Type::F64 | Type::Bool | Type::Rune => true,
            Type::Ptr { pointee, .. } => self.is_format_type(*pointee),
            Type::Struct(fields) => fields.iter().all(|&f| self.is_format_type(f)),
            Type::Array { elem, .. } => self.is_format_type(*elem),
            Type::Union { variants, .. } => variants.iter().all(|&v| self.is_format_type(v)),
            Type::Pattern { base, .. } => self.is_format_type(*base),
            _ => false,
        }
    }

    fn is_clone_type(&self, ty_id: TypeId) -> bool {
        if self.is_opaque_type(ty_id) || self.is_linear_type(ty_id) {
            return false;
        }
        if let Some(comp) = self.composites.get(&ty_id) {
            return if comp.is_struct {
                comp.ownership == StructOwnership::Copy || comp.clone_fn.is_some()
            } else {
                comp.fields
                    .iter()
                    .all(|(_, f_ty, _, _)| self.is_clone_type(*f_ty))
            };
        }
        self.is_copy_type(ty_id)
    }

    fn is_default_type(&self, ty_id: TypeId) -> bool {
        if self.is_opaque_type(ty_id) || self.opaque_newtypes.contains_key(&ty_id) {
            return false;
        }
        if let Some(comp) = self.composites.get(&ty_id) {
            return if comp.is_struct {
                comp.default_fn.is_some()
            } else {
                comp.fields
                    .iter()
                    .all(|(_, f_ty, _, f_def)| f_def.is_some() || self.is_default_type(*f_ty))
            };
        }
        if self.slices.contains_key(&ty_id) || self.raw_ptrs.contains_key(&ty_id) {
            return false;
        }
        match &self.program.types[ty_id.0 as usize] {
            Type::Bool | Type::Int { .. } | Type::Rune | Type::F32 | Type::F64 => true,
            Type::Struct(fields) => fields.iter().all(|&f| self.is_default_type(f)),
            Type::Array { elem, .. } | Type::Simd { elem, .. } => self.is_default_type(*elem),
            Type::Union { variants, .. } => {
                !self.results.contains_key(&ty_id)
                    && !self.errors.contains_key(&ty_id)
                    && !self.unions.contains_key(&ty_id)
                    && !variants.is_empty()
                    && matches!(self.program.types[variants[0].0 as usize], Type::Void)
            }
            _ => false,
        }
    }

    fn eval_where_clauses(
        &self,
        env: &HashMap<String, ComptimeVal>,
        clauses: &[WherePredicate],
    ) -> Result<bool, String> {
        for pred in clauses {
            let Some(ComptimeVal::Type(ty_id)) = env.get(&pred.type_param) else {
                return Err(format!(
                    "Unknown comptime type parameter '{}' in 'where' clause",
                    pred.type_param
                ));
            };
            let sat = self.type_satisfies_constraint(*ty_id, pred.constraint);
            let matched = if pred.negated { !sat } else { sat };
            if !matched {
                return Ok(false);
            }
        }
        Ok(true)
    }

    fn check_where_clauses_or_err(
        &self,
        env: &HashMap<String, ComptimeVal>,
        clauses: &[WherePredicate],
        item_desc: &str,
    ) -> Result<(), String> {
        for pred in clauses {
            let Some(ComptimeVal::Type(ty_id)) = env.get(&pred.type_param) else {
                return Err(format!(
                    "Unknown comptime type parameter '{}' in 'where' clause of {}",
                    pred.type_param, item_desc
                ));
            };
            let sat = self.type_satisfies_constraint(*ty_id, pred.constraint);
            let matched = if pred.negated { !sat } else { sat };
            if !matched {
                let t_disp = self
                    .composites
                    .get(ty_id)
                    .map(|c| c.name.clone())
                    .unwrap_or_else(|| self.program.types[ty_id.0 as usize].to_string());
                let neg_prefix = if pred.negated { "!" } else { "" };
                return Err(format!(
                    "Cannot call {}: where-clause constraint '{}: {}{}' is not satisfied for type '{}'",
                    item_desc,
                    pred.type_param,
                    neg_prefix,
                    pred.constraint.name(),
                    t_disp
                ));
            }
        }
        Ok(())
    }

    fn type_satisfies_constraint(&self, ty_id: TypeId, constraint: TypeConstraint) -> bool {
        if self.is_opaque_type(ty_id) {
            return matches!(constraint, TypeConstraint::AnyType);
        }
        let mut cur = &self.program.types[ty_id.0 as usize];
        if let Type::Pattern { base, .. } = cur {
            cur = &self.program.types[base.0 as usize];
        }
        let is_enum = self.enums.contains_key(&ty_id);
        let is_newtype = self.opaque_newtypes.contains_key(&ty_id);
        match constraint {
            TypeConstraint::AnyType => true,
            TypeConstraint::Send => self.is_send_type(ty_id),
            TypeConstraint::Sync => self.is_sync_type(ty_id),
            TypeConstraint::Format => self.is_format_type(ty_id),
            TypeConstraint::Clone => self.is_clone_type(ty_id),
            TypeConstraint::Default => self.is_default_type(ty_id),
            TypeConstraint::Scalar => {
                !is_enum
                    && !is_newtype
                    && matches!(
                        cur,
                        Type::Int { .. }
                            | Type::F32
                            | Type::F64
                            | Type::Bool
                            | Type::Rune
                            | Type::Ptr { .. }
                    )
            }
            TypeConstraint::Number => {
                !is_enum && !is_newtype && matches!(cur, Type::Int { .. } | Type::F32 | Type::F64)
            }
            TypeConstraint::Callable => {
                matches!(cur, Type::FnPtr { .. }) || self.closures.contains_key(&ty_id)
            }
            TypeConstraint::FnPtr => matches!(cur, Type::FnPtr { .. }),
            TypeConstraint::Closure => self.closures.contains_key(&ty_id),
            TypeConstraint::Integer => !is_enum && !is_newtype && matches!(cur, Type::Int { .. }),
            TypeConstraint::Signed => {
                !is_enum && !is_newtype && matches!(cur, Type::Int { signed: true, .. })
            }
            TypeConstraint::Unsigned => {
                !is_enum && !is_newtype && matches!(cur, Type::Int { signed: false, .. })
            }
            TypeConstraint::Float => !is_newtype && matches!(cur, Type::F32 | Type::F64),
            TypeConstraint::Aggregate => {
                self.type_satisfies_constraint(ty_id, TypeConstraint::Record)
                    || self.type_satisfies_constraint(ty_id, TypeConstraint::Tuple)
            }
            TypeConstraint::Record => self.composites.get(&ty_id).is_some_and(|c| !c.is_struct),
            TypeConstraint::Tuple => {
                matches!(cur, Type::Struct(_))
                    && !self.composites.contains_key(&ty_id)
                    && !self.trait_objs.contains_key(&ty_id)
                    && !self.closures.contains_key(&ty_id)
                    && !self.slices.contains_key(&ty_id)
            }
            TypeConstraint::Struct => self.composites.get(&ty_id).is_some_and(|c| c.is_struct),
            TypeConstraint::Copy => self.is_copy_type(ty_id),
            TypeConstraint::Affine => !self.is_copy_type(ty_id) && !self.is_linear_type(ty_id),
            TypeConstraint::Linear => self.is_linear_type(ty_id),
            TypeConstraint::Simd => matches!(cur, Type::Simd { .. }),
            TypeConstraint::Sequence => {
                matches!(cur, Type::Array { .. }) || self.slices.contains_key(&ty_id)
            }
            TypeConstraint::Array => matches!(cur, Type::Array { .. }),
            TypeConstraint::Slice => self.slices.contains_key(&ty_id),
            TypeConstraint::Discriminated => {
                self.type_satisfies_constraint(ty_id, TypeConstraint::Enum)
                    || self.type_satisfies_constraint(ty_id, TypeConstraint::Union)
                    || self.type_satisfies_constraint(ty_id, TypeConstraint::Error)
            }
            TypeConstraint::Enum => is_enum,
            TypeConstraint::Union => {
                matches!(cur, Type::Union { .. }) && !self.errors.contains_key(&ty_id)
            }
            TypeConstraint::Error => self.errors.contains_key(&ty_id),
        }
    }

    /// Collects all visible `FuncDecl`s (including disjoint meta-type overloads) named `name` in `target_mod`.
    fn find_funcs_in_module(
        &self,
        from_mod: &str,
        target_mod: &str,
        name: &str,
    ) -> Result<Vec<(String, String, FuncDecl)>, String> {
        let Some(ast) = self.modules.get(target_mod) else {
            return Err(format!("Undefined module '{target_mod}'"));
        };
        let mut out = Vec::new();
        for item in &ast.items {
            if let Item::Func(f) = item
                && f.name == name
            {
                self.check_item_visibility(from_mod, target_mod, name, f.vis)?;
                out.push((target_mod.to_string(), f.name.clone(), f.clone()));
            }
        }
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
                            out.extend(self.find_funcs_in_module(target_mod, &imp_mod, orig)?);
                        }
                    }
                }
                ImportTargets::Glob => {
                    if let Ok(found) = self.find_funcs_in_module(target_mod, &imp_mod, name) {
                        out.extend(found);
                    }
                }
                ImportTargets::Module(alias) => {
                    if !self.modules.contains_key(&imp_mod) && imp.path.len() >= 2 {
                        let parent_mod = imp.path[..imp.path.len() - 1].join("::");
                        let orig = imp.path.last().unwrap();
                        let bound = alias.as_deref().unwrap_or(orig);
                        if bound == name {
                            out.extend(self.find_funcs_in_module(target_mod, &parent_mod, orig)?);
                        }
                    }
                }
            }
        }
        Ok(out)
    }

    /// Collects all top-level functions visible in `cur_mod` under `name`
    /// (defined locally, imported by item/alias, or imported by glob `*`).
    /// Compiler-injected prelude imports (`imp.is_prelude`) have the lowest lexical priority
    /// and are only consulted when no local or explicitly imported function named `name` exists.
    fn find_in_scope_functions(
        &self,
        cur_mod: &str,
        name: &str,
    ) -> Result<Vec<(String, String, FuncDecl)>, String> {
        let mut results: Vec<(String, String, FuncDecl)> = Vec::new();
        let push_unique =
            |results: &mut Vec<(String, String, FuncDecl)>, m: String, orig: String, decl: FuncDecl| {
                if !results
                    .iter()
                    .any(|(em, eo, ed)| em == &m && eo == &orig && ed.params == decl.params)
                {
                    results.push((m, orig, decl));
                }
            };

        let Some(ast) = self.modules.get(cur_mod) else {
            return Ok(results);
        };

        // 1. Local functions in `cur_mod`
        for item in &ast.items {
            if let Item::Func(f) = item
                && f.name == name
            {
                push_unique(&mut results, cur_mod.to_string(), f.name.clone(), f.clone());
            }
        }

        // 2. Explicitly imported functions (`!imp.is_prelude`), then fallback to prelude (`imp.is_prelude`)
        for check_prelude in [false, true] {
            if check_prelude && !results.is_empty() {
                break;
            }
            for imp in &ast.imports {
                if imp.is_prelude != check_prelude {
                    continue;
                }
                let target_mod = imp.path.join("::");
                match &imp.targets {
                    ImportTargets::Items(list) => {
                        for (orig, alias) in list {
                            let bound = alias.as_deref().unwrap_or(orig);
                            if bound == name {
                                for (fm, fo, fd) in
                                    self.find_funcs_in_module(cur_mod, &target_mod, orig)?
                                {
                                    push_unique(&mut results, fm, fo, fd);
                                }
                            }
                        }
                    }
                    ImportTargets::Glob => {
                        if let Ok(found) = self.find_funcs_in_module(cur_mod, &target_mod, name) {
                            for (fm, fo, fd) in found {
                                push_unique(&mut results, fm, fo, fd);
                            }
                        }
                    }
                    ImportTargets::Module(alias) => {
                        if !self.modules.contains_key(&target_mod) && imp.path.len() >= 2 {
                            let parent_mod = imp.path[..imp.path.len() - 1].join("::");
                            let orig = imp.path.last().unwrap();
                            let bound = alias.as_deref().unwrap_or(orig);
                            if bound == name {
                                for (fm, fo, fd) in
                                    self.find_funcs_in_module(cur_mod, &parent_mod, orig)?
                                {
                                    push_unique(&mut results, fm, fo, fd);
                                }
                            }
                        }
                    }
                }
            }
        }

        Ok(results)
    }

    fn type_display_name(&self, ty_id: TypeId) -> String {
        if self.is_universal_opaque_type(ty_id) {
            return "opaque".to_string();
        }
        if let Some(nt) = self.opaque_newtypes.get(&ty_id) {
            return nt.name.clone();
        }
        if let Some(&ck) = self.c_ints.get(&ty_id) {
            return ck.name().to_string();
        }
        if let Some(&(mutable, pointee)) = self.raw_ptrs.get(&ty_id) {
            return format!(
                "*{}{}",
                if mutable { "mut " } else { "const " },
                self.type_display_name(pointee)
            );
        }
        if let Some(comp) = self.composites.get(&ty_id) {
            return comp.name.clone();
        }
        if let Some(tr) = self.traits.get(&ty_id) {
            return tr.name.clone();
        }
        if let Some(tobj) = self.trait_objs.get(&ty_id)
            && let Some(tr) = self.traits.get(&tobj.trait_ty)
        {
            return format!(
                "&{}{}",
                if tobj.mutable { "mut " } else { "" },
                tr.name
            );
        }
        if let Some((ename, _)) = self.enums.get(&ty_id) {
            return ename.clone();
        }
        if let Some(uinfo) = self.unions.get(&ty_id) {
            return uinfo.name.clone();
        }
        if let Some(einfo) = self.errors.get(&ty_id) {
            return einfo.name.clone();
        }
        if let Type::Ptr { mutable, pointee } = self.program.types[ty_id.0 as usize]
            && !self.slices.contains_key(&ty_id)
        {
            return format!(
                "&{}{}",
                if mutable { "mut " } else { "" },
                self.type_display_name(pointee)
            );
        }
        if let Type::Array { elem, len } = self.program.types[ty_id.0 as usize] {
            return format!("[{}; {}]", self.type_display_name(elem), len);
        }
        self.program.types[ty_id.0 as usize].to_string()
    }

    fn type_expr_mentions_self(te: &TypeExpr) -> bool {
        match te {
            TypeExpr::SelfType => true,
            TypeExpr::Named(p) => p.len() == 1 && p[0] == "Self",
            TypeExpr::Ref { inner, .. }
            | TypeExpr::Ptr { inner, .. }
            | TypeExpr::Optional(inner)
            | TypeExpr::Slice { elem: inner, .. }
            | TypeExpr::RelRef(inner)
            | TypeExpr::RelSlice(inner)
            | TypeExpr::Array { elem: inner, .. }
            | TypeExpr::Simd { elem: inner, .. }
            | TypeExpr::Pattern { base: inner, .. } => Self::type_expr_mentions_self(inner),
            TypeExpr::Result { err, ok } => {
                Self::type_expr_mentions_self(err) || Self::type_expr_mentions_self(ok)
            }
            TypeExpr::ErrorSetUnion(terms)
            | TypeExpr::TraitBounds(terms)
            | TypeExpr::Tuple(terms) => terms.iter().any(Self::type_expr_mentions_self),
            TypeExpr::FnPtr { params, ret } => {
                params.iter().any(Self::type_expr_mentions_self)
                    || Self::type_expr_mentions_self(ret)
            }
            TypeExpr::TypeCall { args, .. } => args.iter().any(|a| match a {
                Expr::TypeVal(inner_te) => Self::type_expr_mentions_self(inner_te),
                Expr::Path(p) => p.len() == 1 && p[0] == "Self",
                _ => false,
            }),
            _ => false,
        }
    }

    fn instantiate_trait(
        &mut self,
        mod_path: &str,
        type_name: &str,
        env: &HashMap<String, ComptimeVal>,
        memo_key: Option<(String, String, Vec<ComptimeVal>)>,
        methods: &[TraitMethodDecl],
    ) -> Result<TypeId, String> {
        let ty_id = self.alloc_distinct_type(Type::Void);
        self.traits.insert(
            ty_id,
            TraitInfo {
                name: type_name.to_string(),
                def_module: mod_path.to_string(),
                comptime_env: env.clone(),
                methods: methods.to_vec(),
            },
        );
        if let Some(key) = memo_key {
            self.memoized_type_calls.insert(key, ty_id);
        }
        Ok(ty_id)
    }

    fn instantiate_trait_obj_type(
        &mut self,
        trait_ty: TypeId,
        mutable: bool,
    ) -> Result<TypeId, String> {
        if let Some(&existing) = self.memoized_trait_objs.get(&(trait_ty, mutable)) {
            return Ok(existing);
        }
        let Some(trait_info) = self.traits.get(&trait_ty).cloned() else {
            return Err(format!("Type {trait_ty} is not a trait"));
        };
        let mut_prefix = if mutable { "mut " } else { "" };

        // Validate VTable Eligibility (Object Safety)
        for m in &trait_info.methods {
            if m.params.iter().any(|p| p.is_comptime) {
                return Err(format!(
                    "Trait '{}' is not object-safe and cannot form '&{}{}': method '{}' has comptime parameters",
                    trait_info.name, mut_prefix, trait_info.name, m.name
                ));
            }
            let Some(first_param) = m.params.first() else {
                return Err(format!(
                    "Trait '{}' is not object-safe and cannot form '&{}{}': method '{}' has no 'self: &Self' or 'self: &mut Self' receiver",
                    trait_info.name, mut_prefix, trait_info.name, m.name
                ));
            };
            let is_ref_self = first_param.name == "self"
                && matches!(
                    &first_param.ty,
                    TypeExpr::Ref { inner, .. }
                        if matches!(inner.as_ref(), TypeExpr::SelfType)
                            || matches!(inner.as_ref(), TypeExpr::Named(p) if p.len() == 1 && p[0] == "Self")
                );
            if !is_ref_self {
                return Err(format!(
                    "Trait '{}' is not object-safe and cannot form '&{}{}': method '{}' must take 'self: &Self' or 'self: &mut Self' (not by value or without receiver)",
                    trait_info.name, mut_prefix, trait_info.name, m.name
                ));
            }
            for p in &m.params[1..] {
                if Self::type_expr_mentions_self(&p.ty) {
                    return Err(format!(
                        "Trait '{}' is not object-safe and cannot form '&{}{}': parameter '{}' of method '{}' mentions 'Self'",
                        trait_info.name, mut_prefix, trait_info.name, p.name, m.name
                    ));
                }
            }
            if Self::type_expr_mentions_self(&m.ret_ty) {
                return Err(format!(
                    "Trait '{}' is not object-safe and cannot form '&{}{}': return type of method '{}' mentions 'Self'",
                    trait_info.name, mut_prefix, trait_info.name, m.name
                ));
            }
        }

        let u8_ty = self.intern_type(Type::Int {
            signed: false,
            bits: 8,
        });
        let data_ptr_ty = self.intern_type(Type::Ptr {
            mutable,
            pointee: u8_ty,
        });
        let mut method_fn_ptr_tys = Vec::with_capacity(trait_info.methods.len());
        for m in &trait_info.methods {
            let recv_mut = matches!(&m.params[0].ty, TypeExpr::Ref { mutable: true, .. });
            let erased_self_ty = self.intern_type(Type::Ptr {
                mutable: recv_mut,
                pointee: u8_ty,
            });
            let mut arg_tys = Vec::with_capacity(m.params.len());
            arg_tys.push(erased_self_ty);
            for p in &m.params[1..] {
                arg_tys.push(self.resolve_type_expr(
                    &trait_info.def_module,
                    None,
                    &trait_info.comptime_env,
                    &p.ty,
                )?);
            }
            let ret_ty = self.resolve_type_expr(
                &trait_info.def_module,
                None,
                &trait_info.comptime_env,
                &m.ret_ty,
            )?;
            method_fn_ptr_tys.push(self.intern_type(Type::FnPtr {
                args: arg_tys,
                ret: ret_ty,
            }));
        }

        let vtable_ty = self.alloc_distinct_type(Type::Struct(method_fn_ptr_tys.clone()));
        let vtable_ptr_ty = self.intern_type(Type::Ptr {
            mutable: false,
            pointee: vtable_ty,
        });
        let obj_ty = self.alloc_distinct_type(Type::Struct(vec![data_ptr_ty, vtable_ptr_ty]));
        self.trait_objs.insert(
            obj_ty,
            TraitObjInfo {
                trait_ty,
                mutable,
                data_ptr_ty,
                vtable_ty,
                vtable_ptr_ty,
                method_fn_ptr_tys,
            },
        );
        self.memoized_trait_objs.insert((trait_ty, mutable), obj_ty);
        Ok(obj_ty)
    }

    fn resolve_trait_impl_method(
        &mut self,
        caller_mod: &str,
        concrete_ty: TypeId,
        trait_ty: TypeId,
        method_idx: usize,
        enforce_orphan_rule: bool,
    ) -> Result<FuncId, String> {
        let trait_info = self.traits[&trait_ty].clone();
        let m = &trait_info.methods[method_idx];
        let type_display = self.type_display_name(concrete_ty);

        let has_ct_params = m.params.iter().any(|p| p.is_comptime);
        let mut expected_param_tys = Vec::new();
        let mut expected_ret_ty = None;
        if !has_ct_params {
            for p in &m.params {
                expected_param_tys.push(self.resolve_type_expr(
                    &trait_info.def_module,
                    Some(concrete_ty),
                    &trait_info.comptime_env,
                    &p.ty,
                )?);
            }
            expected_ret_ty = Some(self.resolve_type_expr(
                &trait_info.def_module,
                Some(concrete_ty),
                &trait_info.comptime_env,
                &m.ret_ty,
            )?);
        }

        // 1. Check inherent methods on `concrete_ty`
        if let Some(nt) = self.opaque_newtypes.get(&concrete_ty).cloned()
            && let Some((m_vis, m_decl)) = nt.methods.get(&m.name)
        {
            if *m_vis == Visibility::Private && caller_mod != nt.def_module {
                return Err(format!(
                    "Cannot satisfy trait '{}' for '{}' using private method '{}'",
                    trait_info.name, nt.name, m.name
                ));
            }
            if has_ct_params {
                if m_decl.params.len() != m.params.len() {
                    return Err(format!(
                        "Method '{}.{}' has {} parameters, but trait '{}' expects {}",
                        nt.name,
                        m.name,
                        m_decl.params.len(),
                        trait_info.name,
                        m.params.len()
                    ));
                }
                return Ok(FuncId(0));
            }
            let fn_id = nt.method_fn_ids[&m.name];
            let (actual_params, actual_ret) = self.func_sigs[&fn_id].clone();
            let exp_ret = expected_ret_ty.unwrap();
            if actual_params != expected_param_tys || actual_ret != exp_ret {
                return Err(format!(
                    "Method '{}.{}' has signature incompatible with trait '{}'",
                    nt.name, m.name, trait_info.name
                ));
            }
            return Ok(fn_id);
        }
        if let Some(comp) = self.composites.get(&concrete_ty).cloned()
            && let Some((m_vis, m_decl)) = comp.methods.get(&m.name)
        {
            if comp.is_struct && *m_vis == Visibility::Private && caller_mod != comp.def_module {
                return Err(format!(
                    "Cannot satisfy trait '{}' for struct '{}' using private method '{}'",
                    trait_info.name, comp.name, m.name
                ));
            }
            if has_ct_params {
                if m_decl.params.len() != m.params.len() {
                    return Err(format!(
                        "Method '{}.{}' has {} parameters, but trait '{}' expects {}",
                        comp.name,
                        m.name,
                        m_decl.params.len(),
                        trait_info.name,
                        m.params.len()
                    ));
                }
                return Ok(FuncId(0));
            }
            let fn_id = comp.method_fn_ids[&m.name];
            let (actual_params, actual_ret) = self.func_sigs[&fn_id].clone();
            let exp_ret = expected_ret_ty.unwrap();
            if actual_params != expected_param_tys || actual_ret != exp_ret {
                return Err(format!(
                    "Method '{}.{}' has signature incompatible with trait '{}'",
                    comp.name, m.name, trait_info.name
                ));
            }
            return Ok(fn_id);
        }

        // 2. Check module-level extension functions
        let t_def_mod = self
            .composites
            .get(&concrete_ty)
            .map(|c| c.def_module.clone())
            .or_else(|| {
                self.opaque_newtypes
                    .get(&concrete_ty)
                    .map(|nt| nt.def_module.clone())
            });
        let mut candidates = self.find_in_scope_functions(caller_mod, &m.name)?;
        if let Some(ref tm) = t_def_mod
            && tm != caller_mod
            && let Ok(found) = self.find_funcs_in_module(tm, tm, &m.name)
        {
            for item in found {
                if !candidates
                    .iter()
                    .any(|(em, eo, ed)| em == &item.0 && eo == &item.1 && ed.params == item.2.params)
                {
                    candidates.push(item);
                }
            }
        }
        if trait_info.def_module != caller_mod
            && let Ok(found) =
                self.find_funcs_in_module(&trait_info.def_module, &trait_info.def_module, &m.name)
        {
            for item in found {
                if !candidates
                    .iter()
                    .any(|(em, eo, ed)| em == &item.0 && eo == &item.1 && ed.params == item.2.params)
                {
                    candidates.push(item);
                }
            }
        }
        let all_mods: Vec<String> = self.modules.keys().cloned().collect();
        for mod_name in all_mods {
            if let Ok(found) = self.find_funcs_in_module(&mod_name, &mod_name, &m.name) {
                for item in found {
                    if !candidates.iter().any(|(em, eo, ed)| {
                        em == &item.0 && eo == &item.1 && ed.params == item.2.params
                    }) {
                        candidates.push(item);
                    }
                }
            }
        }

        let mut matched: Vec<(String, String, FuncDecl, HashMap<String, ComptimeVal>, u8)> =
            Vec::new();
        for (fn_mod, orig_name, decl) in candidates {
            let Some(self_param) = decl.params.iter().find(|p| !p.is_comptime) else {
                continue;
            };
            if self_param.name != "self" {
                continue;
            }
            let comptime_params: Vec<(String, TypeExpr)> = decl
                .params
                .iter()
                .filter(|p| p.is_comptime)
                .map(|p| (p.name.clone(), p.ty.clone()))
                .collect();
            let self_target_pat = match &self_param.ty {
                TypeExpr::Ref { inner, .. } => inner.as_ref(),
                other => other,
            };
            let mut inferred = HashMap::new();
            if let Some(specificity) = self.unify_type_pattern(
                &fn_mod,
                &comptime_params,
                self_target_pat,
                concrete_ty,
                &mut inferred,
            )? {
                matched.push((fn_mod, orig_name, decl, inferred, specificity));
            }
        }

        if matched.is_empty() {
            return Err(format!(
                "Type '{}' does not satisfy trait '{}': missing method '{}'",
                type_display, trait_info.name, m.name
            ));
        }

        let max_spec = matched.iter().map(|c| c.4).max().unwrap();
        let best: Vec<_> = matched.into_iter().filter(|c| c.4 == max_spec).collect();
        if best.len() > 1 {
            return Err(format!(
                "Ambiguous implementation of '{}.{}' for type '{}': conflicting definitions in module '{}' and module '{}'",
                trait_info.name, m.name, type_display, best[0].0, best[1].0
            ));
        }
        let (ext_mod, _, ext_decl, inferred, _) = best.into_iter().next().unwrap();

        if enforce_orphan_rule {
            let in_trait_mod = ext_mod == trait_info.def_module;
            let in_type_mod = t_def_mod.as_ref().is_some_and(|tm| tm == &ext_mod);
            if !in_trait_mod && !in_type_mod {
                let t_mod_disp = t_def_mod.as_deref().unwrap_or("<builtin>");
                return Err(format!(
                    "Orphan rule violation: extension method '{}' in module '{}' cannot satisfy trait '{}' (defined in '{}') for type '{}' (defined in '{}'); the method must be defined in either '{}' or '{}'",
                    m.name,
                    ext_mod,
                    trait_info.name,
                    trait_info.def_module,
                    type_display,
                    t_mod_disp,
                    t_mod_disp,
                    trait_info.def_module
                ));
            }
        }

        if has_ct_params {
            return Ok(FuncId(0));
        }

        let mut ct_args = Vec::new();
        for p in &ext_decl.params {
            if p.is_comptime {
                let Some(v) = inferred.get(&p.name) else {
                    return Err(format!(
                        "Extension method '{}' has unconstrained comptime parameter '{}' and cannot satisfy trait '{}'",
                        m.name, p.name, trait_info.name
                    ));
                };
                ct_args.push(v.clone());
            }
        }
        let fn_id = self.instantiate_specific_func_decl(&ext_mod, &ext_decl, &ct_args)?;
        let (actual_params, actual_ret) = self.func_sigs[&fn_id].clone();
        let exp_ret = expected_ret_ty.unwrap();
        if actual_params != expected_param_tys || actual_ret != exp_ret {
            return Err(format!(
                "Extension method '{}' for type '{}' has signature incompatible with trait '{}'",
                m.name, type_display, trait_info.name
            ));
        }
        Ok(fn_id)
    }

    fn get_or_create_vtable(
        &mut self,
        caller_mod: &str,
        concrete_ty: TypeId,
        trait_ty: TypeId,
    ) -> Result<(GlobalId, Vec<FuncId>), String> {
        if let Some(existing) = self.memoized_vtables.get(&(concrete_ty, trait_ty)).cloned() {
            return Ok(existing);
        }
        let obj_ty = self.instantiate_trait_obj_type(trait_ty, false)?;
        let tobj_info = self.trait_objs[&obj_ty].clone();
        let method_count = self.traits[&trait_ty].methods.len();
        let mut thunk_ids = Vec::with_capacity(method_count);

        for m_idx in 0..method_count {
            let target_fn_id =
                self.resolve_trait_impl_method(caller_mod, concrete_ty, trait_ty, m_idx, true)?;
            let fn_ptr_ty = tobj_info.method_fn_ptr_tys[m_idx];
            let Type::FnPtr {
                args: thunk_arg_tys,
                ret: thunk_ret_ty,
            } = self.program.types[fn_ptr_ty.0 as usize].clone()
            else {
                unreachable!()
            };
            let (impl_arg_tys, _) = self.func_sigs[&target_fn_id].clone();
            let thunk_id =
                self.reserve_function(Visibility::Private, None, &thunk_arg_tys, thunk_ret_ty);

            let typed_self_local = LocalId((thunk_arg_tys.len() + 1) as u32);
            let mut locals = vec![thunk_ret_ty];
            locals.extend_from_slice(&thunk_arg_tys);
            locals.push(impl_arg_tys[0]);

            let mut call_args = Vec::with_capacity(thunk_arg_tys.len());
            let self_op = if self.is_copy_type(impl_arg_tys[0]) {
                Operand::Copy(Place::new(typed_self_local))
            } else {
                Operand::Move(Place::new(typed_self_local))
            };
            call_args.push(self_op);
            for (i, &arg_ty) in thunk_arg_tys.iter().enumerate().skip(1) {
                let loc = LocalId((i + 1) as u32);
                if self.is_copy_type(arg_ty) {
                    call_args.push(Operand::Copy(Place::new(loc)));
                } else {
                    call_args.push(Operand::Move(Place::new(loc)));
                }
            }

            let blocks = vec![
                BasicBlock {
                    statements: vec![Statement::Assign(
                        Place::new(typed_self_local),
                        Rvalue::Cast(Operand::Copy(Place::new(LocalId(1))), impl_arg_tys[0]),
                    )],
                    terminator: Terminator::Call {
                        func: Operand::Const(ConstValue::Func(target_fn_id)),
                        args: call_args,
                        destination: Place::new(LocalId(0)),
                        target: BlockId(1),
                    },
                },
                BasicBlock {
                    statements: Vec::new(),
                    terminator: Terminator::Return,
                },
            ];

            let (target_rb, target_pb) = self
                .program
                .functions
                .iter()
                .find(|f| f.id == target_fn_id)
                .map(|f| (f.ret_borrows.clone(), f.param_borrows.clone()))
                .unwrap_or((None, None));

            if let Some(func) = self.program.functions.iter_mut().find(|f| f.id == thunk_id) {
                func.locals = locals;
                func.blocks = blocks;
                func.ret_borrows = target_rb;
                func.param_borrows = target_pb;
            }
            thunk_ids.push(thunk_id);
        }

        let gl_id = GlobalId(self.program.globals.len() as u32);
        self.program.globals.push(Global {
            id: gl_id,
            ty: tobj_info.vtable_ty,
            mutable: true,
            init: ConstValue::Void,
        });
        self.memoized_vtables
            .insert((concrete_ty, trait_ty), (gl_id, thunk_ids.clone()));
        Ok((gl_id, thunk_ids))
    }

    fn eval_comptime_type_bound(
        &mut self,
        bound_mod: &str,
        self_ty: Option<TypeId>,
        env: &HashMap<String, ComptimeVal>,
        bound_expr: &TypeExpr,
        actual_ty: TypeId,
    ) -> Result<Option<Result<u8, String>>, String> {
        match bound_expr {
            TypeExpr::MetaType => Ok(Some(Ok(1))),
            TypeExpr::Constraint(c) => {
                if self.type_satisfies_constraint(actual_ty, *c) {
                    Ok(Some(Ok(c.specificity())))
                } else {
                    Ok(Some(Err(format!(
                        "Type '{}' does not satisfy comptime constraint '{}'",
                        self.type_display_name(actual_ty),
                        c.name()
                    ))))
                }
            }
            TypeExpr::TraitBounds(bounds) => {
                let mut max_spec = 1u8;
                for b in bounds {
                    match self.eval_comptime_type_bound(bound_mod, self_ty, env, b, actual_ty)? {
                        Some(Ok(s)) => max_spec = max_spec.max(s),
                        Some(Err(e)) => return Ok(Some(Err(e))),
                        None => {
                            return Err(format!(
                                "Invalid non-trait/non-constraint bound '{b:?}' in '+' bound list"
                            ));
                        }
                    }
                }
                Ok(Some(Ok(max_spec)))
            }
            TypeExpr::Trait(_) | TypeExpr::Named(_) | TypeExpr::TypeCall { .. } => {
                let Ok(bound_ty_id) = self.resolve_type_expr(bound_mod, self_ty, env, bound_expr)
                else {
                    return Ok(None);
                };
                if self.traits.contains_key(&bound_ty_id) {
                    let method_count = self.traits[&bound_ty_id].methods.len();
                    for m_idx in 0..method_count {
                        if let Err(e) = self.resolve_trait_impl_method(
                            bound_mod,
                            actual_ty,
                            bound_ty_id,
                            m_idx,
                            true,
                        ) {
                            return Ok(Some(Err(e)));
                        }
                    }
                    Ok(Some(Ok(6)))
                } else if matches!(
                    self.program.types[bound_ty_id.0 as usize],
                    Type::MetaType
                ) {
                    Ok(Some(Ok(1)))
                } else {
                    Ok(None)
                }
            }
            _ => Ok(None),
        }
    }

    /// Unifies a `TypeExpr` pattern from a function in `fn_mod` against a concrete `actual_ty`,
    /// binding any `comptime_params` into `inferred` and returning a specificity score:
    /// - `20`: Concrete type match (`Point`, `i32`, `Pair(i32)`)
    /// - `11..=16`: Parameterized structural or type-constructor match (`simd[T; N]`, `[T; N]`, `?T`, `Pair(T)`),
    ///   sub-ranked by `T`'s meta-type or trait constraint
    /// - `1..=6`: Blanket generic type parameter (`T: type` = 1, `T: number` = 3, `T: signed` = 5, `T: MyTrait` = 6)
    fn unify_type_pattern(
        &mut self,
        fn_mod: &str,
        comptime_params: &[(String, TypeExpr)],
        pat: &TypeExpr,
        actual_ty: TypeId,
        inferred: &mut HashMap<String, ComptimeVal>,
    ) -> Result<Option<u8>, String> {
        match pat {
            TypeExpr::Named(path)
                if path.len() == 1 && comptime_params.iter().any(|(n, _)| n == &path[0]) =>
            {
                let (_, bound_expr) = comptime_params
                    .iter()
                    .find(|(n, _)| n == &path[0])
                    .unwrap()
                    .clone();
                let spec = match self.eval_comptime_type_bound(
                    fn_mod,
                    None,
                    inferred,
                    &bound_expr,
                    actual_ty,
                )? {
                    Some(Ok(s)) => s,
                    Some(Err(_)) => return Ok(None),
                    None => 1,
                };
                if let Some(existing) = inferred.get(&path[0]) {
                    Ok((existing == &ComptimeVal::Type(actual_ty)).then_some(spec))
                } else {
                    inferred.insert(path[0].clone(), ComptimeVal::Type(actual_ty));
                    Ok(Some(spec))
                }
            }
            TypeExpr::Ref { inner, .. } | TypeExpr::Ptr { inner, .. } => {
                if let Type::Ptr { pointee, .. } = self.program.types[actual_ty.0 as usize] {
                    self.unify_type_pattern(fn_mod, comptime_params, inner, pointee, inferred)
                } else {
                    Ok(None)
                }
            }
            TypeExpr::Simd { elem, len } => {
                let Type::Simd {
                    elem: act_elem,
                    len: act_len,
                } = self.program.types[actual_ty.0 as usize]
                else {
                    return Ok(None);
                };
                let Some(s1) =
                    self.unify_type_pattern(fn_mod, comptime_params, elem, act_elem, inferred)?
                else {
                    return Ok(None);
                };
                let Some(s2) = self.unify_comptime_expr(
                    fn_mod,
                    comptime_params,
                    len,
                    &ComptimeVal::Int(act_len as i128),
                    inferred,
                )?
                else {
                    return Ok(None);
                };
                Ok(Some(if s1 == 20 && s2 == 20 {
                    20
                } else {
                    10 + s1.min(9)
                }))
            }
            TypeExpr::Array { elem, len } => {
                let Type::Array {
                    elem: act_elem,
                    len: act_len,
                } = self.program.types[actual_ty.0 as usize]
                else {
                    return Ok(None);
                };
                let Some(s1) =
                    self.unify_type_pattern(fn_mod, comptime_params, elem, act_elem, inferred)?
                else {
                    return Ok(None);
                };
                let Some(s2) = self.unify_comptime_expr(
                    fn_mod,
                    comptime_params,
                    len,
                    &ComptimeVal::Int(act_len as i128),
                    inferred,
                )?
                else {
                    return Ok(None);
                };
                Ok(Some(if s1 == 20 && s2 == 20 {
                    20
                } else {
                    10 + s1.min(9)
                }))
            }
            TypeExpr::Slice { mutable, elem } => {
                let act_elem = if let Some(&info) = self.slices.get(&actual_ty) {
                    if *mutable && !info.mutable {
                        return Ok(None);
                    }
                    info.elem
                } else if let Type::Ptr {
                    mutable: act_mut,
                    pointee,
                } = self.program.types[actual_ty.0 as usize]
                    && let Type::Array { elem: arr_elem, .. } =
                        self.program.types[pointee.0 as usize]
                {
                    if *mutable && !act_mut {
                        return Ok(None);
                    }
                    arr_elem
                } else {
                    return Ok(None);
                };
                let Some(s) =
                    self.unify_type_pattern(fn_mod, comptime_params, elem, act_elem, inferred)?
                else {
                    return Ok(None);
                };
                Ok(Some(if s == 20 { 20 } else { 10 + s.min(9) }))
            }
            TypeExpr::Optional(inner) => {
                if self.results.contains_key(&actual_ty)
                    || self.errors.contains_key(&actual_ty)
                    || self.unions.contains_key(&actual_ty)
                {
                    return Ok(None);
                }
                let Type::Union { variants, .. } =
                    self.program.types[actual_ty.0 as usize].clone()
                else {
                    return Ok(None);
                };
                if variants.len() != 2
                    || !matches!(self.program.types[variants[0].0 as usize], Type::Void)
                {
                    return Ok(None);
                }
                let Some(s) = self.unify_type_pattern(
                    fn_mod,
                    comptime_params,
                    inner,
                    variants[1],
                    inferred,
                )?
                else {
                    return Ok(None);
                };
                Ok(Some(if s == 20 { 20 } else { 10 + s.min(9) }))
            }
            TypeExpr::Result { err, ok } => {
                let Some(&res_info) = self.results.get(&actual_ty) else {
                    return Ok(None);
                };
                let Some(s_err) = self.unify_type_pattern(
                    fn_mod,
                    comptime_params,
                    err,
                    res_info.err_ty,
                    inferred,
                )?
                else {
                    return Ok(None);
                };
                let Some(s_ok) = self.unify_type_pattern(
                    fn_mod,
                    comptime_params,
                    ok,
                    res_info.ok_ty,
                    inferred,
                )?
                else {
                    return Ok(None);
                };
                let min_s = s_err.min(s_ok);
                Ok(Some(if min_s == 20 { 20 } else { 10 + min_s.min(9) }))
            }
            TypeExpr::Tuple(elems) => {
                if self.composites.contains_key(&actual_ty)
                    || self.trait_objs.contains_key(&actual_ty)
                    || self.closures.contains_key(&actual_ty)
                    || self.slices.contains_key(&actual_ty)
                {
                    return Ok(None);
                }
                let Type::Struct(act_fields) = self.program.types[actual_ty.0 as usize].clone()
                else {
                    return Ok(None);
                };
                if act_fields.len() != elems.len() {
                    return Ok(None);
                }
                let mut all_concrete = true;
                let mut min_sub = 9u8;
                for (e_pat, act_f) in elems.iter().zip(act_fields.iter()) {
                    let Some(s) =
                        self.unify_type_pattern(fn_mod, comptime_params, e_pat, *act_f, inferred)?
                    else {
                        return Ok(None);
                    };
                    if s < 20 {
                        all_concrete = false;
                        min_sub = min_sub.min(s);
                    }
                }
                Ok(Some(if all_concrete { 20 } else { 10 + min_sub }))
            }
            TypeExpr::FnPtr { params, ret } => {
                let Type::FnPtr {
                    args: act_args,
                    ret: act_ret,
                } = self.program.types[actual_ty.0 as usize].clone()
                else {
                    return Ok(None);
                };
                if act_args.len() != params.len() {
                    return Ok(None);
                }
                let mut all_concrete = true;
                let mut min_sub = 9u8;
                for (p_pat, act_a) in params.iter().zip(act_args.iter()) {
                    let Some(s) =
                        self.unify_type_pattern(fn_mod, comptime_params, p_pat, *act_a, inferred)?
                    else {
                        return Ok(None);
                    };
                    if s < 20 {
                        all_concrete = false;
                        min_sub = min_sub.min(s);
                    }
                }
                let Some(rs) =
                    self.unify_type_pattern(fn_mod, comptime_params, ret, act_ret, inferred)?
                else {
                    return Ok(None);
                };
                if rs < 20 {
                    all_concrete = false;
                    min_sub = min_sub.min(rs);
                }
                Ok(Some(if all_concrete { 20 } else { 10 + min_sub }))
            }
            TypeExpr::TypeCall { path, args } => {
                let Ok(ResolvedItem::Func(target_mod, target_fn)) =
                    self.resolve_path(fn_mod, path)
                else {
                    return Ok(None);
                };
                let memo_match = self
                    .memoized_type_calls
                    .iter()
                    .find(|((m_mod, m_fn, m_args), m_ty_id)| {
                        **m_ty_id == actual_ty
                            && m_mod == &target_mod
                            && m_fn == &target_fn
                            && m_args.len() == args.len()
                    })
                    .map(|((_, _, m_args), _)| m_args.clone());
                let Some(m_args) = memo_match else {
                    return Ok(None);
                };
                let mut all_concrete = true;
                let mut min_sub = 9u8;
                for (arg_expr, actual_val) in args.iter().zip(m_args.iter()) {
                    let Some(s) = self.unify_comptime_expr(
                        fn_mod,
                        comptime_params,
                        arg_expr,
                        actual_val,
                        inferred,
                    )?
                    else {
                        return Ok(None);
                    };
                    if s < 20 {
                        all_concrete = false;
                        min_sub = min_sub.min(s);
                    }
                }
                Ok(Some(if all_concrete { 20 } else { 10 + min_sub }))
            }
            _ => {
                if let Ok(resolved_ty) = self.resolve_type_expr(fn_mod, None, inferred, pat)
                    && resolved_ty == actual_ty
                {
                    Ok(Some(20))
                } else {
                    Ok(None)
                }
            }
        }
    }

    fn unify_comptime_expr(
        &mut self,
        fn_mod: &str,
        comptime_params: &[(String, TypeExpr)],
        expr: &Expr,
        actual: &ComptimeVal,
        inferred: &mut HashMap<String, ComptimeVal>,
    ) -> Result<Option<u8>, String> {
        match expr {
            Expr::Path(p)
                if p.len() == 1 && comptime_params.iter().any(|(n, _)| n == &p[0]) =>
            {
                let (_, bound_expr) = comptime_params
                    .iter()
                    .find(|(n, _)| n == &p[0])
                    .unwrap()
                    .clone();
                let spec = if let ComptimeVal::Type(act_ty) = actual {
                    match self.eval_comptime_type_bound(
                        fn_mod,
                        None,
                        inferred,
                        &bound_expr,
                        *act_ty,
                    )? {
                        Some(Ok(s)) => s,
                        Some(Err(_)) => return Ok(None),
                        None => 1,
                    }
                } else {
                    1
                };
                if let Some(existing) = inferred.get(&p[0]) {
                    Ok((existing == actual).then_some(spec))
                } else {
                    inferred.insert(p[0].clone(), actual.clone());
                    Ok(Some(spec))
                }
            }
            Expr::TypeVal(te) => {
                if let ComptimeVal::Type(act_ty) = actual {
                    self.unify_type_pattern(fn_mod, comptime_params, te, *act_ty, inferred)
                } else {
                    Ok(None)
                }
            }
            _ => {
                if let Ok(val) = self.eval_comptime_val(fn_mod, None, inferred, expr)
                    && &val == actual
                {
                    Ok(Some(20))
                } else {
                    Ok(None)
                }
            }
        }
    }

    /// Resolves a `self`-receiver extension function in `cur_mod` for receiver base type `comp_ty`.
    fn resolve_extension_method(
        &mut self,
        cur_mod: &str,
        comp_ty: TypeId,
        method_name: &str,
    ) -> Result<(String, String, FuncDecl, HashMap<String, ComptimeVal>), String> {
        let mut candidates = self.find_in_scope_functions(cur_mod, method_name)?;
        // Also check the composite's/newtype's defining module if `comp_ty` is a user-defined type
        // and no candidates were found in `cur_mod` (e.g. inside a generic function).
        if candidates.is_empty() {
            let def_mod_opt = self
                .composites
                .get(&comp_ty)
                .map(|c| c.def_module.clone())
                .or_else(|| {
                    self.opaque_newtypes
                        .get(&comp_ty)
                        .map(|nt| nt.def_module.clone())
                });
            if let Some(def_mod) = def_mod_opt
                && def_mod != cur_mod
                && let Ok(found) = self.find_funcs_in_module(cur_mod, &def_mod, method_name)
            {
                candidates.extend(found);
            }
        }
        // Also check defining modules of traits that declare `method_name`
        if candidates.is_empty() {
            let trait_mods: Vec<String> = self
                .traits
                .values()
                .filter(|tr| {
                    tr.def_module != cur_mod && tr.methods.iter().any(|m| m.name == method_name)
                })
                .map(|tr| tr.def_module.clone())
                .collect();
            for tmod in trait_mods {
                if let Ok(found) = self.find_funcs_in_module(&tmod, &tmod, method_name) {
                    for item in found {
                        if !candidates.iter().any(|(em, eo, ed)| {
                            em == &item.0 && eo == &item.1 && ed.params == item.2.params
                        }) {
                            candidates.push(item);
                        }
                    }
                }
            }
        }

        let mut matched: Vec<(String, String, FuncDecl, HashMap<String, ComptimeVal>, u8)> =
            Vec::new();

        for (fn_mod, orig_name, decl) in candidates {
            let Some(self_param) = decl.params.iter().find(|p| !p.is_comptime) else {
                continue;
            };
            if self_param.name != "self" {
                continue;
            }
            let comptime_params: Vec<(String, TypeExpr)> = decl
                .params
                .iter()
                .filter(|p| p.is_comptime)
                .map(|p| (p.name.clone(), p.ty.clone()))
                .collect();
            let self_target_pat = match &self_param.ty {
                TypeExpr::Ref { inner, .. } | TypeExpr::Ptr { inner, .. } => inner.as_ref(),
                other => other,
            };
            let mut inferred = HashMap::new();
            if let Some(specificity) = self.unify_type_pattern(
                &fn_mod,
                &comptime_params,
                self_target_pat,
                comp_ty,
                &mut inferred,
            )? {
                matched.push((fn_mod, orig_name, decl, inferred, specificity));
            }
        }

        let type_display = self.type_display_name(comp_ty);

        if matched.is_empty() {
            return Err(format!(
                "Type '{}' has no method '{}'",
                type_display, method_name
            ));
        }

        let max_spec = matched.iter().map(|m| m.4).max().unwrap();
        let best: Vec<_> = matched.into_iter().filter(|m| m.4 == max_spec).collect();
        if best.len() > 1 {
            return Err(format!(
                "Ambiguous extension method '{}' for type '{}': conflicting definitions in module '{}' and module '{}'",
                method_name, type_display, best[0].0, best[1].0
            ));
        }

        let (fn_mod, orig_name, decl, inferred, _) = best.into_iter().next().unwrap();
        Ok((fn_mod, orig_name, decl, inferred))
    }

    fn resolve_named_type(&mut self, mod_path: &str, name: &str) -> Result<TypeId, String> {
        let key = (mod_path.to_string(), name.to_string());
        if let Some(&id) = self.named_types.get(&key) {
            return Ok(id);
        }
        let Some((def_mod, orig_name, Item::TypeDecl { vis, ty, .. }, _)) =
            self.find_item_in_module(mod_path, mod_path, name)?
        else {
            return Err(format!("Type '{name}' not found in '{mod_path}'"));
        };
        let env = HashMap::new();
        let ty_id = self.instantiate_type_decl(&def_mod, &orig_name, &env, &ty)?;
        self.named_types.insert(key, ty_id);
        if vis.is_export() {
            self.register_and_validate_exported_type(&def_mod, &orig_name, ty_id, &ty)?;
        }
        Ok(ty_id)
    }

    pub fn as_optional_type(&self, ty_id: TypeId) -> Option<TypeId> {
        if self.results.contains_key(&ty_id)
            || self.errors.contains_key(&ty_id)
            || self.unions.contains_key(&ty_id)
        {
            return None;
        }
        if let Type::Union { variants, .. } = &self.program.types[ty_id.0 as usize]
            && variants.len() == 2
            && matches!(self.program.types[variants[0].0 as usize], Type::Void)
        {
            Some(variants[1])
        } else {
            None
        }
    }

    pub fn as_nullable_raw_ptr(&self, ty_id: TypeId) -> Option<(bool, TypeId, TypeId)> {
        let inner = self.as_optional_type(ty_id)?;
        let &(mutable, pointee) = self.raw_ptrs.get(&inner)?;
        Some((mutable, pointee, inner))
    }

    fn register_and_validate_exported_type(
        &mut self,
        _def_mod: &str,
        orig_name: &str,
        ty_id: TypeId,
        ty_expr: &TypeExpr,
    ) -> Result<(), String> {
        if !self.exported_type_set.insert(ty_id)
            && self.exported_types.iter().any(|m| m.ty_id == ty_id)
        {
            return Ok(());
        }
        match ty_expr {
            TypeExpr::Union(_) => {
                return Err(format!(
                    "Tagged 'union' types cannot be declared 'export' ('{orig_name}'); use an 'export record' with an explicit tag or an 'export struct' opaque handle"
                ));
            }
            TypeExpr::Trait(_) => {
                return Err(format!(
                    "Traits cannot be declared 'export' ('{orig_name}')"
                ));
            }
            TypeExpr::Error(_) => {
                let void_ty = self.intern_type(Type::Void);
                if let Some(err_info) = self.errors.get(&ty_id) {
                    for leaf in &err_info.leaves {
                        if leaf.payload_ty != void_ty {
                            return Err(format!(
                                "Exported error type '{}' cannot have payload-carrying variant '{}::{}'; 'export error' is restricted to unit variants",
                                orig_name, leaf.key.error_name, leaf.key.variant_name
                            ));
                        }
                    }
                }
            }
            TypeExpr::Record { .. } => {
                if let Some(comp) = self.composites.get(&ty_id).cloned() {
                    for (fname, fty, _, _) in &comp.fields {
                        self.validate_export_field_type(
                            *fty,
                            &format!("field '{}' of export record '{}'", fname, orig_name),
                        )?;
                    }
                }
            }
            TypeExpr::Struct { .. } | TypeExpr::Opaque | TypeExpr::OpaqueDef { .. } | TypeExpr::Enum(_) => {}
            TypeExpr::OpaqueNewtype { .. } => {
                if let Some(nt) = self.opaque_newtypes.get(&ty_id).cloned() {
                    self.validate_export_value_type(
                        nt.underlying,
                        &format!("export opaque newtype '{}'", orig_name),
                    )?;
                }
            }
            _ => {
                if let Some(err_info) = self.errors.get(&ty_id).cloned() {
                    let void_ty = self.intern_type(Type::Void);
                    for leaf in &err_info.leaves {
                        if leaf.payload_ty != void_ty {
                            return Err(format!(
                                "Exported error type '{}' cannot have payload-carrying variant '{}::{}'; 'export error' is restricted to unit variants",
                                orig_name, leaf.key.error_name, leaf.key.variant_name
                            ));
                        }
                    }
                } else {
                    self.validate_export_value_type(
                        ty_id,
                        &format!("export type '{orig_name}'"),
                    )?;
                }
            }
        }
        if !self.exported_types.iter().any(|m| m.ty_id == ty_id) {
            self.exported_types.push(ExportedTypeMeta {
                name: orig_name.to_string(),
                ty_id,
            });
        }
        Ok(())
    }

    fn validate_export_pointee_type(&self, pointee: TypeId, ctx: &str) -> Result<(), String> {
        if self.is_universal_opaque_type(pointee) {
            return Ok(());
        }
        if self.named_opaques.contains(&pointee) {
            if !self.exported_type_set.contains(&pointee) {
                return Err(format!(
                    "Cannot use pointer to non-exported opaque type '{}' in {}; declare it with 'export opaque {}'",
                    self.type_display_name(pointee),
                    ctx,
                    self.type_display_name(pointee)
                ));
            }
            return Ok(());
        }
        if let Some(comp) = self.composites.get(&pointee)
            && comp.is_struct
        {
            if !self.exported_type_set.contains(&pointee) {
                return Err(format!(
                    "Cannot use pointer to non-exported struct '{}' in {}; declare it with 'export struct {}'",
                    comp.name, ctx, comp.name
                ));
            }
            return Ok(());
        }
        self.validate_export_field_type(pointee, ctx)
    }

    fn validate_export_field_type(&self, ty_id: TypeId, ctx: &str) -> Result<(), String> {
        if let Type::Array { elem, .. } = self.program.types[ty_id.0 as usize] {
            return self.validate_export_field_type(elem, ctx);
        }
        self.validate_export_value_type(ty_id, ctx)
    }

    fn validate_export_value_type(&self, ty_id: TypeId, ctx: &str) -> Result<(), String> {
        if self.slices.contains_key(&ty_id) {
            return Err(format!(
                "Safe slice or string reference '{}' is forbidden across FFI in {}; pass a raw pointer and length instead",
                self.type_display_name(ty_id),
                ctx
            ));
        }
        if self.trait_objs.contains_key(&ty_id) {
            return Err(format!(
                "Dynamic trait reference '{}' is forbidden across FFI in {}",
                self.type_display_name(ty_id),
                ctx
            ));
        }
        if let Some((_, pointee, _)) = self.as_nullable_raw_ptr(ty_id) {
            return self.validate_export_pointee_type(pointee, ctx);
        }
        if let Some(&(_, pointee)) = self.raw_ptrs.get(&ty_id) {
            return self.validate_export_pointee_type(pointee, ctx);
        }
        if matches!(self.program.types[ty_id.0 as usize], Type::Ptr { .. }) {
            return Err(format!(
                "Safe reference '{}' is forbidden across FFI in {}; use raw pointers ('*const T', '*mut T', '?*const T', '?*mut T') instead",
                self.type_display_name(ty_id),
                ctx
            ));
        }
        if let Some(comp) = self.composites.get(&ty_id) {
            if comp.is_struct {
                return Err(format!(
                    "Struct '{}' cannot be passed, returned, or embedded by value in {}; 'export struct' is an opaque handle type and must be passed behind a raw pointer ('*const {}' or '*mut {}')",
                    comp.name, ctx, comp.name, comp.name
                ));
            }
            if !self.exported_type_set.contains(&ty_id) {
                return Err(format!(
                    "Record '{}' used in {} is not declared 'export'; declare it with 'export record {}'",
                    comp.name, ctx, comp.name
                ));
            }
            return Ok(());
        }
        if let Some((ename, _)) = self.enums.get(&ty_id) {
            if !self.exported_type_set.contains(&ty_id) {
                return Err(format!(
                    "Enum '{}' used in {} is not declared 'export'; declare it with 'export enum {}'",
                    ename, ctx, ename
                ));
            }
            return Ok(());
        }
        if let Some(err_info) = self.errors.get(&ty_id) {
            if !self.exported_type_set.contains(&ty_id) {
                return Err(format!(
                    "Error type '{}' used in {} is not declared 'export'; declare it with 'export error {}'",
                    err_info.name, ctx, err_info.name
                ));
            }
            let void_ty = TypeId(0);
            for leaf in &err_info.leaves {
                if !matches!(self.program.types[leaf.payload_ty.0 as usize], Type::Void)
                    && leaf.payload_ty != void_ty
                {
                    return Err(format!(
                        "Error type '{}' used in {} has payload-carrying variant '{}::{}'; exported errors are restricted to unit variants",
                        err_info.name, ctx, leaf.key.error_name, leaf.key.variant_name
                    ));
                }
            }
            return Ok(());
        }
        if let Some(u_info) = self.unions.get(&ty_id) {
            return Err(format!(
                "Tagged union '{}' is forbidden across FFI in {}",
                u_info.name, ctx
            ));
        }
        if let Some(nt) = self.opaque_newtypes.get(&ty_id) {
            if !self.exported_type_set.contains(&ty_id) {
                return Err(format!(
                    "Opaque newtype '{}' used in {} is not declared 'export'; declare it with 'export type {} = opaque ...'",
                    nt.name, ctx, nt.name
                ));
            }
            return self.validate_export_value_type(nt.underlying, ctx);
        }
        if self.is_opaque_type(ty_id) {
            return Err(format!(
                "Unsized opaque type '{}' cannot be used by value in {}",
                self.type_display_name(ty_id),
                ctx
            ));
        }
        if self.c_ints.contains_key(&ty_id) {
            return Ok(());
        }
        match &self.program.types[ty_id.0 as usize] {
            Type::Void | Type::Bool | Type::F32 | Type::F64 | Type::Rune => Ok(()),
            Type::Int { bits, .. } if matches!(*bits, 8 | 16 | 32 | 64) => Ok(()),
            Type::Array { .. } => Err(format!(
                "Bare fixed-size array '{}' cannot be passed or returned by value in {}; wrap it in an 'export record' or pass a pointer",
                self.type_display_name(ty_id),
                ctx
            )),
            _ => Err(format!(
                "Type '{}' is not valid across C FFI in {}",
                self.type_display_name(ty_id),
                ctx
            )),
        }
    }

    fn instantiate_type_decl(
        &mut self,
        mod_path: &str,
        type_name: &str,
        env: &HashMap<String, ComptimeVal>,
        ty_expr: &TypeExpr,
    ) -> Result<TypeId, String> {
        match ty_expr {
            TypeExpr::Opaque => self.instantiate_named_opaque(mod_path, type_name, env, None, &[]),
            TypeExpr::OpaqueDef { methods } => {
                self.instantiate_named_opaque(mod_path, type_name, env, None, methods)
            }
            TypeExpr::OpaqueNewtype {
                underlying,
                methods,
            } => self.instantiate_opaque_newtype(
                mod_path,
                type_name,
                env,
                None,
                underlying,
                methods,
            ),
            TypeExpr::Trait(methods) => {
                self.instantiate_trait(mod_path, type_name, env, None, methods)
            }
            TypeExpr::Enum(variants) => self.instantiate_enum(type_name, variants),
            TypeExpr::Union(variants) => {
                self.instantiate_union(mod_path, type_name, env, None, variants)
            }
            TypeExpr::Error(items) => {
                self.instantiate_error(mod_path, type_name, env, None, items)
            }
            TypeExpr::Record { fields, methods } => {
                self.instantiate_composite(
                    mod_path,
                    type_name,
                    false,
                    StructOwnership::Copy,
                    false,
                    env,
                    None,
                    fields,
                    methods,
                    None,
                    &[],
                    &[],
                    None,
                )
            }
            TypeExpr::Struct {
                ownership,
                is_sync,
                fields,
                methods,
                default_hook,
                clone_hooks,
                drop_hooks,
                format_hook,
            } => self.instantiate_composite(
                mod_path,
                type_name,
                true,
                *ownership,
                *is_sync,
                env,
                None,
                fields,
                methods,
                default_hook.clone(),
                clone_hooks,
                drop_hooks,
                format_hook.clone(),
            ),
            other => self.resolve_type_expr(mod_path, None, env, other),
        }
    }

    fn instantiate_named_opaque(
        &mut self,
        mod_path: &str,
        type_name: &str,
        env: &HashMap<String, ComptimeVal>,
        memo_key: Option<(String, String, Vec<ComptimeVal>)>,
        methods: &[FuncDecl],
    ) -> Result<TypeId, String> {
        let ty_id = self.alloc_distinct_type(Type::Int {
            signed: false,
            bits: 8,
        });
        self.named_opaques.insert(ty_id);
        let mut method_map = HashMap::new();
        for m in methods {
            method_map.insert(m.name.clone(), (m.vis, m.clone()));
        }
        let info = CompositeInfo {
            name: type_name.to_string(),
            is_struct: true,
            ownership: StructOwnership::Affine,
            is_sync: false,
            has_format_hook: false,
            def_module: mod_path.to_string(),
            comptime_env: env.clone(),
            fields: Vec::new(),
            rel_fields: HashMap::new(),
            methods: method_map,
            method_fn_ids: HashMap::new(),
            default_fn: None,
            clone_fn: None,
            drop_fn: None,
            format_fn: None,
        };
        self.composites.insert(ty_id, info);
        if let Some(key) = memo_key {
            self.memoized_type_calls.insert(key, ty_id);
        } else if !type_name.starts_with('<') {
            self.named_types
                .insert((mod_path.to_string(), type_name.to_string()), ty_id);
        }
        if let Ok(Some((_, _, Item::TypeDecl { vis, .. }, _))) =
            self.find_item_in_module(mod_path, mod_path, type_name)
            && vis.is_export()
        {
            self.exported_type_set.insert(ty_id);
        }
        for m in methods {
            if m.vis.is_export() && m.params.iter().any(|p| p.is_comptime) {
                return Err(format!(
                    "Exported method '{}.{}' cannot have 'comptime' parameters",
                    type_name, m.name
                ));
            }
            if !m.params.iter().any(|p| p.is_comptime)
                && self.eval_where_clauses(env, &m.where_clauses)?
            {
                let fn_id = self.schedule_method(mod_path, ty_id, env, m)?;
                self.composites
                    .get_mut(&ty_id)
                    .unwrap()
                    .method_fn_ids
                    .insert(m.name.clone(), fn_id);
            }
        }
        Ok(ty_id)
    }

    fn instantiate_opaque_newtype(
        &mut self,
        mod_path: &str,
        type_name: &str,
        env: &HashMap<String, ComptimeVal>,
        memo_key: Option<(String, String, Vec<ComptimeVal>)>,
        underlying_expr: &TypeExpr,
        methods: &[FuncDecl],
    ) -> Result<TypeId, String> {
        let underlying_id = self.resolve_type_expr(mod_path, None, env, underlying_expr)?;
        if self.is_opaque_type(underlying_id) {
            return Err(format!(
                "Opaque newtype '{}' cannot wrap unsized opaque type '{}'",
                type_name,
                self.type_display_name(underlying_id)
            ));
        }
        let underlying_stage3 = self.program.types[underlying_id.0 as usize].clone();
        let ty_id = self.alloc_distinct_type(underlying_stage3);
        let mut method_map = HashMap::new();
        for m in methods {
            method_map.insert(m.name.clone(), (m.vis, m.clone()));
        }
        self.opaque_newtypes.insert(
            ty_id,
            OpaqueNewtypeInfo {
                name: type_name.to_string(),
                def_module: mod_path.to_string(),
                underlying: underlying_id,
                comptime_env: env.clone(),
                methods: method_map,
                method_fn_ids: HashMap::new(),
            },
        );
        if let Some(key) = memo_key {
            self.memoized_type_calls.insert(key, ty_id);
        } else if !type_name.starts_with('<') {
            self.named_types
                .insert((mod_path.to_string(), type_name.to_string()), ty_id);
        }
        if let Ok(Some((_, _, Item::TypeDecl { vis, .. }, _))) =
            self.find_item_in_module(mod_path, mod_path, type_name)
            && vis.is_export()
        {
            self.exported_type_set.insert(ty_id);
        }
        for m in methods {
            if m.vis.is_export() && m.params.iter().any(|p| p.is_comptime) {
                return Err(format!(
                    "Exported method '{}.{}' cannot have 'comptime' parameters",
                    type_name, m.name
                ));
            }
            if !m.params.iter().any(|p| p.is_comptime)
                && self.eval_where_clauses(env, &m.where_clauses)?
            {
                let fn_id = self.schedule_method(mod_path, ty_id, env, m)?;
                self.opaque_newtypes
                    .get_mut(&ty_id)
                    .unwrap()
                    .method_fn_ids
                    .insert(m.name.clone(), fn_id);
            }
        }
        Ok(ty_id)
    }

    fn instantiate_enum(
        &mut self,
        type_name: &str,
        variants: &[(String, Option<i128>)],
    ) -> Result<TypeId, String> {
        let mut next_val = 0i128;
        let mut resolved = Vec::with_capacity(variants.len());
        for (vname, explicit) in variants {
            let val = explicit.unwrap_or(next_val);
            resolved.push((vname.clone(), val));
            next_val = val + 1;
        }
        let ty_id = self.alloc_distinct_type(Type::Int {
            signed: false,
            bits: 32,
        });
        self.enums.insert(ty_id, (type_name.to_string(), resolved));
        Ok(ty_id)
    }

    fn resolve_variant_payload_ty(
        &mut self,
        mod_path: &str,
        owner_name: &str,
        vname: &str,
        env: &HashMap<String, ComptimeVal>,
        payload: &Option<TypeExpr>,
    ) -> Result<TypeId, String> {
        match payload {
            None => Ok(self.intern_type(Type::Void)),
            Some(TypeExpr::Record { fields, methods }) => self.instantiate_composite(
                mod_path,
                &format!("{owner_name}::{vname}"),
                false,
                StructOwnership::Copy,
                false,
                env,
                None,
                fields,
                methods,
                None,
                &[],
                &[],
                None,
            ),
            Some(te) => {
                let p_ty = self.resolve_type_expr(mod_path, None, env, te)?;
                if self.is_opaque_type(p_ty) {
                    return Err(format!(
                        "Unsized type 'opaque' cannot be stored by value in variant '{}::{}'; use '*const opaque', '*mut opaque', '&opaque', or '&mut opaque'",
                        owner_name, vname
                    ));
                }
                Ok(p_ty)
            }
        }
    }

    fn instantiate_union(
        &mut self,
        mod_path: &str,
        type_name: &str,
        env: &HashMap<String, ComptimeVal>,
        memo_key: Option<(String, String, Vec<ComptimeVal>)>,
        variants: &[(String, Option<TypeExpr>)],
    ) -> Result<TypeId, String> {
        let mut resolved_variants = Vec::with_capacity(variants.len());
        let mut variant_tys = Vec::with_capacity(variants.len());
        for (vname, payload_expr) in variants {
            if resolved_variants.iter().any(|(n, _): &(String, TypeId)| n == vname) {
                return Err(format!(
                    "Duplicate variant '{}' in union '{}'",
                    vname, type_name
                ));
            }
            let p_ty =
                self.resolve_variant_payload_ty(mod_path, type_name, vname, env, payload_expr)?;
            resolved_variants.push((vname.clone(), p_ty));
            variant_tys.push(p_ty);
        }
        let tag_ty = self.intern_type(Type::Int {
            signed: false,
            bits: 32,
        });
        let ty_id = self.alloc_distinct_type(Type::Union {
            tag: tag_ty,
            variants: variant_tys,
        });
        self.unions.insert(
            ty_id,
            UnionTypeInfo {
                name: type_name.to_string(),
                variants: resolved_variants,
            },
        );
        if let Some(key) = memo_key {
            self.memoized_type_calls.insert(key, ty_id);
        }
        self.ensure_union_destructor(ty_id);
        Ok(ty_id)
    }

    fn instantiate_error(
        &mut self,
        mod_path: &str,
        type_name: &str,
        env: &HashMap<String, ComptimeVal>,
        memo_key: Option<(String, String, Vec<ComptimeVal>)>,
        items: &[(String, Option<TypeExpr>)],
    ) -> Result<TypeId, String> {
        let mut leaves: Vec<ErrorLeafInfo> = Vec::new();
        for (vname, payload) in items {
            if payload.is_none() {
                let path: Vec<String> = vname.split("::").map(str::to_string).collect();
                let maybe_emb_ty = if path.len() == 1
                    && let Some(ComptimeVal::Type(t_id)) = env.get(&path[0])
                {
                    Some(*t_id)
                } else if let Ok(ResolvedItem::Type(tmod, tname)) =
                    self.resolve_path(mod_path, &path)
                {
                    Some(self.resolve_named_type(&tmod, &tname)?)
                } else if path.len() > 1 {
                    return Err(format!(
                        "Cannot resolve embedded error path '{}' in error '{}'",
                        vname, type_name
                    ));
                } else {
                    None
                };
                if let Some(emb_ty) = maybe_emb_ty {
                    let Some(emb_err) = self.errors.get(&emb_ty).cloned() else {
                        return Err(format!(
                            "Embedded type '{}' in error '{}' is not an `error` type",
                            vname, type_name
                        ));
                    };
                    for leaf in emb_err.leaves {
                        if let Some(existing) = leaves.iter().find(|l| l.key == leaf.key) {
                            if existing.payload_ty != leaf.payload_ty {
                                return Err(format!(
                                    "Conflicting payload types for embedded error variant '{}::{}'",
                                    leaf.key.error_name, leaf.key.variant_name
                                ));
                            }
                        } else {
                            leaves.push(leaf);
                        }
                    }
                    continue;
                }
            }
            let key = ErrorLeafKey {
                def_module: mod_path.to_string(),
                error_name: type_name.to_string(),
                variant_name: vname.clone(),
            };
            if leaves.iter().any(|l| l.key == key) {
                return Err(format!(
                    "Duplicate variant '{}' in error '{}'",
                    vname, type_name
                ));
            }
            let payload_ty =
                self.resolve_variant_payload_ty(mod_path, type_name, vname, env, payload)?;
            if self.is_linear_type(payload_ty) {
                return Err(format!(
                    "Error variant '{}::{}' cannot carry a linear payload",
                    type_name, vname
                ));
            }
            leaves.push(ErrorLeafInfo { key, payload_ty });
        }
        leaves.sort_by(|a, b| a.key.cmp(&b.key));
        let canonical_key: Vec<(ErrorLeafKey, TypeId)> =
            leaves.iter().map(|l| (l.key.clone(), l.payload_ty)).collect();
        if !canonical_key.is_empty()
            && let Some(&existing_ty) = self.memoized_error_unions.get(&canonical_key)
        {
            if let Some(key) = memo_key {
                self.memoized_type_calls.insert(key, existing_ty);
            }
            return Ok(existing_ty);
        }

        let tag_ty = self.intern_type(Type::Int {
            signed: false,
            bits: 32,
        });
        let variant_tys: Vec<TypeId> = leaves.iter().map(|l| l.payload_ty).collect();
        let ty_id = self.alloc_distinct_type(Type::Union {
            tag: tag_ty,
            variants: variant_tys,
        });
        self.errors.insert(
            ty_id,
            ErrorTypeInfo {
                name: type_name.to_string(),
                leaves,
            },
        );
        if !canonical_key.is_empty() {
            self.memoized_error_unions.insert(canonical_key, ty_id);
        }
        if let Some(key) = memo_key {
            self.memoized_type_calls.insert(key, ty_id);
        }
        self.ensure_union_destructor(ty_id);
        Ok(ty_id)
    }

    fn combine_error_types(&mut self, lhs_ty: TypeId, rhs_ty: TypeId) -> Result<TypeId, String> {
        let Some(lhs_err) = self.errors.get(&lhs_ty).cloned() else {
            return Err(format!(
                "Left operand of error union '||' is not an `error` type ({})",
                self.program.types[lhs_ty.0 as usize]
            ));
        };
        let Some(rhs_err) = self.errors.get(&rhs_ty).cloned() else {
            return Err(format!(
                "Right operand of error union '||' is not an `error` type ({})",
                self.program.types[rhs_ty.0 as usize]
            ));
        };
        let mut leaves = lhs_err.leaves.clone();
        for leaf in rhs_err.leaves {
            if let Some(existing) = leaves.iter().find(|l| l.key == leaf.key) {
                if existing.payload_ty != leaf.payload_ty {
                    return Err(format!(
                        "Conflicting payload types for error variant '{}::{}'",
                        leaf.key.error_name, leaf.key.variant_name
                    ));
                }
            } else {
                leaves.push(leaf);
            }
        }
        leaves.sort_by(|a, b| a.key.cmp(&b.key));
        let canonical_key: Vec<(ErrorLeafKey, TypeId)> =
            leaves.iter().map(|l| (l.key.clone(), l.payload_ty)).collect();
        if let Some(&existing_ty) = self.memoized_error_unions.get(&canonical_key) {
            return Ok(existing_ty);
        }
        let tag_ty = self.intern_type(Type::Int {
            signed: false,
            bits: 32,
        });
        let variant_tys: Vec<TypeId> = leaves.iter().map(|l| l.payload_ty).collect();
        let ty_id = self.alloc_distinct_type(Type::Union {
            tag: tag_ty,
            variants: variant_tys,
        });
        let name = format!("{} || {}", lhs_err.name, rhs_err.name);
        self.errors.insert(ty_id, ErrorTypeInfo { name, leaves });
        self.memoized_error_unions.insert(canonical_key, ty_id);
        self.ensure_union_destructor(ty_id);
        Ok(ty_id)
    }

    fn instantiate_result_type(&mut self, err_ty: TypeId, ok_ty: TypeId) -> Result<TypeId, String> {
        if !self.errors.contains_key(&err_ty) {
            let t_disp = self
                .composites
                .get(&err_ty)
                .map(|c| c.name.clone())
                .unwrap_or_else(|| self.program.types[err_ty.0 as usize].to_string());
            return Err(format!(
                "Error type '{}' in result type '{}!...' must be an `error` type",
                t_disp, t_disp
            ));
        }
        if let Some(&existing) = self.memoized_results.get(&(err_ty, ok_ty)) {
            return Ok(existing);
        }
        let u8_ty = self.intern_type(Type::Int {
            signed: false,
            bits: 8,
        });
        let ty_id = self.alloc_distinct_type(Type::Union {
            tag: u8_ty,
            variants: vec![ok_ty, err_ty],
        });
        self.results.insert(ty_id, ResultTypeInfo { err_ty, ok_ty });
        self.memoized_results.insert((err_ty, ok_ty), ty_id);
        self.ensure_union_destructor(ty_id);
        Ok(ty_id)
    }

    fn type_has_destructor(&self, ty_id: TypeId) -> bool {
        if self.program.destructors.iter().any(|(t, _)| *t == ty_id) {
            return true;
        }
        match &self.program.types[ty_id.0 as usize] {
            Type::Struct(fields) => fields.iter().any(|&f| self.type_has_destructor(f)),
            _ => false,
        }
    }

    fn ensure_union_destructor(&mut self, union_ty: TypeId) {
        if self.program.destructors.iter().any(|(t, _)| *t == union_ty) {
            return;
        }
        if self.is_linear_type(union_ty) {
            return;
        }
        let Type::Union { tag, variants } = self.program.types[union_ty.0 as usize].clone() else {
            return;
        };
        if !variants.iter().any(|&v| self.type_has_destructor(v)) {
            return;
        }
        let self_ref_ty = self.intern_type(Type::Ptr {
            mutable: true,
            pointee: union_ty,
        });
        let void_ty = self.intern_type(Type::Void);
        let dtor_fn_id = self.reserve_function(Visibility::Private, None, &[self_ref_ty], void_ty);
        self.program.destructors.push((union_ty, dtor_fn_id));

        let discr_local = LocalId(2);
        let mut locals = vec![void_ty, self_ref_ty, tag];
        let mut blocks = Vec::new();
        // bb0: discr = Discriminant(*_1); SwitchInt
        blocks.push(BasicBlock {
            statements: vec![Statement::Assign(
                Place::new(discr_local),
                Rvalue::Discriminant(Place {
                    local: LocalId(1),
                    projections: vec![Projection::Deref],
                }),
            )],
            terminator: Terminator::Unreachable,
        });
        let join_bb = BlockId(1);
        blocks.push(BasicBlock {
            statements: vec![Statement::Assign(
                Place::new(LocalId(0)),
                Rvalue::Use(Operand::Const(ConstValue::Void)),
            )],
            terminator: Terminator::Return,
        });
        let mut targets = Vec::new();
        for (v_idx, &v_ty) in variants.iter().enumerate() {
            if self.type_has_destructor(v_ty) {
                let drop_bb = BlockId(blocks.len() as u32);
                blocks.push(BasicBlock {
                    statements: Vec::new(),
                    terminator: Terminator::Drop {
                        place: Place {
                            local: LocalId(1),
                            projections: vec![Projection::Deref, Projection::Variant(v_idx as u32)],
                        },
                        target: join_bb,
                    },
                });
                targets.push((v_idx as i128, drop_bb));
            }
        }
        blocks[0].terminator = Terminator::SwitchInt {
            discr: Operand::Copy(Place::new(discr_local)),
            targets,
            otherwise: join_bb,
        };
        if let Some(func) = self.program.functions.iter_mut().find(|f| f.id == dtor_fn_id) {
            func.locals = std::mem::take(&mut locals);
            func.blocks = blocks;
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn instantiate_composite(
        &mut self,
        mod_path: &str,
        type_name: &str,
        is_struct: bool,
        ownership: StructOwnership,
        is_sync: bool,
        env: &HashMap<String, ComptimeVal>,
        memo_key: Option<(String, String, Vec<ComptimeVal>)>,
        fields: &[FieldDecl],
        methods: &[FuncDecl],
        default_hook: Option<Block>,
        clone_hooks: &[CloneHookDecl],
        drop_hooks: &[DropHookDecl],
        format_hook: Option<(String, String, Option<String>, Block)>,
    ) -> Result<TypeId, String> {
        let mut matched_drop_hooks = Vec::new();
        for h in drop_hooks {
            if self.eval_where_clauses(env, &h.where_clauses)? {
                matched_drop_hooks.push(h);
            }
        }
        if matched_drop_hooks.len() > 1 {
            return Err(format!(
                "Conflicting 'drop' hooks match for struct '{type_name}'"
            ));
        }
        if matched_drop_hooks.is_empty() && ownership != StructOwnership::Linear {
            for h in drop_hooks {
                for w in &h.where_clauses {
                    if w.constraint == TypeConstraint::Linear
                        && w.negated
                        && let Some(ComptimeVal::Type(t_id)) = env.get(&w.type_param)
                        && self.is_linear_type(*t_id)
                    {
                        return Err(format!(
                            "Struct '{type_name}' defines 'drop' with 'where {}: !linear', but is missing a matching 'drop(self: &mut Self) where {}: linear' teardown hook",
                            w.type_param, w.type_param
                        ));
                    }
                }
            }
        }
        let selected_drop = matched_drop_hooks.into_iter().next();

        let mut matched_clone_hooks = Vec::new();
        for h in clone_hooks {
            if self.eval_where_clauses(env, &h.where_clauses)? {
                matched_clone_hooks.push(h);
            }
        }
        if matched_clone_hooks.len() > 1 {
            return Err(format!(
                "Conflicting 'clone' hooks match for struct '{type_name}'"
            ));
        }
        let selected_clone = matched_clone_hooks.into_iter().next();

        let mut effective_ownership = ownership;
        if is_struct
            && let Some(dh) = selected_drop
            && dh
                .where_clauses
                .iter()
                .any(|w| w.constraint == TypeConstraint::Linear && !w.negated)
        {
            effective_ownership = StructOwnership::Linear;
        }

        let is_linear = is_struct && effective_ownership == StructOwnership::Linear;
        if is_linear && selected_clone.is_some() {
            return Err(format!(
                "Linear struct '{type_name}' cannot implement `clone`; linear values must be consumed exactly once"
            ));
        }
        if is_struct && effective_ownership == StructOwnership::Copy {
            if selected_drop.is_some() {
                return Err(format!(
                    "Copy struct '{type_name}' ('struct(copy)') cannot implement `drop`"
                ));
            }
            if selected_clone.is_some() {
                return Err(format!(
                    "Copy struct '{type_name}' ('struct(copy)') is implicitly copyable and cannot define a custom `clone` hook"
                ));
            }
        }
        let mut field_tys = Vec::with_capacity(fields.len());
        let mut field_infos = Vec::with_capacity(fields.len());
        let mut rel_fields = HashMap::new();
        for (idx, f) in fields.iter().enumerate() {
            let f_ty = match &f.ty {
                TypeExpr::RelRef(inner) => {
                    if !is_struct {
                        return Err(format!(
                            "'&rel' relative references are only permitted in 'struct' field declarations (found in record '{}', field '{}')",
                            type_name, f.name
                        ));
                    }
                    let elem_ty = self.resolve_type_expr(mod_path, None, env, inner)?;
                    let isize_ty = self.intern_type(Type::Int {
                        signed: true,
                        bits: 64,
                    });
                    rel_fields.insert(idx as u32, RelFieldKind::Elem(elem_ty));
                    isize_ty
                }
                TypeExpr::RelSlice(inner) => {
                    if !is_struct {
                        return Err(format!(
                            "'&rel' relative references are only permitted in 'struct' field declarations (found in record '{}', field '{}')",
                            type_name, f.name
                        ));
                    }
                    let elem_ty = self.resolve_type_expr(mod_path, None, env, inner)?;
                    let isize_ty = self.intern_type(Type::Int {
                        signed: true,
                        bits: 64,
                    });
                    let usize_ty = self.intern_type(Type::Int {
                        signed: false,
                        bits: 64,
                    });
                    let repr_ty = self.intern_type(Type::Struct(vec![isize_ty, usize_ty]));
                    rel_fields.insert(idx as u32, RelFieldKind::Slice(elem_ty));
                    repr_ty
                }
                TypeExpr::RelStr => {
                    if !is_struct {
                        return Err(format!(
                            "'&rel' relative references are only permitted in 'struct' field declarations (found in record '{}', field '{}')",
                            type_name, f.name
                        ));
                    }
                    let isize_ty = self.intern_type(Type::Int {
                        signed: true,
                        bits: 64,
                    });
                    let usize_ty = self.intern_type(Type::Int {
                        signed: false,
                        bits: 64,
                    });
                    let repr_ty = self.intern_type(Type::Struct(vec![isize_ty, usize_ty]));
                    rel_fields.insert(idx as u32, RelFieldKind::Str);
                    repr_ty
                }
                other => self.resolve_type_expr(mod_path, None, env, other)?,
            };
            if let Some(tr) = self.traits.get(&f_ty) {
                return Err(format!(
                    "Trait '{}' is an unsized meta-type constraint and cannot be stored by value in field '{}' of '{}'; use a generic comptime type parameter or '&{}'",
                    tr.name, f.name, type_name, tr.name
                ));
            }
            if self.is_opaque_type(f_ty) {
                return Err(format!(
                    "Unsized type 'opaque' cannot be stored by value in field '{}' of '{}'; use '*const opaque', '*mut opaque', '&opaque', or '&mut opaque'",
                    f.name, type_name
                ));
            }
            if is_struct {
                match effective_ownership {
                    StructOwnership::Copy => {
                        if !self.is_copy_type(f_ty) {
                            return Err(format!(
                                "Field '{}' of 'struct(copy) {}' has non-copy type",
                                f.name, type_name
                            ));
                        }
                    }
                    StructOwnership::Affine => {
                        if self.is_linear_type(f_ty) {
                            return Err(format!(
                                "Field '{}' of affine struct '{}' has linear type; declare 'struct(linear) {}' instead",
                                f.name, type_name, type_name
                            ));
                        }
                    }
                    StructOwnership::Linear => {}
                }
            }
            field_tys.push(f_ty);
            field_infos.push((f.name.clone(), f_ty, f.vis, f.default_val.clone()));
        }

        // Every distinct record/struct declaration gets a distinct TypeId so its field names,
        // defaults, and methods in `self.composites` never collide (tuples use `intern_type`).
        let ty_id = self.alloc_distinct_type(Type::Struct(field_tys));
        if is_linear {
            self.program.linear_types.push((ty_id, type_name.to_string()));
        }

        let mut method_map = HashMap::new();
        for m in methods {
            method_map.insert(m.name.clone(), (m.vis, m.clone()));
        }

        let info = CompositeInfo {
            name: type_name.to_string(),
            is_struct,
            ownership: effective_ownership,
            is_sync,
            has_format_hook: format_hook.is_some(),
            def_module: mod_path.to_string(),
            comptime_env: env.clone(),
            fields: field_infos,
            rel_fields,
            methods: method_map,
            method_fn_ids: HashMap::new(),
            default_fn: None,
            clone_fn: None,
            drop_fn: None,
            format_fn: None,
        };
        self.composites.insert(ty_id, info);
        if let Some(key) = memo_key {
            self.memoized_type_calls.insert(key, ty_id);
        } else if !type_name.starts_with('<') {
            self.named_types
                .insert((mod_path.to_string(), type_name.to_string()), ty_id);
        }

        // Instantiate non-generic inherent methods eagerly (only if their `where` clauses are satisfied);
        // generic inherent methods (with `comptime` parameters) are instantiated on demand at call sites.
        if let Ok(Some((_, _, Item::TypeDecl { vis, .. }, _))) =
            self.find_item_in_module(mod_path, mod_path, type_name)
            && vis.is_export()
        {
            self.exported_type_set.insert(ty_id);
        }
        for m in methods {
            if m.vis.is_export() && m.params.iter().any(|p| p.is_comptime) {
                return Err(format!(
                    "Exported method '{}.{}' cannot have 'comptime' parameters",
                    type_name, m.name
                ));
            }
            if !m.params.iter().any(|p| p.is_comptime)
                && self.eval_where_clauses(env, &m.where_clauses)?
            {
                let fn_id = self.schedule_method(mod_path, ty_id, env, m)?;
                self.composites
                    .get_mut(&ty_id)
                    .unwrap()
                    .method_fn_ids
                    .insert(m.name.clone(), fn_id);
            }
        }

        // Instantiate `default`, `clone`, `drop`, `format` lifecycle hooks on `struct`
        if let Some(def_blk) = default_hook {
            let decl = FuncDecl {
                vis: Visibility::Pub,
                name: format!("{type_name}::default"),
                params: vec![],
                ret_ty: TypeExpr::SelfType,
                borrows: None,
                where_clauses: Vec::new(),
                body: def_blk,
            };
            let fn_id = self.schedule_method(mod_path, ty_id, env, &decl)?;
            self.composites.get_mut(&ty_id).unwrap().default_fn = Some(fn_id);
        }

        if let Some(clone_hook) = selected_clone {
            let decl = FuncDecl {
                vis: Visibility::Pub,
                name: format!("{type_name}::clone"),
                params: vec![crate::ast::Param {
                    is_comptime: false,
                    is_mut: false,
                    name: clone_hook.self_name.clone(),
                    ty: TypeExpr::Ref {
                        mutable: false,
                        inner: Box::new(TypeExpr::SelfType),
                    },
                }],
                ret_ty: TypeExpr::SelfType,
                borrows: None,
                where_clauses: Vec::new(),
                body: clone_hook.body.clone(),
            };
            let fn_id = self.schedule_method(mod_path, ty_id, env, &decl)?;
            self.composites.get_mut(&ty_id).unwrap().clone_fn = Some(fn_id);
        }

        if let Some(drop_hook) = selected_drop {
            let decl = FuncDecl {
                vis: Visibility::Pub,
                name: format!("{type_name}::drop"),
                params: vec![crate::ast::Param {
                    is_comptime: false,
                    is_mut: false,
                    name: drop_hook.self_name.clone(),
                    ty: TypeExpr::Ref {
                        mutable: true,
                        inner: Box::new(TypeExpr::SelfType),
                    },
                }],
                ret_ty: TypeExpr::Void,
                borrows: None,
                where_clauses: Vec::new(),
                body: drop_hook.body.clone(),
            };
            let fn_id = self.schedule_method(mod_path, ty_id, env, &decl)?;
            self.composites.get_mut(&ty_id).unwrap().drop_fn = Some(fn_id);
            self.program.destructors.push((ty_id, fn_id));
        }

        if let Some((self_name, fmt_name, opt_spec_name, fmt_blk)) = format_hook {
            let mut params = vec![
                crate::ast::Param {
                    is_comptime: false,
                    is_mut: false,
                    name: self_name,
                    ty: TypeExpr::Ref {
                        mutable: false,
                        inner: Box::new(TypeExpr::SelfType),
                    },
                },
                crate::ast::Param {
                    is_comptime: false,
                    is_mut: false,
                    name: fmt_name,
                    ty: TypeExpr::Ref {
                        mutable: true,
                        inner: Box::new(TypeExpr::Named(vec![
                            "core".to_string(),
                            "fmt".to_string(),
                            "Formatter".to_string(),
                        ])),
                    },
                },
            ];
            let takes_spec = if let Some(spec_name) = opt_spec_name {
                params.push(crate::ast::Param {
                    is_comptime: false,
                    is_mut: false,
                    name: spec_name,
                    ty: TypeExpr::StrRef,
                });
                true
            } else {
                false
            };
            let decl = FuncDecl {
                vis: Visibility::Pub,
                name: format!("{type_name}::format"),
                params,
                ret_ty: TypeExpr::Void,
                borrows: None,
                where_clauses: Vec::new(),
                body: fmt_blk,
            };
            let fn_id = self.schedule_method(mod_path, ty_id, env, &decl)?;
            self.composites.get_mut(&ty_id).unwrap().format_fn = Some((fn_id, takes_spec));
        }

        Ok(ty_id)
    }

    fn type_contains_safe_ref(&self, ty_id: TypeId) -> bool {
        if self.raw_ptrs.contains_key(&ty_id) {
            return false;
        }
        if self.slices.contains_key(&ty_id) {
            return true;
        }
        match &self.program.types[ty_id.0 as usize] {
            Type::Ptr { .. } => true,
            Type::Struct(fields) | Type::Overlay(fields) => {
                fields.iter().any(|&f| self.type_contains_safe_ref(f))
            }
            Type::Array { elem, .. } => self.type_contains_safe_ref(*elem),
            Type::Union { variants, .. } => {
                variants.iter().any(|&v| self.type_contains_safe_ref(v))
            }
            Type::Pattern { base, .. } => self.type_contains_safe_ref(*base),
            _ => false,
        }
    }

    fn apply_func_borrow_contracts(
        &mut self,
        fn_id: FuncId,
        decl: &FuncDecl,
        param_tys: &[TypeId],
        ret_ty: TypeId,
    ) -> Result<(), String> {
        let rt_params: Vec<(String, TypeId)> = decl
            .params
            .iter()
            .filter(|p| !p.is_comptime)
            .map(|p| p.name.clone())
            .zip(param_tys.iter().copied())
            .collect();

        let first_is_self = rt_params.first().is_some_and(|(n, _)| n == "self");
        let is_generic = decl.params.iter().any(|p| p.is_comptime);
        let ref_params: Vec<LocalId> = rt_params
            .iter()
            .enumerate()
            .filter(|(_, (_, ty))| self.type_contains_safe_ref(*ty))
            .map(|(i, _)| LocalId((i + 1) as u32))
            .collect();

        let (ret_borrows, param_borrows) = if let Some(items) = &decl.borrows {
            let mut ret_list = Vec::new();
            let mut param_list = Vec::new();
            let mut has_ret_item = false;
            let mut has_param_item = false;
            for item in items {
                match item {
                    BorrowContractItem::Return(name) => {
                        has_ret_item = true;
                        let Some(idx) = rt_params.iter().position(|(pname, _)| pname == name)
                        else {
                            return Err(format!(
                                "Unknown runtime parameter '{}' in borrows(...) contract on '{}'",
                                name, decl.name
                            ));
                        };
                        let loc = LocalId((idx + 1) as u32);
                        if !ret_list.contains(&loc) {
                            ret_list.push(loc);
                        }
                    }
                    BorrowContractItem::ParamFlow { dst, src } => {
                        has_param_item = true;
                        let Some(dst_idx) = rt_params.iter().position(|(pname, _)| pname == dst)
                        else {
                            return Err(format!(
                                "Unknown destination parameter '{}' in borrows({}: {}) contract on '{}'",
                                dst, dst, src, decl.name
                            ));
                        };
                        let Some(src_idx) = rt_params.iter().position(|(pname, _)| pname == src)
                        else {
                            return Err(format!(
                                "Unknown source parameter '{}' in borrows({}: {}) contract on '{}'",
                                src, dst, src, decl.name
                            ));
                        };
                        let pair = (LocalId((dst_idx + 1) as u32), LocalId((src_idx + 1) as u32));
                        if !param_list.contains(&pair) {
                            param_list.push(pair);
                        }
                    }
                }
            }
            let rb = if has_ret_item || self.type_contains_safe_ref(ret_ty) {
                Some(ret_list)
            } else {
                None
            };
            let pb = if has_param_item
                || (decl.vis.is_public_or_export() && !first_is_self && !is_generic && ref_params.len() >= 2)
            {
                Some(param_list)
            } else {
                None
            };
            (rb, pb)
        } else if decl.vis.is_public_or_export() {
            let rb = if self.type_contains_safe_ref(ret_ty) {
                if first_is_self && self.type_contains_safe_ref(rt_params[0].1) {
                    Some(vec![LocalId(1)])
                } else if ref_params.len() == 1 {
                    Some(vec![ref_params[0]])
                } else if ref_params.len() > 1 {
                    return Err(format!(
                        "Public function '{}' returns a reference and takes multiple reference parameters; add an explicit 'borrows(...)' contract",
                        decl.name
                    ));
                } else {
                    Some(Vec::new())
                }
            } else {
                None
            };

            let pb = if !first_is_self && !is_generic && ref_params.len() >= 2 {
                Some(Vec::new())
            } else {
                None
            };
            (rb, pb)
        } else {
            (None, None)
        };

        if let Some(func) = self.program.functions.iter_mut().find(|f| f.id == fn_id) {
            func.ret_borrows = ret_borrows;
            func.param_borrows = param_borrows;
        }
        Ok(())
    }

    fn setup_export_function(
        &mut self,
        fn_id: FuncId,
        export_symbol: String,
        decl: &FuncDecl,
        param_tys: &[TypeId],
        ret_ty: TypeId,
    ) -> Result<(), String> {
        let mut user_params = Vec::with_capacity(param_tys.len());
        let mut c_abi_params = Vec::with_capacity(param_tys.len());
        let mut c_abi_param_tys = Vec::with_capacity(param_tys.len() + 2);

        for (p, &pty) in decl
            .params
            .iter()
            .filter(|p| !p.is_comptime)
            .zip(param_tys.iter())
        {
            self.validate_export_value_type(
                pty,
                &format!("parameter '{}' of export function '{}'", p.name, export_symbol),
            )?;
            user_params.push((p.name.clone(), pty));
            if let Some((_, _, raw_ptr_ty)) = self.as_nullable_raw_ptr(pty) {
                c_abi_params.push(CAbiParamInfo {
                    name: p.name.clone(),
                    inner_ty: pty,
                    c_abi_ty: raw_ptr_ty,
                    is_nullable_raw_ptr: Some((pty, raw_ptr_ty)),
                });
                c_abi_param_tys.push(raw_ptr_ty);
            } else {
                c_abi_params.push(CAbiParamInfo {
                    name: p.name.clone(),
                    inner_ty: pty,
                    c_abi_ty: pty,
                    is_nullable_raw_ptr: None,
                });
                c_abi_param_tys.push(pty);
            }
        }

        let (ret_kind, c_abi_ret_ty) = if let Some(&res_info) = self.results.get(&ret_ty) {
            self.validate_export_value_type(
                res_info.err_ty,
                &format!("error return of export function '{}'", export_symbol),
            )?;
            self.validate_export_value_type(
                res_info.ok_ty,
                &format!("return value of export function '{}'", export_symbol),
            )?;
            let out_err_ptr_ty = self.intern_raw_ptr_type(true, res_info.err_ty);
            c_abi_param_tys.push(out_err_ptr_ty);
            let out_val_ptr_ty = if matches!(self.program.types[res_info.ok_ty.0 as usize], Type::Void)
            {
                None
            } else {
                let p = self.intern_raw_ptr_type(true, res_info.ok_ty);
                c_abi_param_tys.push(p);
                Some(p)
            };
            let bool_ty = self.intern_type(Type::Bool);
            (
                ExportRetKind::ResultVal {
                    res_ty: ret_ty,
                    err_ty: res_info.err_ty,
                    out_err_ptr_ty,
                    ok_ty: res_info.ok_ty,
                    out_val_ptr_ty,
                },
                bool_ty,
            )
        } else if let Some(inner_opt_ty) = self.as_optional_type(ret_ty) {
            self.validate_export_value_type(
                inner_opt_ty,
                &format!("optional return of export function '{}'", export_symbol),
            )?;
            if self.raw_ptrs.contains_key(&inner_opt_ty) {
                (
                    ExportRetKind::OptionalPtr {
                        opt_ty: ret_ty,
                        raw_ptr_ty: inner_opt_ty,
                    },
                    inner_opt_ty,
                )
            } else {
                let out_ptr_ty = self.intern_raw_ptr_type(true, inner_opt_ty);
                c_abi_param_tys.push(out_ptr_ty);
                let bool_ty = self.intern_type(Type::Bool);
                (
                    ExportRetKind::OptionalVal {
                        opt_ty: ret_ty,
                        val_ty: inner_opt_ty,
                        out_ptr_ty,
                    },
                    bool_ty,
                )
            }
        } else {
            self.validate_export_value_type(
                ret_ty,
                &format!("return type of export function '{}'", export_symbol),
            )?;
            (ExportRetKind::Direct(ret_ty), ret_ty)
        };

        if !self.exported_funcs.iter().any(|f| f.symbol == export_symbol) {
            self.exported_funcs.push(ExportedFuncMeta {
                symbol: export_symbol.clone(),
                params: user_params,
                ret_kind: ret_kind.clone(),
            });
        }

        let needs_wrapper = c_abi_params.iter().any(|p| p.is_nullable_raw_ptr.is_some())
            || !matches!(ret_kind, ExportRetKind::Direct(_));

        if !needs_wrapper {
            if let Some(func) = self.program.functions.iter_mut().find(|f| f.id == fn_id) {
                func.export = Some(export_symbol);
            }
        } else {
            if let Some(func) = self.program.functions.iter_mut().find(|f| f.id == fn_id) {
                func.export = None;
            }
            let c_abi_fn_id = self.reserve_function(
                Visibility::Export,
                Some(export_symbol.clone()),
                &c_abi_param_tys,
                c_abi_ret_ty,
            );
            self.build_c_abi_export_wrapper(
                c_abi_fn_id,
                fn_id,
                &c_abi_params,
                &c_abi_param_tys,
                c_abi_ret_ty,
                &ret_kind,
            );
            self.c_abi_func_wrappers.insert(
                fn_id,
                CAbiExportWrapperInfo {
                    c_abi_fn_id,
                    export_symbol,
                    user_params: c_abi_params,
                    c_abi_param_tys,
                    c_abi_ret_ty,
                    ret_kind,
                },
            );
        }
        Ok(())
    }

    fn build_c_abi_export_wrapper(
        &mut self,
        c_abi_fn_id: FuncId,
        inner_fn_id: FuncId,
        c_abi_params: &[CAbiParamInfo],
        c_abi_param_tys: &[TypeId],
        c_abi_ret_ty: TypeId,
        ret_kind: &ExportRetKind,
    ) {
        let usize_ty = self.intern_type(Type::Int {
            signed: false,
            bits: 64,
        });
        let u8_ty = self.intern_type(Type::Int {
            signed: false,
            bits: 8,
        });
        let (_, inner_ret_ty) = self.func_sigs[&inner_fn_id].clone();

        let mut locals = vec![c_abi_ret_ty];
        locals.extend_from_slice(c_abi_param_tys);
        let mut alloc_local = |ty: TypeId| -> LocalId {
            let id = LocalId(locals.len() as u32);
            locals.push(ty);
            id
        };

        let mut blocks = vec![BasicBlock {
            statements: Vec::new(),
            terminator: Terminator::Unreachable,
        }];
        let new_block = |blocks: &mut Vec<BasicBlock>| -> BlockId {
            let id = BlockId(blocks.len() as u32);
            blocks.push(BasicBlock {
                statements: Vec::new(),
                terminator: Terminator::Unreachable,
            });
            id
        };

        let mut cur_bb = BlockId(0);
        let mut call_args = Vec::with_capacity(c_abi_params.len());

        for (idx, pinfo) in c_abi_params.iter().enumerate() {
            let param_local = LocalId((idx + 1) as u32);
            if let Some((opt_ty, _)) = pinfo.is_nullable_raw_ptr {
                let addr_local = alloc_local(usize_ty);
                let opt_local = alloc_local(opt_ty);
                blocks[cur_bb.0 as usize].statements.push(Statement::Assign(
                    Place::new(addr_local),
                    Rvalue::Cast(Operand::Copy(Place::new(param_local)), usize_ty),
                ));
                let null_bb = new_block(&mut blocks);
                let some_bb = new_block(&mut blocks);
                let join_bb = new_block(&mut blocks);
                blocks[cur_bb.0 as usize].terminator = Terminator::SwitchInt {
                    discr: Operand::Copy(Place::new(addr_local)),
                    targets: vec![(0, null_bb)],
                    otherwise: some_bb,
                };
                blocks[null_bb.0 as usize].statements.push(Statement::Assign(
                    Place::new(opt_local),
                    Rvalue::Union {
                        ty: opt_ty,
                        variant: 0,
                        payload: Operand::Const(ConstValue::Void),
                    },
                ));
                blocks[null_bb.0 as usize].terminator = Terminator::Goto { target: join_bb };
                blocks[some_bb.0 as usize].statements.push(Statement::Assign(
                    Place::new(opt_local),
                    Rvalue::Union {
                        ty: opt_ty,
                        variant: 1,
                        payload: Operand::Copy(Place::new(param_local)),
                    },
                ));
                blocks[some_bb.0 as usize].terminator = Terminator::Goto { target: join_bb };
                cur_bb = join_bb;
                call_args.push(Operand::Copy(Place::new(opt_local)));
            } else {
                call_args.push(Operand::Copy(Place::new(param_local)));
            }
        }

        let inner_ret_local = alloc_local(inner_ret_ty);
        let after_call_bb = new_block(&mut blocks);
        blocks[cur_bb.0 as usize].terminator = Terminator::Call {
            func: Operand::Const(ConstValue::Func(inner_fn_id)),
            args: call_args,
            destination: Place::new(inner_ret_local),
            target: after_call_bb,
        };
        cur_bb = after_call_bb;

        match ret_kind {
            ExportRetKind::Direct(_) => {
                blocks[cur_bb.0 as usize].statements.push(Statement::Assign(
                    Place::new(LocalId(0)),
                    Rvalue::Use(Operand::Copy(Place::new(inner_ret_local))),
                ));
                blocks[cur_bb.0 as usize].terminator = Terminator::Return;
            }
            ExportRetKind::OptionalPtr { raw_ptr_ty, .. } => {
                let discr_local = alloc_local(u8_ty);
                blocks[cur_bb.0 as usize].statements.push(Statement::Assign(
                    Place::new(discr_local),
                    Rvalue::Discriminant(Place::new(inner_ret_local)),
                ));
                let some_bb = new_block(&mut blocks);
                let none_bb = new_block(&mut blocks);
                blocks[cur_bb.0 as usize].terminator = Terminator::SwitchInt {
                    discr: Operand::Copy(Place::new(discr_local)),
                    targets: vec![(1, some_bb)],
                    otherwise: none_bb,
                };
                blocks[some_bb.0 as usize].statements.push(Statement::Assign(
                    Place::new(LocalId(0)),
                    Rvalue::Use(Operand::Copy(Place {
                        local: inner_ret_local,
                        projections: vec![Projection::Variant(1)],
                    })),
                ));
                blocks[some_bb.0 as usize].terminator = Terminator::Return;

                let zero_local = alloc_local(usize_ty);
                blocks[none_bb.0 as usize].statements.push(Statement::Assign(
                    Place::new(zero_local),
                    Rvalue::Use(Operand::Const(ConstValue::I64(0))),
                ));
                blocks[none_bb.0 as usize].statements.push(Statement::Assign(
                    Place::new(LocalId(0)),
                    Rvalue::Cast(Operand::Copy(Place::new(zero_local)), *raw_ptr_ty),
                ));
                blocks[none_bb.0 as usize].terminator = Terminator::Return;
            }
            ExportRetKind::OptionalVal { .. } => {
                let out_val_local = LocalId(c_abi_param_tys.len() as u32);
                let discr_local = alloc_local(u8_ty);
                blocks[cur_bb.0 as usize].statements.push(Statement::Assign(
                    Place::new(discr_local),
                    Rvalue::Discriminant(Place::new(inner_ret_local)),
                ));
                let some_bb = new_block(&mut blocks);
                let none_bb = new_block(&mut blocks);
                let write_bb = new_block(&mut blocks);
                let ret_true_bb = new_block(&mut blocks);
                blocks[cur_bb.0 as usize].terminator = Terminator::SwitchInt {
                    discr: Operand::Copy(Place::new(discr_local)),
                    targets: vec![(1, some_bb)],
                    otherwise: none_bb,
                };
                let addr_local = alloc_local(usize_ty);
                blocks[some_bb.0 as usize].statements.push(Statement::Assign(
                    Place::new(addr_local),
                    Rvalue::Cast(Operand::Copy(Place::new(out_val_local)), usize_ty),
                ));
                blocks[some_bb.0 as usize].terminator = Terminator::SwitchInt {
                    discr: Operand::Copy(Place::new(addr_local)),
                    targets: vec![(0, ret_true_bb)],
                    otherwise: write_bb,
                };
                blocks[write_bb.0 as usize].statements.push(Statement::Assign(
                    Place {
                        local: out_val_local,
                        projections: vec![Projection::Deref],
                    },
                    Rvalue::Use(Operand::Copy(Place {
                        local: inner_ret_local,
                        projections: vec![Projection::Variant(1)],
                    })),
                ));
                blocks[write_bb.0 as usize].terminator = Terminator::Goto {
                    target: ret_true_bb,
                };
                blocks[ret_true_bb.0 as usize]
                    .statements
                    .push(Statement::Assign(
                        Place::new(LocalId(0)),
                        Rvalue::Use(Operand::Const(ConstValue::Bool(true))),
                    ));
                blocks[ret_true_bb.0 as usize].terminator = Terminator::Return;

                blocks[none_bb.0 as usize]
                    .statements
                    .push(Statement::Assign(
                        Place::new(LocalId(0)),
                        Rvalue::Use(Operand::Const(ConstValue::Bool(false))),
                    ));
                blocks[none_bb.0 as usize].terminator = Terminator::Return;
            }
            ExportRetKind::ResultVal {
                out_val_ptr_ty, ..
            } => {
                let (out_err_local, out_val_local) = if out_val_ptr_ty.is_some() {
                    (
                        LocalId((c_abi_param_tys.len() - 1) as u32),
                        Some(LocalId(c_abi_param_tys.len() as u32)),
                    )
                } else {
                    (LocalId(c_abi_param_tys.len() as u32), None)
                };
                let discr_local = alloc_local(u8_ty);
                blocks[cur_bb.0 as usize].statements.push(Statement::Assign(
                    Place::new(discr_local),
                    Rvalue::Discriminant(Place::new(inner_ret_local)),
                ));
                let ok_bb = new_block(&mut blocks);
                let err_bb = new_block(&mut blocks);
                blocks[cur_bb.0 as usize].terminator = Terminator::SwitchInt {
                    discr: Operand::Copy(Place::new(discr_local)),
                    targets: vec![(0, ok_bb)],
                    otherwise: err_bb,
                };

                if let Some(ov_local) = out_val_local {
                    let write_ok_bb = new_block(&mut blocks);
                    let ret_true_bb = new_block(&mut blocks);
                    let ok_addr = alloc_local(usize_ty);
                    blocks[ok_bb.0 as usize].statements.push(Statement::Assign(
                        Place::new(ok_addr),
                        Rvalue::Cast(Operand::Copy(Place::new(ov_local)), usize_ty),
                    ));
                    blocks[ok_bb.0 as usize].terminator = Terminator::SwitchInt {
                        discr: Operand::Copy(Place::new(ok_addr)),
                        targets: vec![(0, ret_true_bb)],
                        otherwise: write_ok_bb,
                    };
                    blocks[write_ok_bb.0 as usize]
                        .statements
                        .push(Statement::Assign(
                            Place {
                                local: ov_local,
                                projections: vec![Projection::Deref],
                            },
                            Rvalue::Use(Operand::Copy(Place {
                                local: inner_ret_local,
                                projections: vec![Projection::Variant(0)],
                            })),
                        ));
                    blocks[write_ok_bb.0 as usize].terminator = Terminator::Goto {
                        target: ret_true_bb,
                    };
                    blocks[ret_true_bb.0 as usize]
                        .statements
                        .push(Statement::Assign(
                            Place::new(LocalId(0)),
                            Rvalue::Use(Operand::Const(ConstValue::Bool(true))),
                        ));
                    blocks[ret_true_bb.0 as usize].terminator = Terminator::Return;
                } else {
                    blocks[ok_bb.0 as usize].statements.push(Statement::Assign(
                        Place::new(LocalId(0)),
                        Rvalue::Use(Operand::Const(ConstValue::Bool(true))),
                    ));
                    blocks[ok_bb.0 as usize].terminator = Terminator::Return;
                }

                let write_err_bb = new_block(&mut blocks);
                let ret_false_bb = new_block(&mut blocks);
                let err_addr = alloc_local(usize_ty);
                blocks[err_bb.0 as usize].statements.push(Statement::Assign(
                    Place::new(err_addr),
                    Rvalue::Cast(Operand::Copy(Place::new(out_err_local)), usize_ty),
                ));
                blocks[err_bb.0 as usize].terminator = Terminator::SwitchInt {
                    discr: Operand::Copy(Place::new(err_addr)),
                    targets: vec![(0, ret_false_bb)],
                    otherwise: write_err_bb,
                };
                blocks[write_err_bb.0 as usize]
                    .statements
                    .push(Statement::Assign(
                        Place {
                            local: out_err_local,
                            projections: vec![Projection::Deref],
                        },
                        Rvalue::Use(Operand::Copy(Place {
                            local: inner_ret_local,
                            projections: vec![Projection::Variant(1)],
                        })),
                    ));
                blocks[write_err_bb.0 as usize].terminator = Terminator::Goto {
                    target: ret_false_bb,
                };
                blocks[ret_false_bb.0 as usize]
                    .statements
                    .push(Statement::Assign(
                        Place::new(LocalId(0)),
                        Rvalue::Use(Operand::Const(ConstValue::Bool(false))),
                    ));
                blocks[ret_false_bb.0 as usize].terminator = Terminator::Return;
            }
        }

        if let Some(func) = self.program.functions.iter_mut().find(|f| f.id == c_abi_fn_id) {
            func.locals = locals;
            func.blocks = blocks;
        }
    }

    fn schedule_method(
        &mut self,
        mod_path: &str,
        owner_ty: TypeId,
        env: &HashMap<String, ComptimeVal>,
        decl: &FuncDecl,
    ) -> Result<FuncId, String> {
        let mut param_tys = Vec::new();
        for p in &decl.params {
            if !p.is_comptime {
                if matches!(p.ty, TypeExpr::Constraint(_) | TypeExpr::TraitBounds(_)) {
                    return Err(format!(
                        "Parameter '{}' of '{}' has a meta-type constraint by value; use '(comptime T: ..., {}: T)' for static dispatch or '&Trait' for dynamic dispatch",
                        p.name, decl.name, p.name
                    ));
                }
                let pty = self.resolve_type_expr(mod_path, Some(owner_ty), env, &p.ty)?;
                if let Some(tr) = self.traits.get(&pty) {
                    return Err(format!(
                        "Trait '{}' is an unsized meta-type constraint and cannot be passed by value in parameter '{}' of '{}'; use '(comptime T: {}, {}: T)' for static dispatch or '({}: &{})' for dynamic dispatch",
                        tr.name, p.name, decl.name, tr.name, p.name, p.name, tr.name
                    ));
                }
                if self.is_opaque_type(pty) {
                    return Err(format!(
                        "Unsized type '{}' cannot be passed by value in parameter '{}' of '{}'; use '*const {0}', '*mut {0}', '&{0}', or '&mut {0}'",
                        self.type_display_name(pty),
                        p.name,
                        decl.name
                    ));
                }
                param_tys.push(pty);
            }
        }
        if let TypeExpr::OpaqueTrait(bound_expr) = &decl.ret_ty {
            if decl.vis.is_export() {
                return Err(format!(
                    "Exported method '{}' cannot return existential 'opaque Trait'; 'export fn' requires a C-compatible return type",
                    decl.name
                ));
            }
            let void_ty = self.intern_type(Type::Void);
            let fn_id = self.reserve_function(decl.vis, None, &param_tys, void_ty);
            self.opaque_ret_funcs.insert(
                fn_id,
                OpaqueRetBound {
                    bound_mod: mod_path.to_string(),
                    owner_ty: Some(owner_ty),
                    env: env.clone(),
                    bound_expr: (**bound_expr).clone(),
                },
            );
            let pending = PendingFunc {
                func_id: fn_id,
                module_path: mod_path.to_string(),
                owner_ty: Some(owner_ty),
                decl: decl.clone(),
                comptime_env: env.clone(),
                closure_captures: Vec::new(),
            };
            self.lower_function_body(pending)?;
            let (_, ret_ty) = self.func_sigs[&fn_id].clone();
            self.apply_func_borrow_contracts(fn_id, decl, &param_tys, ret_ty)?;
            return Ok(fn_id);
        }
        let ret_ty = self.resolve_type_expr(mod_path, Some(owner_ty), env, &decl.ret_ty)?;
        if let Some(tr) = self.traits.get(&ret_ty) {
            return Err(format!(
                "Trait '{}' is an unsized meta-type constraint and cannot be returned by value from '{}'",
                tr.name, decl.name
            ));
        }
        if self.is_opaque_type(ret_ty) {
            return Err(format!(
                "Unsized type '{}' cannot be returned by value from '{}'; use '*const {0}', '*mut {0}', '&{0}', or '&mut {0}'",
                self.type_display_name(ret_ty),
                decl.name
            ));
        }
        let fn_id = self.reserve_function(decl.vis, None, &param_tys, ret_ty);
        self.apply_func_borrow_contracts(fn_id, decl, &param_tys, ret_ty)?;
        if decl.vis.is_export() {
            let owner_name = self.type_display_name(owner_ty);
            let export_sym = format!("{}_{}", owner_name, decl.name);
            self.setup_export_function(fn_id, export_sym, decl, &param_tys, ret_ty)?;
        }
        if self
            .composites
            .get(&owner_ty)
            .is_some_and(|c| c.is_struct && c.ownership == StructOwnership::Linear)
            && param_tys.first() == Some(&owner_ty)
        {
            if let Some(func) = self.program.functions.iter_mut().find(|f| f.id == fn_id) {
                func.linear_self = Some(owner_ty);
            }
        }
        self.pending_funcs.push(PendingFunc {
            func_id: fn_id,
            module_path: mod_path.to_string(),
            owner_ty: Some(owner_ty),
            decl: decl.clone(),
            comptime_env: env.clone(),
            closure_captures: Vec::new(),
        });
        Ok(fn_id)
    }

    fn reserve_function(
        &mut self,
        _vis: Visibility,
        export: Option<String>,
        param_tys: &[TypeId],
        ret_ty: TypeId,
    ) -> FuncId {
        let fn_id = FuncId((self.program.externs.len() + self.program.functions.len()) as u32);
        let mut locals = vec![ret_ty];
        locals.extend_from_slice(param_tys);
        self.program.functions.push(Function {
            id: fn_id,
            arg_count: param_tys.len(),
            ret_borrows: None,
            param_borrows: None,
            linear_self: None,
            export,
            locals,
            blocks: Vec::new(),
        });
        self.func_sigs
            .insert(fn_id, (param_tys.to_vec(), ret_ty));
        fn_id
    }

    fn get_or_instantiate_func(
        &mut self,
        mod_path: &str,
        name: &str,
        comptime_args: &[ComptimeVal],
    ) -> Result<FuncId, String> {
        let key = (
            mod_path.to_string(),
            name.to_string(),
            comptime_args.to_vec(),
        );
        if let Some(&id) = self.resolved_funcs.get(&key) {
            return Ok(id);
        }
        let overloads = self.find_funcs_in_module(mod_path, mod_path, name)?;
        if overloads.is_empty() {
            return Err(format!("Function '{name}' not found in '{mod_path}'"));
        }

        let mut matching_overloads: Vec<(FuncDecl, HashMap<String, ComptimeVal>, u32)> = Vec::new();
        let mut last_constraint_err: Option<String> = None;

        for (_, _, decl) in overloads {
            let ct_count = decl.params.iter().filter(|p| p.is_comptime).count();
            if ct_count != comptime_args.len() {
                continue;
            }
            let mut env = HashMap::new();
            let mut ct_idx = 0;
            let mut spec_sum = 0u32;
            let mut ok = true;
            for p in &decl.params {
                if p.is_comptime {
                    let val = comptime_args[ct_idx].clone();
                    match &val {
                        ComptimeVal::Type(arg_ty) => {
                            match self.eval_comptime_type_bound(mod_path, None, &env, &p.ty, *arg_ty)? {
                                Some(Ok(s)) => spec_sum += s as u32,
                                Some(Err(e)) => {
                                    last_constraint_err = Some(format!(
                                        "{} (for parameter '{}' in '{}')",
                                        e, p.name, name
                                    ));
                                    ok = false;
                                    break;
                                }
                                None => {
                                    ok = false;
                                    break;
                                }
                            }
                        }
                        ComptimeVal::ConstExpr(_, cexpr) => {
                            if let Ok(param_ty) = self.resolve_type_expr(mod_path, None, &env, &p.ty)
                                && let Some(tobj) = self.trait_objs.get(&param_ty).cloned()
                            {
                                if let Expr::Ref {
                                    mutable: ref_mut,
                                    expr: inner,
                                } = cexpr
                                {
                                    if tobj.mutable && !*ref_mut {
                                        last_constraint_err = Some(format!(
                                            "Cannot pass immutable comptime reference to '&mut {}' parameter '{}' in '{}'",
                                            self.type_display_name(tobj.trait_ty),
                                            p.name,
                                            name
                                        ));
                                        ok = false;
                                        break;
                                    }
                                    if let Expr::StructLit { ty: inner_te, .. } = inner.as_ref() {
                                        let concrete_ty =
                                            self.resolve_type_expr(mod_path, None, &env, inner_te)?;
                                        let m_count = self.traits[&tobj.trait_ty].methods.len();
                                        for m_idx in 0..m_count {
                                            if let Err(e) = self.resolve_trait_impl_method(
                                                mod_path,
                                                concrete_ty,
                                                tobj.trait_ty,
                                                m_idx,
                                                true,
                                            ) {
                                                last_constraint_err = Some(e);
                                                ok = false;
                                                break;
                                            }
                                        }
                                        if !ok {
                                            break;
                                        }
                                        spec_sum += 6;
                                    }
                                } else {
                                    last_constraint_err = Some(format!(
                                        "Comptime parameter '{}' in '{}' expects a reference to a type implementing '{}'",
                                        p.name,
                                        name,
                                        self.type_display_name(tobj.trait_ty)
                                    ));
                                    ok = false;
                                    break;
                                }
                            }
                        }
                        _ => {
                            if self
                                .eval_comptime_type_bound(
                                    mod_path,
                                    None,
                                    &env,
                                    &p.ty,
                                    TypeId(0),
                                )?
                                .is_some()
                            {
                                ok = false;
                                break;
                            }
                        }
                    }
                    env.insert(p.name.clone(), val);
                    ct_idx += 1;
                }
            }
            if ok {
                matching_overloads.push((decl, env, spec_sum));
            }
        }

        if matching_overloads.is_empty() {
            return Err(last_constraint_err.unwrap_or_else(|| {
                format!(
                    "No overload of '{name}' in '{mod_path}' matches {} comptime arguments",
                    comptime_args.len()
                )
            }));
        }

        matching_overloads.sort_by_key(|b| std::cmp::Reverse(b.2));
        let (decl, _, _) = matching_overloads.into_iter().next().unwrap();
        let fn_id = self.instantiate_specific_func_decl(mod_path, &decl, comptime_args)?;
        self.resolved_funcs.insert(key, fn_id);
        Ok(fn_id)
    }

    fn instantiate_specific_func_decl(
        &mut self,
        mod_path: &str,
        decl: &FuncDecl,
        comptime_args: &[ComptimeVal],
    ) -> Result<FuncId, String> {
        let specific_key = (
            mod_path.to_string(),
            format!("{}#{:?}", decl.name, decl.params),
            comptime_args.to_vec(),
        );
        if let Some(&id) = self.resolved_funcs.get(&specific_key) {
            return Ok(id);
        }
        let simple_key = (
            mod_path.to_string(),
            decl.name.clone(),
            comptime_args.to_vec(),
        );
        let mut env = HashMap::new();
        let mut ct_idx = 0;
        for p in &decl.params {
            if p.is_comptime {
                env.insert(p.name.clone(), comptime_args[ct_idx].clone());
                ct_idx += 1;
            }
        }
        let mut param_tys = Vec::new();
        for p in &decl.params {
            if !p.is_comptime {
                if matches!(p.ty, TypeExpr::Constraint(_) | TypeExpr::TraitBounds(_)) {
                    return Err(format!(
                        "Parameter '{}' of '{}' has a meta-type constraint by value; use '(comptime T: ..., {}: T)' for static dispatch or '&Trait' for dynamic dispatch",
                        p.name, decl.name, p.name
                    ));
                }
                let pty = self.resolve_type_expr(mod_path, None, &env, &p.ty)?;
                if let Some(tr) = self.traits.get(&pty) {
                    return Err(format!(
                        "Trait '{}' is an unsized meta-type constraint and cannot be passed by value in parameter '{}' of '{}'; use '(comptime T: {}, {}: T)' for static dispatch or '({}: &{})' for dynamic dispatch",
                        tr.name, p.name, decl.name, tr.name, p.name, p.name, tr.name
                    ));
                }
                if self.is_opaque_type(pty) {
                    return Err(format!(
                        "Unsized type '{}' cannot be passed by value in parameter '{}' of '{}'; use '*const {0}', '*mut {0}', '&{0}', or '&mut {0}'",
                        self.type_display_name(pty),
                        p.name,
                        decl.name
                    ));
                }
                param_tys.push(pty);
            }
        }
        let export = if decl.name == "main" {
            Some("main".to_string())
        } else {
            None
        };
        if let TypeExpr::OpaqueTrait(bound_expr) = &decl.ret_ty {
            if decl.vis.is_export() {
                return Err(format!(
                    "Exported function '{}' cannot return existential 'opaque Trait'; 'export fn' requires a C-compatible return type",
                    decl.name
                ));
            }
            let void_ty = self.intern_type(Type::Void);
            let fn_id = self.reserve_function(decl.vis, export, &param_tys, void_ty);
            self.opaque_ret_funcs.insert(
                fn_id,
                OpaqueRetBound {
                    bound_mod: mod_path.to_string(),
                    owner_ty: None,
                    env: env.clone(),
                    bound_expr: (**bound_expr).clone(),
                },
            );
            self.resolved_funcs.insert(specific_key, fn_id);
            self.resolved_funcs.entry(simple_key).or_insert(fn_id);
            let pending = PendingFunc {
                func_id: fn_id,
                module_path: mod_path.to_string(),
                owner_ty: None,
                decl: decl.clone(),
                comptime_env: env,
                closure_captures: Vec::new(),
            };
            self.lower_function_body(pending)?;
            let (_, ret_ty) = self.func_sigs[&fn_id].clone();
            self.apply_func_borrow_contracts(fn_id, decl, &param_tys, ret_ty)?;
            return Ok(fn_id);
        }
        let ret_ty = self.resolve_type_expr(mod_path, None, &env, &decl.ret_ty)?;
        if let Some(tr) = self.traits.get(&ret_ty) {
            return Err(format!(
                "Trait '{}' is an unsized meta-type constraint and cannot be returned by value from '{}'",
                tr.name, decl.name
            ));
        }
        if self.is_opaque_type(ret_ty) {
            return Err(format!(
                "Unsized type '{}' cannot be returned by value from '{}'; use '*const {0}', '*mut {0}', '&{0}', or '&mut {0}'",
                self.type_display_name(ret_ty),
                decl.name
            ));
        }
        let fn_id = self.reserve_function(decl.vis, export, &param_tys, ret_ty);
        self.apply_func_borrow_contracts(fn_id, decl, &param_tys, ret_ty)?;
        if decl.vis.is_export() {
            self.setup_export_function(fn_id, decl.name.clone(), decl, &param_tys, ret_ty)?;
        }
        self.resolved_funcs.insert(specific_key, fn_id);
        self.resolved_funcs.entry(simple_key).or_insert(fn_id);
        self.pending_funcs.push(PendingFunc {
            func_id: fn_id,
            module_path: mod_path.to_string(),
            owner_ty: None,
            decl: decl.clone(),
            comptime_env: env,
            closure_captures: Vec::new(),
        });
        Ok(fn_id)
    }

    pub fn resolve_type_expr(
        &mut self,
        mod_path: &str,
        self_ty: Option<TypeId>,
        env: &HashMap<String, ComptimeVal>,
        ty_expr: &TypeExpr,
    ) -> Result<TypeId, String> {
        match ty_expr {
            TypeExpr::Void => Ok(self.intern_type(Type::Void)),
            TypeExpr::Opaque => Ok(self.intern_opaque_type()),
            TypeExpr::OpaqueDef { methods } => {
                self.instantiate_named_opaque(mod_path, "<anon_opaque>", env, None, methods)
            }
            TypeExpr::OpaqueNewtype {
                underlying,
                methods,
            } => self.instantiate_opaque_newtype(
                mod_path,
                "<anon_newtype>",
                env,
                None,
                underlying,
                methods,
            ),
            TypeExpr::OpaqueTrait(_) => Err(
                "'opaque Trait' existential types are only permitted in function return types ('-> opaque Trait'); use '(comptime T: Trait, x: T)' or '&Trait' for parameters"
                    .to_string(),
            ),
            TypeExpr::Never => Ok(self.intern_type(Type::Never)),
            TypeExpr::Bool => Ok(self.intern_type(Type::Bool)),
            TypeExpr::Rune => Ok(self.intern_type(Type::Rune)),
            TypeExpr::F32 => Ok(self.intern_type(Type::F32)),
            TypeExpr::F64 => Ok(self.intern_type(Type::F64)),
            TypeExpr::Isize => Ok(self.intern_type(Type::Int {
                signed: true,
                bits: 64,
            })),
            TypeExpr::Usize => Ok(self.intern_type(Type::Int {
                signed: false,
                bits: 64,
            })),
            TypeExpr::Int { signed, bits } => Ok(self.intern_type(Type::Int {
                signed: *signed,
                bits: *bits,
            })),
            TypeExpr::CInt(ck) => Ok(self.intern_c_int_type(*ck)),
            TypeExpr::MetaType | TypeExpr::Constraint(_) | TypeExpr::TraitBounds(_) => {
                Ok(self.intern_type(Type::MetaType))
            }
            TypeExpr::Trait(methods) => {
                self.instantiate_trait(mod_path, "<anon_trait>", env, None, methods)
            }
            TypeExpr::SelfType => {
                self_ty.ok_or_else(|| "'Self' type used outside of a struct/record context".to_string())
            }
            TypeExpr::Ref { mutable, inner } => {
                if let TypeExpr::Constraint(c) = inner.as_ref() {
                    return Err(format!(
                        "Built-in meta-type constraint '{}' cannot be used as a dynamic trait object '&{}{}'",
                        c.name(),
                        if *mutable { "mut " } else { "" },
                        c.name()
                    ));
                }
                if matches!(inner.as_ref(), TypeExpr::MetaType) {
                    return Err("Meta-type 'type' cannot be used as a dynamic trait object".to_string());
                }
                if matches!(inner.as_ref(), TypeExpr::TraitBounds(_)) {
                    return Err(
                        "Multi-trait bounds ('A + B') are only valid on comptime type parameters; define a combined trait for dynamic dispatch"
                            .to_string(),
                    );
                }
                let pointee = self.resolve_type_expr(mod_path, self_ty, env, inner)?;
                if self.traits.contains_key(&pointee) {
                    return self.instantiate_trait_obj_type(pointee, *mutable);
                }
                Ok(self.intern_type(Type::Ptr {
                    mutable: *mutable,
                    pointee,
                }))
            }
            TypeExpr::Ptr { mutable, inner } => {
                let pointee = self.resolve_type_expr(mod_path, self_ty, env, inner)?;
                Ok(self.intern_raw_ptr_type(*mutable, pointee))
            }
            TypeExpr::Slice { mutable, elem } => {
                let elem_id = self.resolve_type_expr(mod_path, self_ty, env, elem)?;
                if self.is_opaque_type(elem_id) {
                    return Err(
                        "Unsized type 'opaque' has unknown element size and cannot form a slice '&[opaque]'"
                            .to_string(),
                    );
                }
                Ok(self.intern_slice_type(*mutable, elem_id))
            }
            TypeExpr::StrRef => Ok(self.intern_str_type()),
            TypeExpr::RelRef(_) | TypeExpr::RelSlice(_) | TypeExpr::RelStr => Err(
                "'&rel' relative references are only permitted in 'struct' field declarations"
                    .to_string(),
            ),
            TypeExpr::Optional(inner) => {
                let inner_id = self.resolve_type_expr(mod_path, self_ty, env, inner)?;
                if self.is_opaque_type(inner_id) {
                    return Err(
                        "Unsized type 'opaque' cannot be stored by value in '?opaque'; use '?*const opaque', '?*mut opaque', '?&opaque', or '?&mut opaque'"
                            .to_string(),
                    );
                }
                let u8_id = self.intern_type(Type::Int {
                    signed: false,
                    bits: 8,
                });
                let void_id = self.intern_type(Type::Void);
                let opt_id = self.intern_type(Type::Union {
                    tag: u8_id,
                    variants: vec![void_id, inner_id],
                });
                self.ensure_union_destructor(opt_id);
                Ok(opt_id)
            }
            TypeExpr::ErrorSetUnion(terms) => {
                let mut acc = self.resolve_type_expr(mod_path, self_ty, env, &terms[0])?;
                for term in &terms[1..] {
                    let next = self.resolve_type_expr(mod_path, self_ty, env, term)?;
                    acc = self.combine_error_types(acc, next)?;
                }
                Ok(acc)
            }
            TypeExpr::Result { err, ok } => {
                let err_id = self.resolve_type_expr(mod_path, self_ty, env, err)?;
                let ok_id = self.resolve_type_expr(mod_path, self_ty, env, ok)?;
                if self.is_opaque_type(ok_id) {
                    return Err(
                        "Unsized type 'opaque' cannot be used by value in result type 'E!opaque'"
                            .to_string(),
                    );
                }
                self.instantiate_result_type(err_id, ok_id)
            }
            TypeExpr::Array { elem, len } => {
                let elem_id = self.resolve_type_expr(mod_path, self_ty, env, elem)?;
                if self.is_opaque_type(elem_id) {
                    return Err(
                        "Unsized type 'opaque' has unknown size and cannot be an array element '[opaque; N]'"
                            .to_string(),
                    );
                }
                let len_val = self.eval_comptime_int(mod_path, self_ty, env, len)?;
                Ok(self.intern_type(Type::Array {
                    elem: elem_id,
                    len: len_val as u64,
                }))
            }
            TypeExpr::Simd { elem, len } => {
                let elem_id = self.resolve_type_expr(mod_path, self_ty, env, elem)?;
                if self.is_opaque_type(elem_id) {
                    return Err(
                        "Unsized type 'opaque' cannot be a SIMD vector element".to_string(),
                    );
                }
                let len_val = self.eval_comptime_int(mod_path, self_ty, env, len)?;
                Ok(self.intern_type(Type::Simd {
                    elem: elem_id,
                    len: len_val as u64,
                }))
            }
            TypeExpr::Pattern { base, ranges } => {
                let base_id = self.resolve_type_expr(mod_path, self_ty, env, base)?;
                if self.is_opaque_type(base_id) {
                    return Err(
                        "Unsized type 'opaque' cannot be a pattern base type".to_string(),
                    );
                }
                let mut resolved_ranges = Vec::with_capacity(ranges.len());
                for (lo_e, hi_e) in ranges {
                    let lo = self.eval_comptime_int(mod_path, self_ty, env, lo_e)?;
                    let hi = self.eval_comptime_int(mod_path, self_ty, env, hi_e)?;
                    if lo > hi {
                        return Err(format!("Invalid pattern range {lo}..={hi}: lower > upper"));
                    }
                    resolved_ranges.push((lo, hi));
                }
                Ok(self.intern_type(Type::Pattern {
                    base: base_id,
                    ranges: resolved_ranges,
                }))
            }
            TypeExpr::Tuple(elems) => {
                let mut tys = Vec::with_capacity(elems.len());
                for e in elems {
                    let e_id = self.resolve_type_expr(mod_path, self_ty, env, e)?;
                    if self.is_opaque_type(e_id) {
                        return Err(
                            "Unsized type 'opaque' cannot be stored by value in a tuple"
                                .to_string(),
                        );
                    }
                    tys.push(e_id);
                }
                Ok(self.intern_type(Type::Struct(tys)))
            }
            TypeExpr::FnPtr { params, ret } => {
                let mut args = Vec::with_capacity(params.len());
                for p in params {
                    args.push(self.resolve_type_expr(mod_path, self_ty, env, p)?);
                }
                let ret_id = self.resolve_type_expr(mod_path, self_ty, env, ret)?;
                Ok(self.intern_type(Type::FnPtr { args, ret: ret_id }))
            }
            TypeExpr::Enum(variants) => self.instantiate_enum("<anon_enum>", variants),
            TypeExpr::Union(variants) => {
                self.instantiate_union(mod_path, "<anon_union>", env, None, variants)
            }
            TypeExpr::Error(items) => {
                self.instantiate_error(mod_path, "<anon_error>", env, None, items)
            }
            TypeExpr::Record { fields, methods } => {
                self.instantiate_composite(
                    mod_path,
                    "<anon_record>",
                    false,
                    StructOwnership::Copy,
                    false,
                    env,
                    None,
                    fields,
                    methods,
                    None,
                    &[],
                    &[],
                    None,
                )
            }
            TypeExpr::Struct {
                ownership,
                is_sync,
                fields,
                methods,
                default_hook,
                clone_hooks,
                drop_hooks,
                format_hook,
            } => self.instantiate_composite(
                mod_path,
                "<anon_struct>",
                true,
                *ownership,
                *is_sync,
                env,
                None,
                fields,
                methods,
                default_hook.clone(),
                clone_hooks,
                drop_hooks,
                format_hook.clone(),
            ),
            TypeExpr::Named(path) => {
                if path.len() == 1
                    && let Some(ComptimeVal::Type(t_id)) = env.get(&path[0])
                {
                    return Ok(*t_id);
                }
                match self.resolve_path(mod_path, path)? {
                    ResolvedItem::Type(tmod, tname) => self.resolve_named_type(&tmod, &tname),
                    other => Err(format!("Expected type for path '{}', found {other:?}", path.join("::"))),
                }
            }
            TypeExpr::TypeCall { path, args } => {
                let ResolvedItem::Func(fmod, fname) = self.resolve_path(mod_path, path)? else {
                    return Err(format!(
                        "'{}' is not a comptime type function",
                        path.join("::")
                    ));
                };
                let mut ct_args = Vec::with_capacity(args.len());
                for arg in args {
                    ct_args.push(self.eval_comptime_val(mod_path, self_ty, env, arg)?);
                }
                self.eval_comptime_type_func(&fmod, &fname, &ct_args)
            }
        }
    }

    fn eval_comptime_val(
        &mut self,
        mod_path: &str,
        self_ty: Option<TypeId>,
        env: &HashMap<String, ComptimeVal>,
        expr: &Expr,
    ) -> Result<ComptimeVal, String> {
        match expr {
            Expr::TypeVal(te) => Ok(ComptimeVal::Type(
                self.resolve_type_expr(mod_path, self_ty, env, te)?,
            )),
            Expr::LogicalOr(lhs, rhs) => {
                let l_val = self.eval_comptime_val(mod_path, self_ty, env, lhs)?;
                let r_val = self.eval_comptime_val(mod_path, self_ty, env, rhs)?;
                match (l_val, r_val) {
                    (ComptimeVal::Type(l_ty), ComptimeVal::Type(r_ty)) => {
                        Ok(ComptimeVal::Type(self.combine_error_types(l_ty, r_ty)?))
                    }
                    (ComptimeVal::Bool(l_b), ComptimeVal::Bool(r_b)) => {
                        Ok(ComptimeVal::Bool(l_b || r_b))
                    }
                    _ => Err("Unsupported operands for comptime '||'".to_string()),
                }
            }
            Expr::Int(n) => Ok(ComptimeVal::Int(*n)),
            Expr::Bool(b) => Ok(ComptimeVal::Bool(*b)),
            Expr::Path(p) => {
                if p.len() == 1
                    && let Some(v) = env.get(&p[0])
                {
                    return Ok(v.clone());
                }
                if let Ok(ResolvedItem::Type(tmod, tname)) = self.resolve_path(mod_path, p) {
                    return Ok(ComptimeVal::Type(self.resolve_named_type(&tmod, &tname)?));
                }
                Err(format!(
                    "Cannot evaluate '{}' at comptime",
                    p.join("::")
                ))
            }
            Expr::Call { callee, args } => {
                if let Expr::Path(path) = callee.as_ref()
                    && let Ok(ResolvedItem::Func(fmod, fname)) = self.resolve_path(mod_path, path)
                {
                    let mut ct_args = Vec::with_capacity(args.len());
                    for a in args {
                        ct_args.push(self.eval_comptime_val(mod_path, self_ty, env, a)?);
                    }
                    return self.eval_comptime_func(&fmod, &fname, &ct_args);
                }
                Err(format!("Unsupported comptime call {expr:?}"))
            }
            Expr::StructLit { .. } | Expr::Ref { .. } => {
                Ok(ComptimeVal::ConstExpr(format!("{expr:?}"), expr.clone()))
            }
            _ => Ok(ComptimeVal::Int(
                self.eval_comptime_int(mod_path, self_ty, env, expr)?,
            )),
        }
    }

    #[allow(clippy::only_used_in_recursion)]
    fn eval_comptime_int(
        &mut self,
        mod_path: &str,
        self_ty: Option<TypeId>,
        env: &HashMap<String, ComptimeVal>,
        expr: &Expr,
    ) -> Result<i128, String> {
        match expr {
            Expr::Int(n) => Ok(*n),
            Expr::Path(p) if p.len() == 1 => {
                if let Some(ComptimeVal::Int(n)) = env.get(&p[0]) {
                    Ok(*n)
                } else {
                    Err(format!("Expected comptime integer for '{}'", p[0]))
                }
            }
            Expr::Unary {
                op: UnOp::Neg,
                expr: inner,
            } => Ok(-self.eval_comptime_int(mod_path, self_ty, env, inner)?),
            Expr::Binary { op, lhs, rhs } => {
                let l = self.eval_comptime_int(mod_path, self_ty, env, lhs)?;
                let r = self.eval_comptime_int(mod_path, self_ty, env, rhs)?;
                match op {
                    BinOp::Add | BinOp::AddWrap => Ok(l + r),
                    BinOp::Sub | BinOp::SubWrap => Ok(l - r),
                    BinOp::Mul | BinOp::MulWrap => Ok(l * r),
                    BinOp::Div => Ok(l / r),
                    BinOp::Rem => Ok(l % r),
                    _ => Err(format!("Unsupported comptime binary op {op}")),
                }
            }
            _ => Err(format!(
                "Cannot evaluate expression as comptime integer: {expr:?}"
            )),
        }
    }

    fn eval_comptime_type_func(
        &mut self,
        mod_path: &str,
        fname: &str,
        args: &[ComptimeVal],
    ) -> Result<TypeId, String> {
        let key = (mod_path.to_string(), fname.to_string(), args.to_vec());
        if let Some(&ty_id) = self.memoized_type_calls.get(&key) {
            return Ok(ty_id);
        }
        let val = self.eval_comptime_func(mod_path, fname, args)?;
        let ComptimeVal::Type(ty_id) = val else {
            return Err(format!(
                "Expected comptime function '{fname}' to return a type, got {val:?}"
            ));
        };
        self.memoized_type_calls.insert(key, ty_id);
        Ok(ty_id)
    }

    fn eval_comptime_func(
        &mut self,
        mod_path: &str,
        fname: &str,
        args: &[ComptimeVal],
    ) -> Result<ComptimeVal, String> {
        let Some((def_mod, orig_name, Item::Func(decl), _)) =
            self.find_item_in_module(mod_path, mod_path, fname)?
        else {
            return Err(format!("Comptime function '{fname}' not found in '{mod_path}'"));
        };
        let mod_path = def_mod.as_str();
        let fname = orig_name.as_str();
        if decl.params.len() != args.len() {
            return Err(format!(
                "Comptime function '{fname}' expects {} args, got {}",
                decl.params.len(),
                args.len()
            ));
        }
        let mut local_env = HashMap::new();
        for (p, arg) in decl.params.iter().zip(args.iter()) {
            if let ComptimeVal::Type(arg_ty) = arg
                && let Some(Err(e)) =
                    self.eval_comptime_type_bound(mod_path, None, &local_env, &p.ty, *arg_ty)?
            {
                return Err(format!("{} (for parameter '{}' in '{}')", e, p.name, fname));
            }
            local_env.insert(p.name.clone(), arg.clone());
        }
        for stmt in &decl.body.stmts {
            match stmt {
                Stmt::Let { name, init, .. } => {
                    let v = self.eval_comptime_val(mod_path, None, &local_env, init)?;
                    local_env.insert(name.clone(), v);
                }
                Stmt::Return(Some(Expr::TypeVal(TypeExpr::Opaque))) => {
                    let ty_id = self.instantiate_named_opaque(
                        mod_path,
                        fname,
                        &local_env,
                        Some((mod_path.to_string(), fname.to_string(), args.to_vec())),
                        &[],
                    )?;
                    return Ok(ComptimeVal::Type(ty_id));
                }
                Stmt::Return(Some(Expr::TypeVal(TypeExpr::OpaqueDef { methods }))) => {
                    let ty_id = self.instantiate_named_opaque(
                        mod_path,
                        fname,
                        &local_env,
                        Some((mod_path.to_string(), fname.to_string(), args.to_vec())),
                        methods,
                    )?;
                    return Ok(ComptimeVal::Type(ty_id));
                }
                Stmt::Return(Some(Expr::TypeVal(TypeExpr::OpaqueNewtype {
                    underlying,
                    methods,
                }))) => {
                    let ty_id = self.instantiate_opaque_newtype(
                        mod_path,
                        fname,
                        &local_env,
                        Some((mod_path.to_string(), fname.to_string(), args.to_vec())),
                        underlying,
                        methods,
                    )?;
                    return Ok(ComptimeVal::Type(ty_id));
                }
                Stmt::Return(Some(Expr::TypeVal(TypeExpr::Trait(methods)))) => {
                    let ty_id = self.instantiate_trait(
                        mod_path,
                        fname,
                        &local_env,
                        Some((mod_path.to_string(), fname.to_string(), args.to_vec())),
                        methods,
                    )?;
                    return Ok(ComptimeVal::Type(ty_id));
                }
                Stmt::Return(Some(Expr::TypeVal(TypeExpr::Union(variants)))) => {
                    let ty_id = self.instantiate_union(
                        mod_path,
                        fname,
                        &local_env,
                        Some((mod_path.to_string(), fname.to_string(), args.to_vec())),
                        variants,
                    )?;
                    return Ok(ComptimeVal::Type(ty_id));
                }
                Stmt::Return(Some(Expr::TypeVal(TypeExpr::Error(items)))) => {
                    let ty_id = self.instantiate_error(
                        mod_path,
                        fname,
                        &local_env,
                        Some((mod_path.to_string(), fname.to_string(), args.to_vec())),
                        items,
                    )?;
                    return Ok(ComptimeVal::Type(ty_id));
                }
                Stmt::Return(Some(Expr::TypeVal(TypeExpr::Record { fields, methods }))) => {
                    let ty_id = self.instantiate_composite(
                        mod_path,
                        fname,
                        false,
                        StructOwnership::Copy,
                        false,
                        &local_env,
                        Some((mod_path.to_string(), fname.to_string(), args.to_vec())),
                        fields,
                        methods,
                        None,
                        &[],
                        &[],
                        None,
                    )?;
                    return Ok(ComptimeVal::Type(ty_id));
                }
                Stmt::Return(Some(Expr::TypeVal(TypeExpr::Struct {
                    ownership,
                    is_sync,
                    fields,
                    methods,
                    default_hook,
                    clone_hooks,
                    drop_hooks,
                    format_hook,
                }))) => {
                    let ty_id = self.instantiate_composite(
                        mod_path,
                        fname,
                        true,
                        *ownership,
                        *is_sync,
                        &local_env,
                        Some((mod_path.to_string(), fname.to_string(), args.to_vec())),
                        fields,
                        methods,
                        default_hook.clone(),
                        clone_hooks,
                        drop_hooks,
                        format_hook.clone(),
                    )?;
                    return Ok(ComptimeVal::Type(ty_id));
                }
                Stmt::Return(Some(expr)) => {
                    return self.eval_comptime_val(mod_path, None, &local_env, expr);
                }
                _ => {
                    return Err(format!(
                        "Unsupported statement in comptime function '{fname}': {stmt:?}"
                    ));
                }
            }
        }
        Err(format!("Comptime function '{fname}' did not return a value"))
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
}

impl<'a> FuncLowerer<'a> {
    fn new(compiler: &'a mut Compiler, pending: PendingFunc) -> Self {
        let existing_locals = compiler.program.functions
            .iter()
            .find(|f| f.id == pending.func_id)
            .unwrap()
            .locals
            .clone();
        Self {
            compiler,
            func_id: pending.func_id,
            mod_path: pending.module_path,
            owner_ty: pending.owner_ty,
            decl: pending.decl,
            comptime_env: pending.comptime_env,
            closure_captures: pending.closure_captures,
            locals: existing_locals,
            blocks: vec![BasicBlock {
                statements: Vec::new(),
                terminator: Terminator::Unreachable,
            }],
            terminated: vec![false],
            cur_block: BlockId(0),
            scopes: vec![Vec::new()],
            inferred_opaque_ret: None,
            last_call_opaque_bound: None,
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

    fn lookup_var(&self, name: &str) -> Option<(LocalId, TypeId)> {
        for scope in self.scopes.iter().rev() {
            for var in scope.iter().rev() {
                if var.name == name {
                    return Some((var.local, var.ty));
                }
            }
        }
        None
    }

    fn lookup_var_opaque_bound(&self, name: &str) -> Option<OpaqueRetBound> {
        for scope in self.scopes.iter().rev() {
            for var in scope.iter().rev() {
                if var.name == name {
                    return var.opaque_bound.clone();
                }
            }
        }
        None
    }

    fn check_opaque_ret_expr(
        &mut self,
        bound_expr: &TypeExpr,
        expr_ty: TypeId,
    ) -> Result<TypeId, String> {
        let check_res = self.compiler.eval_comptime_type_bound(
            &self.mod_path,
            self.owner_ty,
            &self.comptime_env,
            bound_expr,
            expr_ty,
        )?;
        match check_res {
            Some(Ok(_)) => {}
            Some(Err(e)) => {
                return Err(format!(
                    "Return type '{}' in '{}' does not satisfy 'opaque' return bound: {}",
                    self.compiler.type_display_name(expr_ty),
                    self.decl.name,
                    e
                ));
            }
            None => {
                return Err(format!(
                    "Invalid trait or constraint bound in '-> opaque ...' on '{}'",
                    self.decl.name
                ));
            }
        }
        if let Some(prev_ty) = self.inferred_opaque_ret {
            if prev_ty != expr_ty {
                return Err(format!(
                    "Conflicting concrete return types in '-> opaque ...' function '{}': '{}' vs '{}'; all return paths must return the same concrete type",
                    self.decl.name,
                    self.compiler.type_display_name(prev_ty),
                    self.compiler.type_display_name(expr_ty)
                ));
            }
        } else {
            self.inferred_opaque_ret = Some(expr_ty);
            self.locals[0] = expr_ty;
            if let Some(sig) = self.compiler.func_sigs.get_mut(&self.func_id) {
                sig.1 = expr_ty;
            }
        }
        Ok(expr_ty)
    }

    fn lookup_capture(&self, name: &str) -> Option<(Place, TypeId)> {
        let (idx, (_, outer_ty, is_by_ref)) = self
            .closure_captures
            .iter()
            .enumerate()
            .find(|(_, (n, _, _))| n == name)?;
        let mut place = Place::new(LocalId(1));
        if matches!(
            self.compiler.program.types[self.locals[1].0 as usize],
            Type::Ptr { .. }
        ) {
            place.projections.push(Projection::Deref);
        }
        place.projections.push(Projection::Field(idx as u32));
        if *is_by_ref {
            place.projections.push(Projection::Deref);
        }
        Some((place, *outer_ty))
    }

    fn emit_drop_and_dead(&mut self, local: LocalId) {
        let arg_count = self
            .decl
            .params
            .iter()
            .filter(|p| !p.is_comptime)
            .count() as u32
            + u32::from(!self.closure_captures.is_empty());
        let next_bb = self.new_block();
        self.terminate(Terminator::Drop {
            place: Place::new(local),
            target: next_bb,
        });
        self.cur_block = next_bb;
        if local.0 > arg_count {
            self.emit(Statement::StorageDead(local));
        }
    }

    fn cleanup_top_scope(&mut self) {
        if let Some(top) = self.scopes.last().cloned() {
            for var in top.iter().rev() {
                self.emit_drop_and_dead(var.local);
            }
        }
    }

    fn cleanup_all_scopes(&mut self) {
        let all_scopes = self.scopes.clone();
        for scope in all_scopes.iter().rev() {
            for var in scope.iter().rev() {
                self.emit_drop_and_dead(var.local);
            }
        }
    }

    fn lower(&mut self) -> Result<(), String> {
        // Bind runtime parameters into root scope (`LocalId(1)` is `__env` when `closure_captures` is non-empty)
        let mut arg_local_idx = if self.closure_captures.is_empty() {
            1u32
        } else {
            if !matches!(
                self.compiler.program.types[self.locals[1].0 as usize],
                Type::Ptr { .. }
            ) {
                self.scopes[0].push(ScopeVar {
                    name: "__env".to_string(),
                    local: LocalId(1),
                    ty: self.locals[1],
                    opaque_bound: None,
                });
            }
            2u32
        };
        for p in &self.decl.params.clone() {
            if !p.is_comptime {
                let local = LocalId(arg_local_idx);
                let ty = self.locals[arg_local_idx as usize];
                self.scopes[0].push(ScopeVar {
                    name: p.name.clone(),
                    local,
                    ty,
                    opaque_bound: None,
                });
                arg_local_idx += 1;
            } else if let Some(ComptimeVal::ConstExpr(_, const_expr)) =
                self.comptime_env.get(&p.name).cloned()
            {
                match &const_expr {
                    Expr::Ref {
                        mutable,
                        expr: inner,
                    } => {
                        let (val_op, val_ty) = self.lower_expr(inner, None)?;
                        let val_loc = self.alloc_temp(val_ty);
                        self.emit(Statement::StorageLive(val_loc));
                        self.emit(Statement::Assign(Place::new(val_loc), Rvalue::Use(val_op)));
                        let ref_ty = self.compiler.intern_type(Type::Ptr {
                            mutable: *mutable,
                            pointee: val_ty,
                        });
                        let ref_loc = self.alloc_temp(ref_ty);
                        self.emit(Statement::StorageLive(ref_loc));
                        self.emit(Statement::Assign(
                            Place::new(ref_loc),
                            Rvalue::Ref {
                                mutable: *mutable,
                                place: Place::new(val_loc),
                            },
                        ));
                        self.scopes[0].push(ScopeVar {
                            name: p.name.clone(),
                            local: ref_loc,
                            ty: ref_ty,
                            opaque_bound: None,
                        });
                    }
                    _ => {
                        let exp_ty = self
                            .compiler
                            .resolve_type_expr(
                                &self.mod_path,
                                self.owner_ty,
                                &self.comptime_env,
                                &p.ty,
                            )
                            .ok();
                        let (val_op, val_ty) = self.lower_expr(&const_expr, exp_ty)?;
                        let val_loc = self.alloc_temp(val_ty);
                        self.emit(Statement::StorageLive(val_loc));
                        self.emit(Statement::Assign(Place::new(val_loc), Rvalue::Use(val_op)));
                        self.scopes[0].push(ScopeVar {
                            name: p.name.clone(),
                            local: val_loc,
                            ty: val_ty,
                            opaque_bound: None,
                        });
                    }
                }
            }
        }

        if self.decl.vis.is_export() {
            let usize_ty = self.compiler.intern_type(Type::Int {
                signed: false,
                bits: 64,
            });
            let mut check_locals = Vec::new();
            let mut idx = if self.closure_captures.is_empty() {
                1u32
            } else {
                2u32
            };
            for p in &self.decl.params {
                if !p.is_comptime {
                    let local = LocalId(idx);
                    let ty = self.locals[idx as usize];
                    if self.compiler.raw_ptrs.contains_key(&ty) {
                        check_locals.push(local);
                    }
                    idx += 1;
                }
            }
            for local in check_locals {
                let addr_tmp = self.alloc_temp(usize_ty);
                self.emit(Statement::Assign(
                    Place::new(addr_tmp),
                    Rvalue::Cast(Operand::Copy(Place::new(local)), usize_ty),
                ));
                let ok_bb = self.new_block();
                let trap_bb = self.new_block();
                self.terminate(Terminator::SwitchInt {
                    discr: Operand::Copy(Place::new(addr_tmp)),
                    targets: vec![(0, trap_bb)],
                    otherwise: ok_bb,
                });
                self.cur_block = trap_bb;
                self.terminate(Terminator::Unreachable);
                self.cur_block = ok_bb;
            }
        }

        let body = self.decl.body.clone();
        self.lower_block_stmts(&body)?;

        if matches!(self.decl.ret_ty, TypeExpr::OpaqueTrait(_))
            && self.inferred_opaque_ret.is_none()
        {
            return Err(format!(
                "Function '{}' with '-> opaque ...' return type must return a concrete value",
                self.decl.name
            ));
        }

        let ret_ty = self.locals[0];
        if !self.is_terminated() {
            if matches!(self.compiler.program.types[ret_ty.0 as usize], Type::Void) {
                self.emit(Statement::Assign(
                    Place::new(LocalId(0)),
                    Rvalue::Use(Operand::Const(ConstValue::Void)),
                ));
                self.cleanup_all_scopes();
                self.terminate(Terminator::Return);
            } else if let Some(&res_info) = self.compiler.results.get(&ret_ty)
                && matches!(
                    self.compiler.program.types[res_info.ok_ty.0 as usize],
                    Type::Void
                )
            {
                self.emit(Statement::Assign(
                    Place::new(LocalId(0)),
                    Rvalue::Union {
                        ty: ret_ty,
                        variant: 0,
                        payload: Operand::Const(ConstValue::Void),
                    },
                ));
                self.cleanup_all_scopes();
                self.terminate(Terminator::Return);
            } else if matches!(self.compiler.program.types[ret_ty.0 as usize], Type::Never) {
                return Err(format!(
                    "Function '{}' declared '-> never' reaches end of function without diverging",
                    self.decl.name
                ));
            } else {
                return Err(format!(
                    "Function '{}' reaches end of non-void function without returning",
                    self.decl.name
                ));
            }
        }

        let func = self
            .compiler
            .program
            .functions
            .iter_mut()
            .find(|f| f.id == self.func_id)
            .unwrap();
        func.locals = self.locals.clone();
        func.blocks = self.blocks.clone();
        Ok(())
    }

    fn lower_scoped_block(&mut self, block: &Block) -> Result<(), String> {
        self.scopes.push(Vec::new());
        self.lower_block_stmts(block)?;
        if !self.is_terminated() {
            self.cleanup_top_scope();
        }
        self.scopes.pop();
        Ok(())
    }

    fn lower_block_stmts(&mut self, block: &Block) -> Result<(), String> {
        for stmt in &block.stmts {
            if self.is_terminated() {
                break;
            }
            self.lower_stmt(stmt)?;
        }
        Ok(())
    }

    fn verify_pattern_const(&self, ty_id: TypeId, val: i128) -> Result<(), String> {
        if let Type::Pattern { ranges, .. } = &self.compiler.program.types[ty_id.0 as usize] {
            let valid = ranges.iter().any(|&(lo, hi)| val >= lo && val <= hi);
            if !valid {
                return Err(format!(
                    "Compile-time value {val} is outside valid pattern ranges of {}",
                    self.compiler.program.types[ty_id.0 as usize]
                ));
            }
        }
        Ok(())
    }

    fn coerce_operand(
        &mut self,
        op: Operand,
        src_ty: TypeId,
        target_ty: TypeId,
    ) -> Result<Operand, String> {
        // Automatic reborrowing of a named `&mut T` local or field when passed to `&mut T`/`&T` (or `&mut opaque`/`&opaque`)
        if let (
            Type::Ptr {
                mutable: true,
                pointee: src_pt,
            },
            Type::Ptr {
                mutable: dst_mut,
                pointee: dst_pt,
            },
        ) = (
            self.compiler.program.types[src_ty.0 as usize].clone(),
            self.compiler.program.types[target_ty.0 as usize].clone(),
        ) && (src_pt == dst_pt || self.compiler.is_universal_opaque_type(dst_pt))
            && !self.compiler.raw_ptrs.contains_key(&src_ty)
            && !self.compiler.raw_ptrs.contains_key(&target_ty)
            && let Operand::Move(mut place) = op.clone()
            && (!place.projections.is_empty()
                || self
                    .scopes
                    .iter()
                    .flatten()
                    .any(|v| v.local == place.local))
        {
            place.projections.push(Projection::Deref);
            let tmp = self.alloc_temp(target_ty);
            self.emit(Statement::Assign(
                Place::new(tmp),
                Rvalue::Ref {
                    mutable: dst_mut,
                    place,
                },
            ));
            return Ok(Operand::Move(Place::new(tmp)));
        }

        // Automatic reborrowing of a named `&mut [T]` slice local when passed to `&mut [T]` or `&[T]`
        if let (Some(&src_slice), Some(&target_slice)) = (
            self.compiler.slices.get(&src_ty),
            self.compiler.slices.get(&target_ty),
        ) && src_slice.mutable
            && src_slice.elem == target_slice.elem
            && let Operand::Move(place) = op.clone()
            && place.projections.is_empty()
            && self
                .scopes
                .iter()
                .flatten()
                .any(|v| v.local == place.local)
        {
            let mut deref_ptr = Place::new(place.local);
            deref_ptr.projections.push(Projection::Field(0));
            deref_ptr.projections.push(Projection::Deref);
            let mut len_field = Place::new(place.local);
            len_field.projections.push(Projection::Field(1));
            let reborrow_ptr = self.alloc_temp(target_slice.ptr_ty);
            self.emit(Statement::Assign(
                Place::new(reborrow_ptr),
                Rvalue::Ref {
                    mutable: target_slice.mutable,
                    place: deref_ptr,
                },
            ));
            let dst = self.alloc_temp(target_ty);
            self.emit(Statement::Assign(
                Place::new(dst),
                Rvalue::Aggregate(
                    target_ty,
                    vec![
                        Operand::Move(Place::new(reborrow_ptr)),
                        Operand::Copy(len_field),
                    ],
                ),
            ));
            return Ok(Operand::Move(Place::new(dst)));
        }

        // Automatic reborrowing of a named `&mut MyTrait` trait object local when passed to `&mut MyTrait` or `&MyTrait`
        if let (Some(src_tobj), Some(target_tobj)) = (
            self.compiler.trait_objs.get(&src_ty).cloned(),
            self.compiler.trait_objs.get(&target_ty).cloned(),
        ) && src_tobj.mutable
            && src_tobj.trait_ty == target_tobj.trait_ty
            && let Operand::Move(place) = op.clone()
            && place.projections.is_empty()
            && self
                .scopes
                .iter()
                .flatten()
                .any(|v| v.local == place.local)
        {
            let mut deref_ptr = Place::new(place.local);
            deref_ptr.projections.push(Projection::Field(0));
            deref_ptr.projections.push(Projection::Deref);
            let mut vt_field = Place::new(place.local);
            vt_field.projections.push(Projection::Field(1));
            let reborrow_ptr = self.alloc_temp(target_tobj.data_ptr_ty);
            self.emit(Statement::Assign(
                Place::new(reborrow_ptr),
                Rvalue::Ref {
                    mutable: target_tobj.mutable,
                    place: deref_ptr,
                },
            ));
            let dst = self.alloc_temp(target_ty);
            self.emit(Statement::Assign(
                Place::new(dst),
                Rvalue::Aggregate(
                    target_ty,
                    vec![
                        Operand::Move(Place::new(reborrow_ptr)),
                        Operand::Copy(vt_field),
                    ],
                ),
            ));
            return Ok(Operand::Move(Place::new(dst)));
        }

        if src_ty == target_ty {
            if let Operand::Const(ConstValue::I64(n)) = &op {
                self.verify_pattern_const(target_ty, *n)?;
            }
            return Ok(op);
        }

        // Coerce `&T`/`&mut T` -> `&MyTrait`/`&mut MyTrait` and `&mut MyTrait` -> `&MyTrait`
        if let Some(target_tobj) = self.compiler.trait_objs.get(&target_ty).cloned() {
            if let Some(src_tobj) = self.compiler.trait_objs.get(&src_ty).cloned()
                && src_tobj.trait_ty == target_tobj.trait_ty
            {
                if target_tobj.mutable && !src_tobj.mutable {
                    return Err(format!(
                        "Cannot coerce shared trait object '&{}' to mutable trait object '&mut {}'",
                        self.compiler.type_display_name(target_tobj.trait_ty),
                        self.compiler.type_display_name(target_tobj.trait_ty)
                    ));
                }
                let src_local = match op {
                    Operand::Copy(p) | Operand::Move(p) if p.projections.is_empty() => p.local,
                    other => {
                        let tmp = self.alloc_temp(src_ty);
                        self.emit(Statement::Assign(Place::new(tmp), Rvalue::Use(other)));
                        tmp
                    }
                };
                let mut ptr_field = Place::new(src_local);
                ptr_field.projections.push(Projection::Field(0));
                let mut vt_field = Place::new(src_local);
                vt_field.projections.push(Projection::Field(1));
                let cast_ptr = self.alloc_temp(target_tobj.data_ptr_ty);
                self.emit(Statement::Assign(
                    Place::new(cast_ptr),
                    Rvalue::Cast(Operand::Copy(ptr_field), target_tobj.data_ptr_ty),
                ));
                let dst = self.alloc_temp(target_ty);
                self.emit(Statement::Assign(
                    Place::new(dst),
                    Rvalue::Aggregate(
                        target_ty,
                        vec![
                            Operand::Copy(Place::new(cast_ptr)),
                            Operand::Copy(vt_field),
                        ],
                    ),
                ));
                return Ok(Operand::Copy(Place::new(dst)));
            }
            if let Type::Ptr {
                mutable: src_mut,
                pointee: concrete_ty,
            } = self.compiler.program.types[src_ty.0 as usize]
                && !self.compiler.raw_ptrs.contains_key(&src_ty)
            {
                if target_tobj.mutable && !src_mut {
                    return Err(format!(
                        "Cannot coerce immutable reference '&{}' to mutable trait object '&mut {}'",
                        self.compiler.type_display_name(concrete_ty),
                        self.compiler.type_display_name(target_tobj.trait_ty)
                    ));
                }
                let (gl_id, thunk_ids) = self.compiler.get_or_create_vtable(
                    &self.mod_path,
                    concrete_ty,
                    target_tobj.trait_ty,
                )?;
                let gl_mut_ptr_ty = self.compiler.intern_type(Type::Ptr {
                    mutable: true,
                    pointee: target_tobj.vtable_ty,
                });
                let gl_mut_ptr_tmp = self.alloc_temp(gl_mut_ptr_ty);
                self.emit(Statement::Assign(
                    Place::new(gl_mut_ptr_tmp),
                    Rvalue::Use(Operand::Const(ConstValue::Global(gl_id))),
                ));
                let mut deref_gl = Place::new(gl_mut_ptr_tmp);
                deref_gl.projections.push(Projection::Deref);
                let thunk_ops = thunk_ids
                    .into_iter()
                    .map(|id| Operand::Const(ConstValue::Func(id)))
                    .collect();
                self.emit(Statement::Assign(
                    deref_gl,
                    Rvalue::Aggregate(target_tobj.vtable_ty, thunk_ops),
                ));
                let vt_ptr_tmp = self.alloc_temp(target_tobj.vtable_ptr_ty);
                self.emit(Statement::Assign(
                    Place::new(vt_ptr_tmp),
                    Rvalue::Cast(
                        Operand::Copy(Place::new(gl_mut_ptr_tmp)),
                        target_tobj.vtable_ptr_ty,
                    ),
                ));
                let data_ptr_tmp = self.alloc_temp(target_tobj.data_ptr_ty);
                self.emit(Statement::Assign(
                    Place::new(data_ptr_tmp),
                    Rvalue::Cast(op, target_tobj.data_ptr_ty),
                ));
                let dst = self.alloc_temp(target_ty);
                self.emit(Statement::Assign(
                    Place::new(dst),
                    Rvalue::Aggregate(
                        target_ty,
                        vec![
                            if target_tobj.mutable {
                                Operand::Move(Place::new(data_ptr_tmp))
                            } else {
                                Operand::Copy(Place::new(data_ptr_tmp))
                            },
                            Operand::Copy(Place::new(vt_ptr_tmp)),
                        ],
                    ),
                ));
                return Ok(if target_tobj.mutable {
                    Operand::Move(Place::new(dst))
                } else {
                    Operand::Copy(Place::new(dst))
                });
            }
            return Err(format!(
                "Cannot coerce '{}' to trait object '{}'",
                self.compiler.type_display_name(src_ty),
                self.compiler.type_display_name(target_ty)
            ));
        }
        // Coerce safe references (`&mut T` -> `&T`, `&T`/`&mut T` -> `*const T`/`*mut T`, `&T`/`&mut T` -> `&opaque`/`&mut opaque`) and raw pointers (`*mut T` -> `*const T`, `*const T`/`*mut T` -> `*const opaque`/`*mut opaque`)
        if let (
            Type::Ptr {
                mutable: src_mut,
                pointee: src_pt,
            },
            Type::Ptr {
                mutable: dst_mut,
                pointee: dst_pt,
            },
        ) = (
            self.compiler.program.types[src_ty.0 as usize].clone(),
            self.compiler.program.types[target_ty.0 as usize].clone(),
        ) && (src_pt == dst_pt || self.compiler.is_universal_opaque_type(dst_pt))
            && (!dst_mut || src_mut)
            && (!self.compiler.raw_ptrs.contains_key(&src_ty)
                || self.compiler.raw_ptrs.contains_key(&target_ty))
        {
            let tmp = self.alloc_temp(target_ty);
            self.emit(Statement::Assign(
                Place::new(tmp),
                Rvalue::Cast(op, target_ty),
            ));
            return Ok(if dst_mut && !self.compiler.raw_ptrs.contains_key(&target_ty) {
                Operand::Move(Place::new(tmp))
            } else {
                Operand::Copy(Place::new(tmp))
            });
        }
        // Coerce `&[T; N]` / `&mut [T; N]` into `&[T]` / `&mut [T]`, string literals into `&str`, and `&mut [T]` into `&[T]`
        if let Some(&target_slice) = self.compiler.slices.get(&target_ty) {
            if let Operand::Const(ConstValue::Str(s)) = &op
                && !target_slice.mutable
                && matches!(
                    self.compiler.program.types[target_slice.elem.0 as usize],
                    Type::Int {
                        signed: false,
                        bits: 8
                    }
                )
            {
                let str_len = s.len() as i128;
                let str_tmp = self.alloc_temp(src_ty);
                self.emit(Statement::Assign(Place::new(str_tmp), Rvalue::Use(op)));
                let cast_ptr = self.alloc_temp(target_slice.ptr_ty);
                self.emit(Statement::Assign(
                    Place::new(cast_ptr),
                    Rvalue::Cast(Operand::Copy(Place::new(str_tmp)), target_slice.ptr_ty),
                ));
                let len_op = Operand::Const(ConstValue::I64(str_len));
                let dst = self.alloc_temp(target_ty);
                self.emit(Statement::Assign(
                    Place::new(dst),
                    Rvalue::Aggregate(
                        target_ty,
                        vec![Operand::Copy(Place::new(cast_ptr)), len_op],
                    ),
                ));
                return Ok(Operand::Copy(Place::new(dst)));
            }
            if let Type::Ptr {
                mutable: src_mut,
                pointee,
            } = self.compiler.program.types[src_ty.0 as usize]
                && let Type::Array {
                    elem: src_elem,
                    len: src_len,
                } = self.compiler.program.types[pointee.0 as usize]
                && src_elem == target_slice.elem
                && (!target_slice.mutable || src_mut)
            {
                let cast_ptr = self.alloc_temp(target_slice.ptr_ty);
                self.emit(Statement::Assign(
                    Place::new(cast_ptr),
                    Rvalue::Cast(op, target_slice.ptr_ty),
                ));
                let len_op = Operand::Const(ConstValue::I64(src_len as i128));
                let dst = self.alloc_temp(target_ty);
                self.emit(Statement::Assign(
                    Place::new(dst),
                    Rvalue::Aggregate(
                        target_ty,
                        vec![Operand::Copy(Place::new(cast_ptr)), len_op],
                    ),
                ));
                return Ok(Operand::Copy(Place::new(dst)));
            }
            if let Some(&src_slice) = self.compiler.slices.get(&src_ty)
                && src_slice.elem == target_slice.elem
                && (!target_slice.mutable || src_slice.mutable)
            {
                let src_local = match op {
                    Operand::Copy(p) | Operand::Move(p) if p.projections.is_empty() => p.local,
                    other => {
                        let tmp = self.alloc_temp(src_ty);
                        self.emit(Statement::Assign(Place::new(tmp), Rvalue::Use(other)));
                        tmp
                    }
                };
                let mut ptr_field = Place::new(src_local);
                ptr_field.projections.push(Projection::Field(0));
                let mut len_field = Place::new(src_local);
                len_field.projections.push(Projection::Field(1));
                let cast_ptr = self.alloc_temp(target_slice.ptr_ty);
                self.emit(Statement::Assign(
                    Place::new(cast_ptr),
                    Rvalue::Cast(Operand::Copy(ptr_field), target_slice.ptr_ty),
                ));
                let dst = self.alloc_temp(target_ty);
                self.emit(Statement::Assign(
                    Place::new(dst),
                    Rvalue::Aggregate(
                        target_ty,
                        vec![
                            Operand::Copy(Place::new(cast_ptr)),
                            Operand::Copy(len_field),
                        ],
                    ),
                ));
                return Ok(Operand::Copy(Place::new(dst)));
            }
        }

        // Widening coercion between `error` types (`E_src` -> `E_dst` when `E_src` is a subset of `E_dst`)
        if self.compiler.errors.contains_key(&src_ty)
            && self.compiler.errors.contains_key(&target_ty)
        {
            return self.widen_error_operand(op, src_ty, target_ty);
        }

        // Coercions into `E_dst!T_dst` (`Result` type)
        if let Some(&dst_res) = self.compiler.results.get(&target_ty) {
            if let Some(&src_res) = self.compiler.results.get(&src_ty)
                && src_res.ok_ty == dst_res.ok_ty
            {
                let u8_ty = self.compiler.intern_type(Type::Int {
                    signed: false,
                    bits: 8,
                });
                let src_local = self.alloc_temp(src_ty);
                self.emit(Statement::Assign(Place::new(src_local), Rvalue::Use(op)));
                let discr_local = self.alloc_temp(u8_ty);
                self.emit(Statement::Assign(
                    Place::new(discr_local),
                    Rvalue::Discriminant(Place::new(src_local)),
                ));
                let dst_local = self.alloc_temp(target_ty);
                let ok_bb = self.new_block();
                let err_bb = self.new_block();
                let join_bb = self.new_block();
                self.terminate(Terminator::SwitchInt {
                    discr: Operand::Copy(Place::new(discr_local)),
                    targets: vec![(0, ok_bb)],
                    otherwise: err_bb,
                });

                self.cur_block = ok_bb;
                let mut ok_place = Place::new(src_local);
                ok_place.projections.push(Projection::Variant(0));
                let ok_op = if self.is_copy_type(src_res.ok_ty) {
                    Operand::Copy(ok_place)
                } else {
                    Operand::Move(ok_place)
                };
                self.emit(Statement::Assign(
                    Place::new(dst_local),
                    Rvalue::Union {
                        ty: target_ty,
                        variant: 0,
                        payload: ok_op,
                    },
                ));
                self.terminate(Terminator::Goto { target: join_bb });

                self.cur_block = err_bb;
                let mut err_place = Place::new(src_local);
                err_place.projections.push(Projection::Variant(1));
                let err_op = if self.is_copy_type(src_res.err_ty) {
                    Operand::Copy(err_place)
                } else {
                    Operand::Move(err_place)
                };
                let widened_err =
                    self.widen_error_operand(err_op, src_res.err_ty, dst_res.err_ty)?;
                self.emit(Statement::Assign(
                    Place::new(dst_local),
                    Rvalue::Union {
                        ty: target_ty,
                        variant: 1,
                        payload: widened_err,
                    },
                ));
                self.terminate(Terminator::Goto { target: join_bb });

                self.cur_block = join_bb;
                let res_op = if self.is_copy_type(target_ty) {
                    Operand::Copy(Place::new(dst_local))
                } else {
                    Operand::Move(Place::new(dst_local))
                };
                return Ok(res_op);
            }
            if self.compiler.errors.contains_key(&src_ty)
                && !self.compiler.errors.contains_key(&dst_res.ok_ty)
            {
                let widened_err = self.widen_error_operand(op, src_ty, dst_res.err_ty)?;
                let dst_local = self.alloc_temp(target_ty);
                self.emit(Statement::Assign(
                    Place::new(dst_local),
                    Rvalue::Union {
                        ty: target_ty,
                        variant: 1,
                        payload: widened_err,
                    },
                ));
                let res_op = if self.is_copy_type(target_ty) {
                    Operand::Copy(Place::new(dst_local))
                } else {
                    Operand::Move(Place::new(dst_local))
                };
                return Ok(res_op);
            }
            let ok_op = self.coerce_operand(op, src_ty, dst_res.ok_ty)?;
            let dst_local = self.alloc_temp(target_ty);
            self.emit(Statement::Assign(
                Place::new(dst_local),
                Rvalue::Union {
                    ty: target_ty,
                    variant: 0,
                    payload: ok_op,
                },
            ));
            let res_op = if self.is_copy_type(target_ty) {
                Operand::Copy(Place::new(dst_local))
            } else {
                Operand::Move(Place::new(dst_local))
            };
            return Ok(res_op);
        }

        // Coerce `T` into `?T` (`union u8 { void, T }`)
        if !self.compiler.results.contains_key(&target_ty)
            && !self.compiler.errors.contains_key(&target_ty)
            && !self.compiler.unions.contains_key(&target_ty)
            && let Type::Union { variants, .. } = &self.compiler.program.types[target_ty.0 as usize]
            && variants.len() == 2
            && matches!(
                self.compiler.program.types[variants[0].0 as usize],
                Type::Void
            )
        {
            let inner_ty = variants[1];
            if src_ty == inner_ty && self.compiler.raw_ptrs.contains_key(&inner_ty) {
                let usize_ty = self.compiler.intern_type(Type::Int {
                    signed: false,
                    bits: 64,
                });
                let ptr_tmp = self.alloc_temp(inner_ty);
                self.emit(Statement::Assign(Place::new(ptr_tmp), Rvalue::Use(op)));
                let addr_tmp = self.alloc_temp(usize_ty);
                self.emit(Statement::Assign(
                    Place::new(addr_tmp),
                    Rvalue::Cast(Operand::Copy(Place::new(ptr_tmp)), usize_ty),
                ));
                let tmp = self.alloc_temp(target_ty);
                let null_bb = self.new_block();
                let some_bb = self.new_block();
                let join_bb = self.new_block();
                self.terminate(Terminator::SwitchInt {
                    discr: Operand::Copy(Place::new(addr_tmp)),
                    targets: vec![(0, null_bb)],
                    otherwise: some_bb,
                });
                self.cur_block = null_bb;
                self.emit(Statement::Assign(
                    Place::new(tmp),
                    Rvalue::Union {
                        ty: target_ty,
                        variant: 0,
                        payload: Operand::Const(ConstValue::Void),
                    },
                ));
                self.terminate(Terminator::Goto { target: join_bb });

                self.cur_block = some_bb;
                self.emit(Statement::Assign(
                    Place::new(tmp),
                    Rvalue::Union {
                        ty: target_ty,
                        variant: 1,
                        payload: Operand::Copy(Place::new(ptr_tmp)),
                    },
                ));
                self.terminate(Terminator::Goto { target: join_bb });

                self.cur_block = join_bb;
                return Ok(Operand::Move(Place::new(tmp)));
            }
            if src_ty == inner_ty {
                let tmp = self.alloc_temp(target_ty);
                self.emit(Statement::Assign(
                    Place::new(tmp),
                    Rvalue::Union {
                        ty: target_ty,
                        variant: 1,
                        payload: op,
                    },
                ));
                return Ok(Operand::Move(Place::new(tmp)));
            }
            if self.compiler.raw_ptrs.contains_key(&inner_ty)
                && matches!(
                    self.compiler.program.types[src_ty.0 as usize],
                    Type::Ptr { .. }
                )
            {
                let coerced_ptr = self.coerce_operand(op, src_ty, inner_ty)?;
                let tmp = self.alloc_temp(target_ty);
                self.emit(Statement::Assign(
                    Place::new(tmp),
                    Rvalue::Union {
                        ty: target_ty,
                        variant: 1,
                        payload: coerced_ptr,
                    },
                ));
                return Ok(Operand::Move(Place::new(tmp)));
            }
        }

        // Pattern type constant or subset widening
        if let Type::Pattern { base, .. } = self.compiler.program.types[target_ty.0 as usize]
            && src_ty == base
        {
            if let Operand::Const(ConstValue::I64(n)) = &op {
                self.verify_pattern_const(target_ty, *n)?;
            }
            let src_place_op = if matches!(op, Operand::Const(_)) {
                let src_tmp = self.alloc_temp(src_ty);
                self.emit(Statement::Assign(Place::new(src_tmp), Rvalue::Use(op)));
                Operand::Copy(Place::new(src_tmp))
            } else {
                op
            };
            let tmp = self.alloc_temp(target_ty);
            self.emit(Statement::Assign(
                Place::new(tmp),
                Rvalue::Cast(src_place_op, target_ty),
            ));
            return Ok(Operand::Copy(Place::new(tmp)));
        }

        if let Type::Pattern { base, .. } = self.compiler.program.types[src_ty.0 as usize]
            && target_ty == base
        {
            let src_place_op = if matches!(op, Operand::Const(_)) {
                let src_tmp = self.alloc_temp(src_ty);
                self.emit(Statement::Assign(Place::new(src_tmp), Rvalue::Use(op)));
                Operand::Copy(Place::new(src_tmp))
            } else {
                op
            };
            let tmp = self.alloc_temp(target_ty);
            self.emit(Statement::Assign(
                Place::new(tmp),
                Rvalue::Cast(src_place_op, target_ty),
            ));
            return Ok(Operand::Copy(Place::new(tmp)));
        }

        // Opaque newtype coercion (`UserId` <-> `u64` inside `def_module`; rejected outside `def_module`)
        if let Some(nt) = self.compiler.opaque_newtypes.get(&target_ty).cloned() {
            if nt.def_module == self.mod_path && src_ty == nt.underlying {
                if matches!(op, Operand::Const(_)) {
                    return Ok(op);
                }
                let tmp = self.alloc_temp(target_ty);
                self.emit(Statement::Assign(
                    Place::new(tmp),
                    Rvalue::Cast(op, target_ty),
                ));
                return Ok(if self.is_copy_type(target_ty) {
                    Operand::Copy(Place::new(tmp))
                } else {
                    Operand::Move(Place::new(tmp))
                });
            }
            return Err(format!(
                "Type mismatch: '{}' is an opaque newtype outside module '{}' and cannot be implicitly converted from '{}'; use a constructor or explicit 'as {}' cast",
                self.compiler.type_display_name(target_ty),
                nt.def_module,
                self.compiler.type_display_name(src_ty),
                self.compiler.type_display_name(target_ty)
            ));
        }
        if let Some(nt) = self.compiler.opaque_newtypes.get(&src_ty).cloned() {
            if nt.def_module == self.mod_path && target_ty == nt.underlying {
                if matches!(op, Operand::Const(_)) {
                    return Ok(op);
                }
                let tmp = self.alloc_temp(target_ty);
                self.emit(Statement::Assign(
                    Place::new(tmp),
                    Rvalue::Cast(op, target_ty),
                ));
                return Ok(if self.is_copy_type(target_ty) {
                    Operand::Copy(Place::new(tmp))
                } else {
                    Operand::Move(Place::new(tmp))
                });
            }
            return Err(format!(
                "Type mismatch: '{}' is an opaque newtype outside module '{}' and cannot be implicitly converted to '{}'; use an explicit 'as {}' cast",
                self.compiler.type_display_name(src_ty),
                nt.def_module,
                self.compiler.type_display_name(target_ty),
                self.compiler.type_display_name(target_ty)
            ));
        }

        if !matches!(
            self.compiler.program.types[src_ty.0 as usize],
            Type::Never
        ) {
            if self.compiler.c_ints.contains_key(&src_ty)
                || self.compiler.c_ints.contains_key(&target_ty)
            {
                return Err(format!(
                    "Type mismatch: cannot implicitly convert '{}' to '{}'; use an explicit 'as {}' cast",
                    self.compiler.type_display_name(src_ty),
                    self.compiler.type_display_name(target_ty),
                    self.compiler.type_display_name(target_ty)
                ));
            }
            if matches!(
                self.compiler.program.types[src_ty.0 as usize],
                Type::Ptr { .. }
            ) && matches!(
                self.compiler.program.types[target_ty.0 as usize],
                Type::Ptr { .. }
            ) {
                return Err(format!(
                    "Type mismatch: cannot implicitly convert '{}' to '{}'",
                    self.compiler.type_display_name(src_ty),
                    self.compiler.type_display_name(target_ty)
                ));
            }
        }

        Ok(op)
    }

    fn widen_error_operand(
        &mut self,
        op: Operand,
        src_err_ty: TypeId,
        dst_err_ty: TypeId,
    ) -> Result<Operand, String> {
        if src_err_ty == dst_err_ty {
            return Ok(op);
        }
        let Some(src_err) = self.compiler.errors.get(&src_err_ty).cloned() else {
            return Err(format!("Type {src_err_ty} is not an `error` type"));
        };
        let Some(dst_err) = self.compiler.errors.get(&dst_err_ty).cloned() else {
            return Err(format!("Type {dst_err_ty} is not an `error` type"));
        };
        let mut mapping: Vec<(usize, usize, TypeId)> = Vec::with_capacity(src_err.leaves.len());
        for (src_idx, src_leaf) in src_err.leaves.iter().enumerate() {
            let Some((dst_idx, dst_leaf)) = dst_err
                .leaves
                .iter()
                .enumerate()
                .find(|(_, dl)| dl.key == src_leaf.key)
            else {
                return Err(format!(
                    "Error type '{}' is not a subset of '{}': missing variant '{}::{}'",
                    src_err.name, dst_err.name, src_leaf.key.error_name, src_leaf.key.variant_name
                ));
            };
            if dst_leaf.payload_ty != src_leaf.payload_ty {
                return Err(format!(
                    "Error variant '{}::{}' has conflicting payload types in '{}' and '{}'",
                    src_leaf.key.error_name, src_leaf.key.variant_name, src_err.name, dst_err.name
                ));
            }
            mapping.push((src_idx, dst_idx, src_leaf.payload_ty));
        }

        let tag_ty = self.compiler.intern_type(Type::Int {
            signed: false,
            bits: 32,
        });
        let src_local = self.alloc_temp(src_err_ty);
        self.emit(Statement::Assign(Place::new(src_local), Rvalue::Use(op)));
        let discr_local = self.alloc_temp(tag_ty);
        self.emit(Statement::Assign(
            Place::new(discr_local),
            Rvalue::Discriminant(Place::new(src_local)),
        ));
        let dst_local = self.alloc_temp(dst_err_ty);
        let join_bb = self.new_block();
        let unreach_bb = self.new_block();
        self.blocks[unreach_bb.0 as usize].terminator = Terminator::Unreachable;
        self.terminated[unreach_bb.0 as usize] = true;

        let mut targets = Vec::with_capacity(mapping.len());
        let mut branch_bbs = Vec::with_capacity(mapping.len());
        for &(src_idx, dst_idx, p_ty) in &mapping {
            let bb = self.new_block();
            targets.push((src_idx as i128, bb));
            branch_bbs.push((src_idx, dst_idx, p_ty, bb));
        }
        self.terminate(Terminator::SwitchInt {
            discr: Operand::Copy(Place::new(discr_local)),
            targets,
            otherwise: unreach_bb,
        });

        for (src_idx, dst_idx, p_ty, bb) in branch_bbs {
            self.cur_block = bb;
            let payload_op = if matches!(self.compiler.program.types[p_ty.0 as usize], Type::Void) {
                Operand::Const(ConstValue::Void)
            } else {
                let mut p_place = Place::new(src_local);
                p_place
                    .projections
                    .push(Projection::Variant(src_idx as u32));
                if self.is_copy_type(p_ty) {
                    Operand::Copy(p_place)
                } else {
                    Operand::Move(p_place)
                }
            };
            self.emit(Statement::Assign(
                Place::new(dst_local),
                Rvalue::Union {
                    ty: dst_err_ty,
                    variant: dst_idx as u32,
                    payload: payload_op,
                },
            ));
            self.terminate(Terminator::Goto { target: join_bb });
        }

        self.cur_block = join_bb;
        let res_op = if self.is_copy_type(dst_err_ty) {
            Operand::Copy(Place::new(dst_local))
        } else {
            Operand::Move(Place::new(dst_local))
        };
        Ok(res_op)
    }

    fn lower_stmt(&mut self, stmt: &Stmt) -> Result<(), String> {
        match stmt {
            Stmt::Let {
                name, ty, init, ..
            } => {
                let expected_ty = if let Some(te) = ty {
                    let resolved = self.compiler.resolve_type_expr(
                        &self.mod_path,
                        self.owner_ty,
                        &self.comptime_env,
                        te,
                    )?;
                    if let Some(tr) = self.compiler.traits.get(&resolved) {
                        return Err(format!(
                            "Trait '{}' is an unsized meta-type constraint and cannot be bound by value in 'let {}'; use '&{}' or '&mut {}'",
                            tr.name, name, tr.name, tr.name
                        ));
                    }
                    if self.compiler.is_opaque_type(resolved) {
                        return Err(format!(
                            "Unsized type '{}' cannot be bound by value in 'let {}'; use '*const {0}', '*mut {0}', '&{0}', or '&mut {0}'",
                            self.compiler.type_display_name(resolved),
                            name
                        ));
                    }
                    Some(resolved)
                } else {
                    None
                };
                self.last_call_opaque_bound = None;
                let (init_op, inferred_ty) = self.lower_expr(init, expected_ty)?;
                let mut call_opaque_bound = self.last_call_opaque_bound.take();
                if call_opaque_bound.is_none() {
                    if let Expr::Path(p) = init
                        && p.len() == 1
                    {
                        call_opaque_bound = self.lookup_var_opaque_bound(&p[0]);
                    } else if let Expr::Move(inner) = init
                        && let Expr::Path(p) = inner.as_ref()
                        && p.len() == 1
                    {
                        call_opaque_bound = self.lookup_var_opaque_bound(&p[0]);
                    }
                }
                if let Some(ref ob) = call_opaque_bound
                    && let Some(exp_ty) = expected_ty
                {
                    return Err(format!(
                        "Cannot bind existential 'opaque {:?}' return value to explicit concrete type '{}' in 'let {}'; omit the type annotation or borrow via '&Trait'",
                        ob.bound_expr,
                        self.compiler.type_display_name(exp_ty),
                        name
                    ));
                }
                if self.is_terminated() {
                    return Ok(());
                }
                let var_ty = expected_ty.unwrap_or(inferred_ty);
                let coerced_op = if inferred_ty == var_ty
                    && !matches!(
                        self.compiler.program.types[var_ty.0 as usize],
                        Type::Pattern { .. }
                    ) {
                    init_op
                } else {
                    self.coerce_operand(init_op, inferred_ty, var_ty)?
                };
                let local = self.alloc_temp(var_ty);
                self.emit(Statement::StorageLive(local));
                self.emit(Statement::Assign(
                    Place::new(local),
                    Rvalue::Use(coerced_op),
                ));
                self.scopes.last_mut().unwrap().push(ScopeVar {
                    name: name.clone(),
                    local,
                    ty: var_ty,
                    opaque_bound: call_opaque_bound,
                });
                Ok(())
            }
            Stmt::Assign { target, op, value } => {
                if let Expr::Field { base, field } = target {
                    let (mut base_place, mut base_ty) = self.lower_place(base, true)?;
                    if let Type::Ptr { pointee, .. } =
                        self.compiler.program.types[base_ty.0 as usize]
                    {
                        base_place.projections.push(Projection::Deref);
                        base_ty = pointee;
                    }
                    if let Some(comp) = self.compiler.composites.get(&base_ty).cloned()
                        && let Ok((f_idx, _)) = self.check_field_access(base_ty, field)
                        && let Some(&rel_kind) = comp.rel_fields.get(&f_idx)
                    {
                        if op.is_some() {
                            return Err(format!(
                                "Cannot use compound assignment on '&rel' field '{}.{}'",
                                comp.name, field
                            ));
                        }
                        if self.place_traverses_immutable_ptr(&base_place) {
                            return Err(format!(
                                "Cannot assign to '&rel' field '{}.{}' through an immutable '&Self' reference",
                                comp.name, field
                            ));
                        }
                        let mut dest_field_place = base_place.clone();
                        dest_field_place.projections.push(Projection::Field(f_idx));
                        return self.assign_rel_field(
                            &comp.name,
                            field,
                            &base_place,
                            dest_field_place,
                            rel_kind,
                            value,
                        );
                    }
                }
                let (place, target_ty) = self.lower_place(target, true)?;
                if let Some(binop) = op {
                    if let Type::Ptr { pointee, .. } =
                        self.compiler.program.types[target_ty.0 as usize]
                        && self.compiler.is_opaque_type(pointee)
                        && matches!(
                            binop,
                            BinOp::Add | BinOp::AddWrap | BinOp::Sub | BinOp::SubWrap
                        )
                    {
                        return Err(format!(
                            "Cannot perform element-scaled pointer arithmetic on '{}'; cast to '*const u8' or '*mut u8' for byte offsets",
                            self.compiler.type_display_name(target_ty)
                        ));
                    }
                    let (rhs_op, rhs_ty) = self.lower_expr(value, Some(target_ty))?;
                    if let Some(nt) = self.compiler.opaque_newtypes.get(&target_ty)
                        && nt.def_module != self.mod_path
                    {
                        return Err(format!(
                            "Cannot perform operator '{}=' directly on opaque newtype '{}' outside module '{}'",
                            binop, nt.name, nt.def_module
                        ));
                    }
                    if !matches!(
                        self.compiler.program.types[target_ty.0 as usize],
                        Type::Ptr { .. }
                    ) && rhs_ty != target_ty
                        && (self.compiler.c_ints.contains_key(&target_ty)
                            || self.compiler.c_ints.contains_key(&rhs_ty))
                    {
                        return Err(format!(
                            "Type mismatch in compound assignment '{}=': cannot mix '{}' and '{}' without an explicit 'as' cast",
                            binop,
                            self.compiler.type_display_name(target_ty),
                            self.compiler.type_display_name(rhs_ty)
                        ));
                    }
                    let cur_op = Operand::Copy(place.clone());
                    self.emit(Statement::Assign(
                        place,
                        Rvalue::BinaryOp(*binop, cur_op, rhs_op),
                    ));
                } else {
                    let (val_op, val_ty) = self.lower_expr(value, Some(target_ty))?;
                    let coerced = self.coerce_operand(val_op, val_ty, target_ty)?;
                    if place.projections.is_empty() && !self.is_copy_type(target_ty) {
                        let next_bb = self.new_block();
                        self.terminate(Terminator::Drop {
                            place: place.clone(),
                            target: next_bb,
                        });
                        self.cur_block = next_bb;
                    }
                    self.emit(Statement::Assign(place, Rvalue::Use(coerced)));
                }
                Ok(())
            }
            Stmt::If {
                cond,
                then_block,
                else_block,
            } => {
                let (cond_op, _) = self.lower_expr(cond, None)?;
                let then_bb = self.new_block();
                let else_bb = self.new_block();
                self.terminate(Terminator::SwitchInt {
                    discr: cond_op,
                    targets: vec![(1, then_bb)],
                    otherwise: else_bb,
                });

                self.cur_block = then_bb;
                self.lower_scoped_block(then_block)?;
                let then_end_bb = self.cur_block;
                let then_open = !self.is_terminated();

                self.cur_block = else_bb;
                if let Some(eb) = else_block {
                    self.lower_scoped_block(eb)?;
                }
                let else_end_bb = self.cur_block;
                let else_open = !self.is_terminated();

                if then_open || else_open {
                    let join_bb = self.new_block();
                    if then_open {
                        self.blocks[then_end_bb.0 as usize].terminator =
                            Terminator::Goto { target: join_bb };
                    }
                    if else_open {
                        self.blocks[else_end_bb.0 as usize].terminator =
                            Terminator::Goto { target: join_bb };
                    }
                    self.cur_block = join_bb;
                }
                Ok(())
            }
            Stmt::IfLet {
                var_name,
                opt_expr,
                then_block,
                else_block,
            } => {
                let (opt_op, opt_ty) = self.lower_expr(opt_expr, None)?;
                let Type::Union { tag, variants } =
                    self.compiler.program.types[opt_ty.0 as usize].clone()
                else {
                    return Err("`if let` requires an optional `?T` expression".to_string());
                };
                let payload_ty = variants[1];
                let opt_local = self.alloc_temp(opt_ty);
                self.emit(Statement::Assign(
                    Place::new(opt_local),
                    Rvalue::Use(opt_op),
                ));
                let discr_local = self.alloc_temp(tag);
                self.emit(Statement::Assign(
                    Place::new(discr_local),
                    Rvalue::Discriminant(Place::new(opt_local)),
                ));

                let then_bb = self.new_block();
                let else_bb = self.new_block();
                self.terminate(Terminator::SwitchInt {
                    discr: Operand::Copy(Place::new(discr_local)),
                    targets: vec![(1, then_bb)],
                    otherwise: else_bb,
                });

                self.cur_block = then_bb;
                self.scopes.push(Vec::new());
                let var_local = self.alloc_temp(payload_ty);
                self.emit(Statement::StorageLive(var_local));
                let mut payload_place = Place::new(opt_local);
                payload_place.projections.push(Projection::Variant(1));
                let payload_op = if self.is_copy_type(payload_ty) {
                    Operand::Copy(payload_place)
                } else {
                    Operand::Move(payload_place)
                };
                self.emit(Statement::Assign(
                    Place::new(var_local),
                    Rvalue::Use(payload_op),
                ));
                self.scopes.last_mut().unwrap().push(ScopeVar {
                    name: var_name.clone(),
                    local: var_local,
                    ty: payload_ty,
                    opaque_bound: None,
                });
                self.lower_block_stmts(then_block)?;
                if !self.is_terminated() {
                    self.cleanup_top_scope();
                }
                let then_end_bb = self.cur_block;
                let then_open = !self.is_terminated();
                self.scopes.pop();

                self.cur_block = else_bb;
                if let Some(eb) = else_block {
                    self.lower_scoped_block(eb)?;
                }
                let else_end_bb = self.cur_block;
                let else_open = !self.is_terminated();

                if then_open || else_open {
                    let join_bb = self.new_block();
                    if then_open {
                        self.blocks[then_end_bb.0 as usize].terminator =
                            Terminator::Goto { target: join_bb };
                    }
                    if else_open {
                        self.blocks[else_end_bb.0 as usize].terminator =
                            Terminator::Goto { target: join_bb };
                    }
                    self.cur_block = join_bb;
                }
                Ok(())
            }
            Stmt::While { cond, body } => {
                let cond_bb = self.new_block();
                let body_bb = self.new_block();
                let exit_bb = self.new_block();
                self.terminate(Terminator::Goto { target: cond_bb });

                self.cur_block = cond_bb;
                let (cond_op, _) = self.lower_expr(cond, None)?;
                self.terminate(Terminator::SwitchInt {
                    discr: cond_op,
                    targets: vec![(1, body_bb)],
                    otherwise: exit_bb,
                });

                self.cur_block = body_bb;
                self.lower_scoped_block(body)?;
                if !self.is_terminated() {
                    self.terminate(Terminator::Goto { target: cond_bb });
                }

                self.cur_block = exit_bb;
                Ok(())
            }
            Stmt::Match { scrutinee, arms } => {
                let void_ty = self.compiler.intern_type(Type::Void);
                let _ = self.lower_match(scrutinee, arms, Some(void_ty), true)?;
                Ok(())
            }
            Stmt::Return(opt_expr) => {
                if let TypeExpr::OpaqueTrait(bound_expr) = self.decl.ret_ty.clone() {
                    let Some(expr) = opt_expr else {
                        return Err(format!(
                            "Function '{}' with '-> opaque ...' return type must return a value",
                            self.decl.name
                        ));
                    };
                    let (op, expr_ty) = self.lower_expr(expr, self.inferred_opaque_ret)?;
                    if self.is_terminated() {
                        return Ok(());
                    }
                    let ret_ty = self.check_opaque_ret_expr(&bound_expr, expr_ty)?;
                    let coerced = self.coerce_operand(op, expr_ty, ret_ty)?;
                    self.emit(Statement::Assign(
                        Place::new(LocalId(0)),
                        Rvalue::Use(coerced),
                    ));
                    self.cleanup_all_scopes();
                    self.terminate(Terminator::Return);
                    return Ok(());
                }
                let ret_ty = self.locals[0];
                if let Some(expr) = opt_expr {
                    let (op, expr_ty) = self.lower_expr(expr, Some(ret_ty))?;
                    if self.is_terminated() {
                        return Ok(());
                    }
                    let coerced = self.coerce_operand(op, expr_ty, ret_ty)?;
                    self.emit(Statement::Assign(
                        Place::new(LocalId(0)),
                        Rvalue::Use(coerced),
                    ));
                } else if let Some(&res_info) = self.compiler.results.get(&ret_ty)
                    && matches!(
                        self.compiler.program.types[res_info.ok_ty.0 as usize],
                        Type::Void
                    )
                {
                    self.emit(Statement::Assign(
                        Place::new(LocalId(0)),
                        Rvalue::Union {
                            ty: ret_ty,
                            variant: 0,
                            payload: Operand::Const(ConstValue::Void),
                        },
                    ));
                } else {
                    self.emit(Statement::Assign(
                        Place::new(LocalId(0)),
                        Rvalue::Use(Operand::Const(ConstValue::Void)),
                    ));
                }
                self.cleanup_all_scopes();
                self.terminate(Terminator::Return);
                Ok(())
            }
            Stmt::Unsafe(blk) => self.lower_scoped_block(blk),
            Stmt::Expr(expr) => {
                let (op, ty) = self.lower_expr(expr, None)?;
                if !self.is_terminated()
                    && !self.is_copy_type(ty)
                    && let Operand::Move(place) = op
                {
                    let next_bb = self.new_block();
                    self.terminate(Terminator::Drop {
                        place,
                        target: next_bb,
                    });
                    self.cur_block = next_bb;
                }
                Ok(())
            }
        }
    }

    fn is_copy_type(&self, ty_id: TypeId) -> bool {
        self.compiler.is_copy_type(ty_id)
    }

    fn check_field_access(
        &self,
        comp_ty: TypeId,
        field_name: &str,
    ) -> Result<(u32, TypeId), String> {
        let Some(comp) = self.compiler.composites.get(&comp_ty) else {
            return Err(format!("Type {comp_ty} has no named fields"));
        };
        let Some((idx, (_, f_ty, f_vis, _))) = comp
            .fields
            .iter()
            .enumerate()
            .find(|(_, (n, _, _, _))| n == field_name)
        else {
            return Err(format!(
                "Type '{}' has no field '{}'",
                comp.name, field_name
            ));
        };
        if comp.is_struct
            && *f_vis == Visibility::Private
            && self.owner_ty != Some(comp_ty)
        {
            return Err(format!(
                "Cannot access private field '{}' of struct '{}' outside its 'struct {{ ... }}' block",
                field_name, comp.name
            ));
        }
        if *f_vis == Visibility::Private && comp.def_module != self.mod_path {
            return Err(format!(
                "Field '{}' of '{}' is private to module '{}'",
                field_name, comp.name, comp.def_module
            ));
        }
        Ok((idx as u32, *f_ty))
    }

    #[allow(clippy::only_used_in_recursion)]
    fn lower_place(&mut self, expr: &Expr, for_write_or_move: bool) -> Result<(Place, TypeId), String> {
        match expr {
            Expr::Path(p) if p.len() == 1 => {
                if let Some((local, ty)) = self.lookup_var(&p[0]) {
                    return Ok((Place::new(local), ty));
                }
                if let Some((cap_place, ty)) = self.lookup_capture(&p[0]) {
                    return Ok((cap_place, ty));
                }
                Err(format!("Undefined local variable '{}'", p[0]))
            }
            Expr::Deref(inner) => {
                let (mut place, ty) = self.lower_place(inner, for_write_or_move)?;
                let Type::Ptr { pointee, .. } = self.compiler.program.types[ty.0 as usize] else {
                    return Err(format!("Cannot dereference non-pointer type {ty}"));
                };
                if self.compiler.is_opaque_type(pointee) {
                    return Err(format!(
                        "Cannot dereference pointer of type '{}'; 'opaque' has unknown size and layout (cast to a concrete pointer type first)",
                        self.compiler.type_display_name(ty)
                    ));
                }
                place.projections.push(Projection::Deref);
                Ok((place, pointee))
            }
            Expr::Field { base, field } => {
                if let Some(root_var) = Self::root_var_of_place_expr(base)
                    && let Some(ob) = self.lookup_var_opaque_bound(root_var)
                {
                    return Err(format!(
                        "Cannot access concrete field '{}' on existential 'opaque {:?}' value '{}'; only methods from its trait bound are accessible",
                        field, ob.bound_expr, root_var
                    ));
                }
                let (mut place, mut base_ty) = self.lower_place(base, for_write_or_move)?;
                // Auto-deref reference/pointer on field access (`self.x`)
                if let Type::Ptr { pointee, .. } = self.compiler.program.types[base_ty.0 as usize] {
                    place.projections.push(Projection::Deref);
                    base_ty = pointee;
                }
                if field == "len" {
                    let usize_ty = self.compiler.intern_type(Type::Int {
                        signed: false,
                        bits: 64,
                    });
                    if self.compiler.slices.contains_key(&base_ty) {
                        place.projections.push(Projection::Field(1));
                        return Ok((place, usize_ty));
                    }
                    if let Type::Array { len, .. } | Type::Simd { len, .. } =
                        self.compiler.program.types[base_ty.0 as usize]
                    {
                        let len_tmp = self.alloc_temp(usize_ty);
                        self.emit(Statement::Assign(
                            Place::new(len_tmp),
                            Rvalue::Use(Operand::Const(ConstValue::I64(len as i128))),
                        ));
                        return Ok((Place::new(len_tmp), usize_ty));
                    }
                }
                let (f_idx, f_ty) = self.check_field_access(base_ty, field)?;
                if let Some(comp) = self.compiler.composites.get(&base_ty)
                    && let Some(&rel_kind) = comp.rel_fields.get(&f_idx)
                {
                    let comp_name = comp.name.clone();
                    return self.resolve_rel_field_access(
                        &comp_name,
                        field,
                        place,
                        f_idx,
                        base_ty,
                        rel_kind,
                        for_write_or_move,
                    );
                }
                place.projections.push(Projection::Field(f_idx));
                Ok((place, f_ty))
            }
            Expr::TupleIndex { base, index } => {
                let (mut place, mut base_ty) = self.lower_place(base, for_write_or_move)?;
                if let Type::Ptr { pointee, .. } = self.compiler.program.types[base_ty.0 as usize] {
                    place.projections.push(Projection::Deref);
                    base_ty = pointee;
                }
                let Type::Struct(fields) = &self.compiler.program.types[base_ty.0 as usize] else {
                    return Err(format!("Cannot tuple-index non-tuple type {base_ty}"));
                };
                let &elem_ty = fields
                    .get(*index as usize)
                    .ok_or_else(|| format!("Tuple index .{index} out of bounds"))?;
                place.projections.push(Projection::Field(*index));
                Ok((place, elem_ty))
            }
            Expr::Index { base, index } => {
                let (mut place, mut base_ty) = self.lower_place(base, for_write_or_move)?;
                if let Type::Ptr { pointee, .. } = self.compiler.program.types[base_ty.0 as usize] {
                    place.projections.push(Projection::Deref);
                    base_ty = pointee;
                }
                let elem_ty = if let Some(&slice_info) = self.compiler.slices.get(&base_ty) {
                    place.projections.push(Projection::Field(0));
                    place.projections.push(Projection::Deref);
                    slice_info.elem
                } else {
                    match self.compiler.program.types[base_ty.0 as usize] {
                        Type::Array { elem, .. } | Type::Simd { elem, .. } => elem,
                        _ => {
                            return Err(format!(
                                "Cannot index non-array/slice/simd type {base_ty}"
                            ));
                        }
                    }
                };
                let u64_ty = self.compiler.intern_type(Type::Int {
                    signed: false,
                    bits: 64,
                });
                let (idx_op, _) = self.lower_expr(index, Some(u64_ty))?;
                let idx_local = self.alloc_temp(u64_ty);
                self.emit(Statement::Assign(
                    Place::new(idx_local),
                    Rvalue::Use(idx_op),
                ));
                place.projections.push(Projection::Index(idx_local));
                Ok((place, elem_ty))
            }
            _ => {
                // Materialize rvalue into a temporary local place
                let (op, ty) = self.lower_expr(expr, None)?;
                let tmp = self.alloc_temp(ty);
                self.emit(Statement::Assign(Place::new(tmp), Rvalue::Use(op)));
                Ok((Place::new(tmp), ty))
            }
        }
    }

    fn lower_expr(
        &mut self,
        expr: &Expr,
        expected_ty: Option<TypeId>,
    ) -> Result<(Operand, TypeId), String> {
        match expr {
            Expr::Int(n) => {
                let unwrapped_expected = expected_ty.map(|mut t| {
                    if let Some(&res_info) = self.compiler.results.get(&t) {
                        t = res_info.ok_ty;
                    }
                    if !self.compiler.results.contains_key(&t)
                        && !self.compiler.errors.contains_key(&t)
                        && !self.compiler.unions.contains_key(&t)
                        && let Type::Union { variants, .. } =
                            &self.compiler.program.types[t.0 as usize]
                        && variants.len() == 2
                        && matches!(
                            self.compiler.program.types[variants[0].0 as usize],
                            Type::Void
                        )
                    {
                        variants[1]
                    } else {
                        t
                    }
                });
                if let Some(t) = unwrapped_expected
                    && let Some(nt) = self.compiler.opaque_newtypes.get(&t)
                    && nt.def_module != self.mod_path
                {
                    return Err(format!(
                        "Cannot initialize opaque newtype '{}' directly from an integer literal outside module '{}'; use a constructor or explicit 'as {}' cast",
                        nt.name, nt.def_module, nt.name
                    ));
                }
                if let Some(t) = unwrapped_expected
                    && matches!(
                        self.compiler.program.types[t.0 as usize],
                        Type::F32 | Type::F64
                    )
                {
                    return Ok((
                        Operand::Const(ConstValue::F64((*n as f64).to_bits())),
                        t,
                    ));
                }
                let ty = match unwrapped_expected {
                    Some(t)
                        if matches!(
                            self.compiler.program.types[t.0 as usize],
                            Type::Int { .. } | Type::Pattern { .. }
                        ) =>
                    {
                        if let Type::Pattern { base, .. } =
                            self.compiler.program.types[t.0 as usize]
                        {
                            self.verify_pattern_const(t, *n)?;
                            base
                        } else {
                            t
                        }
                    }
                    _ => self.compiler.intern_type(Type::Int {
                        signed: true,
                        bits: 64,
                    }),
                };
                Ok((Operand::Const(ConstValue::I64(*n)), ty))
            }
            Expr::Float(bits) => {
                if let Some(t) = expected_ty
                    && let Some(nt) = self.compiler.opaque_newtypes.get(&t)
                    && nt.def_module != self.mod_path
                {
                    return Err(format!(
                        "Cannot initialize opaque newtype '{}' directly from a float literal outside module '{}'; use a constructor or explicit 'as {}' cast",
                        nt.name, nt.def_module, nt.name
                    ));
                }
                let ty = match expected_ty {
                    Some(t)
                        if matches!(
                            self.compiler.program.types[t.0 as usize],
                            Type::F32 | Type::F64
                        ) =>
                    {
                        t
                    }
                    _ => self.compiler.intern_type(Type::F64),
                };
                Ok((Operand::Const(ConstValue::F64(*bits)), ty))
            }
            Expr::Bool(b) => {
                let ty = self.compiler.intern_type(Type::Bool);
                Ok((Operand::Const(ConstValue::Bool(*b)), ty))
            }
            Expr::Rune(ch) => {
                let ty = self.compiler.intern_type(Type::Rune);
                let tmp = self.alloc_temp(ty);
                self.emit(Statement::Assign(
                    Place::new(tmp),
                    Rvalue::Use(Operand::Const(ConstValue::I64(u32::from(*ch) as i128))),
                ));
                Ok((Operand::Copy(Place::new(tmp)), ty))
            }
            Expr::Str(s) => {
                let u8_ty = self.compiler.intern_type(Type::Int {
                    signed: false,
                    bits: 8,
                });
                let ptr_ty = self.compiler.intern_type(Type::Ptr {
                    mutable: false,
                    pointee: u8_ty,
                });
                Ok((Operand::Const(ConstValue::Str(s.clone())), ptr_ty))
            }
            Expr::Null => {
                let opt_ty = expected_ty
                    .ok_or_else(|| "`null` requires a known optional `?T` type context".to_string())?;
                let tmp = self.alloc_temp(opt_ty);
                self.emit(Statement::Assign(
                    Place::new(tmp),
                    Rvalue::Union {
                        ty: opt_ty,
                        variant: 0,
                        payload: Operand::Const(ConstValue::Void),
                    },
                ));
                Ok((Operand::Move(Place::new(tmp)), opt_ty))
            }
            Expr::TypeVal(te) => {
                let t_id = self.compiler.resolve_type_expr(
                    &self.mod_path,
                    self.owner_ty,
                    &self.comptime_env,
                    te,
                )?;
                let meta_ty = self.compiler.intern_type(Type::MetaType);
                Ok((Operand::Const(ConstValue::Type(t_id)), meta_ty))
            }
            Expr::Path(p) => {
                if p.len() == 1 {
                    if let Some((local, ty)) = self.lookup_var(&p[0]) {
                        let op = if self.is_copy_type(ty) {
                            Operand::Copy(Place::new(local))
                        } else {
                            Operand::Move(Place::new(local))
                        };
                        return Ok((op, ty));
                    }
                    if let Some((cap_place, ty)) = self.lookup_capture(&p[0]) {
                        let op = if self.is_copy_type(ty) {
                            Operand::Copy(cap_place)
                        } else {
                            Operand::Move(cap_place)
                        };
                        return Ok((op, ty));
                    }
                    if let Some(ComptimeVal::Int(n)) = self.comptime_env.get(&p[0]).cloned() {
                        let ty = expected_ty.unwrap_or_else(|| {
                            self.compiler.intern_type(Type::Int {
                                signed: true,
                                bits: 64,
                            })
                        });
                        return Ok((Operand::Const(ConstValue::I64(n)), ty));
                    }
                } else if p.len() >= 2 {
                    let type_prefix = &p[..p.len() - 1];
                    let vname = p.last().unwrap();
                    let enum_ty_opt = if type_prefix.len() == 1
                        && let Some(ComptimeVal::Type(t_id)) = self.comptime_env.get(&type_prefix[0])
                    {
                        Some(*t_id)
                    } else if let Ok(ResolvedItem::Type(tmod, tname)) =
                        self.compiler.resolve_path(&self.mod_path, type_prefix)
                    {
                        Some(self.compiler.resolve_named_type(&tmod, &tname)?)
                    } else {
                        None
                    };
                    if let Some(enum_ty) = enum_ty_opt {
                        if let Some((_, variants)) = self.compiler.enums.get(&enum_ty)
                            && let Some((_, val)) = variants.iter().find(|(vn, _)| vn == vname)
                        {
                            return Ok((Operand::Const(ConstValue::I64(*val)), enum_ty));
                        }
                        if let Some(err_info) = self.compiler.errors.get(&enum_ty).cloned() {
                            let found = err_info
                                .leaves
                                .iter()
                                .enumerate()
                                .find(|(_, l)| {
                                    l.key.error_name == err_info.name
                                        && l.key.variant_name == *vname
                                })
                                .or_else(|| {
                                    err_info
                                        .leaves
                                        .iter()
                                        .enumerate()
                                        .find(|(_, l)| l.key.variant_name == *vname)
                                });
                            if let Some((v_idx, leaf)) = found {
                                if !matches!(
                                    self.compiler.program.types[leaf.payload_ty.0 as usize],
                                    Type::Void
                                ) {
                                    return Err(format!(
                                        "Error variant '{}::{}' carries a payload and must be constructed with arguments",
                                        err_info.name, vname
                                    ));
                                }
                                let tmp = self.alloc_temp(enum_ty);
                                self.emit(Statement::Assign(
                                    Place::new(tmp),
                                    Rvalue::Union {
                                        ty: enum_ty,
                                        variant: v_idx as u32,
                                        payload: Operand::Const(ConstValue::Void),
                                    },
                                ));
                                let op = if self.is_copy_type(enum_ty) {
                                    Operand::Copy(Place::new(tmp))
                                } else {
                                    Operand::Move(Place::new(tmp))
                                };
                                return Ok((op, enum_ty));
                            }
                        }
                        if let Some(union_info) = self.compiler.unions.get(&enum_ty).cloned()
                            && let Some((v_idx, (_, payload_ty))) = union_info
                                .variants
                                .iter()
                                .enumerate()
                                .find(|(_, (vn, _))| vn == vname)
                        {
                            if !matches!(
                                self.compiler.program.types[payload_ty.0 as usize],
                                Type::Void
                            ) {
                                return Err(format!(
                                    "Union variant '{}::{}' carries a payload and must be constructed with arguments",
                                    union_info.name, vname
                                ));
                            }
                            let tmp = self.alloc_temp(enum_ty);
                            self.emit(Statement::Assign(
                                Place::new(tmp),
                                Rvalue::Union {
                                    ty: enum_ty,
                                    variant: v_idx as u32,
                                    payload: Operand::Const(ConstValue::Void),
                                },
                            ));
                            let op = if self.is_copy_type(enum_ty) {
                                Operand::Copy(Place::new(tmp))
                            } else {
                                Operand::Move(Place::new(tmp))
                            };
                            return Ok((op, enum_ty));
                        }
                    }
                }
                if let Ok(ResolvedItem::Func(fmod, fname)) =
                    self.compiler.resolve_path(&self.mod_path, p)
                {
                    let fn_id = self.compiler.get_or_instantiate_func(&fmod, &fname, &[])?;
                    let (args, ret) = self.compiler.func_sigs[&fn_id].clone();
                    let fn_ptr_ty = self.compiler.intern_type(Type::FnPtr { args, ret });
                    return Ok((Operand::Const(ConstValue::Func(fn_id)), fn_ptr_ty));
                }
                Err(format!("Cannot resolve value path '{}'", p.join("::")))
            }
            Expr::Move(inner) => {
                if let Expr::Field { base, .. } = inner.as_ref() {
                    let (_, mut base_ty) = self.lower_place(base, true)?;
                    if let Type::Ptr { pointee, .. } =
                        self.compiler.program.types[base_ty.0 as usize]
                    {
                        base_ty = pointee;
                    }
                    if let Some(comp) = self.compiler.composites.get(&base_ty)
                        && comp.is_struct
                    {
                        return Err(format!(
                            "Cannot partially move field out of struct '{}'; only 'record' and 'tuple' allow partial moves",
                            comp.name
                        ));
                    }
                }
                let (place, ty) = self.lower_place(inner, true)?;
                if self.place_traverses_safe_ref(&place) {
                    return Err(format!(
                        "Cannot move out of dereferenced safe reference '{}'",
                        place
                    ));
                }
                Ok((Operand::Move(place), ty))
            }
            Expr::Field { .. } | Expr::TupleIndex { .. } | Expr::Index { .. } | Expr::Deref(_) => {
                let want_mut = matches!(expr, Expr::Field { .. })
                    && expected_ty.is_some_and(|t| {
                        matches!(
                            self.compiler.program.types[t.0 as usize],
                            Type::Ptr { mutable: true, .. }
                        ) || self
                            .compiler
                            .slices
                            .get(&t)
                            .is_some_and(|info| info.mutable)
                            || self
                                .compiler
                                .trait_objs
                                .get(&t)
                                .is_some_and(|info| info.mutable)
                    });
                let (place, ty) = self.lower_place(expr, want_mut)?;
                let op = if self.is_copy_type(ty) {
                    Operand::Copy(place)
                } else if let Some(exp_ty) = expected_ty
                    && let (
                        Type::Ptr {
                            mutable: true,
                            pointee: src_pt,
                        },
                        Type::Ptr {
                            mutable: dst_mut,
                            pointee: dst_pt,
                        },
                    ) = (
                        self.compiler.program.types[ty.0 as usize].clone(),
                        self.compiler.program.types[exp_ty.0 as usize].clone(),
                    )
                    && (src_pt == dst_pt || self.compiler.is_universal_opaque_type(dst_pt))
                    && !self.compiler.raw_ptrs.contains_key(&ty)
                    && !self.compiler.raw_ptrs.contains_key(&exp_ty)
                {
                    if dst_mut && self.place_traverses_immutable_ptr(&place) {
                        return Err(format!(
                            "Cannot mutably reborrow '{}' through an immutable reference",
                            place
                        ));
                    }
                    let mut deref_p = place;
                    deref_p.projections.push(Projection::Deref);
                    let tmp = self.alloc_temp(exp_ty);
                    self.emit(Statement::Assign(
                        Place::new(tmp),
                        Rvalue::Ref {
                            mutable: dst_mut,
                            place: deref_p,
                        },
                    ));
                    return Ok((Operand::Move(Place::new(tmp)), exp_ty));
                } else {
                    if self.place_traverses_safe_ref(&place) {
                        return Err(format!(
                            "Cannot move out of dereferenced safe reference '{}'",
                            place
                        ));
                    }
                    Operand::Move(place)
                };
                Ok((op, ty))
            }
            Expr::RelRef(_) => Err(
                "'&rel' expressions are only permitted when initializing or assigning a '&rel' struct field"
                    .to_string(),
            ),
            Expr::Ref { mutable, expr: inner } => {
                if let Expr::Slice { base, start, end } = inner.as_ref() {
                    return self.lower_slice(base, start, end, Some(*mutable), expected_ty);
                }
                let (place, inner_ty) = self.lower_place(inner, *mutable)?;
                let ref_ty = self.compiler.intern_type(Type::Ptr {
                    mutable: *mutable,
                    pointee: inner_ty,
                });
                let tmp = self.alloc_temp(ref_ty);
                self.emit(Statement::Assign(
                    Place::new(tmp),
                    Rvalue::Ref {
                        mutable: *mutable,
                        place,
                    },
                ));
                Ok((Operand::Copy(Place::new(tmp)), ref_ty))
            }
            Expr::Slice { base, start, end } => {
                self.lower_slice(base, start, end, None, expected_ty)
            }
            Expr::Unary { op, expr: inner } => {
                let (inner_op, ty) = self.lower_expr(inner, expected_ty)?;
                let tmp = self.alloc_temp(ty);
                self.emit(Statement::Assign(
                    Place::new(tmp),
                    Rvalue::UnaryOp(*op, inner_op),
                ));
                Ok((Operand::Copy(Place::new(tmp)), ty))
            }
            Expr::Binary { op, lhs, rhs } => {
                let (l_op, l_ty, r_op, r_ty) = if expected_ty.is_none()
                    && matches!(lhs.as_ref(), Expr::Int(_) | Expr::Float(_))
                    && !matches!(rhs.as_ref(), Expr::Int(_) | Expr::Float(_))
                {
                    let (r_op, r_ty) = self.lower_expr(rhs, None)?;
                    let (l_op, l_ty) = self.lower_expr(lhs, Some(r_ty))?;
                    (l_op, l_ty, r_op, r_ty)
                } else {
                    let (l_op, l_ty) = self.lower_expr(lhs, expected_ty)?;
                    let rhs_exp = if matches!(
                        self.compiler.program.types[l_ty.0 as usize],
                        Type::Ptr { .. }
                    ) {
                        Some(self.compiler.intern_type(Type::Int {
                            signed: true,
                            bits: 64,
                        }))
                    } else {
                        Some(l_ty)
                    };
                    let (r_op, r_ty) = self.lower_expr(rhs, rhs_exp)?;
                    (l_op, l_ty, r_op, r_ty)
                };
                if let Type::Ptr { pointee, .. } = self.compiler.program.types[l_ty.0 as usize] {
                    if self.compiler.is_opaque_type(pointee)
                        && matches!(op, BinOp::Add | BinOp::AddWrap | BinOp::Sub | BinOp::SubWrap)
                    {
                        return Err(format!(
                            "Cannot perform element-scaled pointer arithmetic on '{}'; cast to '*const u8' or '*mut u8' for byte offsets",
                            self.compiler.type_display_name(l_ty)
                        ));
                    }
                } else {
                    if let Some(nt) = self.compiler.opaque_newtypes.get(&l_ty)
                        && nt.def_module != self.mod_path
                    {
                        return Err(format!(
                            "Cannot perform binary operator '{}' directly on opaque newtype '{}' outside module '{}'",
                            op, nt.name, nt.def_module
                        ));
                    }
                    if let Some(nt) = self.compiler.opaque_newtypes.get(&r_ty)
                        && nt.def_module != self.mod_path
                    {
                        return Err(format!(
                            "Cannot perform binary operator '{}' directly on opaque newtype '{}' outside module '{}'",
                            op, nt.name, nt.def_module
                        ));
                    }
                    if r_ty != l_ty
                        && (self.compiler.c_ints.contains_key(&l_ty)
                            || self.compiler.c_ints.contains_key(&r_ty))
                    {
                        return Err(format!(
                            "Type mismatch in binary operation '{}': cannot mix '{}' and '{}' without an explicit 'as' cast",
                            op,
                            self.compiler.type_display_name(l_ty),
                            self.compiler.type_display_name(r_ty)
                        ));
                    }
                    if r_ty != l_ty
                        && let (Some(l_nt), Some(r_nt)) = (
                            self.compiler.opaque_newtypes.get(&l_ty),
                            self.compiler.opaque_newtypes.get(&r_ty),
                        )
                    {
                        return Err(format!(
                            "Type mismatch in binary operation '{}': cannot mix distinct opaque newtypes '{}' and '{}'",
                            op, l_nt.name, r_nt.name
                        ));
                    }
                }
                let res_ty = match op {
                    BinOp::Eq
                    | BinOp::Ne
                    | BinOp::Lt
                    | BinOp::Le
                    | BinOp::Gt
                    | BinOp::Ge => self.compiler.intern_type(Type::Bool),
                    _ => l_ty,
                };
                let tmp = self.alloc_temp(res_ty);
                self.emit(Statement::Assign(
                    Place::new(tmp),
                    Rvalue::BinaryOp(*op, l_op, r_op),
                ));
                Ok((Operand::Copy(Place::new(tmp)), res_ty))
            }
            Expr::LogicalAnd(lhs, rhs) => {
                let bool_ty = self.compiler.intern_type(Type::Bool);
                let res_local = self.alloc_temp(bool_ty);
                let (l_op, _) = self.lower_expr(lhs, Some(bool_ty))?;
                let rhs_bb = self.new_block();
                let short_bb = self.new_block();
                let join_bb = self.new_block();
                self.terminate(Terminator::SwitchInt {
                    discr: l_op,
                    targets: vec![(1, rhs_bb)],
                    otherwise: short_bb,
                });

                self.cur_block = short_bb;
                self.emit(Statement::Assign(
                    Place::new(res_local),
                    Rvalue::Use(Operand::Const(ConstValue::Bool(false))),
                ));
                self.terminate(Terminator::Goto { target: join_bb });

                self.cur_block = rhs_bb;
                let (r_op, _) = self.lower_expr(rhs, Some(bool_ty))?;
                self.emit(Statement::Assign(Place::new(res_local), Rvalue::Use(r_op)));
                self.terminate(Terminator::Goto { target: join_bb });

                self.cur_block = join_bb;
                Ok((Operand::Copy(Place::new(res_local)), bool_ty))
            }
            Expr::LogicalOr(lhs, rhs) => {
                let bool_ty = self.compiler.intern_type(Type::Bool);
                let res_local = self.alloc_temp(bool_ty);
                let (l_op, _) = self.lower_expr(lhs, Some(bool_ty))?;
                let rhs_bb = self.new_block();
                let short_bb = self.new_block();
                let join_bb = self.new_block();
                self.terminate(Terminator::SwitchInt {
                    discr: l_op,
                    targets: vec![(1, short_bb)],
                    otherwise: rhs_bb,
                });

                self.cur_block = short_bb;
                self.emit(Statement::Assign(
                    Place::new(res_local),
                    Rvalue::Use(Operand::Const(ConstValue::Bool(true))),
                ));
                self.terminate(Terminator::Goto { target: join_bb });

                self.cur_block = rhs_bb;
                let (r_op, _) = self.lower_expr(rhs, Some(bool_ty))?;
                self.emit(Statement::Assign(Place::new(res_local), Rvalue::Use(r_op)));
                self.terminate(Terminator::Goto { target: join_bb });

                self.cur_block = join_bb;
                Ok((Operand::Copy(Place::new(res_local)), bool_ty))
            }
            Expr::Cast { expr: inner, ty } => {
                let target_ty = self.compiler.resolve_type_expr(
                    &self.mod_path,
                    self.owner_ty,
                    &self.comptime_env,
                    ty,
                )?;
                if self.compiler.is_opaque_type(target_ty) {
                    return Err(
                        "Cannot cast a value to unsized type 'opaque' by value; cast to '*const opaque' or '*mut opaque' instead"
                            .to_string(),
                    );
                }
                let (op, src_ty) = self.lower_expr(inner, None)?;
                if let Operand::Const(ConstValue::I64(n)) = &op {
                    self.verify_pattern_const(target_ty, *n)?;
                }
                let src_place_op = if matches!(op, Operand::Const(_)) {
                    let src_tmp = self.alloc_temp(src_ty);
                    self.emit(Statement::Assign(Place::new(src_tmp), Rvalue::Use(op)));
                    Operand::Copy(Place::new(src_tmp))
                } else {
                    op
                };
                let dst_tmp = self.alloc_temp(target_ty);
                self.emit(Statement::Assign(
                    Place::new(dst_tmp),
                    Rvalue::Cast(src_place_op, target_ty),
                ));
                Ok((Operand::Copy(Place::new(dst_tmp)), target_ty))
            }
            Expr::OrElse { opt, fallback } => {
                let (opt_op, opt_ty) = self.lower_expr(opt, None)?;
                let Type::Union { tag, variants } =
                    self.compiler.program.types[opt_ty.0 as usize].clone()
                else {
                    return Err("`orelse` requires an optional `?T` left-hand side".to_string());
                };
                let payload_ty = variants[1];
                let opt_local = self.alloc_temp(opt_ty);
                self.emit(Statement::Assign(
                    Place::new(opt_local),
                    Rvalue::Use(opt_op),
                ));
                let discr_local = self.alloc_temp(tag);
                self.emit(Statement::Assign(
                    Place::new(discr_local),
                    Rvalue::Discriminant(Place::new(opt_local)),
                ));

                let res_local = self.alloc_temp(payload_ty);
                let some_bb = self.new_block();
                let none_bb = self.new_block();
                let join_bb = self.new_block();
                self.terminate(Terminator::SwitchInt {
                    discr: Operand::Copy(Place::new(discr_local)),
                    targets: vec![(1, some_bb)],
                    otherwise: none_bb,
                });

                self.cur_block = some_bb;
                let mut payload_place = Place::new(opt_local);
                payload_place.projections.push(Projection::Variant(1));
                let p_op = if self.is_copy_type(payload_ty) {
                    Operand::Copy(payload_place)
                } else {
                    Operand::Move(payload_place)
                };
                self.emit(Statement::Assign(Place::new(res_local), Rvalue::Use(p_op)));
                self.terminate(Terminator::Goto { target: join_bb });

                self.cur_block = none_bb;
                let (fb_op, fb_ty) = self.lower_expr(fallback, Some(payload_ty))?;
                if !self.is_terminated() {
                    let coerced = self.coerce_operand(fb_op, fb_ty, payload_ty)?;
                    self.emit(Statement::Assign(Place::new(res_local), Rvalue::Use(coerced)));
                    self.terminate(Terminator::Goto { target: join_bb });
                }

                self.cur_block = join_bb;
                Ok((Operand::Move(Place::new(res_local)), payload_ty))
            }
            Expr::Try(inner) => {
                let (res_op, res_ty) = self.lower_expr(inner, None)?;
                let Some(&src_res) = self.compiler.results.get(&res_ty) else {
                    return Err("`try` requires a fallible `E!T` result expression".to_string());
                };
                let ret_ty = self.locals[0];
                let Some(&fn_res) = self.compiler.results.get(&ret_ty) else {
                    return Err(format!(
                        "`try` can only be used inside a function returning a fallible `E!T` result (function '{}' returns {})",
                        self.decl.name,
                        self.compiler.program.types[ret_ty.0 as usize]
                    ));
                };
                let u8_ty = self.compiler.intern_type(Type::Int {
                    signed: false,
                    bits: 8,
                });
                let res_local = self.alloc_temp(res_ty);
                self.emit(Statement::Assign(Place::new(res_local), Rvalue::Use(res_op)));
                let discr_local = self.alloc_temp(u8_ty);
                self.emit(Statement::Assign(
                    Place::new(discr_local),
                    Rvalue::Discriminant(Place::new(res_local)),
                ));

                let ok_bb = self.new_block();
                let err_bb = self.new_block();
                self.terminate(Terminator::SwitchInt {
                    discr: Operand::Copy(Place::new(discr_local)),
                    targets: vec![(0, ok_bb)],
                    otherwise: err_bb,
                });

                self.cur_block = err_bb;
                let mut err_place = Place::new(res_local);
                err_place.projections.push(Projection::Variant(1));
                let err_op = if self.is_copy_type(src_res.err_ty) {
                    Operand::Copy(err_place)
                } else {
                    Operand::Move(err_place)
                };
                let widened_err =
                    self.widen_error_operand(err_op, src_res.err_ty, fn_res.err_ty)?;
                self.emit(Statement::Assign(
                    Place::new(LocalId(0)),
                    Rvalue::Union {
                        ty: ret_ty,
                        variant: 1,
                        payload: widened_err,
                    },
                ));
                self.cleanup_all_scopes();
                self.terminate(Terminator::Return);

                self.cur_block = ok_bb;
                if matches!(
                    self.compiler.program.types[src_res.ok_ty.0 as usize],
                    Type::Void
                ) {
                    return Ok((Operand::Const(ConstValue::Void), src_res.ok_ty));
                }
                let mut ok_place = Place::new(res_local);
                ok_place.projections.push(Projection::Variant(0));
                let ok_op = if self.is_copy_type(src_res.ok_ty) {
                    Operand::Copy(ok_place)
                } else {
                    Operand::Move(ok_place)
                };
                let ok_local = self.alloc_temp(src_res.ok_ty);
                self.emit(Statement::Assign(Place::new(ok_local), Rvalue::Use(ok_op)));
                let out_op = if self.is_copy_type(src_res.ok_ty) {
                    Operand::Copy(Place::new(ok_local))
                } else {
                    Operand::Move(Place::new(ok_local))
                };
                Ok((out_op, src_res.ok_ty))
            }
            Expr::Catch {
                expr: inner,
                err_binding,
                fallback,
            } => {
                let (res_op, res_ty) = self.lower_expr(inner, None)?;
                let Some(&src_res) = self.compiler.results.get(&res_ty) else {
                    return Err("`catch` requires a fallible `E!T` left-hand side".to_string());
                };
                let ok_ty = src_res.ok_ty;
                let err_ty = src_res.err_ty;
                let u8_ty = self.compiler.intern_type(Type::Int {
                    signed: false,
                    bits: 8,
                });
                let res_local = self.alloc_temp(res_ty);
                self.emit(Statement::Assign(Place::new(res_local), Rvalue::Use(res_op)));
                let discr_local = self.alloc_temp(u8_ty);
                self.emit(Statement::Assign(
                    Place::new(discr_local),
                    Rvalue::Discriminant(Place::new(res_local)),
                ));

                let out_local = self.alloc_temp(ok_ty);
                let ok_bb = self.new_block();
                let err_bb = self.new_block();
                let join_bb = self.new_block();
                self.terminate(Terminator::SwitchInt {
                    discr: Operand::Copy(Place::new(discr_local)),
                    targets: vec![(0, ok_bb)],
                    otherwise: err_bb,
                });

                self.cur_block = ok_bb;
                if matches!(self.compiler.program.types[ok_ty.0 as usize], Type::Void) {
                    self.emit(Statement::Assign(
                        Place::new(out_local),
                        Rvalue::Use(Operand::Const(ConstValue::Void)),
                    ));
                } else {
                    let mut ok_place = Place::new(res_local);
                    ok_place.projections.push(Projection::Variant(0));
                    let ok_op = if self.is_copy_type(ok_ty) {
                        Operand::Copy(ok_place)
                    } else {
                        Operand::Move(ok_place)
                    };
                    self.emit(Statement::Assign(Place::new(out_local), Rvalue::Use(ok_op)));
                }
                self.terminate(Terminator::Goto { target: join_bb });

                self.cur_block = err_bb;
                self.scopes.push(Vec::new());
                if let Some(b_name) = err_binding
                    && b_name != "_"
                {
                    let err_var = self.alloc_temp(err_ty);
                    self.emit(Statement::StorageLive(err_var));
                    let mut err_place = Place::new(res_local);
                    err_place.projections.push(Projection::Variant(1));
                    let err_op = if self.is_copy_type(err_ty) {
                        Operand::Copy(err_place)
                    } else {
                        Operand::Move(err_place)
                    };
                    self.emit(Statement::Assign(Place::new(err_var), Rvalue::Use(err_op)));
                    self.scopes.last_mut().unwrap().push(ScopeVar {
                        name: b_name.clone(),
                        local: err_var,
                        ty: err_ty,
                        opaque_bound: None,
                    });
                }
                let (fb_op, fb_ty) = self.lower_expr(fallback, Some(ok_ty))?;
                if !self.is_terminated() {
                    let coerced = self.coerce_operand(fb_op, fb_ty, ok_ty)?;
                    self.emit(Statement::Assign(
                        Place::new(out_local),
                        Rvalue::Use(coerced),
                    ));
                    self.cleanup_top_scope();
                    self.terminate(Terminator::Goto { target: join_bb });
                }
                self.scopes.pop();

                self.cur_block = join_bb;
                let out_op = if self.is_copy_type(ok_ty) {
                    Operand::Copy(Place::new(out_local))
                } else {
                    Operand::Move(Place::new(out_local))
                };
                Ok((out_op, ok_ty))
            }
            Expr::Match { scrutinee, arms } => {
                self.lower_match(scrutinee, arms, expected_ty, false)
            }
            Expr::Block(blk) => {
                let void_ty = self.compiler.intern_type(Type::Void);
                let never_ty = self.compiler.intern_type(Type::Never);
                if expected_ty != Some(void_ty)
                    && let Some(Stmt::Expr(tail_expr)) = blk.stmts.last()
                {
                    self.scopes.push(Vec::new());
                    for s in &blk.stmts[..blk.stmts.len() - 1] {
                        if self.is_terminated() {
                            break;
                        }
                        self.lower_stmt(s)?;
                    }
                    if self.is_terminated() {
                        self.scopes.pop();
                        return Ok((Operand::Const(ConstValue::Void), never_ty));
                    }
                    let (tail_op, tail_ty) = self.lower_expr(tail_expr, expected_ty)?;
                    if self.is_terminated() {
                        self.scopes.pop();
                        return Ok((Operand::Const(ConstValue::Void), never_ty));
                    }
                    if matches!(self.compiler.program.types[tail_ty.0 as usize], Type::Void) {
                        self.cleanup_top_scope();
                        self.scopes.pop();
                        return Ok((Operand::Const(ConstValue::Void), void_ty));
                    }
                    let res_local = self.alloc_temp(tail_ty);
                    self.emit(Statement::Assign(Place::new(res_local), Rvalue::Use(tail_op)));
                    self.cleanup_top_scope();
                    self.scopes.pop();
                    let out_op = if self.is_copy_type(tail_ty) {
                        Operand::Copy(Place::new(res_local))
                    } else {
                        Operand::Move(Place::new(res_local))
                    };
                    Ok((out_op, tail_ty))
                } else {
                    self.lower_scoped_block(blk)?;
                    if self.is_terminated() {
                        Ok((Operand::Const(ConstValue::Void), never_ty))
                    } else {
                        Ok((Operand::Const(ConstValue::Void), void_ty))
                    }
                }
            }
            Expr::TupleLit(elems) => {
                if let Some(t) = expected_ty
                    && let Type::Array { elem, len } = self.compiler.program.types[t.0 as usize]
                    && elems.len() == len as usize
                {
                    let mut ops = Vec::with_capacity(elems.len());
                    for e in elems {
                        let (op, ety) = self.lower_expr(e, Some(elem))?;
                        let coerced = self.coerce_operand(op, ety, elem)?;
                        ops.push(coerced);
                    }
                    let tmp = self.alloc_temp(t);
                    self.emit(Statement::Assign(
                        Place::new(tmp),
                        Rvalue::Aggregate(t, ops),
                    ));
                    let res_op = if self.is_copy_type(t) {
                        Operand::Copy(Place::new(tmp))
                    } else {
                        Operand::Move(Place::new(tmp))
                    };
                    return Ok((res_op, t));
                }
                let expected_fields = if let Some(t) = expected_ty
                    && let Type::Struct(ftys) = &self.compiler.program.types[t.0 as usize]
                {
                    Some(ftys.clone())
                } else {
                    None
                };
                let mut ops = Vec::with_capacity(elems.len());
                let mut tys = Vec::with_capacity(elems.len());
                for (i, e) in elems.iter().enumerate() {
                    let exp = expected_fields.as_ref().and_then(|v| v.get(i).copied());
                    let (op, ty) = self.lower_expr(e, exp)?;
                    ops.push(op);
                    tys.push(ty);
                }
                let tup_ty = self.compiler.intern_type(Type::Struct(tys));
                let tmp = self.alloc_temp(tup_ty);
                self.emit(Statement::Assign(
                    Place::new(tmp),
                    Rvalue::Aggregate(tup_ty, ops),
                ));
                Ok((Operand::Move(Place::new(tmp)), tup_ty))
            }
            Expr::SimdLit { ty, elems } => {
                let simd_ty = self.compiler.resolve_type_expr(
                    &self.mod_path,
                    self.owner_ty,
                    &self.comptime_env,
                    ty,
                )?;
                let elem = match self.compiler.program.types[simd_ty.0 as usize] {
                    Type::Simd { elem, .. } | Type::Array { elem, .. } => elem,
                    _ => {
                        return Err(format!(
                            "Expected SIMD or Array type in literal, got {simd_ty}"
                        ));
                    }
                };
                let mut ops = Vec::with_capacity(elems.len());
                for e in elems {
                    let (op, ety) = self.lower_expr(e, Some(elem))?;
                    let coerced = self.coerce_operand(op, ety, elem)?;
                    ops.push(coerced);
                }
                let tmp = self.alloc_temp(simd_ty);
                self.emit(Statement::Assign(
                    Place::new(tmp),
                    Rvalue::Aggregate(simd_ty, ops),
                ));
                let res_op = if self.is_copy_type(simd_ty) {
                    Operand::Copy(Place::new(tmp))
                } else {
                    Operand::Move(Place::new(tmp))
                };
                Ok((res_op, simd_ty))
            }
            Expr::StructLit { ty, fields } => {
                let mut wrap_union: Option<(TypeId, u32)> = None;
                let comp_ty = if let TypeExpr::Named(path) = ty
                    && path.len() >= 2
                    && self
                        .compiler
                        .resolve_path(&self.mod_path, path)
                        .is_err()
                {
                    let prefix = &path[..path.len() - 1];
                    let vname = path.last().unwrap();
                    let owner_ty = if prefix.len() == 1
                        && let Some(ComptimeVal::Type(t_id)) = self.comptime_env.get(&prefix[0])
                    {
                        *t_id
                    } else if let Ok(ResolvedItem::Type(tmod, tname)) =
                        self.compiler.resolve_path(&self.mod_path, prefix)
                    {
                        self.compiler.resolve_named_type(&tmod, &tname)?
                    } else {
                        return Err(format!("Cannot resolve type path '{}'", path.join("::")));
                    };
                    if let Some(err_info) = self.compiler.errors.get(&owner_ty).cloned() {
                        let Some((v_idx, leaf)) = err_info
                            .leaves
                            .iter()
                            .enumerate()
                            .find(|(_, l)| {
                                l.key.error_name == err_info.name && l.key.variant_name == *vname
                            })
                            .or_else(|| {
                                err_info
                                    .leaves
                                    .iter()
                                    .enumerate()
                                    .find(|(_, l)| l.key.variant_name == *vname)
                            })
                        else {
                            return Err(format!(
                                "Error '{}' has no variant '{}'",
                                err_info.name, vname
                            ));
                        };
                        wrap_union = Some((owner_ty, v_idx as u32));
                        leaf.payload_ty
                    } else if let Some(union_info) = self.compiler.unions.get(&owner_ty).cloned() {
                        let Some((v_idx, (_, payload_ty))) = union_info
                            .variants
                            .iter()
                            .enumerate()
                            .find(|(_, (vn, _))| vn == vname)
                        else {
                            return Err(format!(
                                "Union '{}' has no variant '{}'",
                                union_info.name, vname
                            ));
                        };
                        wrap_union = Some((owner_ty, v_idx as u32));
                        *payload_ty
                    } else {
                        return Err(format!("Cannot resolve type path '{}'", path.join("::")));
                    }
                } else {
                    self.compiler.resolve_type_expr(
                        &self.mod_path,
                        self.owner_ty,
                        &self.comptime_env,
                        ty,
                    )?
                };
                let Some(comp) = self.compiler.composites.get(&comp_ty).cloned() else {
                    return Err(format!("Cannot construct non-record/struct type {comp_ty}"));
                };
                // Enforce `struct` private field encapsulation on literal construction!
                for (f_name, _, f_vis, _) in &comp.fields {
                    if comp.is_struct
                        && *f_vis == Visibility::Private
                        && self.owner_ty != Some(comp_ty)
                    {
                        return Err(format!(
                            "Cannot construct struct '{}' with private field '{}' outside its 'struct {{ ... }}' block",
                            comp.name, f_name
                        ));
                    }
                }
                if !comp.rel_fields.is_empty() {
                    let mut initial_field_ops = Vec::with_capacity(comp.fields.len());
                    for (idx, (f_name, f_ty, _, f_default)) in comp.fields.iter().enumerate() {
                        if let Some(&rel_kind) = comp.rel_fields.get(&(idx as u32)) {
                            match rel_kind {
                                RelFieldKind::Elem(_) => {
                                    initial_field_ops.push(Operand::Const(ConstValue::I64(0)));
                                }
                                RelFieldKind::Slice(_) | RelFieldKind::Str => {
                                    let zero_rel = self.alloc_temp(*f_ty);
                                    self.emit(Statement::Assign(
                                        Place::new(zero_rel),
                                        Rvalue::Aggregate(
                                            *f_ty,
                                            vec![
                                                Operand::Const(ConstValue::I64(0)),
                                                Operand::Const(ConstValue::I64(0)),
                                            ],
                                        ),
                                    ));
                                    initial_field_ops.push(Operand::Copy(Place::new(zero_rel)));
                                }
                            }
                            continue;
                        }
                        if let Some((_, val_expr)) = fields.iter().find(|(n, _)| n == f_name) {
                            let (op, val_ty) = self.lower_expr(val_expr, Some(*f_ty))?;
                            let coerced = self.coerce_operand(op, val_ty, *f_ty)?;
                            initial_field_ops.push(coerced);
                        } else if let Some(def_expr) = f_default {
                            let (op, val_ty) = self.lower_expr(def_expr, Some(*f_ty))?;
                            let coerced = self.coerce_operand(op, val_ty, *f_ty)?;
                            initial_field_ops.push(coerced);
                        } else {
                            return Err(format!(
                                "Missing field '{}' in '{}' literal",
                                f_name, comp.name
                            ));
                        }
                    }
                    let tmp = self.alloc_temp(comp_ty);
                    self.emit(Statement::Assign(
                        Place::new(tmp),
                        Rvalue::Aggregate(comp_ty, initial_field_ops),
                    ));
                    // Bind `self` to `tmp` in a temporary scope so `&rel self.<field>` resolves to `tmp`!
                    self.scopes.push(vec![ScopeVar {
                        name: "self".to_string(),
                        local: tmp,
                        ty: comp_ty,
                        opaque_bound: None,
                    }]);
                    let base_place = Place::new(tmp);
                    let mut rel_res = Ok(());
                    for (idx, (f_name, _, _, f_default)) in comp.fields.iter().enumerate() {
                        let Some(&rel_kind) = comp.rel_fields.get(&(idx as u32)) else {
                            continue;
                        };
                        let val_expr =
                            if let Some((_, ve)) = fields.iter().find(|(n, _)| n == f_name) {
                                ve
                            } else if let Some(def_expr) = f_default {
                                def_expr
                            } else {
                                rel_res = Err(format!(
                                    "Missing field '{}' in '{}' literal",
                                    f_name, comp.name
                                ));
                                break;
                            };
                        let mut dest_field_place = Place::new(tmp);
                        dest_field_place.projections.push(Projection::Field(idx as u32));
                        if let Err(e) = self.assign_rel_field(
                            &comp.name,
                            f_name,
                            &base_place,
                            dest_field_place,
                            rel_kind,
                            val_expr,
                        ) {
                            rel_res = Err(e);
                            break;
                        }
                    }
                    self.scopes.pop();
                    rel_res?;
                    let res_op = if self.is_copy_type(comp_ty) {
                        Operand::Copy(Place::new(tmp))
                    } else {
                        Operand::Move(Place::new(tmp))
                    };
                    return Ok((res_op, comp_ty));
                }
                let mut field_ops = Vec::with_capacity(comp.fields.len());
                for (f_name, f_ty, _, f_default) in &comp.fields {
                    if let Some((_, val_expr)) = fields.iter().find(|(n, _)| n == f_name) {
                        let (op, val_ty) = self.lower_expr(val_expr, Some(*f_ty))?;
                        let coerced = self.coerce_operand(op, val_ty, *f_ty)?;
                        field_ops.push(coerced);
                    } else if let Some(def_expr) = f_default {
                        let (op, val_ty) = self.lower_expr(def_expr, Some(*f_ty))?;
                        let coerced = self.coerce_operand(op, val_ty, *f_ty)?;
                        field_ops.push(coerced);
                    } else {
                        return Err(format!(
                            "Missing field '{}' in '{}' literal",
                            f_name, comp.name
                        ));
                    }
                }
                let tmp = self.alloc_temp(comp_ty);
                self.emit(Statement::Assign(
                    Place::new(tmp),
                    Rvalue::Aggregate(comp_ty, field_ops),
                ));
                let res_op = if self.is_copy_type(comp_ty) {
                    Operand::Copy(Place::new(tmp))
                } else {
                    Operand::Move(Place::new(tmp))
                };
                if let Some((owner_ty, v_idx)) = wrap_union {
                    let u_tmp = self.alloc_temp(owner_ty);
                    self.emit(Statement::Assign(
                        Place::new(u_tmp),
                        Rvalue::Union {
                            ty: owner_ty,
                            variant: v_idx,
                            payload: res_op,
                        },
                    ));
                    let u_op = if self.is_copy_type(owner_ty) {
                        Operand::Copy(Place::new(u_tmp))
                    } else {
                        Operand::Move(Place::new(u_tmp))
                    };
                    return Ok((u_op, owner_ty));
                }
                Ok((res_op, comp_ty))
            }
            Expr::IntrinsicDefault(ty_expr) => {
                let ty_id = self.compiler.resolve_type_expr(
                    &self.mod_path,
                    self.owner_ty,
                    &self.comptime_env,
                    ty_expr,
                )?;
                self.lower_default_for_type(ty_id)
            }
            Expr::IntrinsicClone(inner) => {
                let (mut place, mut ty_id) = match inner.as_ref() {
                    Expr::Ref { expr, .. } => self.lower_place(expr, false)?,
                    _ => self.lower_place(inner, false)?,
                };
                if let Type::Ptr { pointee, .. } = self.compiler.program.types[ty_id.0 as usize]
                    && !self.compiler.raw_ptrs.contains_key(&ty_id)
                {
                    place.projections.push(Projection::Deref);
                    ty_id = pointee;
                }
                self.lower_clone_for_place(place, ty_id)
            }
            Expr::IntrinsicDrop(inner) => {
                let (place, _) = self.lower_place(inner, true)?;
                let drop_target = if let Type::Ptr { .. } =
                    self.compiler.program.types[self.place_type(&place).0 as usize]
                {
                    let mut deref_p = place;
                    deref_p.projections.push(Projection::Deref);
                    deref_p
                } else {
                    place
                };
                let target_ty = self.place_type(&drop_target);
                if self.compiler.is_linear_type(target_ty) {
                    let t_disp = self
                        .compiler
                        .composites
                        .get(&target_ty)
                        .map(|c| c.name.clone())
                        .unwrap_or_else(|| {
                            self.compiler.program.types[target_ty.0 as usize].to_string()
                        });
                    return Err(format!(
                        "Linear value '{}' of type '{}' cannot be dropped via '@drop'; call a consuming method instead",
                        drop_target, t_disp
                    ));
                }
                let next_bb = self.new_block();
                self.terminate(Terminator::Drop {
                    place: drop_target,
                    target: next_bb,
                });
                self.cur_block = next_bb;
                let void_ty = self.compiler.intern_type(Type::Void);
                Ok((Operand::Const(ConstValue::Void), void_ty))
            }
            Expr::IntrinsicFormat {
                formatter,
                value,
                spec,
            } => {
                let (fmt_op, _) = self.lower_expr(formatter, None)?;
                let fmt_ref_op = match fmt_op {
                    Operand::Copy(p) => Operand::Copy(p),
                    Operand::Move(p) => Operand::Copy(p),
                    other => other,
                };
                let (val_place, val_ty) = self.lower_place(value, false)?;
                let spec_str = spec.as_deref().unwrap_or("");
                self.emit_format_place(fmt_ref_op, val_place, val_ty, spec_str)?;
                let void_ty = self.compiler.intern_type(Type::Void);
                Ok((Operand::Const(ConstValue::Void), void_ty))
            }
            Expr::FormatStr(segments) => self.lower_format_str(segments),
            Expr::IntrinsicTrap => {
                self.terminate(Terminator::Unreachable);
                let never_ty = self.compiler.intern_type(Type::Never);
                Ok((Operand::Const(ConstValue::Void), never_ty))
            }
            Expr::Return(opt_expr) => {
                if let TypeExpr::OpaqueTrait(bound_expr) = self.decl.ret_ty.clone() {
                    if let Some(expr) = opt_expr {
                        let exp_ty = self.inferred_opaque_ret;
                        let (op, expr_ty) = self.lower_expr(expr, exp_ty)?;
                        if !self.is_terminated() {
                            let target_ty = self.check_opaque_ret_expr(&bound_expr, expr_ty)?;
                            let coerced = self.coerce_operand(op, expr_ty, target_ty)?;
                            self.emit(Statement::Assign(
                                Place::new(LocalId(0)),
                                Rvalue::Use(coerced),
                            ));
                        }
                    } else {
                        let void_ty = self.compiler.intern_type(Type::Void);
                        let _ = self.check_opaque_ret_expr(&bound_expr, void_ty)?;
                        self.emit(Statement::Assign(
                            Place::new(LocalId(0)),
                            Rvalue::Use(Operand::Const(ConstValue::Void)),
                        ));
                    }
                    if !self.is_terminated() {
                        self.cleanup_all_scopes();
                        self.terminate(Terminator::Return);
                    }
                    let never_ty = self.compiler.intern_type(Type::Never);
                    return Ok((Operand::Const(ConstValue::Void), never_ty));
                }
                let ret_ty = self.locals[0];
                if let Some(expr) = opt_expr {
                    let (op, expr_ty) = self.lower_expr(expr, Some(ret_ty))?;
                    if !self.is_terminated() {
                        let coerced = self.coerce_operand(op, expr_ty, ret_ty)?;
                        self.emit(Statement::Assign(
                            Place::new(LocalId(0)),
                            Rvalue::Use(coerced),
                        ));
                    }
                } else if let Some(&res_info) = self.compiler.results.get(&ret_ty)
                    && matches!(
                        self.compiler.program.types[res_info.ok_ty.0 as usize],
                        Type::Void
                    )
                {
                    self.emit(Statement::Assign(
                        Place::new(LocalId(0)),
                        Rvalue::Union {
                            ty: ret_ty,
                            variant: 0,
                            payload: Operand::Const(ConstValue::Void),
                        },
                    ));
                } else {
                    self.emit(Statement::Assign(
                        Place::new(LocalId(0)),
                        Rvalue::Use(Operand::Const(ConstValue::Void)),
                    ));
                }
                if !self.is_terminated() {
                    self.cleanup_all_scopes();
                    self.terminate(Terminator::Return);
                }
                let never_ty = self.compiler.intern_type(Type::Never);
                Ok((Operand::Const(ConstValue::Void), never_ty))
            }
            Expr::UnsafeBlock(blk) => {
                self.lower_scoped_block(blk)?;
                let void_ty = self.compiler.intern_type(Type::Void);
                Ok((Operand::Const(ConstValue::Void), void_ty))
            }
            Expr::Lambda {
                is_move,
                params,
                ret_ty,
                body,
            } => {
                let mut param_tys = Vec::with_capacity(params.len());
                let mut ast_params = Vec::with_capacity(params.len());
                let mut initial_bound = std::collections::HashSet::new();
                for (is_mut, pname, pty_expr) in params {
                    let pty = self.compiler.resolve_type_expr(
                        &self.mod_path,
                        self.owner_ty,
                        &self.comptime_env,
                        pty_expr,
                    )?;
                    param_tys.push(pty);
                    ast_params.push(crate::ast::Param {
                        is_comptime: false,
                        is_mut: *is_mut,
                        name: pname.clone(),
                        ty: pty_expr.clone(),
                    });
                    initial_bound.insert(pname.clone());
                }
                let ret_ty_id = self.compiler.resolve_type_expr(
                    &self.mod_path,
                    self.owner_ty,
                    &self.comptime_env,
                    ret_ty,
                )?;

                let mut captures: Vec<(String, bool)> = Vec::new();
                self.collect_captures_in_block(body, &initial_bound, &mut captures);

                if captures.is_empty() {
                    // Non-capturing lambda decays directly to a `fn(...) -> R` function pointer (`Type::FnPtr`).
                    let fn_id = self.compiler.reserve_function(
                        Visibility::Private,
                        None,
                        &param_tys,
                        ret_ty_id,
                    );
                    let decl = FuncDecl {
                        vis: Visibility::Private,
                        name: format!("<lambda_{}>", fn_id.0),
                        params: ast_params,
                        ret_ty: ret_ty.clone(),
                        borrows: None,
                        where_clauses: Vec::new(),
                        body: body.clone(),
                    };
                    self.compiler.pending_funcs.push(PendingFunc {
                        func_id: fn_id,
                        module_path: self.mod_path.clone(),
                        owner_ty: self.owner_ty,
                        decl,
                        comptime_env: self.comptime_env.clone(),
                        closure_captures: Vec::new(),
                    });
                    let fn_ptr_ty = self.compiler.intern_type(Type::FnPtr {
                        args: param_tys,
                        ret: ret_ty_id,
                    });
                    Ok((Operand::Const(ConstValue::Func(fn_id)), fn_ptr_ty))
                } else {
                    // Capturing closure: synthesize unique environment struct type & hidden `__env` parameter.
                    let env_mut = captures.iter().any(|(_, needs_mut)| *needs_mut);
                    let mut env_field_tys = Vec::with_capacity(captures.len());
                    let mut env_field_ops = Vec::with_capacity(captures.len());
                    let mut closure_captures = Vec::with_capacity(captures.len());

                    for (cap_name, needs_mut) in &captures {
                        let (outer_place, outer_ty) = self
                            .lookup_var(cap_name)
                            .map(|(l, t)| (Place::new(l), t))
                            .or_else(|| self.lookup_capture(cap_name))
                            .ok_or_else(|| format!("Undefined captured variable '{cap_name}'"))?;

                        if *is_move {
                            env_field_tys.push(outer_ty);
                            let op = if self.is_copy_type(outer_ty) {
                                Operand::Copy(outer_place)
                            } else {
                                Operand::Move(outer_place)
                            };
                            env_field_ops.push(op);
                            closure_captures.push((cap_name.clone(), outer_ty, false));
                        } else {
                            let ref_ty = self.compiler.intern_type(Type::Ptr {
                                mutable: *needs_mut,
                                pointee: outer_ty,
                            });
                            let ref_tmp = self.alloc_temp(ref_ty);
                            self.emit(Statement::Assign(
                                Place::new(ref_tmp),
                                Rvalue::Ref {
                                    mutable: *needs_mut,
                                    place: outer_place,
                                },
                            ));
                            env_field_tys.push(ref_ty);
                            env_field_ops.push(Operand::Copy(Place::new(ref_tmp)));
                            closure_captures.push((cap_name.clone(), outer_ty, true));
                        }
                    }

                    let closure_ty = self
                        .compiler
                        .alloc_distinct_type(Type::Struct(env_field_tys));
                    let env_by_val = *is_move && self.compiler.is_linear_type(closure_ty);
                    let env_param_ty = if env_by_val {
                        closure_ty
                    } else {
                        self.compiler.intern_type(Type::Ptr {
                            mutable: env_mut,
                            pointee: closure_ty,
                        })
                    };

                    let mut call_param_tys = Vec::with_capacity(param_tys.len() + 1);
                    call_param_tys.push(env_param_ty);
                    call_param_tys.extend_from_slice(&param_tys);

                    let call_fn_id = self.compiler.reserve_function(
                        Visibility::Private,
                        None,
                        &call_param_tys,
                        ret_ty_id,
                    );
                    self.compiler.closures.insert(
                        closure_ty,
                        ClosureInfo {
                            call_fn_id,
                            env_mut,
                            env_by_val,
                            param_tys,
                            ret_ty: ret_ty_id,
                        },
                    );

                    let decl = FuncDecl {
                        vis: Visibility::Private,
                        name: format!("<closure_{}>", call_fn_id.0),
                        params: ast_params,
                        ret_ty: ret_ty.clone(),
                        borrows: None,
                        where_clauses: Vec::new(),
                        body: body.clone(),
                    };
                    self.compiler.pending_funcs.push(PendingFunc {
                        func_id: call_fn_id,
                        module_path: self.mod_path.clone(),
                        owner_ty: self.owner_ty,
                        decl,
                        comptime_env: self.comptime_env.clone(),
                        closure_captures,
                    });

                    let env_tmp = self.alloc_temp(closure_ty);
                    self.emit(Statement::Assign(
                        Place::new(env_tmp),
                        Rvalue::Aggregate(closure_ty, env_field_ops),
                    ));
                    let res_op = if self.is_copy_type(closure_ty) {
                        Operand::Copy(Place::new(env_tmp))
                    } else {
                        Operand::Move(Place::new(env_tmp))
                    };
                    Ok((res_op, closure_ty))
                }
            }
            Expr::Call { callee, args } => self.lower_call(callee, args),
            Expr::MethodCall {
                receiver,
                method,
                args,
            } => self.lower_method_call(receiver, method, args),
        }
    }

    fn resolve_match_type_path(&mut self, path: &[String]) -> Option<TypeId> {
        if path.len() == 1
            && let Some(ComptimeVal::Type(t_id)) = self.comptime_env.get(&path[0])
        {
            return Some(*t_id);
        }
        if let Ok(ResolvedItem::Type(tmod, tname)) =
            self.compiler.resolve_path(&self.mod_path, path)
            && let Ok(t_id) = self.compiler.resolve_named_type(&tmod, &tname)
        {
            return Some(t_id);
        }
        None
    }

    fn lower_match(
        &mut self,
        scrutinee: &Expr,
        arms: &[(MatchPat, Expr)],
        expected_ty: Option<TypeId>,
        is_stmt: bool,
    ) -> Result<(Operand, TypeId), String> {
        let (scrut_op, raw_scrut_ty) = self.lower_expr(scrutinee, None)?;
        let raw_scrut_local = self.alloc_temp(raw_scrut_ty);
        self.emit(Statement::Assign(
            Place::new(raw_scrut_local),
            Rvalue::Use(scrut_op),
        ));
        let (scrut_place, scrut_ty) =
            if let Type::Ptr { pointee, .. } = self.compiler.program.types[raw_scrut_ty.0 as usize]
                && !self.compiler.raw_ptrs.contains_key(&raw_scrut_ty)
                && !self.compiler.slices.contains_key(&raw_scrut_ty)
            {
                (
                    Place {
                        local: raw_scrut_local,
                        projections: vec![Projection::Deref],
                    },
                    pointee,
                )
            } else {
                (Place::new(raw_scrut_local), raw_scrut_ty)
            };

        let void_ty = self.compiler.intern_type(Type::Void);
        let never_ty = self.compiler.intern_type(Type::Never);
        let entry_bb = self.cur_block;

        // 1. `error` scrutinee
        if let Some(err_info) = self.compiler.errors.get(&scrut_ty).cloned() {
            let tag_ty = self.compiler.intern_type(Type::Int {
                signed: false,
                bits: 32,
            });
            let discr_local = self.alloc_temp(tag_ty);
            self.emit(Statement::Assign(
                Place::new(discr_local),
                Rvalue::Discriminant(scrut_place.clone()),
            ));

            let mut covered = vec![false; err_info.leaves.len()];
            let mut has_wildcard = false;
            let mut switch_targets: Vec<(i128, BlockId)> = Vec::new();
            let mut wildcard_bb: Option<BlockId> = None;
            let mut arm_end_bbs: Vec<(BlockId, Operand, TypeId)> = Vec::new();
            let mut inferred_res_ty: Option<TypeId> = expected_ty;

            for (raw_pat, arm_expr) in arms {
                let pat = match raw_pat {
                    MatchPat::CatchAllBind { name, .. }
                        if self
                            .resolve_match_type_path(std::slice::from_ref(name))
                            .is_some_and(|t| self.compiler.errors.contains_key(&t)) =>
                    {
                        MatchPat::Variant {
                            path: vec![name.clone()],
                            binding: None,
                        }
                    }
                    other => other.clone(),
                };

                let arm_bb = self.new_block();
                let mut arm_binding: Option<(String, LocalId, TypeId)> = None;

                match &pat {
                    MatchPat::Wildcard => {
                        has_wildcard = true;
                        for c in &mut covered {
                            *c = true;
                        }
                        if wildcard_bb.is_none() {
                            wildcard_bb = Some(arm_bb);
                        }
                    }
                    MatchPat::CatchAllBind { name, .. } => {
                        has_wildcard = true;
                        for c in &mut covered {
                            *c = true;
                        }
                        if wildcard_bb.is_none() {
                            wildcard_bb = Some(arm_bb);
                        }
                        if name != "_" {
                            let bind_local = self.alloc_temp(scrut_ty);
                            self.cur_block = arm_bb;
                            self.emit(Statement::StorageLive(bind_local));
                            let s_op = if self.is_copy_type(scrut_ty) {
                                Operand::Copy(scrut_place.clone())
                            } else {
                                Operand::Move(scrut_place.clone())
                            };
                            self.emit(Statement::Assign(
                                Place::new(bind_local),
                                Rvalue::Use(s_op),
                            ));
                            arm_binding = Some((name.clone(), bind_local, scrut_ty));
                        }
                    }
                    MatchPat::Variant { path, binding } => {
                        // First check if `path` resolves directly to a subtype `error` (e.g. `IoError(io_err)`)
                        if let Some(sub_ty) = self.resolve_match_type_path(path)
                            && let Some(sub_err) = self.compiler.errors.get(&sub_ty).cloned()
                        {
                            let bind_local_opt = binding
                                .as_ref()
                                .filter(|(_, n)| n != "_")
                                .map(|(_, n)| (n.clone(), self.alloc_temp(sub_ty)));
                            for (sub_idx, sub_leaf) in sub_err.leaves.iter().enumerate() {
                                let Some((scrut_idx, scrut_leaf)) = err_info
                                    .leaves
                                    .iter()
                                    .enumerate()
                                    .find(|(_, sl)| sl.key == sub_leaf.key)
                                else {
                                    return Err(format!(
                                        "Error subtype '{}' in match pattern is not a subset of '{}': missing variant '{}::{}'",
                                        sub_err.name,
                                        err_info.name,
                                        sub_leaf.key.error_name,
                                        sub_leaf.key.variant_name
                                    ));
                                };
                                if scrut_leaf.payload_ty != sub_leaf.payload_ty {
                                    return Err(format!(
                                        "Payload type mismatch for variant '{}::{}' in match",
                                        sub_leaf.key.error_name, sub_leaf.key.variant_name
                                    ));
                                }
                                if covered[scrut_idx] {
                                    continue;
                                }
                                covered[scrut_idx] = true;
                                if let Some((_, sub_local)) = &bind_local_opt {
                                    let tramp_bb = self.new_block();
                                    switch_targets.push((scrut_idx as i128, tramp_bb));
                                    self.cur_block = tramp_bb;
                                    self.emit(Statement::StorageLive(*sub_local));
                                    let p_ty = scrut_leaf.payload_ty;
                                    let p_op = if matches!(
                                        self.compiler.program.types[p_ty.0 as usize],
                                        Type::Void
                                    ) {
                                        Operand::Const(ConstValue::Void)
                                    } else {
                                        let mut p_place = scrut_place.clone();
                                        p_place
                                            .projections
                                            .push(Projection::Variant(scrut_idx as u32));
                                        if self.is_copy_type(p_ty) {
                                            Operand::Copy(p_place)
                                        } else {
                                            Operand::Move(p_place)
                                        }
                                    };
                                    self.emit(Statement::Assign(
                                        Place::new(*sub_local),
                                        Rvalue::Union {
                                            ty: sub_ty,
                                            variant: sub_idx as u32,
                                            payload: p_op,
                                        },
                                    ));
                                    self.terminate(Terminator::Goto { target: arm_bb });
                                } else {
                                    switch_targets.push((scrut_idx as i128, arm_bb));
                                }
                            }
                            if let Some((b_name, sub_local)) = bind_local_opt {
                                arm_binding = Some((b_name, sub_local, sub_ty));
                            }
                        } else {
                            // Leaf variant pattern: `IoError::Timeout` or `ParseError::UnexpectedToken(tok)`
                            if path.len() < 2 {
                                return Err(format!(
                                    "Unqualified error variant '{}' in `match`; qualify as 'ErrorType::{}'",
                                    path.join("::"),
                                    path.join("::")
                                ));
                            }
                            let prefix = &path[..path.len() - 1];
                            let vname = path.last().unwrap();
                            let Some(pat_err_ty) = self.resolve_match_type_path(prefix) else {
                                return Err(format!(
                                    "Cannot resolve error type '{}' in match pattern",
                                    prefix.join("::")
                                ));
                            };
                            let Some(pat_err) = self.compiler.errors.get(&pat_err_ty).cloned()
                            else {
                                return Err(format!(
                                    "'{}' in match pattern is not an `error` type",
                                    prefix.join("::")
                                ));
                            };
                            let Some(pat_leaf) = pat_err
                                .leaves
                                .iter()
                                .find(|l| {
                                    l.key.error_name == pat_err.name
                                        && l.key.variant_name == *vname
                                })
                                .or_else(|| {
                                    pat_err.leaves.iter().find(|l| l.key.variant_name == *vname)
                                })
                            else {
                                return Err(format!(
                                    "Error type '{}' has no variant '{}'",
                                    pat_err.name, vname
                                ));
                            };
                            let Some((scrut_idx, scrut_leaf)) = err_info
                                .leaves
                                .iter()
                                .enumerate()
                                .find(|(_, sl)| sl.key == pat_leaf.key)
                            else {
                                return Err(format!(
                                    "Error variant '{}::{}' is not a member of scrutinee error type '{}'",
                                    pat_leaf.key.error_name, pat_leaf.key.variant_name, err_info.name
                                ));
                            };
                            covered[scrut_idx] = true;
                            switch_targets.push((scrut_idx as i128, arm_bb));
                            if let Some((_, b_name)) = binding
                                && b_name != "_"
                            {
                                let p_ty = scrut_leaf.payload_ty;
                                let var_local = self.alloc_temp(p_ty);
                                self.cur_block = arm_bb;
                                self.emit(Statement::StorageLive(var_local));
                                let mut p_place = scrut_place.clone();
                                p_place
                                    .projections
                                    .push(Projection::Variant(scrut_idx as u32));
                                let p_op = if self.is_copy_type(p_ty) {
                                    Operand::Copy(p_place)
                                } else {
                                    Operand::Move(p_place)
                                };
                                self.emit(Statement::Assign(
                                    Place::new(var_local),
                                    Rvalue::Use(p_op),
                                ));
                                arm_binding = Some((b_name.clone(), var_local, p_ty));
                            }
                        }
                    }
                    MatchPat::Int(_) => {
                        return Err("Cannot match integer literal against `error` type".to_string());
                    }
                }

                self.cur_block = arm_bb;
                self.scopes.push(Vec::new());
                if let Some((b_name, b_local, b_ty)) = arm_binding {
                    self.scopes.last_mut().unwrap().push(ScopeVar {
                        name: b_name,
                        local: b_local,
                        ty: b_ty,
                        opaque_bound: None,
                    });
                }
                let arm_exp = if is_stmt {
                    Some(void_ty)
                } else {
                    inferred_res_ty
                };
                let (arm_op, arm_ty) = self.lower_expr(arm_expr, arm_exp)?;
                if !self.is_terminated() {
                    if !is_stmt
                        && inferred_res_ty.is_none()
                        && arm_ty != never_ty
                    {
                        inferred_res_ty = Some(arm_ty);
                    }
                    let saved_op = if is_stmt || arm_ty == void_ty || arm_ty == never_ty {
                        Operand::Const(ConstValue::Void)
                    } else {
                        let tmp = self.alloc_temp(arm_ty);
                        self.emit(Statement::Assign(Place::new(tmp), Rvalue::Use(arm_op)));
                        if self.is_copy_type(arm_ty) {
                            Operand::Copy(Place::new(tmp))
                        } else {
                            Operand::Move(Place::new(tmp))
                        }
                    };
                    self.cleanup_top_scope();
                    arm_end_bbs.push((self.cur_block, saved_op, arm_ty));
                }
                self.scopes.pop();
            }

            if !has_wildcard && covered.iter().any(|&c| !c) {
                let missing: Vec<String> = err_info
                    .leaves
                    .iter()
                    .enumerate()
                    .filter(|(i, _)| !covered[*i])
                    .map(|(_, l)| format!("{}::{}", l.key.error_name, l.key.variant_name))
                    .collect();
                return Err(format!(
                    "Non-exhaustive `match` on error type '{}': missing variants: {}",
                    err_info.name,
                    missing.join(", ")
                ));
            }

            let otherwise_bb = wildcard_bb.unwrap_or_else(|| {
                let u_bb = self.new_block();
                self.blocks[u_bb.0 as usize].terminator = Terminator::Unreachable;
                self.terminated[u_bb.0 as usize] = true;
                u_bb
            });
            self.blocks[entry_bb.0 as usize].terminator = Terminator::SwitchInt {
                discr: Operand::Copy(Place::new(discr_local)),
                targets: switch_targets,
                otherwise: otherwise_bb,
            };
            self.terminated[entry_bb.0 as usize] = true;

            let final_ty = if is_stmt {
                void_ty
            } else {
                inferred_res_ty.unwrap_or(never_ty)
            };
            if arm_end_bbs.is_empty() {
                let unreach_after = self.new_block();
                self.cur_block = unreach_after;
                self.terminate(Terminator::Unreachable);
                return Ok((Operand::Const(ConstValue::Void), never_ty));
            }
            let join_bb = self.new_block();
            let res_local = self.alloc_temp(final_ty);
            for (end_bb, saved_op, arm_ty) in arm_end_bbs {
                self.cur_block = end_bb;
                if !is_stmt && final_ty != void_ty && final_ty != never_ty {
                    let coerced = self.coerce_operand(saved_op, arm_ty, final_ty)?;
                    self.emit(Statement::Assign(Place::new(res_local), Rvalue::Use(coerced)));
                }
                self.terminate(Terminator::Goto { target: join_bb });
            }
            self.cur_block = join_bb;
            if is_stmt || final_ty == void_ty {
                return Ok((Operand::Const(ConstValue::Void), void_ty));
            }
            let out_op = if self.is_copy_type(final_ty) {
                Operand::Copy(Place::new(res_local))
            } else {
                Operand::Move(Place::new(res_local))
            };
            return Ok((out_op, final_ty));
        }

        // 2. `union` scrutinee
        if let Some(union_info) = self.compiler.unions.get(&scrut_ty).cloned() {
            let tag_ty = self.compiler.intern_type(Type::Int {
                signed: false,
                bits: 32,
            });
            let discr_local = self.alloc_temp(tag_ty);
            self.emit(Statement::Assign(
                Place::new(discr_local),
                Rvalue::Discriminant(scrut_place.clone()),
            ));

            let mut covered = vec![false; union_info.variants.len()];
            let mut has_wildcard = false;
            let mut switch_targets: Vec<(i128, BlockId)> = Vec::new();
            let mut wildcard_bb: Option<BlockId> = None;
            let mut arm_end_bbs: Vec<(BlockId, Operand, TypeId)> = Vec::new();
            let mut inferred_res_ty: Option<TypeId> = expected_ty;

            for (raw_pat, arm_expr) in arms {
                let pat = match raw_pat {
                    MatchPat::CatchAllBind { name, .. }
                        if union_info.variants.iter().any(|(vn, _)| vn == name) =>
                    {
                        MatchPat::Variant {
                            path: vec![name.clone()],
                            binding: None,
                        }
                    }
                    other => other.clone(),
                };

                let arm_bb = self.new_block();
                let mut arm_binding: Option<(String, LocalId, TypeId)> = None;

                match &pat {
                    MatchPat::Wildcard => {
                        has_wildcard = true;
                        for c in &mut covered {
                            *c = true;
                        }
                        if wildcard_bb.is_none() {
                            wildcard_bb = Some(arm_bb);
                        }
                    }
                    MatchPat::CatchAllBind { name, .. } => {
                        has_wildcard = true;
                        for c in &mut covered {
                            *c = true;
                        }
                        if wildcard_bb.is_none() {
                            wildcard_bb = Some(arm_bb);
                        }
                        if name != "_" {
                            let bind_local = self.alloc_temp(scrut_ty);
                            self.cur_block = arm_bb;
                            self.emit(Statement::StorageLive(bind_local));
                            let s_op = if self.is_copy_type(scrut_ty) {
                                Operand::Copy(scrut_place.clone())
                            } else {
                                Operand::Move(scrut_place.clone())
                            };
                            self.emit(Statement::Assign(
                                Place::new(bind_local),
                                Rvalue::Use(s_op),
                            ));
                            arm_binding = Some((name.clone(), bind_local, scrut_ty));
                        }
                    }
                    MatchPat::Variant { path, binding } => {
                        let vname = path.last().unwrap();
                        let Some((v_idx, (_, payload_ty))) = union_info
                            .variants
                            .iter()
                            .enumerate()
                            .find(|(_, (vn, _))| vn == vname)
                        else {
                            return Err(format!(
                                "Union '{}' has no variant '{}'",
                                union_info.name, vname
                            ));
                        };
                        covered[v_idx] = true;
                        switch_targets.push((v_idx as i128, arm_bb));
                        if let Some((_, b_name)) = binding
                            && b_name != "_"
                        {
                            let var_local = self.alloc_temp(*payload_ty);
                            self.cur_block = arm_bb;
                            self.emit(Statement::StorageLive(var_local));
                            let mut p_place = scrut_place.clone();
                            p_place
                                .projections
                                .push(Projection::Variant(v_idx as u32));
                            let p_op = if self.is_copy_type(*payload_ty) {
                                Operand::Copy(p_place)
                            } else {
                                Operand::Move(p_place)
                            };
                            self.emit(Statement::Assign(
                                Place::new(var_local),
                                Rvalue::Use(p_op),
                            ));
                            arm_binding = Some((b_name.clone(), var_local, *payload_ty));
                        }
                    }
                    MatchPat::Int(_) => {
                        return Err("Cannot match integer literal against `union` type".to_string());
                    }
                }

                self.cur_block = arm_bb;
                self.scopes.push(Vec::new());
                if let Some((b_name, b_local, b_ty)) = arm_binding {
                    self.scopes.last_mut().unwrap().push(ScopeVar {
                        name: b_name,
                        local: b_local,
                        ty: b_ty,
                        opaque_bound: None,
                    });
                }
                let arm_exp = if is_stmt {
                    Some(void_ty)
                } else {
                    inferred_res_ty
                };
                let (arm_op, arm_ty) = self.lower_expr(arm_expr, arm_exp)?;
                if !self.is_terminated() {
                    if !is_stmt
                        && inferred_res_ty.is_none()
                        && arm_ty != never_ty
                    {
                        inferred_res_ty = Some(arm_ty);
                    }
                    let saved_op = if is_stmt || arm_ty == void_ty || arm_ty == never_ty {
                        Operand::Const(ConstValue::Void)
                    } else {
                        let tmp = self.alloc_temp(arm_ty);
                        self.emit(Statement::Assign(Place::new(tmp), Rvalue::Use(arm_op)));
                        if self.is_copy_type(arm_ty) {
                            Operand::Copy(Place::new(tmp))
                        } else {
                            Operand::Move(Place::new(tmp))
                        }
                    };
                    self.cleanup_top_scope();
                    arm_end_bbs.push((self.cur_block, saved_op, arm_ty));
                }
                self.scopes.pop();
            }

            if !has_wildcard && covered.iter().any(|&c| !c) {
                let missing: Vec<String> = union_info
                    .variants
                    .iter()
                    .enumerate()
                    .filter(|(i, _)| !covered[*i])
                    .map(|(_, (vn, _))| format!("{}::{}", union_info.name, vn))
                    .collect();
                return Err(format!(
                    "Non-exhaustive `match` on union '{}': missing variants: {}",
                    union_info.name,
                    missing.join(", ")
                ));
            }

            let otherwise_bb = wildcard_bb.unwrap_or_else(|| {
                let u_bb = self.new_block();
                self.blocks[u_bb.0 as usize].terminator = Terminator::Unreachable;
                self.terminated[u_bb.0 as usize] = true;
                u_bb
            });
            self.blocks[entry_bb.0 as usize].terminator = Terminator::SwitchInt {
                discr: Operand::Copy(Place::new(discr_local)),
                targets: switch_targets,
                otherwise: otherwise_bb,
            };
            self.terminated[entry_bb.0 as usize] = true;

            let final_ty = if is_stmt {
                void_ty
            } else {
                inferred_res_ty.unwrap_or(never_ty)
            };
            if arm_end_bbs.is_empty() {
                let unreach_after = self.new_block();
                self.cur_block = unreach_after;
                self.terminate(Terminator::Unreachable);
                return Ok((Operand::Const(ConstValue::Void), never_ty));
            }
            let join_bb = self.new_block();
            let res_local = self.alloc_temp(final_ty);
            for (end_bb, saved_op, arm_ty) in arm_end_bbs {
                self.cur_block = end_bb;
                if !is_stmt && final_ty != void_ty && final_ty != never_ty {
                    let coerced = self.coerce_operand(saved_op, arm_ty, final_ty)?;
                    self.emit(Statement::Assign(Place::new(res_local), Rvalue::Use(coerced)));
                }
                self.terminate(Terminator::Goto { target: join_bb });
            }
            self.cur_block = join_bb;
            if is_stmt || final_ty == void_ty {
                return Ok((Operand::Const(ConstValue::Void), void_ty));
            }
            let out_op = if self.is_copy_type(final_ty) {
                Operand::Copy(Place::new(res_local))
            } else {
                Operand::Move(Place::new(res_local))
            };
            return Ok((out_op, final_ty));
        }

        // 3. `enum` or integer scrutinee
        let enum_info = self.compiler.enums.get(&scrut_ty).cloned();
        let mut covered = enum_info
            .as_ref()
            .map(|(_, vs)| vec![false; vs.len()])
            .unwrap_or_default();
        let mut has_wildcard = false;
        let mut switch_targets: Vec<(i128, BlockId)> = Vec::new();
        let mut wildcard_bb: Option<BlockId> = None;
        let mut arm_end_bbs: Vec<(BlockId, Operand, TypeId)> = Vec::new();
        let mut inferred_res_ty: Option<TypeId> = expected_ty;

        for (raw_pat, arm_expr) in arms {
            let pat = match (raw_pat, &enum_info) {
                (MatchPat::CatchAllBind { name, .. }, Some((_, vs)))
                    if vs.iter().any(|(vn, _)| vn == name) =>
                {
                    MatchPat::Variant {
                        path: vec![name.clone()],
                        binding: None,
                    }
                }
                (other, _) => other.clone(),
            };

            let arm_bb = self.new_block();
            let mut arm_binding: Option<(String, LocalId, TypeId)> = None;

            match &pat {
                MatchPat::Wildcard => {
                    has_wildcard = true;
                    for c in &mut covered {
                        *c = true;
                    }
                    if wildcard_bb.is_none() {
                        wildcard_bb = Some(arm_bb);
                    }
                }
                MatchPat::CatchAllBind { name, .. } => {
                    has_wildcard = true;
                    for c in &mut covered {
                        *c = true;
                    }
                    if wildcard_bb.is_none() {
                        wildcard_bb = Some(arm_bb);
                    }
                    if name != "_" {
                        let bind_local = self.alloc_temp(scrut_ty);
                        self.cur_block = arm_bb;
                        self.emit(Statement::StorageLive(bind_local));
                        self.emit(Statement::Assign(
                            Place::new(bind_local),
                            Rvalue::Use(Operand::Copy(scrut_place.clone())),
                        ));
                        arm_binding = Some((name.clone(), bind_local, scrut_ty));
                    }
                }
                MatchPat::Variant { path, binding } => {
                    if binding.is_some() {
                        return Err("Enum variant cannot bind a payload in `match`".to_string());
                    }
                    let Some((enum_name, variants)) = &enum_info else {
                        return Err(format!(
                            "Cannot match variant pattern '{}' against non-enum/union/error type {}",
                            path.join("::"),
                            self.compiler.program.types[scrut_ty.0 as usize]
                        ));
                    };
                    let vname = path.last().unwrap();
                    let Some((v_idx, (_, v_val))) = variants
                        .iter()
                        .enumerate()
                        .find(|(_, (vn, _))| vn == vname)
                    else {
                        return Err(format!("Enum '{}' has no variant '{}'", enum_name, vname));
                    };
                    covered[v_idx] = true;
                    switch_targets.push((*v_val, arm_bb));
                }
                MatchPat::Int(val) => {
                    switch_targets.push((*val, arm_bb));
                }
            }

            self.cur_block = arm_bb;
            self.scopes.push(Vec::new());
            if let Some((b_name, b_local, b_ty)) = arm_binding {
                self.scopes.last_mut().unwrap().push(ScopeVar {
                    name: b_name,
                    local: b_local,
                    ty: b_ty,
                    opaque_bound: None,
                });
            }
            let arm_exp = if is_stmt {
                Some(void_ty)
            } else {
                inferred_res_ty
            };
            let (arm_op, arm_ty) = self.lower_expr(arm_expr, arm_exp)?;
            if !self.is_terminated() {
                if !is_stmt
                    && inferred_res_ty.is_none()
                    && arm_ty != never_ty
                {
                    inferred_res_ty = Some(arm_ty);
                }
                let saved_op = if is_stmt || arm_ty == void_ty || arm_ty == never_ty {
                    Operand::Const(ConstValue::Void)
                } else {
                    let tmp = self.alloc_temp(arm_ty);
                    self.emit(Statement::Assign(Place::new(tmp), Rvalue::Use(arm_op)));
                    if self.is_copy_type(arm_ty) {
                        Operand::Copy(Place::new(tmp))
                    } else {
                        Operand::Move(Place::new(tmp))
                    }
                };
                self.cleanup_top_scope();
                arm_end_bbs.push((self.cur_block, saved_op, arm_ty));
            }
            self.scopes.pop();
        }

        if let Some((enum_name, variants)) = &enum_info {
            if !has_wildcard && covered.iter().any(|&c| !c) {
                let missing: Vec<String> = variants
                    .iter()
                    .enumerate()
                    .filter(|(i, _)| !covered[*i])
                    .map(|(_, (vn, _))| format!("{enum_name}::{vn}"))
                    .collect();
                return Err(format!(
                    "Non-exhaustive `match` on enum '{}': missing variants: {}",
                    enum_name,
                    missing.join(", ")
                ));
            }
        } else if !has_wildcard {
            return Err("Non-exhaustive `match` on integer requires a wildcard `_` arm".to_string());
        }

        let otherwise_bb = wildcard_bb.unwrap_or_else(|| {
            let u_bb = self.new_block();
            self.blocks[u_bb.0 as usize].terminator = Terminator::Unreachable;
            self.terminated[u_bb.0 as usize] = true;
            u_bb
        });
        self.blocks[entry_bb.0 as usize].terminator = Terminator::SwitchInt {
            discr: Operand::Copy(scrut_place),
            targets: switch_targets,
            otherwise: otherwise_bb,
        };
        self.terminated[entry_bb.0 as usize] = true;

        let final_ty = if is_stmt {
            void_ty
        } else {
            inferred_res_ty.unwrap_or(never_ty)
        };
        if arm_end_bbs.is_empty() {
            let unreach_after = self.new_block();
            self.cur_block = unreach_after;
            self.terminate(Terminator::Unreachable);
            return Ok((Operand::Const(ConstValue::Void), never_ty));
        }
        let join_bb = self.new_block();
        let res_local = self.alloc_temp(final_ty);
        for (end_bb, saved_op, arm_ty) in arm_end_bbs {
            self.cur_block = end_bb;
            if !is_stmt && final_ty != void_ty && final_ty != never_ty {
                let coerced = self.coerce_operand(saved_op, arm_ty, final_ty)?;
                self.emit(Statement::Assign(Place::new(res_local), Rvalue::Use(coerced)));
            }
            self.terminate(Terminator::Goto { target: join_bb });
        }
        self.cur_block = join_bb;
        if is_stmt || final_ty == void_ty {
            return Ok((Operand::Const(ConstValue::Void), void_ty));
        }
        let out_op = if self.is_copy_type(final_ty) {
            Operand::Copy(Place::new(res_local))
        } else {
            Operand::Move(Place::new(res_local))
        };
        Ok((out_op, final_ty))
    }

    fn lower_slice(
        &mut self,
        base: &Expr,
        start: &Expr,
        end: &Expr,
        explicit_mut: Option<bool>,
        expected_ty: Option<TypeId>,
    ) -> Result<(Operand, TypeId), String> {
        let want_mut = explicit_mut.unwrap_or_else(|| {
            expected_ty
                .and_then(|t| self.compiler.slices.get(&t))
                .is_some_and(|info| info.mutable)
        });
        let (mut base_place, mut base_ty) = self.lower_place(base, want_mut)?;
        if let Type::Ptr {
            mutable: ptr_mut,
            pointee,
        } = self.compiler.program.types[base_ty.0 as usize]
        {
            if want_mut && !ptr_mut {
                return Err("Cannot mutably slice through an immutable reference".to_string());
            }
            base_place.projections.push(Projection::Deref);
            base_ty = pointee;
        }
        let elem_ty = if let Some(&slice_info) = self.compiler.slices.get(&base_ty) {
            if want_mut && !slice_info.mutable {
                return Err("Cannot take mutable subslice of an immutable slice".to_string());
            }
            base_place.projections.push(Projection::Field(0));
            base_place.projections.push(Projection::Deref);
            slice_info.elem
        } else if let Type::Array { elem, .. } = self.compiler.program.types[base_ty.0 as usize] {
            elem
        } else {
            return Err(format!("Cannot slice non-array/slice type {base_ty}"));
        };

        let usize_ty = self.compiler.intern_type(Type::Int {
            signed: false,
            bits: 64,
        });
        let (start_op, _) = self.lower_expr(start, Some(usize_ty))?;
        let start_local = self.alloc_temp(usize_ty);
        self.emit(Statement::Assign(
            Place::new(start_local),
            Rvalue::Use(start_op),
        ));
        let (end_op, _) = self.lower_expr(end, Some(usize_ty))?;

        let mut elem_start_place = base_place;
        elem_start_place
            .projections
            .push(Projection::Index(start_local));
        let elem_ptr_ty = self.compiler.intern_type(Type::Ptr {
            mutable: want_mut,
            pointee: elem_ty,
        });
        let elem_ptr_tmp = self.alloc_temp(elem_ptr_ty);
        self.emit(Statement::Assign(
            Place::new(elem_ptr_tmp),
            Rvalue::Ref {
                mutable: want_mut,
                place: elem_start_place,
            },
        ));

        let want_str = expected_ty
            .and_then(|t| self.compiler.slices.get(&t))
            .is_some_and(|info| info.is_str)
            || self
                .compiler
                .slices
                .get(&base_ty)
                .is_some_and(|info| info.is_str);
        let slice_ty = if want_str && !want_mut {
            self.compiler.intern_str_type()
        } else {
            self.compiler.intern_slice_type(want_mut, elem_ty)
        };
        let slice_info = self.compiler.slices[&slice_ty];
        let data_ptr_tmp = self.alloc_temp(slice_info.ptr_ty);
        self.emit(Statement::Assign(
            Place::new(data_ptr_tmp),
            Rvalue::Cast(Operand::Copy(Place::new(elem_ptr_tmp)), slice_info.ptr_ty),
        ));

        let len_tmp = self.alloc_temp(usize_ty);
        self.emit(Statement::Assign(
            Place::new(len_tmp),
            Rvalue::BinaryOp(
                BinOp::Sub,
                end_op,
                Operand::Copy(Place::new(start_local)),
            ),
        ));

        let slice_tmp = self.alloc_temp(slice_ty);
        self.emit(Statement::Assign(
            Place::new(slice_tmp),
            Rvalue::Aggregate(
                slice_ty,
                vec![
                    Operand::Copy(Place::new(data_ptr_tmp)),
                    Operand::Copy(Place::new(len_tmp)),
                ],
            ),
        ));
        Ok((Operand::Copy(Place::new(slice_tmp)), slice_ty))
    }

    fn place_type(&self, place: &Place) -> TypeId {
        let mut ty = self.locals[place.local.0 as usize];
        for proj in &place.projections {
            match proj {
                Projection::Deref => {
                    if let Type::Ptr { pointee, .. } = self.compiler.program.types[ty.0 as usize] {
                        ty = pointee;
                    }
                }
                Projection::Field(idx) => {
                    if let Type::Struct(fields) = &self.compiler.program.types[ty.0 as usize] {
                        ty = fields[*idx as usize];
                    }
                }
                Projection::Variant(idx) => {
                    if let Type::Union { variants, .. } =
                        &self.compiler.program.types[ty.0 as usize]
                    {
                        ty = variants[*idx as usize];
                    }
                }
                Projection::Index(_) => match self.compiler.program.types[ty.0 as usize] {
                    Type::Array { elem, .. } | Type::Simd { elem, .. } => ty = elem,
                    _ => {}
                },
            }
        }
        ty
    }

    fn place_traverses_safe_ref(&self, place: &Place) -> bool {
        let mut ty = self.locals[place.local.0 as usize];
        for proj in &place.projections {
            match proj {
                Projection::Deref => {
                    if !self.compiler.raw_ptrs.contains_key(&ty) {
                        return true;
                    }
                    if let Type::Ptr { pointee, .. } = self.compiler.program.types[ty.0 as usize] {
                        ty = pointee;
                    }
                }
                Projection::Field(idx) => {
                    if let Type::Struct(fields) = &self.compiler.program.types[ty.0 as usize] {
                        ty = fields[*idx as usize];
                    }
                }
                Projection::Variant(idx) => {
                    if let Type::Union { variants, .. } =
                        &self.compiler.program.types[ty.0 as usize]
                    {
                        ty = variants[*idx as usize];
                    }
                }
                Projection::Index(_) => match self.compiler.program.types[ty.0 as usize] {
                    Type::Array { elem, .. } | Type::Simd { elem, .. } => ty = elem,
                    _ => {}
                },
            }
        }
        false
    }

    fn place_traverses_immutable_ptr(&self, place: &Place) -> bool {
        let mut ty = self.locals[place.local.0 as usize];
        for proj in &place.projections {
            match proj {
                Projection::Deref => {
                    if let Type::Ptr { mutable, pointee } =
                        self.compiler.program.types[ty.0 as usize]
                    {
                        if !mutable {
                            return true;
                        }
                        ty = pointee;
                    }
                }
                Projection::Field(idx) => {
                    if let Type::Struct(fields) = &self.compiler.program.types[ty.0 as usize] {
                        ty = fields[*idx as usize];
                    }
                }
                Projection::Variant(idx) => {
                    if let Type::Union { variants, .. } =
                        &self.compiler.program.types[ty.0 as usize]
                    {
                        ty = variants[*idx as usize];
                    }
                }
                Projection::Index(_) => match self.compiler.program.types[ty.0 as usize] {
                    Type::Array { elem, .. } | Type::Simd { elem, .. } => ty = elem,
                    _ => {}
                },
            }
        }
        false
    }

    fn verify_rel_coresidence(
        &self,
        struct_name: &str,
        field_name: &str,
        base_place: &Place,
        dest_field_place: &Place,
        rhs_place: &Place,
    ) -> Result<(), String> {
        if rhs_place.local != base_place.local
            || !rhs_place.projections.starts_with(&base_place.projections)
            || rhs_place.projections.len() <= base_place.projections.len()
        {
            return Err(format!(
                "Co-Residence violation on '{}.{}': '&rel' target must reside inside the enclosing struct 'self' (cannot reference an outer local variable or temporary)",
                struct_name, field_name
            ));
        }
        let rel_projs = &rhs_place.projections[base_place.projections.len()..];
        let mut cur_ty = self.place_type(base_place);
        for proj in rel_projs {
            match proj {
                Projection::Deref => {
                    return Err(format!(
                        "Co-Residence violation on '{}.{}': '&rel' target must be inline storage within 'self' and cannot traverse a pointer or slice dereference",
                        struct_name, field_name
                    ));
                }
                Projection::Variant(_) => {
                    return Err(format!(
                        "Co-Residence violation on '{}.{}': '&rel' target cannot reside inside a union variant or overlay field",
                        struct_name, field_name
                    ));
                }
                Projection::Field(idx) => {
                    match &self.compiler.program.types[cur_ty.0 as usize] {
                        Type::Struct(fields) => {
                            if let Some(&fty) = fields.get(*idx as usize) {
                                cur_ty = fty;
                            }
                        }
                        Type::Overlay(_) | Type::Union { .. } => {
                            return Err(format!(
                                "Co-Residence violation on '{}.{}': '&rel' target cannot reside inside a union variant or overlay field",
                                struct_name, field_name
                            ));
                        }
                        _ => {}
                    }
                }
                Projection::Index(_) => {
                    if let Type::Array { elem, .. } | Type::Simd { elem, .. } =
                        self.compiler.program.types[cur_ty.0 as usize]
                    {
                        cur_ty = elem;
                    }
                }
            }
        }
        if rhs_place.projections.starts_with(&dest_field_place.projections) {
            return Err(format!(
                "Co-Residence violation on '{}.{}': '&rel' field cannot point to itself",
                struct_name, field_name
            ));
        }
        Ok(())
    }

    fn assign_rel_field(
        &mut self,
        struct_name: &str,
        field_name: &str,
        base_place: &Place,
        dest_field_place: Place,
        rel_kind: RelFieldKind,
        val_expr: &Expr,
    ) -> Result<(), String> {
        let Expr::RelRef(target_expr) = val_expr else {
            return Err(format!(
                "Field '{}' of struct '{}' is a relative reference and must be initialized or assigned with '&rel <place>'",
                field_name, struct_name
            ));
        };
        let isize_ty = self.compiler.intern_type(Type::Int {
            signed: true,
            bits: 64,
        });
        let usize_ty = self.compiler.intern_type(Type::Int {
            signed: false,
            bits: 64,
        });
        match rel_kind {
            RelFieldKind::Elem(expected_elem_ty) => {
                let (rhs_place, rhs_ty) = self.lower_place(target_expr, false)?;
                if rhs_ty != expected_elem_ty {
                    return Err(format!(
                        "Type mismatch in '&rel' assignment to '{}.{}': expected target of type {}, found {}",
                        struct_name,
                        field_name,
                        self.compiler.program.types[expected_elem_ty.0 as usize],
                        self.compiler.program.types[rhs_ty.0 as usize]
                    ));
                }
                self.verify_rel_coresidence(
                    struct_name,
                    field_name,
                    base_place,
                    &dest_field_place,
                    &rhs_place,
                )?;
                let target_ptr_ty = self.compiler.intern_type(Type::Ptr {
                    mutable: false,
                    pointee: rhs_ty,
                });
                let target_ptr_tmp = self.alloc_temp(target_ptr_ty);
                self.emit(Statement::Assign(
                    Place::new(target_ptr_tmp),
                    Rvalue::Ref {
                        mutable: false,
                        place: rhs_place,
                    },
                ));
                let target_addr_tmp = self.alloc_temp(isize_ty);
                self.emit(Statement::Assign(
                    Place::new(target_addr_tmp),
                    Rvalue::Cast(Operand::Copy(Place::new(target_ptr_tmp)), isize_ty),
                ));

                let field_ptr_ty = self.compiler.intern_type(Type::Ptr {
                    mutable: false,
                    pointee: isize_ty,
                });
                let field_ptr_tmp = self.alloc_temp(field_ptr_ty);
                self.emit(Statement::Assign(
                    Place::new(field_ptr_tmp),
                    Rvalue::Ref {
                        mutable: false,
                        place: dest_field_place.clone(),
                    },
                ));
                let field_addr_tmp = self.alloc_temp(isize_ty);
                self.emit(Statement::Assign(
                    Place::new(field_addr_tmp),
                    Rvalue::Cast(Operand::Copy(Place::new(field_ptr_tmp)), isize_ty),
                ));

                let offset_tmp = self.alloc_temp(isize_ty);
                self.emit(Statement::Assign(
                    Place::new(offset_tmp),
                    Rvalue::BinaryOp(
                        BinOp::SubWrap,
                        Operand::Copy(Place::new(target_addr_tmp)),
                        Operand::Copy(Place::new(field_addr_tmp)),
                    ),
                ));
                self.emit(Statement::Assign(
                    dest_field_place,
                    Rvalue::Use(Operand::Copy(Place::new(offset_tmp))),
                ));
                Ok(())
            }
            RelFieldKind::Slice(_) | RelFieldKind::Str => {
                let expected_elem = match rel_kind {
                    RelFieldKind::Slice(t) => t,
                    RelFieldKind::Str => self.compiler.intern_type(Type::Int {
                        signed: false,
                        bits: 8,
                    }),
                    RelFieldKind::Elem(_) => unreachable!(),
                };
                let (target_place, target_place_ty, len_op) =
                    if let Expr::Slice { base, start, end } = target_expr.as_ref() {
                        let (mut arr_place, mut arr_ty) = self.lower_place(base, false)?;
                        if let Type::Ptr { pointee, .. } =
                            self.compiler.program.types[arr_ty.0 as usize]
                        {
                            arr_place.projections.push(Projection::Deref);
                            arr_ty = pointee;
                        }
                        if self.compiler.slices.contains_key(&arr_ty) {
                            arr_place.projections.push(Projection::Field(0));
                            arr_place.projections.push(Projection::Deref);
                        }
                        self.verify_rel_coresidence(
                            struct_name,
                            field_name,
                            base_place,
                            &dest_field_place,
                            &arr_place,
                        )?;
                        let Type::Array { elem, .. } =
                            self.compiler.program.types[arr_ty.0 as usize]
                        else {
                            return Err(format!(
                                "'&rel' slice '{}.{}' requires an inline array field, found {}",
                                struct_name,
                                field_name,
                                self.compiler.program.types[arr_ty.0 as usize]
                            ));
                        };
                        if elem != expected_elem {
                            return Err(format!(
                                "Element type mismatch in '&rel' slice '{}.{}': expected {}, found {}",
                                struct_name,
                                field_name,
                                self.compiler.program.types[expected_elem.0 as usize],
                                self.compiler.program.types[elem.0 as usize]
                            ));
                        }
                        let (start_op, _) = self.lower_expr(start, Some(usize_ty))?;
                        let start_local = self.alloc_temp(usize_ty);
                        self.emit(Statement::Assign(
                            Place::new(start_local),
                            Rvalue::Use(start_op),
                        ));
                        let (end_op, _) = self.lower_expr(end, Some(usize_ty))?;
                        let len_tmp = self.alloc_temp(usize_ty);
                        self.emit(Statement::Assign(
                            Place::new(len_tmp),
                            Rvalue::BinaryOp(
                                BinOp::Sub,
                                end_op,
                                Operand::Copy(Place::new(start_local)),
                            ),
                        ));
                        let mut elem_start_place = arr_place;
                        elem_start_place
                            .projections
                            .push(Projection::Index(start_local));
                        (
                            elem_start_place,
                            elem,
                            Operand::Copy(Place::new(len_tmp)),
                        )
                    } else {
                        let (arr_place, arr_ty) = self.lower_place(target_expr, false)?;
                        self.verify_rel_coresidence(
                            struct_name,
                            field_name,
                            base_place,
                            &dest_field_place,
                            &arr_place,
                        )?;
                        let Type::Array { elem, len } =
                            self.compiler.program.types[arr_ty.0 as usize]
                        else {
                            return Err(format!(
                                "'&rel' slice '{}.{}' requires an inline array or slice expression, found {}",
                                struct_name,
                                field_name,
                                self.compiler.program.types[arr_ty.0 as usize]
                            ));
                        };
                        if elem != expected_elem {
                            return Err(format!(
                                "Element type mismatch in '&rel' slice '{}.{}': expected {}, found {}",
                                struct_name,
                                field_name,
                                self.compiler.program.types[expected_elem.0 as usize],
                                self.compiler.program.types[elem.0 as usize]
                            ));
                        }
                        (
                            arr_place,
                            arr_ty,
                            Operand::Const(ConstValue::I64(len as i128)),
                        )
                    };

                let target_ptr_ty = self.compiler.intern_type(Type::Ptr {
                    mutable: false,
                    pointee: target_place_ty,
                });
                let target_ptr_tmp = self.alloc_temp(target_ptr_ty);
                self.emit(Statement::Assign(
                    Place::new(target_ptr_tmp),
                    Rvalue::Ref {
                        mutable: false,
                        place: target_place,
                    },
                ));
                let target_addr_tmp = self.alloc_temp(isize_ty);
                self.emit(Statement::Assign(
                    Place::new(target_addr_tmp),
                    Rvalue::Cast(Operand::Copy(Place::new(target_ptr_tmp)), isize_ty),
                ));

                let repr_ty = self
                    .compiler
                    .intern_type(Type::Struct(vec![isize_ty, usize_ty]));
                let field_ptr_ty = self.compiler.intern_type(Type::Ptr {
                    mutable: false,
                    pointee: repr_ty,
                });
                let field_ptr_tmp = self.alloc_temp(field_ptr_ty);
                self.emit(Statement::Assign(
                    Place::new(field_ptr_tmp),
                    Rvalue::Ref {
                        mutable: false,
                        place: dest_field_place.clone(),
                    },
                ));
                let field_addr_tmp = self.alloc_temp(isize_ty);
                self.emit(Statement::Assign(
                    Place::new(field_addr_tmp),
                    Rvalue::Cast(Operand::Copy(Place::new(field_ptr_tmp)), isize_ty),
                ));

                let offset_tmp = self.alloc_temp(isize_ty);
                self.emit(Statement::Assign(
                    Place::new(offset_tmp),
                    Rvalue::BinaryOp(
                        BinOp::SubWrap,
                        Operand::Copy(Place::new(target_addr_tmp)),
                        Operand::Copy(Place::new(field_addr_tmp)),
                    ),
                ));
                self.emit(Statement::Assign(
                    dest_field_place,
                    Rvalue::Aggregate(
                        repr_ty,
                        vec![Operand::Copy(Place::new(offset_tmp)), len_op],
                    ),
                ));
                Ok(())
            }
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn resolve_rel_field_access(
        &mut self,
        struct_name: &str,
        field_name: &str,
        base_place: Place,
        f_idx: u32,
        base_ty: TypeId,
        rel_kind: RelFieldKind,
        want_mut: bool,
    ) -> Result<(Place, TypeId), String> {
        if want_mut && matches!(rel_kind, RelFieldKind::Str) {
            return Err(format!(
                "Cannot mutably access '&rel str' field '{}.{}'; string slices (&str) are immutable",
                struct_name, field_name
            ));
        }
        if want_mut && self.place_traverses_immutable_ptr(&base_place) {
            return Err(format!(
                "Cannot mutably access '&rel' field '{}.{}' through an immutable '&Self' reference",
                struct_name, field_name
            ));
        }
        let isize_ty = self.compiler.intern_type(Type::Int {
            signed: true,
            bits: 64,
        });
        let usize_ty = self.compiler.intern_type(Type::Int {
            signed: false,
            bits: 64,
        });
        let mut field_place = base_place.clone();
        field_place.projections.push(Projection::Field(f_idx));

        // 1. Read `offset: isize` (and `len: usize` for slice/str) from `field_place` FIRST
        // so that reading `field_place` happens before `base_place` is borrowed.
        let (offset_tmp, len_tmp_opt) = match rel_kind {
            RelFieldKind::Elem(_) => {
                let off = self.alloc_temp(isize_ty);
                self.emit(Statement::Assign(
                    Place::new(off),
                    Rvalue::Use(Operand::Copy(field_place.clone())),
                ));
                (off, None)
            }
            RelFieldKind::Slice(_) | RelFieldKind::Str => {
                let mut off_p = field_place.clone();
                off_p.projections.push(Projection::Field(0));
                let off = self.alloc_temp(isize_ty);
                self.emit(Statement::Assign(
                    Place::new(off),
                    Rvalue::Use(Operand::Copy(off_p)),
                ));
                let mut len_p = field_place.clone();
                len_p.projections.push(Projection::Field(1));
                let len_t = self.alloc_temp(usize_ty);
                self.emit(Statement::Assign(
                    Place::new(len_t),
                    Rvalue::Use(Operand::Copy(len_p)),
                ));
                (off, Some(len_t))
            }
        };

        // 2. Compute `field_addr: isize` and `base_addr: isize` (temporary refs die immediately at `Cast` to `isize_ty`).
        let field_storage_ty = self.place_type(&field_place);
        let field_ptr_ty = self.compiler.intern_type(Type::Ptr {
            mutable: false,
            pointee: field_storage_ty,
        });
        let field_ptr_tmp = self.alloc_temp(field_ptr_ty);
        self.emit(Statement::Assign(
            Place::new(field_ptr_tmp),
            Rvalue::Ref {
                mutable: false,
                place: field_place,
            },
        ));
        let field_addr_tmp = self.alloc_temp(isize_ty);
        self.emit(Statement::Assign(
            Place::new(field_addr_tmp),
            Rvalue::Cast(Operand::Copy(Place::new(field_ptr_tmp)), isize_ty),
        ));

        let base_addr_ptr_ty = self.compiler.intern_type(Type::Ptr {
            mutable: false,
            pointee: base_ty,
        });
        let base_addr_ptr_tmp = self.alloc_temp(base_addr_ptr_ty);
        self.emit(Statement::Assign(
            Place::new(base_addr_ptr_tmp),
            Rvalue::Ref {
                mutable: false,
                place: base_place.clone(),
            },
        ));
        let base_addr_tmp = self.alloc_temp(isize_ty);
        self.emit(Statement::Assign(
            Place::new(base_addr_tmp),
            Rvalue::Cast(Operand::Copy(Place::new(base_addr_ptr_tmp)), isize_ty),
        ));

        // 3. Compute `target_addr = field_addr +% offset` and `total_offset_from_base = target_addr -% base_addr`.
        let target_addr_tmp = self.alloc_temp(isize_ty);
        self.emit(Statement::Assign(
            Place::new(target_addr_tmp),
            Rvalue::BinaryOp(
                BinOp::AddWrap,
                Operand::Copy(Place::new(field_addr_tmp)),
                Operand::Copy(Place::new(offset_tmp)),
            ),
        ));
        let total_offset_tmp = self.alloc_temp(isize_ty);
        self.emit(Statement::Assign(
            Place::new(total_offset_tmp),
            Rvalue::BinaryOp(
                BinOp::SubWrap,
                Operand::Copy(Place::new(target_addr_tmp)),
                Operand::Copy(Place::new(base_addr_tmp)),
            ),
        ));

        // 4. Take NLL borrow `Rvalue::Ref { mutable: want_mut, place: base_place }` of the enclosing struct
        // and derive the resolved pointer via `BinOp::AddWrap` (byte-offset GEP).
        let base_borrow_ptr_ty = self.compiler.intern_type(Type::Ptr {
            mutable: want_mut,
            pointee: base_ty,
        });
        let base_borrow_ptr_tmp = self.alloc_temp(base_borrow_ptr_ty);
        self.emit(Statement::Assign(
            Place::new(base_borrow_ptr_tmp),
            Rvalue::Ref {
                mutable: want_mut,
                place: base_place,
            },
        ));

        match rel_kind {
            RelFieldKind::Elem(elem_ty) => {
                let target_ptr_ty = self.compiler.intern_type(Type::Ptr {
                    mutable: want_mut,
                    pointee: elem_ty,
                });
                let target_ptr_tmp = self.alloc_temp(target_ptr_ty);
                self.emit(Statement::Assign(
                    Place::new(target_ptr_tmp),
                    Rvalue::BinaryOp(
                        BinOp::AddWrap,
                        Operand::Copy(Place::new(base_borrow_ptr_tmp)),
                        Operand::Copy(Place::new(total_offset_tmp)),
                    ),
                ));
                Ok((Place::new(target_ptr_tmp), target_ptr_ty))
            }
            RelFieldKind::Slice(_) | RelFieldKind::Str => {
                let slice_ty = match rel_kind {
                    RelFieldKind::Slice(elem) => self.compiler.intern_slice_type(want_mut, elem),
                    RelFieldKind::Str => self.compiler.intern_str_type(),
                    RelFieldKind::Elem(_) => unreachable!(),
                };
                let slice_info = self.compiler.slices[&slice_ty];
                let data_ptr_tmp = self.alloc_temp(slice_info.ptr_ty);
                self.emit(Statement::Assign(
                    Place::new(data_ptr_tmp),
                    Rvalue::BinaryOp(
                        BinOp::AddWrap,
                        Operand::Copy(Place::new(base_borrow_ptr_tmp)),
                        Operand::Copy(Place::new(total_offset_tmp)),
                    ),
                ));
                let len_tmp = len_tmp_opt.unwrap();
                let slice_tmp = self.alloc_temp(slice_ty);
                self.emit(Statement::Assign(
                    Place::new(slice_tmp),
                    Rvalue::Aggregate(
                        slice_ty,
                        vec![
                            Operand::Copy(Place::new(data_ptr_tmp)),
                            Operand::Copy(Place::new(len_tmp)),
                        ],
                    ),
                ));
                Ok((Place::new(slice_tmp), slice_ty))
            }
        }
    }

    fn lower_default_for_type(&mut self, ty_id: TypeId) -> Result<(Operand, TypeId), String> {
        if let Some(comp) = self.compiler.composites.get(&ty_id).cloned() {
            if let Some(def_fn) = comp.default_fn {
                let dst = self.alloc_temp(ty_id);
                let next_bb = self.new_block();
                self.terminate(Terminator::Call {
                    func: Operand::Const(ConstValue::Func(def_fn)),
                    args: vec![],
                    destination: Place::new(dst),
                    target: next_bb,
                });
                self.cur_block = next_bb;
                return Ok((Operand::Move(Place::new(dst)), ty_id));
            } else if comp.is_struct {
                return Err(format!(
                    "Struct '{}' does not implement a `default()` hook",
                    comp.name
                ));
            } else {
                // Record auto-synthesizes default from field defaults or field `@default`
                let mut f_ops = Vec::with_capacity(comp.fields.len());
                for (_, f_ty, _, f_def) in &comp.fields {
                    if let Some(def_expr) = f_def {
                        let (op, _) = self.lower_expr(def_expr, Some(*f_ty))?;
                        f_ops.push(op);
                    } else {
                        let (op, _) = self.lower_default_for_type(*f_ty)?;
                        f_ops.push(op);
                    }
                }
                let dst = self.alloc_temp(ty_id);
                self.emit(Statement::Assign(
                    Place::new(dst),
                    Rvalue::Aggregate(ty_id, f_ops),
                ));
                return Ok((Operand::Move(Place::new(dst)), ty_id));
            }
        }

        match self.compiler.program.types[ty_id.0 as usize].clone() {
            Type::Bool => Ok((Operand::Const(ConstValue::Bool(false)), ty_id)),
            Type::Int { .. } | Type::Rune => Ok((Operand::Const(ConstValue::I64(0)), ty_id)),
            Type::F32 | Type::F64 => Ok((Operand::Const(ConstValue::F64(0)), ty_id)),
            Type::Struct(fields) => {
                let mut ops = Vec::with_capacity(fields.len());
                for f in fields {
                    let (op, _) = self.lower_default_for_type(f)?;
                    ops.push(op);
                }
                let dst = self.alloc_temp(ty_id);
                self.emit(Statement::Assign(
                    Place::new(dst),
                    Rvalue::Aggregate(ty_id, ops),
                ));
                Ok((Operand::Move(Place::new(dst)), ty_id))
            }
            Type::Array { elem, len } | Type::Simd { elem, len } => {
                let mut ops = Vec::with_capacity(len as usize);
                for _ in 0..len {
                    let (op, _) = self.lower_default_for_type(elem)?;
                    ops.push(op);
                }
                let dst = self.alloc_temp(ty_id);
                self.emit(Statement::Assign(
                    Place::new(dst),
                    Rvalue::Aggregate(ty_id, ops),
                ));
                Ok((Operand::Move(Place::new(dst)), ty_id))
            }
            Type::Union { variants, .. }
                if !variants.is_empty()
                    && matches!(
                        self.compiler.program.types[variants[0].0 as usize],
                        Type::Void
                    ) =>
            {
                let dst = self.alloc_temp(ty_id);
                self.emit(Statement::Assign(
                    Place::new(dst),
                    Rvalue::Union {
                        ty: ty_id,
                        variant: 0,
                        payload: Operand::Const(ConstValue::Void),
                    },
                ));
                Ok((Operand::Move(Place::new(dst)), ty_id))
            }
            _ => Err(format!("Type {ty_id} does not support `@default`")),
        }
    }

    fn lower_clone_for_place(
        &mut self,
        place: Place,
        ty_id: TypeId,
    ) -> Result<(Operand, TypeId), String> {
        if let Some(comp) = self.compiler.composites.get(&ty_id).cloned() {
            if let Some(clone_fn) = comp.clone_fn {
                let ref_ty = self.compiler.intern_type(Type::Ptr {
                    mutable: false,
                    pointee: ty_id,
                });
                let ref_tmp = self.alloc_temp(ref_ty);
                self.emit(Statement::Assign(
                    Place::new(ref_tmp),
                    Rvalue::Ref {
                        mutable: false,
                        place,
                    },
                ));
                let dst = self.alloc_temp(ty_id);
                let next_bb = self.new_block();
                self.terminate(Terminator::Call {
                    func: Operand::Const(ConstValue::Func(clone_fn)),
                    args: vec![Operand::Copy(Place::new(ref_tmp))],
                    destination: Place::new(dst),
                    target: next_bb,
                });
                self.cur_block = next_bb;
                return Ok((Operand::Move(Place::new(dst)), ty_id));
            } else if comp.is_struct {
                if comp.ownership != StructOwnership::Copy {
                    return Err(format!(
                        "Struct '{}' does not implement `clone`",
                        comp.name
                    ));
                }
            } else {
                // Record structural clone
                let mut ops = Vec::with_capacity(comp.fields.len());
                for (idx, (_, f_ty, _, _)) in comp.fields.iter().enumerate() {
                    let mut fp = place.clone();
                    fp.projections.push(Projection::Field(idx as u32));
                    let (f_op, _) = self.lower_clone_for_place(fp, *f_ty)?;
                    ops.push(f_op);
                }
                let dst = self.alloc_temp(ty_id);
                self.emit(Statement::Assign(
                    Place::new(dst),
                    Rvalue::Aggregate(ty_id, ops),
                ));
                return Ok((Operand::Move(Place::new(dst)), ty_id));
            }
        }
        if self.is_copy_type(ty_id) {
            let dst = self.alloc_temp(ty_id);
            self.emit(Statement::Assign(
                Place::new(dst),
                Rvalue::Use(Operand::Copy(place)),
            ));
            Ok((Operand::Copy(Place::new(dst)), ty_id))
        } else {
            Err(format!("Type {ty_id} is not clonable"))
        }
    }

    fn lower_format_str(&mut self, segments: &[FmtSegment]) -> Result<(Operand, TypeId), String> {
        let mut ref_field_tys = Vec::new();
        let mut ref_field_ops = Vec::new();
        let mut interp_meta: Vec<(u32, TypeId, String)> = Vec::new();

        for seg in segments {
            if let FmtSegment::Interp { expr, spec } = seg {
                let (place, val_ty) = if matches!(expr, Expr::Str(_)) {
                    let str_ty = self.compiler.intern_str_type();
                    let (op, src_ty) = self.lower_expr(expr, Some(str_ty))?;
                    let coerced = self.coerce_operand(op, src_ty, str_ty)?;
                    let tmp = self.alloc_temp(str_ty);
                    self.emit(Statement::Assign(Place::new(tmp), Rvalue::Use(coerced)));
                    (Place::new(tmp), str_ty)
                } else {
                    self.lower_place(expr, false)?
                };

                if !self.compiler.is_format_type(val_ty) {
                    let mut inner_ty = val_ty;
                    while let Type::Ptr { pointee, .. } =
                        self.compiler.program.types[inner_ty.0 as usize]
                    {
                        if self.compiler.raw_ptrs.contains_key(&inner_ty)
                            || self.compiler.slices.contains_key(&inner_ty)
                        {
                            break;
                        }
                        inner_ty = pointee;
                    }
                    if let Some(comp) = self.compiler.composites.get(&inner_ty)
                        && comp.is_struct
                    {
                        return Err(format!(
                            "Struct '{}' does not define a 'format' hook; only transparent types or structs with a 'format' hook can be formatted",
                            comp.name
                        ));
                    }
                    return Err(format!(
                        "Type '{}' cannot be formatted",
                        self.compiler.program.types[val_ty.0 as usize]
                    ));
                }

                let ref_ty = self.compiler.intern_type(Type::Ptr {
                    mutable: false,
                    pointee: val_ty,
                });
                let ref_tmp = self.alloc_temp(ref_ty);
                self.emit(Statement::Assign(
                    Place::new(ref_tmp),
                    Rvalue::Ref {
                        mutable: false,
                        place,
                    },
                ));
                let field_idx = ref_field_tys.len() as u32;
                ref_field_tys.push(ref_ty);
                ref_field_ops.push(Operand::Copy(Place::new(ref_tmp)));
                interp_meta.push((field_idx, val_ty, spec.clone()));
            }
        }

        let fmt_struct_ty = self
            .compiler
            .alloc_distinct_type(Type::Struct(ref_field_tys.clone()));
        let self_ref_ty = self.compiler.intern_type(Type::Ptr {
            mutable: false,
            pointee: fmt_struct_ty,
        });
        let formatter_ty = self.compiler.resolve_named_type("core::fmt", "Formatter")?;
        let formatter_mut_ref_ty = self.compiler.intern_type(Type::Ptr {
            mutable: true,
            pointee: formatter_ty,
        });
        let void_ty = self.compiler.intern_type(Type::Void);

        let fmt_fn_id = self.compiler.reserve_function(
            Visibility::Private,
            None,
            &[self_ref_ty, formatter_mut_ref_ty],
            void_ty,
        );

        let mut field_infos = Vec::with_capacity(ref_field_tys.len());
        for (i, &fty) in ref_field_tys.iter().enumerate() {
            field_infos.push((format!("arg{i}"), fty, Visibility::Private, None));
        }

        self.compiler.composites.insert(
            fmt_struct_ty,
            CompositeInfo {
                name: format!("<fmt_str_{}>", fmt_fn_id.0),
                is_struct: true,
                ownership: StructOwnership::Copy,
                is_sync: false,
                has_format_hook: true,
                def_module: self.mod_path.clone(),
                comptime_env: HashMap::new(),
                fields: field_infos,
                rel_fields: HashMap::new(),
                methods: HashMap::new(),
                method_fn_ids: HashMap::new(),
                default_fn: None,
                clone_fn: None,
                drop_fn: None,
                format_fn: Some((fmt_fn_id, false)),
            },
        );

        // Synthesize body of `fmt_fn_id(self: &FmtStruct, f: &mut Formatter)`
        let dummy_decl = FuncDecl {
            vis: Visibility::Private,
            name: format!("<fmt_str_{}::format>", fmt_fn_id.0),
            params: Vec::new(),
            ret_ty: TypeExpr::Void,
            borrows: None,
            where_clauses: Vec::new(),
            body: Block { stmts: Vec::new() },
        };
        let mut sub = FuncLowerer::new(
            self.compiler,
            PendingFunc {
                func_id: fmt_fn_id,
                module_path: self.mod_path.clone(),
                owner_ty: Some(fmt_struct_ty),
                decl: dummy_decl,
                comptime_env: HashMap::new(),
                closure_captures: Vec::new(),
            },
        );
        let fmt_ref_op = Operand::Copy(Place::new(LocalId(2)));
        let mut interp_cursor = 0usize;
        for seg in segments {
            match seg {
                FmtSegment::Lit(s) => {
                    sub.call_formatter_write_str(fmt_ref_op.clone(), s)?;
                }
                FmtSegment::Interp { .. } => {
                    let (f_idx, val_ty, ref spec) = interp_meta[interp_cursor];
                    interp_cursor += 1;
                    let mut arg_place = Place::new(LocalId(1));
                    arg_place.projections.push(Projection::Deref);
                    arg_place.projections.push(Projection::Field(f_idx));
                    arg_place.projections.push(Projection::Deref);
                    sub.emit_format_place(fmt_ref_op.clone(), arg_place, val_ty, spec)?;
                }
            }
        }
        sub.emit(Statement::Assign(
            Place::new(LocalId(0)),
            Rvalue::Use(Operand::Const(ConstValue::Void)),
        ));
        sub.terminate(Terminator::Return);
        let func = sub
            .compiler
            .program
            .functions
            .iter_mut()
            .find(|f| f.id == fmt_fn_id)
            .unwrap();
        func.locals = sub.locals;
        func.blocks = sub.blocks;

        let dst = self.alloc_temp(fmt_struct_ty);
        self.emit(Statement::Assign(
            Place::new(dst),
            Rvalue::Aggregate(fmt_struct_ty, ref_field_ops),
        ));
        Ok((Operand::Copy(Place::new(dst)), fmt_struct_ty))
    }

    fn call_formatter_method(
        &mut self,
        method_name: &str,
        fmt_ref_op: Operand,
        extra_args: Vec<Operand>,
    ) -> Result<(), String> {
        let formatter_ty = self.compiler.resolve_named_type("core::fmt", "Formatter")?;
        let fn_id = self.compiler.composites[&formatter_ty].method_fn_ids[method_name];
        let void_ty = self.compiler.intern_type(Type::Void);
        let dst = self.alloc_temp(void_ty);
        let mut args = Vec::with_capacity(extra_args.len() + 1);
        args.push(fmt_ref_op);
        args.extend(extra_args);
        let next_bb = self.new_block();
        self.terminate(Terminator::Call {
            func: Operand::Const(ConstValue::Func(fn_id)),
            args,
            destination: Place::new(dst),
            target: next_bb,
        });
        self.cur_block = next_bb;
        Ok(())
    }

    fn call_formatter_write_str(&mut self, fmt_ref_op: Operand, s: &str) -> Result<(), String> {
        if s.is_empty() {
            return Ok(());
        }
        let u8_ty = self.compiler.intern_type(Type::Int {
            signed: false,
            bits: 8,
        });
        let ptr_u8_ty = self.compiler.intern_type(Type::Ptr {
            mutable: false,
            pointee: u8_ty,
        });
        let str_ty = self.compiler.intern_str_type();
        let str_op = Operand::Const(ConstValue::Str(s.to_string()));
        let slice_op = self.coerce_operand(str_op, ptr_u8_ty, str_ty)?;
        self.call_formatter_method("write_str", fmt_ref_op, vec![slice_op])
    }

    fn parse_int_format_spec(spec: &str) -> Result<(u64, bool, usize, bool), String> {
        if spec.is_empty() || spec == "?" || spec == "d" {
            return Ok((10, false, 0, false));
        }
        let bytes = spec.as_bytes();
        let mut pos = 0usize;
        let pad_zero = if bytes.get(pos) == Some(&b'0')
            && bytes.get(pos + 1).is_some_and(|b| b.is_ascii_digit())
        {
            pos += 1;
            true
        } else {
            false
        };
        let width_start = pos;
        while pos < bytes.len() && bytes[pos].is_ascii_digit() {
            pos += 1;
        }
        let min_width = if pos > width_start {
            spec[width_start..pos]
                .parse::<usize>()
                .map_err(|_| format!("Invalid width in format specifier '{spec}'"))?
        } else {
            0
        };
        let rest = &spec[pos..];
        match rest {
            "" | "d" | "?" => Ok((10, false, min_width, pad_zero)),
            "x" => Ok((16, false, min_width, pad_zero)),
            "X" => Ok((16, true, min_width, pad_zero)),
            "b" => Ok((2, false, min_width, pad_zero)),
            "o" => Ok((8, false, min_width, pad_zero)),
            _ => Err(format!("Unsupported integer format specifier '{spec}'")),
        }
    }

    fn parse_float_format_spec(spec: &str) -> Result<usize, String> {
        if spec.is_empty() || spec == "?" {
            return Ok(2);
        }
        if let Some(rest) = spec.strip_prefix('.')
            && let Ok(prec) = rest.parse::<usize>()
        {
            return Ok(prec);
        }
        Err(format!("Unsupported float format specifier '{spec}'"))
    }

    fn emit_format_place(
        &mut self,
        fmt_ref_op: Operand,
        mut place: Place,
        mut ty_id: TypeId,
        spec: &str,
    ) -> Result<(), String> {
        // Auto-dereference `&T` / `&mut T` references
        while !self.compiler.raw_ptrs.contains_key(&ty_id)
            && !self.compiler.slices.contains_key(&ty_id)
            && let Type::Ptr { pointee, .. } = self.compiler.program.types[ty_id.0 as usize]
        {
            place.projections.push(Projection::Deref);
            ty_id = pointee;
        }

        if let Type::Pattern { base, .. } = self.compiler.program.types[ty_id.0 as usize] {
            ty_id = base;
        }

        // 1. `struct` (`format` hook required) or `record` (auto-synthesized structural format)
        if let Some(comp) = self.compiler.composites.get(&ty_id).cloned() {
            if comp.is_struct {
                let Some((hook_fn_id, takes_spec)) = comp.format_fn else {
                    return Err(format!(
                        "Struct '{}' does not define a 'format' hook; only transparent types or structs with a 'format' hook can be formatted",
                        comp.name
                    ));
                };
                let self_ref_ty = self.compiler.intern_type(Type::Ptr {
                    mutable: false,
                    pointee: ty_id,
                });
                let self_ref_tmp = self.alloc_temp(self_ref_ty);
                self.emit(Statement::Assign(
                    Place::new(self_ref_tmp),
                    Rvalue::Ref {
                        mutable: false,
                        place,
                    },
                ));
                let mut call_args = vec![Operand::Copy(Place::new(self_ref_tmp)), fmt_ref_op];
                if takes_spec {
                    let u8_ty = self.compiler.intern_type(Type::Int {
                        signed: false,
                        bits: 8,
                    });
                    let ptr_u8_ty = self.compiler.intern_type(Type::Ptr {
                        mutable: false,
                        pointee: u8_ty,
                    });
                    let str_ty = self.compiler.intern_str_type();
                    let str_op = Operand::Const(ConstValue::Str(spec.to_string()));
                    let slice_op = self.coerce_operand(str_op, ptr_u8_ty, str_ty)?;
                    call_args.push(slice_op);
                }
                let void_ty = self.compiler.intern_type(Type::Void);
                let dst = self.alloc_temp(void_ty);
                let next_bb = self.new_block();
                self.terminate(Terminator::Call {
                    func: Operand::Const(ConstValue::Func(hook_fn_id)),
                    args: call_args,
                    destination: Place::new(dst),
                    target: next_bb,
                });
                self.cur_block = next_bb;
                return Ok(());
            } else {
                // Transparent `record`: `RecordName { f0: v0, f1: v1 }`
                if comp.fields.is_empty() {
                    return self
                        .call_formatter_write_str(fmt_ref_op, &format!("{} {{}}", comp.name));
                }
                self.call_formatter_write_str(fmt_ref_op.clone(), &format!("{} {{ ", comp.name))?;
                for (idx, (fname, f_ty, _, _)) in comp.fields.iter().enumerate() {
                    let prefix = if idx == 0 {
                        format!("{fname}: ")
                    } else {
                        format!(", {fname}: ")
                    };
                    self.call_formatter_write_str(fmt_ref_op.clone(), &prefix)?;
                    let mut fp = place.clone();
                    fp.projections.push(Projection::Field(idx as u32));
                    self.emit_format_place(fmt_ref_op.clone(), fp, *f_ty, "")?;
                }
                return self.call_formatter_write_str(fmt_ref_op, " }");
            }
        }

        // 2. `enum` (`EnumName::Variant`)
        if let Some((enum_name, variants)) = self.compiler.enums.get(&ty_id).cloned()
            && (spec.is_empty() || spec == "?")
        {
            let discr_op = Operand::Copy(place);
            let join_bb = self.new_block();
            let otherwise_bb = self.new_block();
            let mut targets = Vec::with_capacity(variants.len());
            let mut branch_bbs = Vec::with_capacity(variants.len());
            for (vname, vval) in &variants {
                let bb = self.new_block();
                targets.push((*vval, bb));
                branch_bbs.push((vname.clone(), bb));
            }
            self.terminate(Terminator::SwitchInt {
                discr: discr_op,
                targets,
                otherwise: otherwise_bb,
            });
            for (vname, bb) in branch_bbs {
                self.cur_block = bb;
                self.call_formatter_write_str(
                    fmt_ref_op.clone(),
                    &format!("{enum_name}::{vname}"),
                )?;
                self.terminate(Terminator::Goto { target: join_bb });
            }
            self.cur_block = otherwise_bb;
            self.call_formatter_write_str(fmt_ref_op, &format!("{enum_name}::?"))?;
            self.terminate(Terminator::Goto { target: join_bb });
            self.cur_block = join_bb;
            return Ok(());
        }

        // 2b. Error types (`ErrorName::Variant` or `ErrorName::Variant(payload)`)
        if let Some(err_info) = self.compiler.errors.get(&ty_id).cloned() {
            let Type::Union { tag, .. } = self.compiler.program.types[ty_id.0 as usize] else {
                return Err("Internal error: expected Type::Union for error type".to_string());
            };
            let discr_tmp = self.alloc_temp(tag);
            self.emit(Statement::Assign(
                Place::new(discr_tmp),
                Rvalue::Discriminant(place.clone()),
            ));
            let join_bb = self.new_block();
            let otherwise_bb = self.new_block();
            let mut targets = Vec::new();
            let mut branch_bbs = Vec::new();
            for (v_idx, leaf) in err_info.leaves.iter().enumerate() {
                let bb = self.new_block();
                targets.push((v_idx as i128, bb));
                branch_bbs.push((v_idx, leaf.clone(), bb));
            }
            self.terminate(Terminator::SwitchInt {
                discr: Operand::Copy(Place::new(discr_tmp)),
                targets,
                otherwise: otherwise_bb,
            });
            let void_ty = self.compiler.intern_type(Type::Void);
            for (v_idx, leaf, bb) in branch_bbs {
                self.cur_block = bb;
                let prefix = format!("{}::{}", leaf.key.error_name, leaf.key.variant_name);
                if leaf.payload_ty == void_ty {
                    self.call_formatter_write_str(fmt_ref_op.clone(), &prefix)?;
                } else {
                    self.call_formatter_write_str(fmt_ref_op.clone(), &format!("{prefix}("))?;
                    let mut vp = place.clone();
                    vp.projections.push(Projection::Variant(v_idx as u32));
                    self.emit_format_place(fmt_ref_op.clone(), vp, leaf.payload_ty, spec)?;
                    self.call_formatter_write_str(fmt_ref_op.clone(), ")")?;
                }
                self.terminate(Terminator::Goto { target: join_bb });
            }
            self.cur_block = otherwise_bb;
            self.call_formatter_write_str(fmt_ref_op, &format!("{}::?", err_info.name))?;
            self.terminate(Terminator::Goto { target: join_bb });
            self.cur_block = join_bb;
            return Ok(());
        }

        // 2c. Tagged unions (`UnionName::Variant` or `UnionName::Variant(payload)`)
        if let Some(u_info) = self.compiler.unions.get(&ty_id).cloned() {
            let Type::Union { tag, .. } = self.compiler.program.types[ty_id.0 as usize] else {
                return Err("Internal error: expected Type::Union for union type".to_string());
            };
            let discr_tmp = self.alloc_temp(tag);
            self.emit(Statement::Assign(
                Place::new(discr_tmp),
                Rvalue::Discriminant(place.clone()),
            ));
            let join_bb = self.new_block();
            let otherwise_bb = self.new_block();
            let mut targets = Vec::new();
            let mut branch_bbs = Vec::new();
            for (v_idx, (vname, v_ty)) in u_info.variants.iter().enumerate() {
                let bb = self.new_block();
                targets.push((v_idx as i128, bb));
                branch_bbs.push((v_idx, vname.clone(), *v_ty, bb));
            }
            self.terminate(Terminator::SwitchInt {
                discr: Operand::Copy(Place::new(discr_tmp)),
                targets,
                otherwise: otherwise_bb,
            });
            let void_ty = self.compiler.intern_type(Type::Void);
            for (v_idx, vname, v_ty, bb) in branch_bbs {
                self.cur_block = bb;
                let prefix = format!("{}::{vname}", u_info.name);
                if v_ty == void_ty {
                    self.call_formatter_write_str(fmt_ref_op.clone(), &prefix)?;
                } else {
                    self.call_formatter_write_str(fmt_ref_op.clone(), &format!("{prefix}("))?;
                    let mut vp = place.clone();
                    vp.projections.push(Projection::Variant(v_idx as u32));
                    self.emit_format_place(fmt_ref_op.clone(), vp, v_ty, spec)?;
                    self.call_formatter_write_str(fmt_ref_op.clone(), ")")?;
                }
                self.terminate(Terminator::Goto { target: join_bb });
            }
            self.cur_block = otherwise_bb;
            self.call_formatter_write_str(fmt_ref_op, &format!("{}::?", u_info.name))?;
            self.terminate(Terminator::Goto { target: join_bb });
            self.cur_block = join_bb;
            return Ok(());
        }

        // 2d. Result types (`E!T`)
        if let Some(res_info) = self.compiler.results.get(&ty_id).cloned() {
            let Type::Union { tag, .. } = self.compiler.program.types[ty_id.0 as usize] else {
                return Err("Internal error: expected Type::Union for result type".to_string());
            };
            let discr_tmp = self.alloc_temp(tag);
            self.emit(Statement::Assign(
                Place::new(discr_tmp),
                Rvalue::Discriminant(place.clone()),
            ));
            let ok_bb = self.new_block();
            let err_bb = self.new_block();
            let join_bb = self.new_block();
            self.terminate(Terminator::SwitchInt {
                discr: Operand::Copy(Place::new(discr_tmp)),
                targets: vec![(0, ok_bb)],
                otherwise: err_bb,
            });
            let void_ty = self.compiler.intern_type(Type::Void);

            self.cur_block = ok_bb;
            if res_info.ok_ty == void_ty {
                self.call_formatter_write_str(fmt_ref_op.clone(), "Ok(())")?;
            } else {
                self.call_formatter_write_str(fmt_ref_op.clone(), "Ok(")?;
                let mut ok_place = place.clone();
                ok_place.projections.push(Projection::Variant(0));
                self.emit_format_place(fmt_ref_op.clone(), ok_place, res_info.ok_ty, spec)?;
                self.call_formatter_write_str(fmt_ref_op.clone(), ")")?;
            }
            self.terminate(Terminator::Goto { target: join_bb });

            self.cur_block = err_bb;
            let mut err_place = place;
            err_place.projections.push(Projection::Variant(1));
            self.emit_format_place(fmt_ref_op, err_place, res_info.err_ty, spec)?;
            self.terminate(Terminator::Goto { target: join_bb });

            self.cur_block = join_bb;
            return Ok(());
        }

        // 3. `&str` or `&[T]` / `&mut [T]` slice
        if let Some(&slice_info) = self.compiler.slices.get(&ty_id) {
            if slice_info.is_str {
                let str_ty = self.compiler.intern_str_type();
                let s_op = self.coerce_operand(Operand::Copy(place), ty_id, str_ty)?;
                let method = if spec == "?" {
                    "write_quoted_str"
                } else {
                    "write_str"
                };
                return self.call_formatter_method(method, fmt_ref_op, vec![s_op]);
            } else {
                self.call_formatter_write_str(fmt_ref_op.clone(), "[")?;
                let usize_ty = self.compiler.intern_type(Type::Int {
                    signed: false,
                    bits: 64,
                });
                let bool_ty = self.compiler.intern_type(Type::Bool);
                let mut len_place = place.clone();
                len_place.projections.push(Projection::Field(1));
                let len_local = self.alloc_temp(usize_ty);
                self.emit(Statement::Assign(
                    Place::new(len_local),
                    Rvalue::Use(Operand::Copy(len_place)),
                ));
                let idx_local = self.alloc_temp(usize_ty);
                self.emit(Statement::Assign(
                    Place::new(idx_local),
                    Rvalue::Use(Operand::Const(ConstValue::I64(0))),
                ));
                let cond_bb = self.new_block();
                let body_bb = self.new_block();
                let exit_bb = self.new_block();
                self.terminate(Terminator::Goto { target: cond_bb });

                self.cur_block = cond_bb;
                let cmp_local = self.alloc_temp(bool_ty);
                self.emit(Statement::Assign(
                    Place::new(cmp_local),
                    Rvalue::BinaryOp(
                        BinOp::Lt,
                        Operand::Copy(Place::new(idx_local)),
                        Operand::Copy(Place::new(len_local)),
                    ),
                ));
                self.terminate(Terminator::SwitchInt {
                    discr: Operand::Copy(Place::new(cmp_local)),
                    targets: vec![(1, body_bb)],
                    otherwise: exit_bb,
                });

                self.cur_block = body_bb;
                let gt0_local = self.alloc_temp(bool_ty);
                self.emit(Statement::Assign(
                    Place::new(gt0_local),
                    Rvalue::BinaryOp(
                        BinOp::Gt,
                        Operand::Copy(Place::new(idx_local)),
                        Operand::Const(ConstValue::I64(0)),
                    ),
                ));
                let comma_bb = self.new_block();
                let elem_bb = self.new_block();
                self.terminate(Terminator::SwitchInt {
                    discr: Operand::Copy(Place::new(gt0_local)),
                    targets: vec![(1, comma_bb)],
                    otherwise: elem_bb,
                });

                self.cur_block = comma_bb;
                self.call_formatter_write_str(fmt_ref_op.clone(), ", ")?;
                self.terminate(Terminator::Goto { target: elem_bb });

                self.cur_block = elem_bb;
                let mut elem_place = place;
                elem_place.projections.push(Projection::Field(0));
                elem_place.projections.push(Projection::Deref);
                elem_place.projections.push(Projection::Index(idx_local));
                self.emit_format_place(fmt_ref_op.clone(), elem_place, slice_info.elem, spec)?;
                self.emit(Statement::Assign(
                    Place::new(idx_local),
                    Rvalue::BinaryOp(
                        BinOp::AddWrap,
                        Operand::Copy(Place::new(idx_local)),
                        Operand::Const(ConstValue::I64(1)),
                    ),
                ));
                self.terminate(Terminator::Goto { target: cond_bb });

                self.cur_block = exit_bb;
                return self.call_formatter_write_str(fmt_ref_op, "]");
            }
        }

        // 4. Primitives, Arrays, Tuples, Optionals
        match self.compiler.program.types[ty_id.0 as usize].clone() {
            Type::Bool => {
                self.call_formatter_method("write_bool", fmt_ref_op, vec![Operand::Copy(place)])
            }
            Type::Rune => {
                let quoted = Operand::Const(ConstValue::Bool(spec == "?"));
                self.call_formatter_method(
                    "write_rune",
                    fmt_ref_op,
                    vec![Operand::Copy(place), quoted],
                )
            }
            Type::Int { signed, bits } => {
                let (radix, uppercase, min_width, pad_zero) = Self::parse_int_format_spec(spec)?;
                let is_signed_dec = signed && radix == 10;
                let i64_ty = self.compiler.intern_type(Type::Int {
                    signed: true,
                    bits: 64,
                });
                let u64_ty = self.compiler.intern_type(Type::Int {
                    signed: false,
                    bits: 64,
                });
                let val_i64_op = if ty_id == i64_ty {
                    Operand::Copy(place)
                } else if !is_signed_dec && signed && bits < 64 {
                    // Zero-extend signed sub-64-bit integer when formatting as hex/bin/oct
                    let unsigned_same_ty = self.compiler.intern_type(Type::Int {
                        signed: false,
                        bits,
                    });
                    let u_tmp = self.alloc_temp(unsigned_same_ty);
                    self.emit(Statement::Assign(
                        Place::new(u_tmp),
                        Rvalue::Cast(Operand::Copy(place), unsigned_same_ty),
                    ));
                    let u64_tmp = self.alloc_temp(u64_ty);
                    self.emit(Statement::Assign(
                        Place::new(u64_tmp),
                        Rvalue::Cast(Operand::Copy(Place::new(u_tmp)), u64_ty),
                    ));
                    let i64_tmp = self.alloc_temp(i64_ty);
                    self.emit(Statement::Assign(
                        Place::new(i64_tmp),
                        Rvalue::Cast(Operand::Copy(Place::new(u64_tmp)), i64_ty),
                    ));
                    Operand::Copy(Place::new(i64_tmp))
                } else {
                    let i64_tmp = self.alloc_temp(i64_ty);
                    self.emit(Statement::Assign(
                        Place::new(i64_tmp),
                        Rvalue::Cast(Operand::Copy(place), i64_ty),
                    ));
                    Operand::Copy(Place::new(i64_tmp))
                };
                self.call_formatter_method(
                    "write_int",
                    fmt_ref_op,
                    vec![
                        val_i64_op,
                        Operand::Const(ConstValue::Bool(is_signed_dec)),
                        Operand::Const(ConstValue::I64(radix as i128)),
                        Operand::Const(ConstValue::Bool(uppercase)),
                        Operand::Const(ConstValue::I64(min_width as i128)),
                        Operand::Const(ConstValue::Bool(pad_zero)),
                    ],
                )
            }
            Type::F32 | Type::F64 => {
                let prec = Self::parse_float_format_spec(spec)?;
                let f64_ty = self.compiler.intern_type(Type::F64);
                let val_f64_op = if ty_id == f64_ty {
                    Operand::Copy(place)
                } else {
                    let tmp = self.alloc_temp(f64_ty);
                    self.emit(Statement::Assign(
                        Place::new(tmp),
                        Rvalue::Cast(Operand::Copy(place), f64_ty),
                    ));
                    Operand::Copy(Place::new(tmp))
                };
                self.call_formatter_method(
                    "write_f64",
                    fmt_ref_op,
                    vec![val_f64_op, Operand::Const(ConstValue::I64(prec as i128))],
                )
            }
            Type::Array { elem, len } => {
                self.call_formatter_write_str(fmt_ref_op.clone(), "[")?;
                let usize_ty = self.compiler.intern_type(Type::Int {
                    signed: false,
                    bits: 64,
                });
                for i in 0..len {
                    if i > 0 {
                        self.call_formatter_write_str(fmt_ref_op.clone(), ", ")?;
                    }
                    let idx_tmp = self.alloc_temp(usize_ty);
                    self.emit(Statement::Assign(
                        Place::new(idx_tmp),
                        Rvalue::Use(Operand::Const(ConstValue::I64(i as i128))),
                    ));
                    let mut ep = place.clone();
                    ep.projections.push(Projection::Index(idx_tmp));
                    self.emit_format_place(fmt_ref_op.clone(), ep, elem, spec)?;
                }
                self.call_formatter_write_str(fmt_ref_op, "]")
            }
            Type::Struct(field_tys) => {
                if field_tys.is_empty() {
                    return self.call_formatter_write_str(fmt_ref_op, "{}");
                }
                self.call_formatter_write_str(fmt_ref_op.clone(), "{ ")?;
                for (idx, f_ty) in field_tys.into_iter().enumerate() {
                    if idx > 0 {
                        self.call_formatter_write_str(fmt_ref_op.clone(), ", ")?;
                    }
                    let mut fp = place.clone();
                    fp.projections.push(Projection::Field(idx as u32));
                    self.emit_format_place(fmt_ref_op.clone(), fp, f_ty, "")?;
                }
                self.call_formatter_write_str(fmt_ref_op, " }")
            }
            Type::Union { tag, variants }
                if variants.len() == 2
                    && matches!(
                        self.compiler.program.types[variants[0].0 as usize],
                        Type::Void
                    ) =>
            {
                let discr_tmp = self.alloc_temp(tag);
                self.emit(Statement::Assign(
                    Place::new(discr_tmp),
                    Rvalue::Discriminant(place.clone()),
                ));
                let some_bb = self.new_block();
                let none_bb = self.new_block();
                let join_bb = self.new_block();
                self.terminate(Terminator::SwitchInt {
                    discr: Operand::Copy(Place::new(discr_tmp)),
                    targets: vec![(1, some_bb)],
                    otherwise: none_bb,
                });

                self.cur_block = none_bb;
                self.call_formatter_write_str(fmt_ref_op.clone(), "null")?;
                self.terminate(Terminator::Goto { target: join_bb });

                self.cur_block = some_bb;
                let mut payload_place = place;
                payload_place.projections.push(Projection::Variant(1));
                self.emit_format_place(fmt_ref_op, payload_place, variants[1], spec)?;
                self.terminate(Terminator::Goto { target: join_bb });

                self.cur_block = join_bb;
                Ok(())
            }
            other => Err(format!("Type '{other}' cannot be formatted")),
        }
    }

    fn root_var_of_place_expr(expr: &Expr) -> Option<&str> {
        match expr {
            Expr::Path(p) if p.len() == 1 => Some(&p[0]),
            Expr::Deref(inner)
            | Expr::Field { base: inner, .. }
            | Expr::TupleIndex { base: inner, .. }
            | Expr::Index { base: inner, .. }
            | Expr::Slice { base: inner, .. } => Self::root_var_of_place_expr(inner),
            _ => None,
        }
    }

    fn method_requires_mut_self(&self, var_name: &str, method_name: &str) -> bool {
        let Some(mut ty_id) = self
            .lookup_var(var_name)
            .map(|(_, t)| t)
            .or_else(|| self.lookup_capture(var_name).map(|(_, t)| t))
        else {
            return false;
        };
        if let Type::Ptr { pointee, .. } = self.compiler.program.types[ty_id.0 as usize] {
            ty_id = pointee;
        }
        if let Some(comp) = self.compiler.composites.get(&ty_id)
            && let Some((_, mdecl)) = comp.methods.get(method_name)
            && let Some(first_rt) = mdecl.params.iter().find(|p| !p.is_comptime)
        {
            return matches!(first_rt.ty, TypeExpr::Ref { mutable: true, .. });
        }
        if let Ok(cands) = self
            .compiler
            .find_in_scope_functions(&self.mod_path, method_name)
        {
            for (_, _, decl) in cands {
                if let Some(first_rt) = decl.params.iter().find(|p| !p.is_comptime)
                    && first_rt.name == "self"
                    && matches!(first_rt.ty, TypeExpr::Ref { mutable: true, .. })
                {
                    return true;
                }
            }
        }
        false
    }

    fn record_capture(
        &self,
        name: &str,
        needs_mut: bool,
        bound: &std::collections::HashSet<String>,
        captures: &mut Vec<(String, bool)>,
    ) {
        if bound.contains(name) {
            return;
        }
        if self.lookup_var(name).is_none() && self.lookup_capture(name).is_none() {
            return;
        }
        if let Some((_, existing_mut)) = captures.iter_mut().find(|(n, _)| n == name) {
            *existing_mut |= needs_mut;
        } else {
            captures.push((name.to_string(), needs_mut));
        }
    }

    fn collect_captures_in_block(
        &self,
        block: &Block,
        bound: &std::collections::HashSet<String>,
        captures: &mut Vec<(String, bool)>,
    ) {
        let mut local_bound = bound.clone();
        for stmt in &block.stmts {
            match stmt {
                Stmt::Let { name, init, .. } => {
                    self.collect_captures_in_expr(init, &local_bound, captures);
                    local_bound.insert(name.clone());
                }
                Stmt::Assign { target, value, .. } => {
                    if let Some(root) = Self::root_var_of_place_expr(target) {
                        self.record_capture(root, true, &local_bound, captures);
                    }
                    self.collect_captures_in_expr(target, &local_bound, captures);
                    self.collect_captures_in_expr(value, &local_bound, captures);
                }
                Stmt::If {
                    cond,
                    then_block,
                    else_block,
                } => {
                    self.collect_captures_in_expr(cond, &local_bound, captures);
                    self.collect_captures_in_block(then_block, &local_bound, captures);
                    if let Some(eb) = else_block {
                        self.collect_captures_in_block(eb, &local_bound, captures);
                    }
                }
                Stmt::IfLet {
                    var_name,
                    opt_expr,
                    then_block,
                    else_block,
                } => {
                    self.collect_captures_in_expr(opt_expr, &local_bound, captures);
                    let mut then_bound = local_bound.clone();
                    then_bound.insert(var_name.clone());
                    self.collect_captures_in_block(then_block, &then_bound, captures);
                    if let Some(eb) = else_block {
                        self.collect_captures_in_block(eb, &local_bound, captures);
                    }
                }
                Stmt::While { cond, body } => {
                    self.collect_captures_in_expr(cond, &local_bound, captures);
                    self.collect_captures_in_block(body, &local_bound, captures);
                }
                Stmt::Return(opt_e) => {
                    if let Some(e) = opt_e {
                        self.collect_captures_in_expr(e, &local_bound, captures);
                    }
                }
                Stmt::Unsafe(blk) => {
                    self.collect_captures_in_block(blk, &local_bound, captures);
                }
                Stmt::Match { scrutinee, arms } => {
                    self.collect_captures_in_expr(scrutinee, &local_bound, captures);
                    for (pat, body) in arms {
                        let mut arm_bound = local_bound.clone();
                        if let MatchPat::Variant {
                            binding: Some((_, b)),
                            ..
                        } = pat
                        {
                            arm_bound.insert(b.clone());
                        }
                        self.collect_captures_in_expr(body, &arm_bound, captures);
                    }
                }
                Stmt::Expr(e) => {
                    self.collect_captures_in_expr(e, &local_bound, captures);
                }
            }
        }
    }

    fn collect_captures_in_expr(
        &self,
        expr: &Expr,
        bound: &std::collections::HashSet<String>,
        captures: &mut Vec<(String, bool)>,
    ) {
        match expr {
            Expr::Int(_)
            | Expr::Float(_)
            | Expr::Bool(_)
            | Expr::Rune(_)
            | Expr::Str(_)
            | Expr::Null
            | Expr::TypeVal(_)
            | Expr::IntrinsicDefault(_)
            | Expr::IntrinsicTrap => {}
            Expr::Path(p) => {
                if p.len() == 1 {
                    self.record_capture(&p[0], false, bound, captures);
                }
            }
            Expr::Move(inner)
            | Expr::RelRef(inner)
            | Expr::Deref(inner)
            | Expr::Field { base: inner, .. }
            | Expr::TupleIndex { base: inner, .. }
            | Expr::Unary { expr: inner, .. }
            | Expr::Cast { expr: inner, .. }
            | Expr::IntrinsicClone(inner)
            | Expr::IntrinsicDrop(inner)
            | Expr::Try(inner) => {
                self.collect_captures_in_expr(inner, bound, captures);
            }
            Expr::Catch {
                expr: inner,
                err_binding,
                fallback,
            } => {
                self.collect_captures_in_expr(inner, bound, captures);
                let mut h_bound = bound.clone();
                if let Some(en) = err_binding {
                    h_bound.insert(en.clone());
                }
                self.collect_captures_in_expr(fallback, &h_bound, captures);
            }
            Expr::Match { scrutinee, arms } => {
                self.collect_captures_in_expr(scrutinee, bound, captures);
                for (pat, body) in arms {
                    let mut arm_bound = bound.clone();
                    if let MatchPat::Variant {
                        binding: Some((_, b)),
                        ..
                    } = pat
                    {
                        arm_bound.insert(b.clone());
                    }
                    self.collect_captures_in_expr(body, &arm_bound, captures);
                }
            }
            Expr::Block(blk) => {
                self.collect_captures_in_block(blk, bound, captures);
            }
            Expr::IntrinsicFormat {
                formatter, value, ..
            } => {
                self.collect_captures_in_expr(formatter, bound, captures);
                self.collect_captures_in_expr(value, bound, captures);
            }
            Expr::FormatStr(segments) => {
                for seg in segments {
                    if let FmtSegment::Interp { expr, .. } = seg {
                        self.collect_captures_in_expr(expr, bound, captures);
                    }
                }
            }
            Expr::Index { base, index } => {
                self.collect_captures_in_expr(base, bound, captures);
                self.collect_captures_in_expr(index, bound, captures);
            }
            Expr::Slice { base, start, end } => {
                self.collect_captures_in_expr(base, bound, captures);
                self.collect_captures_in_expr(start, bound, captures);
                self.collect_captures_in_expr(end, bound, captures);
            }
            Expr::Ref { mutable, expr: inner } => {
                if *mutable
                    && let Some(root) = Self::root_var_of_place_expr(inner)
                {
                    self.record_capture(root, true, bound, captures);
                }
                self.collect_captures_in_expr(inner, bound, captures);
            }
            Expr::Binary { lhs, rhs, .. }
            | Expr::LogicalAnd(lhs, rhs)
            | Expr::LogicalOr(lhs, rhs)
            | Expr::OrElse {
                opt: lhs,
                fallback: rhs,
            } => {
                self.collect_captures_in_expr(lhs, bound, captures);
                self.collect_captures_in_expr(rhs, bound, captures);
            }
            Expr::TupleLit(elems) | Expr::SimdLit { elems, .. } => {
                for e in elems {
                    self.collect_captures_in_expr(e, bound, captures);
                }
            }
            Expr::StructLit { fields, .. } => {
                for (_, e) in fields {
                    self.collect_captures_in_expr(e, bound, captures);
                }
            }
            Expr::Return(opt_e) => {
                if let Some(e) = opt_e {
                    self.collect_captures_in_expr(e, bound, captures);
                }
            }
            Expr::UnsafeBlock(blk) => {
                self.collect_captures_in_block(blk, bound, captures);
            }
            Expr::Lambda { params, body, .. } => {
                let mut inner_bound = bound.clone();
                for (_, pname, _) in params {
                    inner_bound.insert(pname.clone());
                }
                self.collect_captures_in_block(body, &inner_bound, captures);
            }
            Expr::Call { callee, args } => {
                if let Expr::Path(p) = callee.as_ref()
                    && p.len() == 1
                    && let Some(ty_id) = self
                        .lookup_var(&p[0])
                        .map(|(_, t)| t)
                        .or_else(|| self.lookup_capture(&p[0]).map(|(_, t)| t))
                    && self
                        .compiler
                        .closures
                        .get(&ty_id)
                        .is_some_and(|c| c.env_mut)
                {
                    self.record_capture(&p[0], true, bound, captures);
                }
                self.collect_captures_in_expr(callee, bound, captures);
                for a in args {
                    self.collect_captures_in_expr(a, bound, captures);
                }
            }
            Expr::MethodCall {
                receiver,
                method,
                args,
            } => {
                if let Some(root) = Self::root_var_of_place_expr(receiver)
                    && self.method_requires_mut_self(root, method)
                {
                    self.record_capture(root, true, bound, captures);
                }
                self.collect_captures_in_expr(receiver, bound, captures);
                for a in args {
                    self.collect_captures_in_expr(a, bound, captures);
                }
            }
        }
    }

    fn lower_call(&mut self, callee: &Expr, args: &[Expr]) -> Result<(Operand, TypeId), String> {
        let Expr::Path(path) = callee else {
            let (callee_op, callee_ty) = self.lower_expr(callee, None)?;
            if let Type::FnPtr {
                args: param_tys,
                ret: ret_ty,
            } = self.compiler.program.types[callee_ty.0 as usize].clone()
            {
                let mut lowered_args = Vec::with_capacity(args.len());
                for (i, arg) in args.iter().enumerate() {
                    let exp = param_tys.get(i).copied();
                    let (op, a_ty) = self.lower_expr(arg, exp)?;
                    let coerced = if let Some(pt) = exp {
                        self.coerce_operand(op, a_ty, pt)?
                    } else {
                        op
                    };
                    lowered_args.push(coerced);
                }
                let dst = self.alloc_temp(ret_ty);
                let next_bb = self.new_block();
                self.terminate(Terminator::Call {
                    func: callee_op,
                    args: lowered_args,
                    destination: Place::new(dst),
                    target: next_bb,
                });
                self.cur_block = next_bb;
                if matches!(self.compiler.program.types[ret_ty.0 as usize], Type::Never) {
                    self.terminate(Terminator::Unreachable);
                }
                return Ok((Operand::Move(Place::new(dst)), ret_ty));
            }
            if let Some(closure_info) = self.compiler.closures.get(&callee_ty).cloned() {
                let first_arg = if closure_info.env_by_val {
                    callee_op
                } else {
                    let env_local = self.alloc_temp(callee_ty);
                    self.emit(Statement::Assign(
                        Place::new(env_local),
                        Rvalue::Use(callee_op),
                    ));
                    let env_ref_ty = self.compiler.intern_type(Type::Ptr {
                        mutable: closure_info.env_mut,
                        pointee: callee_ty,
                    });
                    let env_ref_tmp = self.alloc_temp(env_ref_ty);
                    self.emit(Statement::Assign(
                        Place::new(env_ref_tmp),
                        Rvalue::Ref {
                            mutable: closure_info.env_mut,
                            place: Place::new(env_local),
                        },
                    ));
                    Operand::Copy(Place::new(env_ref_tmp))
                };
                let mut lowered_args = Vec::with_capacity(args.len() + 1);
                lowered_args.push(first_arg);
                for (i, arg) in args.iter().enumerate() {
                    let exp = closure_info.param_tys.get(i).copied();
                    let (op, a_ty) = self.lower_expr(arg, exp)?;
                    let coerced = if let Some(pt) = exp {
                        self.coerce_operand(op, a_ty, pt)?
                    } else {
                        op
                    };
                    lowered_args.push(coerced);
                }
                let dst = self.alloc_temp(closure_info.ret_ty);
                let next_bb = self.new_block();
                self.terminate(Terminator::Call {
                    func: Operand::Const(ConstValue::Func(closure_info.call_fn_id)),
                    args: lowered_args,
                    destination: Place::new(dst),
                    target: next_bb,
                });
                self.cur_block = next_bb;
                if matches!(
                    self.compiler.program.types[closure_info.ret_ty.0 as usize],
                    Type::Never
                ) {
                    self.terminate(Terminator::Unreachable);
                }
                return Ok((Operand::Move(Place::new(dst)), closure_info.ret_ty));
            }
            return Err(format!("Unsupported callee expression {callee:?}"));
        };

        // Check if `callee` is a local or captured variable holding a function pointer (`fn(...) -> R`) or `closure`:
        if path.len() == 1
            && let Some((var_place, var_ty)) = self
                .lookup_var(&path[0])
                .map(|(l, t)| (Place::new(l), t))
                .or_else(|| self.lookup_capture(&path[0]))
        {
            let (deref_place, pointee_ty, is_ptr, ptr_mut) =
                if let Type::Ptr { mutable, pointee } =
                    self.compiler.program.types[var_ty.0 as usize]
                {
                    let mut dp = var_place.clone();
                    dp.projections.push(Projection::Deref);
                    (dp, pointee, true, mutable)
                } else {
                    (var_place.clone(), var_ty, false, true)
                };

            if let Type::FnPtr {
                args: param_tys,
                ret: ret_ty,
            } = self.compiler.program.types[pointee_ty.0 as usize].clone()
            {
                let mut lowered_args = Vec::with_capacity(args.len());
                for (i, arg) in args.iter().enumerate() {
                    let exp = param_tys.get(i).copied();
                    let (op, a_ty) = self.lower_expr(arg, exp)?;
                    let coerced = if let Some(pt) = exp {
                        self.coerce_operand(op, a_ty, pt)?
                    } else {
                        op
                    };
                    lowered_args.push(coerced);
                }
                let dst = self.alloc_temp(ret_ty);
                let next_bb = self.new_block();
                self.terminate(Terminator::Call {
                    func: Operand::Copy(deref_place),
                    args: lowered_args,
                    destination: Place::new(dst),
                    target: next_bb,
                });
                self.cur_block = next_bb;
                if matches!(self.compiler.program.types[ret_ty.0 as usize], Type::Never) {
                    self.terminate(Terminator::Unreachable);
                }
                return Ok((Operand::Move(Place::new(dst)), ret_ty));
            }

            if let Some(closure_info) = self.compiler.closures.get(&pointee_ty).cloned() {
                if closure_info.env_by_val {
                    if is_ptr {
                        return Err(format!(
                            "Cannot call single-use linear closure '{}' through a reference; it must be called by value",
                            path[0]
                        ));
                    }
                    let mut lowered_args = Vec::with_capacity(args.len() + 1);
                    lowered_args.push(Operand::Move(deref_place));
                    for (i, arg) in args.iter().enumerate() {
                        let exp = closure_info.param_tys.get(i).copied();
                        let (op, a_ty) = self.lower_expr(arg, exp)?;
                        let coerced = if let Some(pt) = exp {
                            self.coerce_operand(op, a_ty, pt)?
                        } else {
                            op
                        };
                        lowered_args.push(coerced);
                    }
                    let dst = self.alloc_temp(closure_info.ret_ty);
                    let next_bb = self.new_block();
                    self.terminate(Terminator::Call {
                        func: Operand::Const(ConstValue::Func(closure_info.call_fn_id)),
                        args: lowered_args,
                        destination: Place::new(dst),
                        target: next_bb,
                    });
                    self.cur_block = next_bb;
                    if matches!(
                        self.compiler.program.types[closure_info.ret_ty.0 as usize],
                        Type::Never
                    ) {
                        self.terminate(Terminator::Unreachable);
                    }
                    return Ok((Operand::Move(Place::new(dst)), closure_info.ret_ty));
                }
                if is_ptr && closure_info.env_mut && !ptr_mut {
                    return Err(format!(
                        "Cannot call mutating closure '{}' through an immutable reference",
                        path[0]
                    ));
                }
                let env_ref_ty = self.compiler.intern_type(Type::Ptr {
                    mutable: closure_info.env_mut,
                    pointee: pointee_ty,
                });
                let env_ref_tmp = self.alloc_temp(env_ref_ty);
                self.emit(Statement::Assign(
                    Place::new(env_ref_tmp),
                    Rvalue::Ref {
                        mutable: closure_info.env_mut,
                        place: deref_place,
                    },
                ));
                let mut lowered_args = Vec::with_capacity(args.len() + 1);
                lowered_args.push(Operand::Copy(Place::new(env_ref_tmp)));
                for (i, arg) in args.iter().enumerate() {
                    let exp = closure_info.param_tys.get(i).copied();
                    let (op, a_ty) = self.lower_expr(arg, exp)?;
                    let coerced = if let Some(pt) = exp {
                        self.coerce_operand(op, a_ty, pt)?
                    } else {
                        op
                    };
                    lowered_args.push(coerced);
                }
                let dst = self.alloc_temp(closure_info.ret_ty);
                let next_bb = self.new_block();
                self.terminate(Terminator::Call {
                    func: Operand::Const(ConstValue::Func(closure_info.call_fn_id)),
                    args: lowered_args,
                    destination: Place::new(dst),
                    target: next_bb,
                });
                self.cur_block = next_bb;
                if matches!(
                    self.compiler.program.types[closure_info.ret_ty.0 as usize],
                    Type::Never
                ) {
                    self.terminate(Terminator::Unreachable);
                }
                return Ok((Operand::Move(Place::new(dst)), closure_info.ret_ty));
            }
        }

        // Check static method call on `Self::method(...)` or `Type::method(...)`
        if path.len() >= 2 {
            let method_name = path.last().unwrap();
            let prefix = &path[..path.len() - 1];
            let maybe_ty = if prefix.len() == 1 && prefix[0] == "Self" {
                self.owner_ty
            } else if prefix.len() == 1
                && let Some(ComptimeVal::Type(t)) = self.comptime_env.get(&prefix[0])
            {
                Some(*t)
            } else if let Ok(ResolvedItem::Type(tmod, tname)) =
                self.compiler.resolve_path(&self.mod_path, prefix)
            {
                Some(self.compiler.resolve_named_type(&tmod, &tname)?)
            } else {
                None
            };
            if let Some(comp_ty) = maybe_ty {
                return self.lower_static_type_call(comp_ty, method_name, args);
            }
        }

        // Check `TypeCall(comptime_args)::method(...)` isn't here, or direct function call
        match self.compiler.resolve_path(&self.mod_path, path)? {
            ResolvedItem::ExternFunc(emod, ename) => {
                let fn_id = self.compiler.get_or_register_extern(&emod, &ename)?;
                let (param_tys, ret_ty) = self.compiler.func_sigs[&fn_id].clone();
                let mut lowered_args = Vec::with_capacity(args.len());
                for (i, arg) in args.iter().enumerate() {
                    let exp = param_tys.get(i).copied();
                    let (op, a_ty) = self.lower_expr(arg, exp)?;
                    let coerced = if let Some(pt) = exp {
                        self.coerce_operand(op, a_ty, pt)?
                    } else {
                        op
                    };
                    lowered_args.push(coerced);
                }
                let dst = self.alloc_temp(ret_ty);
                let next_bb = self.new_block();
                self.terminate(Terminator::Call {
                    func: Operand::Const(ConstValue::Func(fn_id)),
                    args: lowered_args,
                    destination: Place::new(dst),
                    target: next_bb,
                });
                self.cur_block = next_bb;
                if matches!(self.compiler.program.types[ret_ty.0 as usize], Type::Never) {
                    self.terminate(Terminator::Unreachable);
                }
                Ok((Operand::Move(Place::new(dst)), ret_ty))
            }
            ResolvedItem::Func(fmod, fname) => {
                let overloads =
                    self.compiler.find_funcs_in_module(&self.mod_path, &fmod, &fname)?;
                if overloads.is_empty() {
                    return Err(format!("Function '{fname}' not found in '{fmod}'"));
                }

                // Check if caller omitted comptime arguments (inferring them from runtime arguments)
                let has_inferred_candidate = overloads.iter().any(|(_, _, d)| {
                    d.params.iter().any(|p| p.is_comptime)
                        && d.params.iter().filter(|p| !p.is_comptime).count() == args.len()
                });

                if has_inferred_candidate {
                    let first_rt_params: Vec<_> = overloads[0]
                        .2
                        .params
                        .iter()
                        .filter(|p| !p.is_comptime)
                        .cloned()
                        .collect();
                    let first_ct_params: Vec<(String, TypeExpr)> = overloads[0]
                        .2
                        .params
                        .iter()
                        .filter(|p| p.is_comptime)
                        .map(|p| (p.name.clone(), p.ty.clone()))
                        .collect();
                    let mut prog_env = HashMap::new();
                    let mut pre_lowered = Vec::with_capacity(args.len());
                    for (i, arg_expr) in args.iter().enumerate() {
                        let exp_ty = first_rt_params.get(i).and_then(|rp| {
                            self.compiler
                                .resolve_type_expr(&fmod, None, &prog_env, &rp.ty)
                                .ok()
                        });
                        let (op, a_ty) = self.lower_expr(arg_expr, exp_ty)?;
                        if let Some(rp) = first_rt_params.get(i) {
                            let _ = self.compiler.unify_type_pattern(
                                &fmod,
                                &first_ct_params,
                                &rp.ty,
                                a_ty,
                                &mut prog_env,
                            );
                        }
                        pre_lowered.push((op, a_ty));
                    }

                    let mut best_ct_args: Option<(Vec<ComptimeVal>, u32)> = None;
                    for (_, _, cand_decl) in &overloads {
                        let rt_params: Vec<_> =
                            cand_decl.params.iter().filter(|p| !p.is_comptime).collect();
                        if rt_params.len() != pre_lowered.len() {
                            continue;
                        }
                        let ct_params: Vec<(String, TypeExpr)> = cand_decl
                            .params
                            .iter()
                            .filter(|p| p.is_comptime)
                            .map(|p| (p.name.clone(), p.ty.clone()))
                            .collect();
                        let mut inferred = HashMap::new();
                        let mut spec_sum = 0u32;
                        let mut matched_all = true;
                        for (rt_p, (_, a_ty)) in rt_params.iter().zip(pre_lowered.iter()) {
                            if let Some(s) = self.compiler.unify_type_pattern(
                                &fmod,
                                &ct_params,
                                &rt_p.ty,
                                *a_ty,
                                &mut inferred,
                            )? {
                                spec_sum += s as u32;
                            } else {
                                matched_all = false;
                                break;
                            }
                        }
                        if matched_all && ct_params.iter().all(|(n, _)| inferred.contains_key(n)) {
                            let ct_args: Vec<ComptimeVal> = ct_params
                                .iter()
                                .map(|(n, _)| inferred[n].clone())
                                .collect();
                            if best_ct_args.as_ref().is_none_or(|(_, bs)| spec_sum > *bs) {
                                best_ct_args = Some((ct_args, spec_sum));
                            }
                        }
                    }

                    let (ct_args, _) = match best_ct_args {
                        Some(pair) => pair,
                        None => {
                            if overloads.len() == 1 {
                                let cand_decl = &overloads[0].2;
                                let rt_params: Vec<_> =
                                    cand_decl.params.iter().filter(|p| !p.is_comptime).collect();
                                let unconstrained_ct: Vec<(String, TypeExpr)> = cand_decl
                                    .params
                                    .iter()
                                    .filter(|p| p.is_comptime)
                                    .map(|p| (p.name.clone(), TypeExpr::MetaType))
                                    .collect();
                                let mut inferred = HashMap::new();
                                let mut matched_all = rt_params.len() == pre_lowered.len();
                                for (rt_p, (_, a_ty)) in rt_params.iter().zip(pre_lowered.iter()) {
                                    if self
                                        .compiler
                                        .unify_type_pattern(
                                            &fmod,
                                            &unconstrained_ct,
                                            &rt_p.ty,
                                            *a_ty,
                                            &mut inferred,
                                        )?
                                        .is_none()
                                    {
                                        matched_all = false;
                                        break;
                                    }
                                }
                                if matched_all
                                    && unconstrained_ct
                                        .iter()
                                        .all(|(n, _)| inferred.contains_key(n))
                                {
                                    let ct_args: Vec<ComptimeVal> = unconstrained_ct
                                        .iter()
                                        .map(|(n, _)| inferred[n].clone())
                                        .collect();
                                    if let Err(reason) = self
                                        .compiler
                                        .get_or_instantiate_func(&fmod, &fname, &ct_args)
                                    {
                                        return Err(format!(
                                            "No overload of '{}' in '{}' matches inferred argument types: {}",
                                            fname, fmod, reason
                                        ));
                                    }
                                }
                            }
                            return Err(format!(
                                "No overload of '{}' in '{}' matches inferred argument types",
                                fname, fmod
                            ));
                        }
                    };
                    let fn_id = self
                        .compiler
                        .get_or_instantiate_func(&fmod, &fname, &ct_args)?;
                    let (param_tys, ret_ty) = self.compiler.func_sigs[&fn_id].clone();
                    let mut lowered_args = Vec::with_capacity(pre_lowered.len());
                    for (i, (op, a_ty)) in pre_lowered.into_iter().enumerate() {
                        let coerced = if let Some(&pt) = param_tys.get(i) {
                            self.coerce_operand(op, a_ty, pt)?
                        } else {
                            op
                        };
                        lowered_args.push(coerced);
                    }
                    let dst = self.alloc_temp(ret_ty);
                    let next_bb = self.new_block();
                    self.terminate(Terminator::Call {
                        func: Operand::Const(ConstValue::Func(fn_id)),
                        args: lowered_args,
                        destination: Place::new(dst),
                        target: next_bb,
                    });
                    self.cur_block = next_bb;
                    if matches!(self.compiler.program.types[ret_ty.0 as usize], Type::Never) {
                        self.terminate(Terminator::Unreachable);
                    }
                    self.last_call_opaque_bound = self.compiler.opaque_ret_funcs.get(&fn_id).cloned();
                    return Ok((Operand::Move(Place::new(dst)), ret_ty));
                }

                let decl = &overloads[0].2;
                let mut ct_args = Vec::new();
                let mut rt_arg_exprs = Vec::new();
                for (p, arg_expr) in decl.params.iter().zip(args.iter()) {
                    if p.is_comptime {
                        ct_args.push(self.compiler.eval_comptime_val(
                            &self.mod_path,
                            self.owner_ty,
                            &self.comptime_env,
                            arg_expr,
                        )?);
                    } else {
                        rt_arg_exprs.push(arg_expr);
                    }
                }
                let fn_id = self
                    .compiler
                    .get_or_instantiate_func(&fmod, &fname, &ct_args)?;
                if ct_args.is_empty()
                    && let Some(wrapper) = self.compiler.c_abi_func_wrappers.get(&fn_id).cloned()
                    && args.len() == wrapper.c_abi_param_tys.len()
                    && args.len() != decl.params.len()
                {
                    let usize_ty = self.compiler.intern_type(Type::Int {
                        signed: false,
                        bits: 64,
                    });
                    let mut lowered_args = Vec::with_capacity(args.len());
                    for (i, arg) in args.iter().enumerate() {
                        let pt = wrapper.c_abi_param_tys[i];
                        if matches!(arg, Expr::Null) && self.compiler.raw_ptrs.contains_key(&pt) {
                            let z_tmp = self.alloc_temp(usize_ty);
                            self.emit(Statement::Assign(
                                Place::new(z_tmp),
                                Rvalue::Use(Operand::Const(ConstValue::I64(0))),
                            ));
                            let p_tmp = self.alloc_temp(pt);
                            self.emit(Statement::Assign(
                                Place::new(p_tmp),
                                Rvalue::Cast(Operand::Copy(Place::new(z_tmp)), pt),
                            ));
                            lowered_args.push(Operand::Copy(Place::new(p_tmp)));
                        } else {
                            let (op, a_ty) = self.lower_expr(arg, Some(pt))?;
                            let coerced = self.coerce_operand(op, a_ty, pt)?;
                            lowered_args.push(coerced);
                        }
                    }
                    let dst = self.alloc_temp(wrapper.c_abi_ret_ty);
                    let next_bb = self.new_block();
                    self.terminate(Terminator::Call {
                        func: Operand::Const(ConstValue::Func(wrapper.c_abi_fn_id)),
                        args: lowered_args,
                        destination: Place::new(dst),
                        target: next_bb,
                    });
                    self.cur_block = next_bb;
                    return Ok((Operand::Move(Place::new(dst)), wrapper.c_abi_ret_ty));
                }
                let (param_tys, ret_ty) = self.compiler.func_sigs[&fn_id].clone();
                let mut lowered_args = Vec::with_capacity(rt_arg_exprs.len());
                for (i, arg) in rt_arg_exprs.iter().enumerate() {
                    let exp = param_tys.get(i).copied();
                    let (op, a_ty) = self.lower_expr(arg, exp)?;
                    let coerced = if let Some(pt) = exp {
                        self.coerce_operand(op, a_ty, pt)?
                    } else {
                        op
                    };
                    lowered_args.push(coerced);
                }
                let dst = self.alloc_temp(ret_ty);
                let next_bb = self.new_block();
                self.terminate(Terminator::Call {
                    func: Operand::Const(ConstValue::Func(fn_id)),
                    args: lowered_args,
                    destination: Place::new(dst),
                    target: next_bb,
                });
                self.cur_block = next_bb;
                if matches!(self.compiler.program.types[ret_ty.0 as usize], Type::Never) {
                    self.terminate(Terminator::Unreachable);
                }
                self.last_call_opaque_bound = self.compiler.opaque_ret_funcs.get(&fn_id).cloned();
                Ok((Operand::Move(Place::new(dst)), ret_ty))
            }
            other => Err(format!("Cannot call {other:?}")),
        }
    }

    fn lower_static_type_call(
        &mut self,
        comp_ty: TypeId,
        method_name: &str,
        args: &[Expr],
    ) -> Result<(Operand, TypeId), String> {
        if let Some(err_info) = self.compiler.errors.get(&comp_ty).cloned() {
            let mut matched = Vec::new();
            for (v_idx, leaf) in err_info.leaves.iter().enumerate() {
                if leaf.key.variant_name == method_name {
                    matched.push((v_idx, leaf.clone()));
                }
            }
            if matched.is_empty() {
                return Err(format!(
                    "Error type '{}' has no variant '{}'",
                    err_info.name, method_name
                ));
            }
            if matched.len() > 1 {
                return Err(format!(
                    "Variant '{}' is ambiguous in error type '{}'; qualify with the specific error type",
                    method_name, err_info.name
                ));
            }
            let (v_idx, leaf) = &matched[0];
            let void_ty = self.compiler.intern_type(Type::Void);
            if leaf.payload_ty == void_ty {
                if !args.is_empty() {
                    return Err(format!(
                        "Error variant '{}::{}' has no payload, but {} arguments were provided",
                        err_info.name,
                        method_name,
                        args.len()
                    ));
                }
                let tmp = self.alloc_temp(comp_ty);
                self.emit(Statement::Assign(
                    Place::new(tmp),
                    Rvalue::Union {
                        ty: comp_ty,
                        variant: *v_idx as u32,
                        payload: Operand::Const(ConstValue::Void),
                    },
                ));
                return Ok((Operand::Move(Place::new(tmp)), comp_ty));
            }
            if args.len() != 1 {
                return Err(format!(
                    "Error variant '{}::{}' expects 1 payload argument, got {}",
                    err_info.name,
                    method_name,
                    args.len()
                ));
            }
            let (op, a_ty) = self.lower_expr(&args[0], Some(leaf.payload_ty))?;
            let coerced = self.coerce_operand(op, a_ty, leaf.payload_ty)?;
            let tmp = self.alloc_temp(comp_ty);
            self.emit(Statement::Assign(
                Place::new(tmp),
                Rvalue::Union {
                    ty: comp_ty,
                    variant: *v_idx as u32,
                    payload: coerced,
                },
            ));
            return Ok((Operand::Move(Place::new(tmp)), comp_ty));
        }
        if let Some(u_info) = self.compiler.unions.get(&comp_ty).cloned() {
            let Some((v_idx, (_, payload_ty))) = u_info
                .variants
                .iter()
                .enumerate()
                .find(|(_, (vn, _))| vn == method_name)
            else {
                return Err(format!(
                    "Union '{}' has no variant '{}'",
                    u_info.name, method_name
                ));
            };
            let payload_ty = *payload_ty;
            let void_ty = self.compiler.intern_type(Type::Void);
            if payload_ty == void_ty {
                if !args.is_empty() {
                    return Err(format!(
                        "Union variant '{}::{}' has no payload, but {} arguments were provided",
                        u_info.name,
                        method_name,
                        args.len()
                    ));
                }
                let tmp = self.alloc_temp(comp_ty);
                self.emit(Statement::Assign(
                    Place::new(tmp),
                    Rvalue::Union {
                        ty: comp_ty,
                        variant: v_idx as u32,
                        payload: Operand::Const(ConstValue::Void),
                    },
                ));
                return Ok((Operand::Move(Place::new(tmp)), comp_ty));
            }
            if args.len() != 1 {
                return Err(format!(
                    "Union variant '{}::{}' expects 1 payload argument, got {}",
                    u_info.name,
                    method_name,
                    args.len()
                ));
            }
            let (op, a_ty) = self.lower_expr(&args[0], Some(payload_ty))?;
            let coerced = self.coerce_operand(op, a_ty, payload_ty)?;
            let tmp = self.alloc_temp(comp_ty);
            self.emit(Statement::Assign(
                Place::new(tmp),
                Rvalue::Union {
                    ty: comp_ty,
                    variant: v_idx as u32,
                    payload: coerced,
                },
            ));
            return Ok((Operand::Move(Place::new(tmp)), comp_ty));
        }

        let (type_name, is_struct, def_mod, ct_env, methods, method_fn_ids) =
            if let Some(comp) = self.compiler.composites.get(&comp_ty).cloned() {
                (
                    comp.name,
                    comp.is_struct,
                    comp.def_module,
                    comp.comptime_env,
                    comp.methods,
                    comp.method_fn_ids,
                )
            } else if let Some(nt) = self.compiler.opaque_newtypes.get(&comp_ty).cloned() {
                (
                    nt.name,
                    true,
                    nt.def_module,
                    nt.comptime_env,
                    nt.methods,
                    nt.method_fn_ids,
                )
            } else {
                return Err(format!("Type {comp_ty} has no methods"));
            };
        let Some((m_vis, m_decl)) = methods.get(method_name) else {
            return Err(format!(
                "Type '{}' has no method '{}'",
                type_name, method_name
            ));
        };
        if is_struct
            && *m_vis == Visibility::Private
            && self.owner_ty != Some(comp_ty)
            && !(self.compiler.opaque_newtypes.contains_key(&comp_ty) && self.mod_path == def_mod)
        {
            return Err(format!(
                "Cannot call private method '{}' of '{}' outside its defining block",
                method_name, type_name
            ));
        }
        self.compiler.check_where_clauses_or_err(
            &ct_env,
            &m_decl.where_clauses,
            &format!("method '{}.{}'", type_name, method_name),
        )?;
        let fn_id = method_fn_ids[method_name];
        let (param_tys, ret_ty) = self.compiler.func_sigs[&fn_id].clone();
        let mut lowered_args = Vec::with_capacity(args.len());
        for (i, arg) in args.iter().enumerate() {
            let exp = param_tys.get(i).copied();
            let (op, a_ty) = self.lower_expr(arg, exp)?;
            let coerced = if let Some(pt) = exp {
                self.coerce_operand(op, a_ty, pt)?
            } else {
                op
            };
            lowered_args.push(coerced);
        }
        let dst = self.alloc_temp(ret_ty);
        let next_bb = self.new_block();
        self.terminate(Terminator::Call {
            func: Operand::Const(ConstValue::Func(fn_id)),
            args: lowered_args,
            destination: Place::new(dst),
            target: next_bb,
        });
        self.cur_block = next_bb;
        if matches!(self.compiler.program.types[ret_ty.0 as usize], Type::Never) {
            self.terminate(Terminator::Unreachable);
        }
        self.last_call_opaque_bound = self.compiler.opaque_ret_funcs.get(&fn_id).cloned();
        Ok((Operand::Move(Place::new(dst)), ret_ty))
    }

    fn bound_expr_declares_method(
        &mut self,
        mod_path: &str,
        owner_ty: Option<TypeId>,
        env: &HashMap<String, ComptimeVal>,
        bound_te: &TypeExpr,
        method_name: &str,
    ) -> Result<bool, String> {
        match bound_te {
            TypeExpr::TraitBounds(bounds) => {
                for b in bounds {
                    if self.bound_expr_declares_method(mod_path, owner_ty, env, b, method_name)? {
                        return Ok(true);
                    }
                }
                Ok(false)
            }
            _ => {
                let b_ty = self
                    .compiler
                    .resolve_type_expr(mod_path, owner_ty, env, bound_te)?;
                if let Some(t_info) = self.compiler.traits.get(&b_ty) {
                    Ok(t_info.methods.iter().any(|m| m.name == method_name))
                } else {
                    Ok(false)
                }
            }
        }
    }

    fn lower_method_call(
        &mut self,
        receiver: &Expr,
        method_name: &str,
        args: &[Expr],
    ) -> Result<(Operand, TypeId), String> {
        if let Expr::TypeVal(te) = receiver {
            let comp_ty = self.compiler.resolve_type_expr(
                &self.mod_path,
                self.owner_ty,
                &self.comptime_env,
                te,
            )?;
            return self.lower_static_type_call(comp_ty, method_name, args);
        }
        if let Expr::Path(path) = receiver
            && !(path.len() == 1
                && (self.lookup_var(&path[0]).is_some()
                    || self.lookup_capture(&path[0]).is_some()))
        {
            let maybe_ty = if path.len() == 1 && path[0] == "Self" {
                self.owner_ty
            } else if path.len() == 1
                && let Some(ComptimeVal::Type(t)) = self.comptime_env.get(&path[0])
            {
                Some(*t)
            } else if let Ok(ResolvedItem::Type(tmod, tname)) =
                self.compiler.resolve_path(&self.mod_path, path)
            {
                Some(self.compiler.resolve_named_type(&tmod, &tname)?)
            } else {
                None
            };
            if let Some(comp_ty) = maybe_ty {
                return self.lower_static_type_call(comp_ty, method_name, args);
            }
        }
        if let Some(root_var) = Self::root_var_of_place_expr(receiver)
            && let Some(ob) = self.lookup_var_opaque_bound(root_var)
        {
            if !self.bound_expr_declares_method(
                &ob.bound_mod,
                ob.owner_ty,
                &ob.env,
                &ob.bound_expr,
                method_name,
            )? {
                return Err(format!(
                    "Cannot call method '{}' on opaque return value '{}': method '{}' is not declared in its trait bound",
                    method_name, root_var, method_name
                ));
            }
        }
        let (recv_place, recv_ty) = self.lower_place(receiver, false)?;
        let comp_ty = if let Type::Ptr { pointee, .. } =
            self.compiler.program.types[recv_ty.0 as usize]
        {
            pointee
        } else {
            recv_ty
        };

        // 0. Check dynamic trait object method dispatch (`&MyTrait` / `&mut MyTrait`)
        if let Some(tobj_info) = self.compiler.trait_objs.get(&comp_ty).cloned() {
            let trait_info = self.compiler.traits[&tobj_info.trait_ty].clone();
            let Some((m_idx, m_decl)) = trait_info
                .methods
                .iter()
                .enumerate()
                .find(|(_, m)| m.name == method_name)
            else {
                return Err(format!(
                    "Trait '{}' has no method '{}'",
                    trait_info.name, method_name
                ));
            };
            let method_needs_mut = matches!(
                &m_decl.params[0].ty,
                TypeExpr::Ref { mutable: true, .. }
            );
            if method_needs_mut {
                if !tobj_info.mutable {
                    return Err(format!(
                        "Cannot call '&mut Self' method '{}.{}' on shared trait object '&{}'",
                        trait_info.name, method_name, trait_info.name
                    ));
                }
                if recv_ty != comp_ty
                    && matches!(
                        self.compiler.program.types[recv_ty.0 as usize],
                        Type::Ptr { mutable: false, .. }
                    )
                {
                    return Err(format!(
                        "Cannot call '&mut Self' method '{}.{}' through an immutable reference",
                        trait_info.name, method_name
                    ));
                }
            }
            let obj_place = if recv_ty == comp_ty {
                recv_place
            } else {
                let mut dp = recv_place;
                dp.projections.push(Projection::Deref);
                dp
            };
            let fn_ptr_ty = tobj_info.method_fn_ptr_tys[m_idx];
            let Type::FnPtr {
                args: param_tys,
                ret: ret_ty,
            } = self.compiler.program.types[fn_ptr_ty.0 as usize].clone()
            else {
                unreachable!()
            };
            if args.len() + 1 != param_tys.len() {
                return Err(format!(
                    "Method '{}.{}' expects {} arguments, got {}",
                    trait_info.name,
                    method_name,
                    param_tys.len() - 1,
                    args.len()
                ));
            }
            let self_arg = if tobj_info.mutable {
                let mut deref_data = obj_place.clone();
                deref_data.projections.push(Projection::Field(0));
                deref_data.projections.push(Projection::Deref);
                let self_tmp = self.alloc_temp(param_tys[0]);
                self.emit(Statement::Assign(
                    Place::new(self_tmp),
                    Rvalue::Ref {
                        mutable: method_needs_mut,
                        place: deref_data,
                    },
                ));
                Operand::Move(Place::new(self_tmp))
            } else {
                let mut data_field = obj_place.clone();
                data_field.projections.push(Projection::Field(0));
                Operand::Copy(data_field)
            };
            let mut vt_fn_place = obj_place;
            vt_fn_place.projections.push(Projection::Field(1));
            vt_fn_place.projections.push(Projection::Deref);
            vt_fn_place.projections.push(Projection::Field(m_idx as u32));
            let fn_ptr_tmp = self.alloc_temp(fn_ptr_ty);
            self.emit(Statement::Assign(
                Place::new(fn_ptr_tmp),
                Rvalue::Use(Operand::Copy(vt_fn_place)),
            ));

            let mut lowered_args = Vec::with_capacity(param_tys.len());
            lowered_args.push(self_arg);
            for (i, arg_expr) in args.iter().enumerate() {
                let exp = param_tys.get(i + 1).copied();
                let (op, a_ty) = self.lower_expr(arg_expr, exp)?;
                let coerced = if let Some(pt) = exp {
                    self.coerce_operand(op, a_ty, pt)?
                } else {
                    op
                };
                lowered_args.push(coerced);
            }
            let dst = self.alloc_temp(ret_ty);
            let next_bb = self.new_block();
            self.terminate(Terminator::Call {
                func: Operand::Copy(Place::new(fn_ptr_tmp)),
                args: lowered_args,
                destination: Place::new(dst),
                target: next_bb,
            });
            self.cur_block = next_bb;
            if matches!(self.compiler.program.types[ret_ty.0 as usize], Type::Never) {
                self.terminate(Terminator::Unreachable);
            }
            return Ok((Operand::Move(Place::new(dst)), ret_ty));
        }

        // 1. Check inherent methods defined inside `record { ... }`, `struct { ... }`, or `opaque { ... }` first
        let mut pre_lowered_rt_args: Option<Vec<(Operand, TypeId)>> = None;
        let inherent_info = if let Some(comp) = self.compiler.composites.get(&comp_ty).cloned() {
            Some((
                comp.name,
                comp.is_struct,
                comp.def_module,
                comp.comptime_env,
                comp.methods,
                comp.method_fn_ids,
            ))
        } else {
            self.compiler.opaque_newtypes.get(&comp_ty).cloned().map(|nt| {
                (
                    nt.name,
                    true,
                    nt.def_module,
                    nt.comptime_env,
                    nt.methods,
                    nt.method_fn_ids,
                )
            })
        };
        let (fn_id, rt_arg_exprs): (FuncId, Vec<&Expr>) =
            if let Some((type_name, is_struct, def_mod, ct_env, methods, method_fn_ids)) =
                inherent_info
                && let Some((m_vis, m_decl)) = methods.get(method_name)
            {
                if is_struct
                    && *m_vis == Visibility::Private
                    && self.owner_ty != Some(comp_ty)
                    && !(self.compiler.opaque_newtypes.contains_key(&comp_ty)
                        && self.mod_path == def_mod)
                {
                    return Err(format!(
                        "Cannot call private method '{}' of struct '{}' outside its 'struct {{ ... }}' block",
                        method_name, type_name
                    ));
                }
                if !m_decl.params.iter().any(|p| p.is_comptime) {
                    self.compiler.check_where_clauses_or_err(
                        &ct_env,
                        &m_decl.where_clauses,
                        &format!("method '{}.{}'", type_name, method_name),
                    )?;
                    (method_fn_ids[method_name], args.iter().collect())
                } else {
                    let rt_params_after_self: Vec<_> = m_decl
                        .params
                        .iter()
                        .filter(|p| !p.is_comptime)
                        .skip(1)
                        .collect();
                    let ct_params: Vec<(String, TypeExpr)> = m_decl
                        .params
                        .iter()
                        .filter(|p| p.is_comptime)
                        .map(|p| (p.name.clone(), p.ty.clone()))
                        .collect();
                    let mut ct_args = Vec::with_capacity(ct_params.len());
                    let mut rt_exprs = Vec::new();
                    if args.len() == rt_params_after_self.len() {
                        let mut lowered = Vec::with_capacity(args.len());
                        for (i, arg_expr) in args.iter().enumerate() {
                            let exp_ty = rt_params_after_self.get(i).and_then(|rp| {
                                self.compiler
                                    .resolve_type_expr(
                                        &def_mod,
                                        Some(comp_ty),
                                        &ct_env,
                                        &rp.ty,
                                    )
                                    .ok()
                            });
                            lowered.push(self.lower_expr(arg_expr, exp_ty)?);
                        }
                        let unconstrained_ct: Vec<(String, TypeExpr)> = ct_params
                            .iter()
                            .map(|(n, _)| (n.clone(), TypeExpr::MetaType))
                            .collect();
                        let mut inferred = ct_env.clone();
                        for (rt_p, (_, a_ty)) in
                            rt_params_after_self.iter().zip(lowered.iter())
                        {
                            if self
                                .compiler
                                .unify_type_pattern(
                                    &def_mod,
                                    &unconstrained_ct,
                                    &rt_p.ty,
                                    *a_ty,
                                    &mut inferred,
                                )?
                                .is_none()
                            {
                                return Err(format!(
                                    "Argument type {} does not match parameter '{}' of method '{}.{}'",
                                    self.compiler.program.types[a_ty.0 as usize],
                                    rt_p.name,
                                    type_name,
                                    method_name
                                ));
                            }
                        }
                        for (p_name, bound_te) in &ct_params {
                            let Some(val) = inferred.get(p_name).cloned() else {
                                return Err(format!(
                                    "Could not infer comptime parameter '{}' of method '{}.{}'",
                                    p_name, type_name, method_name
                                ));
                            };
                            if let ComptimeVal::Type(arg_ty) = val
                                && let Some(Err(e)) = self.compiler.eval_comptime_type_bound(
                                    &def_mod,
                                    Some(comp_ty),
                                    &inferred,
                                    bound_te,
                                    arg_ty,
                                )?
                            {
                                return Err(format!(
                                    "{} (for parameter '{}' in '{}.{}')",
                                    e, p_name, type_name, method_name
                                ));
                            }
                            ct_args.push(val);
                        }
                        pre_lowered_rt_args = Some(lowered);
                    } else {
                        let mut args_iter = args.iter();
                        let mut seen_self = false;
                        for p in &m_decl.params {
                            if p.is_comptime {
                                let arg_expr = args_iter.next().ok_or_else(|| {
                                    format!(
                                        "Missing comptime argument '{}' for method '{}.{}'",
                                        p.name, type_name, method_name
                                    )
                                })?;
                                let val = self.compiler.eval_comptime_val(
                                    &self.mod_path,
                                    self.owner_ty,
                                    &self.comptime_env,
                                    arg_expr,
                                )?;
                                if let ComptimeVal::Type(arg_ty) = val
                                    && let Some(Err(e)) = self.compiler.eval_comptime_type_bound(
                                        &def_mod,
                                        Some(comp_ty),
                                        &ct_env,
                                        &p.ty,
                                        arg_ty,
                                    )?
                                {
                                    return Err(format!(
                                        "{} (for parameter '{}' in '{}.{}')",
                                        e, p.name, type_name, method_name
                                    ));
                                }
                                ct_args.push(val);
                            } else if !seen_self {
                                seen_self = true;
                            } else if let Some(arg_expr) = args_iter.next() {
                                rt_exprs.push(arg_expr);
                            } else {
                                return Err(format!(
                                    "Missing argument '{}' in call to method '{}.{}'",
                                    p.name, type_name, method_name
                                ));
                            }
                        }
                    }
                    let mut method_env = ct_env.clone();
                    for ((p_name, _), val) in ct_params.iter().zip(ct_args.iter()) {
                        method_env.insert(p_name.clone(), val.clone());
                    }
                    self.compiler.check_where_clauses_or_err(
                        &method_env,
                        &m_decl.where_clauses,
                        &format!("method '{}.{}'", type_name, method_name),
                    )?;
                    let key = (comp_ty, method_name.to_string(), ct_args.clone());
                    let inst_fn_id =
                        if let Some(&existing_id) =
                            self.compiler.memoized_inherent_methods.get(&key)
                        {
                            existing_id
                        } else {
                            let new_id = self.compiler.schedule_method(
                                &def_mod,
                                comp_ty,
                                &method_env,
                                m_decl,
                            )?;
                            self.compiler.memoized_inherent_methods.insert(key, new_id);
                            new_id
                        };
                    (inst_fn_id, rt_exprs)
                }
            } else {
                // 2. Fall back to in-scope `self`-receiver extension functions
                let (ext_mod, _, ext_decl, mut inferred) = self
                    .compiler
                    .resolve_extension_method(&self.mod_path, comp_ty, method_name)?;
                let mut args_iter = args.iter();
                let mut ct_args = Vec::new();
                let mut rt_exprs = Vec::new();
                let mut seen_self = false;
                for p in &ext_decl.params {
                    if p.is_comptime {
                        if let Some(val) = inferred.get(&p.name) {
                            ct_args.push(val.clone());
                        } else {
                            let arg_expr = args_iter.next().ok_or_else(|| {
                                format!(
                                    "Missing comptime argument '{}' for extension method '{}'",
                                    p.name, method_name
                                )
                            })?;
                            let val = self.compiler.eval_comptime_val(
                                &self.mod_path,
                                self.owner_ty,
                                &self.comptime_env,
                                arg_expr,
                            )?;
                            inferred.insert(p.name.clone(), val.clone());
                            ct_args.push(val);
                        }
                    } else if !seen_self {
                        seen_self = true;
                    } else if let Some(arg_expr) = args_iter.next() {
                        rt_exprs.push(arg_expr);
                    } else {
                        return Err(format!(
                            "Missing argument '{}' in call to extension method '{}'",
                            p.name, method_name
                        ));
                    }
                }
                let ext_fn_id = self.compiler.instantiate_specific_func_decl(
                    &ext_mod,
                    &ext_decl,
                    &ct_args,
                )?;
                (ext_fn_id, rt_exprs)
            };

        let (param_tys, ret_ty) = self.compiler.func_sigs[&fn_id].clone();
        let self_param_ty = param_tys[0];

        // Automatically borrow or deref `recv_place` to match `self` parameter type (`&Self`, `&mut Self`, `*const Self`, `*mut Self`, or `Self`)
        let self_arg = if let Type::Ptr { mutable, pointee } =
            self.compiler.program.types[self_param_ty.0 as usize]
            && pointee == comp_ty
            && !self.compiler.raw_ptrs.contains_key(&self_param_ty)
        {
            let target_place = if recv_ty == comp_ty {
                recv_place
            } else {
                let mut deref_p = recv_place;
                deref_p.projections.push(Projection::Deref);
                deref_p
            };
            let ref_tmp = self.alloc_temp(self_param_ty);
            self.emit(Statement::Assign(
                Place::new(ref_tmp),
                Rvalue::Ref {
                    mutable,
                    place: target_place,
                },
            ));
            Operand::Move(Place::new(ref_tmp))
        } else if recv_ty == self_param_ty {
            if self.is_copy_type(recv_ty) {
                Operand::Copy(recv_place)
            } else {
                Operand::Move(recv_place)
            }
        } else if self.compiler.raw_ptrs.contains_key(&self_param_ty) {
            let op = if self.is_copy_type(recv_ty) {
                Operand::Copy(recv_place)
            } else {
                Operand::Move(recv_place)
            };
            self.coerce_operand(op, recv_ty, self_param_ty)?
        } else {
            return Err(format!(
                "Receiver type {recv_ty} does not match method '{method_name}' self parameter {self_param_ty}"
            ));
        };

        let mut lowered_args = Vec::with_capacity(param_tys.len());
        lowered_args.push(self_arg);
        if let Some(pre_lowered) = pre_lowered_rt_args {
            for (i, (op, a_ty)) in pre_lowered.into_iter().enumerate() {
                let coerced = if let Some(&pt) = param_tys.get(i + 1) {
                    self.coerce_operand(op, a_ty, pt)?
                } else {
                    op
                };
                lowered_args.push(coerced);
            }
        } else {
            for (i, arg) in rt_arg_exprs.iter().enumerate() {
                let exp = param_tys.get(i + 1).copied();
                let (op, a_ty) = self.lower_expr(arg, exp)?;
                let coerced = if let Some(pt) = exp {
                    self.coerce_operand(op, a_ty, pt)?
                } else {
                    op
                };
                lowered_args.push(coerced);
            }
        }

        let dst = self.alloc_temp(ret_ty);
        let next_bb = self.new_block();
        self.terminate(Terminator::Call {
            func: Operand::Const(ConstValue::Func(fn_id)),
            args: lowered_args,
            destination: Place::new(dst),
            target: next_bb,
        });
        self.cur_block = next_bb;
        if matches!(self.compiler.program.types[ret_ty.0 as usize], Type::Never) {
            self.terminate(Terminator::Unreachable);
        }
        self.last_call_opaque_bound = self.compiler.opaque_ret_funcs.get(&fn_id).cloned();
        Ok((Operand::Move(Place::new(dst)), ret_ty))
    }
}
