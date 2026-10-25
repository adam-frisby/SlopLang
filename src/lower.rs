use std::collections::HashMap;

use crate::ast::{
    Block, Expr, ExternFuncDecl, FieldDecl, FmtSegment, FuncDecl, ImportDecl, ImportTargets, Item,
    ModuleAst, Stmt, TypeConstraint, TypeExpr, Visibility,
};
use crate::borrowck::check_borrows;
use crate::drop::elaborate_drops;
use crate::frontend::SurfaceParser;
use crate::ir::{
    BasicBlock, BinOp, BlockId, ConstValue, ExternFunc, FuncId, Function, LocalId, Operand, Place,
    Program, Projection, Rvalue, Statement, Terminator, Type, TypeId, UnOp,
};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ComptimeVal {
    Type(TypeId),
    Int(i128),
    Bool(bool),
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
    is_linear: bool,
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

pub struct Compiler {
    modules: HashMap<String, ModuleAst>,
    pub program: Program,
    composites: HashMap<TypeId, CompositeInfo>,
    enums: HashMap<TypeId, (String, Vec<(String, i128)>)>,
    closures: HashMap<TypeId, ClosureInfo>,
    slices: HashMap<TypeId, SliceInfo>,
    raw_ptrs: HashMap<TypeId, (bool, TypeId)>,
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
            closures: HashMap::new(),
            slices: HashMap::new(),
            raw_ptrs: HashMap::new(),
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

    /// Compiles a multi-module package (`[(module_path, source_code), ...]`) in freestanding (`no_std` / `core`-only) mode.
    pub fn compile_package_no_std(sources: &[(&str, &str)]) -> Result<Program, String> {
        Self::compile_package_with_mode(sources, true)
    }

    fn compile_package_with_mode(sources: &[(&str, &str)], no_std: bool) -> Result<Program, String> {
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
        Ok(compiler.program)
    }

    fn intern_type(&mut self, ty: Type) -> TypeId {
        if let Some(idx) = self.program.types.iter().enumerate().find_map(|(i, t)| {
            let tid = TypeId(i as u32);
            (*t == ty
                && !self.composites.contains_key(&tid)
                && !self.enums.contains_key(&tid)
                && !self.closures.contains_key(&tid)
                && !self.slices.contains_key(&tid)
                && !self.raw_ptrs.contains_key(&tid))
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
                if let Item::Func(fdecl) = item
                    && !fdecl.params.iter().any(|p| p.is_comptime)
                    && fdecl.ret_ty != TypeExpr::MetaType
                {
                    let _ = self.get_or_instantiate_func(mod_path, &fdecl.name, &[])?;
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
        for (_, pty) in &ext.params {
            arg_tys.push(self.resolve_type_expr(mod_path, None, &env, pty)?);
        }
        let ret_ty = self.resolve_type_expr(mod_path, None, &env, &ext.ret_ty)?;
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

    fn is_send_type(&self, ty_id: TypeId) -> bool {
        if self.raw_ptrs.contains_key(&ty_id) {
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
        if self.raw_ptrs.contains_key(&ty_id) {
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
        if self.raw_ptrs.contains_key(&ty_id) || self.closures.contains_key(&ty_id) {
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
            Type::Int { .. } | Type::F32 | Type::F64 | Type::Bool | Type::Rune => true,
            Type::Ptr { pointee, .. } => self.is_format_type(*pointee),
            Type::Struct(fields) => fields.iter().all(|&f| self.is_format_type(f)),
            Type::Array { elem, .. } => self.is_format_type(*elem),
            Type::Union { variants, .. } => variants.iter().skip(1).all(|&v| self.is_format_type(v)),
            Type::Pattern { base, .. } => self.is_format_type(*base),
            _ => false,
        }
    }

    fn type_satisfies_constraint(&self, ty_id: TypeId, constraint: TypeConstraint) -> bool {
        let mut cur = &self.program.types[ty_id.0 as usize];
        if let Type::Pattern { base, .. } = cur {
            cur = &self.program.types[base.0 as usize];
        }
        let is_enum = self.enums.contains_key(&ty_id);
        match constraint {
            TypeConstraint::AnyType => true,
            TypeConstraint::Send => self.is_send_type(ty_id),
            TypeConstraint::Sync => self.is_sync_type(ty_id),
            TypeConstraint::Format => self.is_format_type(ty_id),
            TypeConstraint::Scalar => {
                !is_enum
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
                !is_enum && matches!(cur, Type::Int { .. } | Type::F32 | Type::F64)
            }
            TypeConstraint::Callable => {
                matches!(cur, Type::FnPtr { .. }) || self.closures.contains_key(&ty_id)
            }
            TypeConstraint::FnPtr => matches!(cur, Type::FnPtr { .. }),
            TypeConstraint::Closure => self.closures.contains_key(&ty_id),
            TypeConstraint::Integer => !is_enum && matches!(cur, Type::Int { .. }),
            TypeConstraint::Signed => !is_enum && matches!(cur, Type::Int { signed: true, .. }),
            TypeConstraint::Unsigned => !is_enum && matches!(cur, Type::Int { signed: false, .. }),
            TypeConstraint::Float => matches!(cur, Type::F32 | Type::F64),
            TypeConstraint::Aggregate => {
                self.type_satisfies_constraint(ty_id, TypeConstraint::Record)
                    || self.type_satisfies_constraint(ty_id, TypeConstraint::Tuple)
            }
            TypeConstraint::Record => self.composites.get(&ty_id).is_some_and(|c| !c.is_struct),
            TypeConstraint::Tuple => {
                matches!(cur, Type::Struct(_))
                    && !self.composites.contains_key(&ty_id)
                    && !self.closures.contains_key(&ty_id)
                    && !self.slices.contains_key(&ty_id)
            }
            TypeConstraint::Struct => self.composites.get(&ty_id).is_some_and(|c| c.is_struct),
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
            }
            TypeConstraint::Enum => is_enum,
            TypeConstraint::Union => matches!(cur, Type::Union { .. }),
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

    /// Unifies a `TypeExpr` pattern from a function in `fn_mod` against a concrete `actual_ty`,
    /// binding any `comptime_params` into `inferred` and returning a specificity score:
    /// - `20`: Concrete type match (`Point`, `i32`, `Pair(i32)`)
    /// - `11..=14`: Parameterized structural or type-constructor match (`simd[T; N]`, `[T; N]`, `?T`, `Pair(T)`),
    ///   sub-ranked by `T`'s meta-type constraint (`signed`/`unsigned` > `integer`/`float` > `number` > `type`)
    /// - `1..=4`: Blanket generic type parameter (`T: type` = 1, `T: number` = 2, `T: integer`/`float` = 3, `T: signed`/`unsigned` = 4)
    fn unify_type_pattern(
        &mut self,
        fn_mod: &str,
        comptime_params: &[(String, Option<TypeConstraint>)],
        pat: &TypeExpr,
        actual_ty: TypeId,
        inferred: &mut HashMap<String, ComptimeVal>,
    ) -> Result<Option<u8>, String> {
        match pat {
            TypeExpr::Named(path)
                if path.len() == 1 && comptime_params.iter().any(|(n, _)| n == &path[0]) =>
            {
                let (_, maybe_constraint) = comptime_params
                    .iter()
                    .find(|(n, _)| n == &path[0])
                    .unwrap();
                if let Some(constraint) = maybe_constraint
                    && !self.type_satisfies_constraint(actual_ty, *constraint)
                {
                    return Ok(None);
                }
                let spec = maybe_constraint.map_or(1, TypeConstraint::specificity);
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
            TypeExpr::Tuple(elems) => {
                if self.composites.contains_key(&actual_ty)
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
        comptime_params: &[(String, Option<TypeConstraint>)],
        expr: &Expr,
        actual: &ComptimeVal,
        inferred: &mut HashMap<String, ComptimeVal>,
    ) -> Result<Option<u8>, String> {
        match expr {
            Expr::Path(p)
                if p.len() == 1 && comptime_params.iter().any(|(n, _)| n == &p[0]) =>
            {
                let (_, maybe_constraint) =
                    comptime_params.iter().find(|(n, _)| n == &p[0]).unwrap();
                if let Some(constraint) = maybe_constraint
                    && let ComptimeVal::Type(act_ty) = actual
                    && !self.type_satisfies_constraint(*act_ty, *constraint)
                {
                    return Ok(None);
                }
                let spec = maybe_constraint.map_or(1, TypeConstraint::specificity);
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
        // Also check the composite's defining module if `comp_ty` is a user-defined composite
        // and no candidates were found in `cur_mod` (e.g. inside a generic function).
        if candidates.is_empty()
            && let Some(comp) = self.composites.get(&comp_ty)
            && comp.def_module != cur_mod
        {
            let def_mod = comp.def_module.clone();
            if let Ok(found) = self.find_funcs_in_module(cur_mod, &def_mod, method_name) {
                candidates.extend(found);
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
            let comptime_params: Vec<(String, Option<TypeConstraint>)> = decl
                .params
                .iter()
                .filter(|p| p.is_comptime)
                .map(|p| (p.name.clone(), p.ty.as_type_constraint()))
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
                comp_ty,
                &mut inferred,
            )? {
                matched.push((fn_mod, orig_name, decl, inferred, specificity));
            }
        }

        let type_display = self
            .composites
            .get(&comp_ty)
            .map(|c| c.name.clone())
            .unwrap_or_else(|| self.program.types[comp_ty.0 as usize].to_string());

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
        let Some((def_mod, orig_name, Item::TypeDecl { ty, .. }, _)) =
            self.find_item_in_module(mod_path, mod_path, name)?
        else {
            return Err(format!("Type '{name}' not found in '{mod_path}'"));
        };
        let env = HashMap::new();
        let ty_id = self.instantiate_type_decl(&def_mod, &orig_name, &env, &ty)?;
        self.named_types.insert(key, ty_id);
        Ok(ty_id)
    }

    fn instantiate_type_decl(
        &mut self,
        mod_path: &str,
        type_name: &str,
        env: &HashMap<String, ComptimeVal>,
        ty_expr: &TypeExpr,
    ) -> Result<TypeId, String> {
        match ty_expr {
            TypeExpr::Enum(variants) => self.instantiate_enum(type_name, variants),
            TypeExpr::Record { fields, methods } => {
                self.instantiate_composite(
                    mod_path, type_name, false, false, false, env, None, fields, methods, None,
                    None, None, None,
                )
            }
            TypeExpr::Struct {
                is_linear,
                is_sync,
                fields,
                methods,
                default_hook,
                clone_hook,
                drop_hook,
                format_hook,
            } => self.instantiate_composite(
                mod_path,
                type_name,
                true,
                *is_linear,
                *is_sync,
                env,
                None,
                fields,
                methods,
                default_hook.clone(),
                clone_hook.clone(),
                drop_hook.clone(),
                format_hook.clone(),
            ),
            other => self.resolve_type_expr(mod_path, None, env, other),
        }
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

    #[allow(clippy::too_many_arguments)]
    fn instantiate_composite(
        &mut self,
        mod_path: &str,
        type_name: &str,
        is_struct: bool,
        is_linear: bool,
        is_sync: bool,
        env: &HashMap<String, ComptimeVal>,
        memo_key: Option<(String, String, Vec<ComptimeVal>)>,
        fields: &[FieldDecl],
        methods: &[FuncDecl],
        default_hook: Option<Block>,
        clone_hook: Option<(String, Block)>,
        drop_hook: Option<(String, Block)>,
        format_hook: Option<(String, String, Option<String>, Block)>,
    ) -> Result<TypeId, String> {
        if is_linear && clone_hook.is_some() {
            return Err(format!(
                "Linear struct '{type_name}' cannot implement `clone`; linear values must be consumed exactly once"
            ));
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
            is_linear,
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
        }

        // Instantiate non-generic inherent methods eagerly; generic inherent methods
        // (with `comptime` parameters) are instantiated on demand at call sites.
        for m in methods {
            if !m.params.iter().any(|p| p.is_comptime) {
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
                body: def_blk,
            };
            let fn_id = self.schedule_method(mod_path, ty_id, env, &decl)?;
            self.composites.get_mut(&ty_id).unwrap().default_fn = Some(fn_id);
        }

        if let Some((self_name, clone_blk)) = clone_hook {
            let decl = FuncDecl {
                vis: Visibility::Pub,
                name: format!("{type_name}::clone"),
                params: vec![crate::ast::Param {
                    is_comptime: false,
                    is_mut: false,
                    name: self_name,
                    ty: TypeExpr::Ref {
                        mutable: false,
                        inner: Box::new(TypeExpr::SelfType),
                    },
                }],
                ret_ty: TypeExpr::SelfType,
                body: clone_blk,
            };
            let fn_id = self.schedule_method(mod_path, ty_id, env, &decl)?;
            self.composites.get_mut(&ty_id).unwrap().clone_fn = Some(fn_id);
        }

        if let Some((self_name, drop_blk)) = drop_hook {
            let decl = FuncDecl {
                vis: Visibility::Pub,
                name: format!("{type_name}::drop"),
                params: vec![crate::ast::Param {
                    is_comptime: false,
                    is_mut: false,
                    name: self_name,
                    ty: TypeExpr::Ref {
                        mutable: true,
                        inner: Box::new(TypeExpr::SelfType),
                    },
                }],
                ret_ty: TypeExpr::Void,
                body: drop_blk,
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
                body: fmt_blk,
            };
            let fn_id = self.schedule_method(mod_path, ty_id, env, &decl)?;
            self.composites.get_mut(&ty_id).unwrap().format_fn = Some((fn_id, takes_spec));
        }

        Ok(ty_id)
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
                param_tys.push(self.resolve_type_expr(mod_path, Some(owner_ty), env, &p.ty)?);
            }
        }
        let ret_ty = self.resolve_type_expr(mod_path, Some(owner_ty), env, &decl.ret_ty)?;
        let fn_id = self.reserve_function(decl.vis, None, &param_tys, ret_ty);
        if self.composites.get(&owner_ty).is_some_and(|c| c.is_linear)
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
        vis: Visibility,
        export: Option<String>,
        param_tys: &[TypeId],
        ret_ty: TypeId,
    ) -> FuncId {
        let fn_id = FuncId((self.program.externs.len() + self.program.functions.len()) as u32);
        // Apply Section 5.1 Lifetime Elision rule for `pub` functions returning references or slices:
        let is_ref_or_slice = |s: &Self, t: TypeId| {
            matches!(s.program.types[t.0 as usize], Type::Ptr { .. }) || s.slices.contains_key(&t)
        };
        let ret_borrows = if vis == Visibility::Pub
            && is_ref_or_slice(self, ret_ty)
            && !param_tys.is_empty()
            && is_ref_or_slice(self, param_tys[0])
        {
            Some(vec![LocalId(1)])
        } else {
            None
        };
        let mut locals = vec![ret_ty];
        locals.extend_from_slice(param_tys);
        self.program.functions.push(Function {
            id: fn_id,
            arg_count: param_tys.len(),
            ret_borrows,
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
                    if let Some(constraint) = p.ty.as_type_constraint() {
                        if let ComptimeVal::Type(arg_ty) = val {
                            if !self.type_satisfies_constraint(arg_ty, constraint) {
                                let t_disp = self
                                    .composites
                                    .get(&arg_ty)
                                    .map(|c| c.name.clone())
                                    .unwrap_or_else(|| {
                                        self.program.types[arg_ty.0 as usize].to_string()
                                    });
                                last_constraint_err = Some(format!(
                                    "Type '{}' does not satisfy comptime constraint '{}' for parameter '{}' in '{}'",
                                    t_disp,
                                    constraint.name(),
                                    p.name,
                                    name
                                ));
                                ok = false;
                                break;
                            }
                            spec_sum += constraint.specificity() as u32;
                        } else {
                            ok = false;
                            break;
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
        let (decl, env, _) = matching_overloads.into_iter().next().unwrap();

        let mut param_tys = Vec::new();
        for p in &decl.params {
            if !p.is_comptime {
                param_tys.push(self.resolve_type_expr(mod_path, None, &env, &p.ty)?);
            }
        }
        let ret_ty = self.resolve_type_expr(mod_path, None, &env, &decl.ret_ty)?;
        let export = if name == "main" {
            Some("main".to_string())
        } else {
            None
        };
        let fn_id = self.reserve_function(decl.vis, export, &param_tys, ret_ty);
        self.resolved_funcs.insert(key, fn_id);
        self.pending_funcs.push(PendingFunc {
            func_id: fn_id,
            module_path: mod_path.to_string(),
            owner_ty: None,
            decl,
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
            TypeExpr::MetaType | TypeExpr::Constraint(_) => Ok(self.intern_type(Type::MetaType)),
            TypeExpr::SelfType => {
                self_ty.ok_or_else(|| "'Self' type used outside of a struct/record context".to_string())
            }
            TypeExpr::Ref { mutable, inner } => {
                let pointee = self.resolve_type_expr(mod_path, self_ty, env, inner)?;
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
                Ok(self.intern_slice_type(*mutable, elem_id))
            }
            TypeExpr::StrRef => Ok(self.intern_str_type()),
            TypeExpr::RelRef(_) | TypeExpr::RelSlice(_) | TypeExpr::RelStr => Err(
                "'&rel' relative references are only permitted in 'struct' field declarations"
                    .to_string(),
            ),
            TypeExpr::Optional(inner) => {
                let inner_id = self.resolve_type_expr(mod_path, self_ty, env, inner)?;
                let u8_id = self.intern_type(Type::Int {
                    signed: false,
                    bits: 8,
                });
                let void_id = self.intern_type(Type::Void);
                Ok(self.intern_type(Type::Union {
                    tag: u8_id,
                    variants: vec![void_id, inner_id],
                }))
            }
            TypeExpr::Array { elem, len } => {
                let elem_id = self.resolve_type_expr(mod_path, self_ty, env, elem)?;
                let len_val = self.eval_comptime_int(mod_path, self_ty, env, len)?;
                Ok(self.intern_type(Type::Array {
                    elem: elem_id,
                    len: len_val as u64,
                }))
            }
            TypeExpr::Simd { elem, len } => {
                let elem_id = self.resolve_type_expr(mod_path, self_ty, env, elem)?;
                let len_val = self.eval_comptime_int(mod_path, self_ty, env, len)?;
                Ok(self.intern_type(Type::Simd {
                    elem: elem_id,
                    len: len_val as u64,
                }))
            }
            TypeExpr::Pattern { base, ranges } => {
                let base_id = self.resolve_type_expr(mod_path, self_ty, env, base)?;
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
                    tys.push(self.resolve_type_expr(mod_path, self_ty, env, e)?);
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
            TypeExpr::Record { fields, methods } => {
                self.instantiate_composite(
                    mod_path,
                    "<anon_record>",
                    false,
                    false,
                    false,
                    env,
                    None,
                    fields,
                    methods,
                    None,
                    None,
                    None,
                    None,
                )
            }
            TypeExpr::Struct {
                is_linear,
                is_sync,
                fields,
                methods,
                default_hook,
                clone_hook,
                drop_hook,
                format_hook,
            } => self.instantiate_composite(
                mod_path,
                "<anon_struct>",
                true,
                *is_linear,
                *is_sync,
                env,
                None,
                fields,
                methods,
                default_hook.clone(),
                clone_hook.clone(),
                drop_hook.clone(),
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
            if let Some(constraint) = p.ty.as_type_constraint()
                && let ComptimeVal::Type(arg_ty) = arg
                && !self.type_satisfies_constraint(*arg_ty, constraint)
            {
                let t_disp = self
                    .composites
                    .get(arg_ty)
                    .map(|c| c.name.clone())
                    .unwrap_or_else(|| self.program.types[arg_ty.0 as usize].to_string());
                return Err(format!(
                    "Type '{}' does not satisfy comptime constraint '{}' for parameter '{}' in '{}'",
                    t_disp,
                    constraint.name(),
                    p.name,
                    fname
                ));
            }
            local_env.insert(p.name.clone(), arg.clone());
        }
        for stmt in &decl.body.stmts {
            match stmt {
                Stmt::Let { name, init, .. } => {
                    let v = self.eval_comptime_val(mod_path, None, &local_env, init)?;
                    local_env.insert(name.clone(), v);
                }
                Stmt::Return(Some(Expr::TypeVal(TypeExpr::Record { fields, methods }))) => {
                    let ty_id = self.instantiate_composite(
                        mod_path,
                        fname,
                        false,
                        false,
                        false,
                        &local_env,
                        Some((mod_path.to_string(), fname.to_string(), args.to_vec())),
                        fields,
                        methods,
                        None,
                        None,
                        None,
                        None,
                    )?;
                    return Ok(ComptimeVal::Type(ty_id));
                }
                Stmt::Return(Some(Expr::TypeVal(TypeExpr::Struct {
                    is_linear,
                    is_sync,
                    fields,
                    methods,
                    default_hook,
                    clone_hook,
                    drop_hook,
                    format_hook,
                }))) => {
                    let ty_id = self.instantiate_composite(
                        mod_path,
                        fname,
                        true,
                        *is_linear,
                        *is_sync,
                        &local_env,
                        Some((mod_path.to_string(), fname.to_string(), args.to_vec())),
                        fields,
                        methods,
                        default_hook.clone(),
                        clone_hook.clone(),
                        drop_hook.clone(),
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
                });
                arg_local_idx += 1;
            }
        }

        let body = self.decl.body.clone();
        self.lower_block_stmts(&body)?;

        let ret_ty = self.locals[0];
        if !self.is_terminated() {
            if matches!(self.compiler.program.types[ret_ty.0 as usize], Type::Void) {
                self.emit(Statement::Assign(
                    Place::new(LocalId(0)),
                    Rvalue::Use(Operand::Const(ConstValue::Void)),
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
        if src_ty == target_ty {
            if let Operand::Const(ConstValue::I64(n)) = &op {
                self.verify_pattern_const(target_ty, *n)?;
            }
            return Ok(op);
        }
        // Coerce safe references (`&mut T` -> `&T`, `&T`/`&mut T` -> `*const T`/`*mut T`) and raw pointers (`*mut T` -> `*const T`)
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
        ) && src_pt == dst_pt
            && (!dst_mut || src_mut)
            && (!self.compiler.raw_ptrs.contains_key(&src_ty)
                || self.compiler.raw_ptrs.contains_key(&target_ty))
        {
            let tmp = self.alloc_temp(target_ty);
            self.emit(Statement::Assign(
                Place::new(tmp),
                Rvalue::Cast(op, target_ty),
            ));
            return Ok(Operand::Copy(Place::new(tmp)));
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

        // Coerce `T` into `?T` (`union u8 { void, T }`)
        if let Type::Union { variants, .. } = &self.compiler.program.types[target_ty.0 as usize]
            && variants.len() == 2
            && matches!(
                self.compiler.program.types[variants[0].0 as usize],
                Type::Void
            )
            && variants[1] == src_ty
        {
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

        Ok(op)
    }

    fn lower_stmt(&mut self, stmt: &Stmt) -> Result<(), String> {
        match stmt {
            Stmt::Let {
                name, ty, init, ..
            } => {
                let expected_ty = if let Some(te) = ty {
                    Some(self.compiler.resolve_type_expr(
                        &self.mod_path,
                        self.owner_ty,
                        &self.comptime_env,
                        te,
                    )?)
                } else {
                    None
                };
                let (init_op, inferred_ty) = self.lower_expr(init, expected_ty)?;
                if self.is_terminated() {
                    return Ok(());
                }
                let var_ty = expected_ty.unwrap_or(inferred_ty);
                let coerced_op = self.coerce_operand(init_op, inferred_ty, var_ty)?;
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
                    let (rhs_op, _) = self.lower_expr(value, Some(target_ty))?;
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
            Stmt::Return(opt_expr) => {
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
        if self.compiler.is_linear_type(ty_id) {
            return false;
        }
        if self
            .compiler
            .program
            .destructors
            .iter()
            .any(|(t, _)| *t == ty_id)
        {
            return false;
        }
        if let Some(comp) = self.compiler.composites.get(&ty_id)
            && comp.is_struct
            && (comp.drop_fn.is_some() || comp.clone_fn.is_some())
        {
            return false;
        }
        match &self.compiler.program.types[ty_id.0 as usize] {
            Type::Struct(fields) => fields.iter().all(|&f| self.is_copy_type(f)),
            Type::Array { elem, .. } => self.is_copy_type(*elem),
            Type::Union { variants, .. } => variants.iter().all(|&v| self.is_copy_type(v)),
            _ => true,
        }
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
                place.projections.push(Projection::Deref);
                Ok((place, pointee))
            }
            Expr::Field { base, field } => {
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
                let unwrapped_expected = expected_ty.map(|t| {
                    if let Type::Union { variants, .. } =
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
                    if let Some(enum_ty) = enum_ty_opt
                        && let Some((_, variants)) = self.compiler.enums.get(&enum_ty)
                        && let Some((_, val)) = variants.iter().find(|(vn, _)| vn == vname)
                    {
                        return Ok((Operand::Const(ConstValue::I64(*val)), enum_ty));
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
                    });
                let (place, ty) = self.lower_place(expr, want_mut)?;
                let op = if self.is_copy_type(ty) {
                    Operand::Copy(place)
                } else {
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
                let (l_op, l_ty) = self.lower_expr(lhs, expected_ty)?;
                let (r_op, _) = self.lower_expr(rhs, Some(l_ty))?;
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
                let comp_ty = self.compiler.resolve_type_expr(
                    &self.mod_path,
                    self.owner_ty,
                    &self.comptime_env,
                    ty,
                )?;
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
                let (place, ty_id) = self.lower_place(inner, false)?;
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
                self.cleanup_all_scopes();
                self.terminate(Terminator::Unreachable);
                let never_ty = self.compiler.intern_type(Type::Never);
                Ok((Operand::Const(ConstValue::Void), never_ty))
            }
            Expr::Return(opt_expr) => {
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
        if rel_projs.contains(&Projection::Deref) {
            return Err(format!(
                "Co-Residence violation on '{}.{}': '&rel' target must be inline storage within 'self' and cannot traverse a pointer or slice dereference",
                struct_name, field_name
            ));
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
                return Err(format!(
                    "Struct '{}' does not implement `clone`",
                    comp.name
                ));
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
                is_linear: false,
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
            | Expr::IntrinsicDrop(inner) => {
                self.collect_captures_in_expr(inner, bound, captures);
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
                    let first_ct_params: Vec<(String, Option<TypeConstraint>)> = overloads[0]
                        .2
                        .params
                        .iter()
                        .filter(|p| p.is_comptime)
                        .map(|p| (p.name.clone(), p.ty.as_type_constraint()))
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
                        let ct_params: Vec<(String, Option<TypeConstraint>)> = cand_decl
                            .params
                            .iter()
                            .filter(|p| p.is_comptime)
                            .map(|p| (p.name.clone(), p.ty.as_type_constraint()))
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
                                let unconstrained_ct: Vec<(String, Option<TypeConstraint>)> =
                                    cand_decl
                                        .params
                                        .iter()
                                        .filter(|p| p.is_comptime)
                                        .map(|p| (p.name.clone(), None))
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
        let Some(comp) = self.compiler.composites.get(&comp_ty).cloned() else {
            return Err(format!("Type {comp_ty} has no methods"));
        };
        let Some((m_vis, _)) = comp.methods.get(method_name) else {
            return Err(format!(
                "Type '{}' has no method '{}'",
                comp.name, method_name
            ));
        };
        if comp.is_struct && *m_vis == Visibility::Private && self.owner_ty != Some(comp_ty) {
            return Err(format!(
                "Cannot call private method '{}' of struct '{}' outside its 'struct {{ ... }}' block",
                method_name, comp.name
            ));
        }
        let fn_id = comp.method_fn_ids[method_name];
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
        let (recv_place, recv_ty) = self.lower_place(receiver, false)?;
        let comp_ty = if let Type::Ptr { pointee, .. } =
            self.compiler.program.types[recv_ty.0 as usize]
        {
            pointee
        } else {
            recv_ty
        };

        // 1. Check inherent methods defined inside `record { ... }` or `struct { ... }` first
        let mut pre_lowered_rt_args: Option<Vec<(Operand, TypeId)>> = None;
        let (fn_id, rt_arg_exprs): (FuncId, Vec<&Expr>) =
            if let Some(comp) = self.compiler.composites.get(&comp_ty).cloned()
                && let Some((m_vis, m_decl)) = comp.methods.get(method_name)
            {
                if comp.is_struct
                    && *m_vis == Visibility::Private
                    && self.owner_ty != Some(comp_ty)
                {
                    return Err(format!(
                        "Cannot call private method '{}' of struct '{}' outside its 'struct {{ ... }}' block",
                        method_name, comp.name
                    ));
                }
                if !m_decl.params.iter().any(|p| p.is_comptime) {
                    (comp.method_fn_ids[method_name], args.iter().collect())
                } else {
                    let rt_params_after_self: Vec<_> = m_decl
                        .params
                        .iter()
                        .filter(|p| !p.is_comptime)
                        .skip(1)
                        .collect();
                    let ct_params: Vec<(String, Option<TypeConstraint>)> = m_decl
                        .params
                        .iter()
                        .filter(|p| p.is_comptime)
                        .map(|p| (p.name.clone(), p.ty.as_type_constraint()))
                        .collect();
                    let mut ct_args = Vec::with_capacity(ct_params.len());
                    let mut rt_exprs = Vec::new();
                    if args.len() == rt_params_after_self.len() {
                        let mut lowered = Vec::with_capacity(args.len());
                        for (i, arg_expr) in args.iter().enumerate() {
                            let exp_ty = rt_params_after_self.get(i).and_then(|rp| {
                                self.compiler
                                    .resolve_type_expr(
                                        &comp.def_module,
                                        Some(comp_ty),
                                        &comp.comptime_env,
                                        &rp.ty,
                                    )
                                    .ok()
                            });
                            lowered.push(self.lower_expr(arg_expr, exp_ty)?);
                        }
                        let unconstrained_ct: Vec<(String, Option<TypeConstraint>)> = ct_params
                            .iter()
                            .map(|(n, _)| (n.clone(), None))
                            .collect();
                        let mut inferred = comp.comptime_env.clone();
                        for (rt_p, (_, a_ty)) in
                            rt_params_after_self.iter().zip(lowered.iter())
                        {
                            if self
                                .compiler
                                .unify_type_pattern(
                                    &comp.def_module,
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
                                    comp.name,
                                    method_name
                                ));
                            }
                        }
                        for (p_name, constraint_opt) in &ct_params {
                            let Some(val) = inferred.get(p_name).cloned() else {
                                return Err(format!(
                                    "Could not infer comptime parameter '{}' of method '{}.{}'",
                                    p_name, comp.name, method_name
                                ));
                            };
                            if let Some(constraint) = constraint_opt
                                && let ComptimeVal::Type(arg_ty) = val
                                && !self.compiler.type_satisfies_constraint(arg_ty, *constraint)
                            {
                                let t_disp = self
                                    .compiler
                                    .composites
                                    .get(&arg_ty)
                                    .map(|c| c.name.clone())
                                    .unwrap_or_else(|| {
                                        self.compiler.program.types[arg_ty.0 as usize].to_string()
                                    });
                                return Err(format!(
                                    "Type '{}' does not satisfy comptime constraint '{}' for parameter '{}' in '{}.{}'",
                                    t_disp,
                                    constraint.name(),
                                    p_name,
                                    comp.name,
                                    method_name
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
                                        p.name, comp.name, method_name
                                    )
                                })?;
                                let val = self.compiler.eval_comptime_val(
                                    &self.mod_path,
                                    self.owner_ty,
                                    &self.comptime_env,
                                    arg_expr,
                                )?;
                                if let Some(constraint) = p.ty.as_type_constraint()
                                    && let ComptimeVal::Type(arg_ty) = val
                                    && !self.compiler.type_satisfies_constraint(arg_ty, constraint)
                                {
                                    let t_disp = self
                                        .compiler
                                        .composites
                                        .get(&arg_ty)
                                        .map(|c| c.name.clone())
                                        .unwrap_or_else(|| {
                                            self.compiler.program.types[arg_ty.0 as usize]
                                                .to_string()
                                        });
                                    return Err(format!(
                                        "Type '{}' does not satisfy comptime constraint '{}' for parameter '{}' in '{}.{}'",
                                        t_disp,
                                        constraint.name(),
                                        p.name,
                                        comp.name,
                                        method_name
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
                                    p.name, comp.name, method_name
                                ));
                            }
                        }
                    }
                    let key = (comp_ty, method_name.to_string(), ct_args.clone());
                    let inst_fn_id =
                        if let Some(&existing_id) =
                            self.compiler.memoized_inherent_methods.get(&key)
                        {
                            existing_id
                        } else {
                            let mut method_env = comp.comptime_env.clone();
                            for ((p_name, _), val) in ct_params.iter().zip(ct_args.iter()) {
                                method_env.insert(p_name.clone(), val.clone());
                            }
                            let new_id = self.compiler.schedule_method(
                                &comp.def_module,
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
                let (ext_mod, ext_orig_name, ext_decl, mut inferred) = self
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
                let ext_fn_id = self.compiler.get_or_instantiate_func(
                    &ext_mod,
                    &ext_orig_name,
                    &ct_args,
                )?;
                (ext_fn_id, rt_exprs)
            };

        let (param_tys, ret_ty) = self.compiler.func_sigs[&fn_id].clone();
        let self_param_ty = param_tys[0];

        // Automatically borrow or deref `recv_place` to match `self` parameter type (`&Self`, `&mut Self`, or `Self`)
        let self_arg = if recv_ty == self_param_ty {
            if self.is_copy_type(recv_ty) {
                Operand::Copy(recv_place)
            } else {
                Operand::Move(recv_place)
            }
        } else if let Type::Ptr { mutable, pointee } =
            self.compiler.program.types[self_param_ty.0 as usize]
            && pointee == comp_ty
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
            Operand::Copy(Place::new(ref_tmp))
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
        Ok((Operand::Move(Place::new(dst)), ret_ty))
    }
}
