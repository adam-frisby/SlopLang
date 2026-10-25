use std::collections::HashMap;

use crate::ast::{
    Block, Expr, ExternFuncDecl, FieldDecl, FuncDecl, ImportTargets, Item, ModuleAst, Stmt,
    TypeExpr, Visibility,
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

#[derive(Debug, Clone)]
struct CompositeInfo {
    name: String,
    is_struct: bool,
    def_module: String,
    fields: Vec<(String, TypeId, Visibility, Option<Expr>)>,
    methods: HashMap<String, (Visibility, FuncDecl)>,
    method_fn_ids: HashMap<String, FuncId>,
    default_fn: Option<FuncId>,
    clone_fn: Option<FuncId>,
    drop_fn: Option<FuncId>,
}

#[derive(Debug, Clone)]
enum ResolvedItem {
    Module(String),
    Type(String, String),
    Func(String, String),
    ExternFunc(String, String),
}

#[derive(Clone)]
struct PendingFunc {
    func_id: FuncId,
    module_path: String,
    owner_ty: Option<TypeId>,
    decl: FuncDecl,
    comptime_env: HashMap<String, ComptimeVal>,
}

pub struct Compiler {
    modules: HashMap<String, ModuleAst>,
    pub program: Program,
    composites: HashMap<TypeId, CompositeInfo>,
    named_types: HashMap<(String, String), TypeId>,
    memoized_type_calls: HashMap<(String, String, Vec<ComptimeVal>), TypeId>,
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
                globals: Vec::new(),
                externs: Vec::new(),
                functions: Vec::new(),
            },
            composites: HashMap::new(),
            named_types: HashMap::new(),
            memoized_type_calls: HashMap::new(),
            resolved_funcs: HashMap::new(),
            resolved_externs: HashMap::new(),
            func_sigs: HashMap::new(),
            pending_funcs: Vec::new(),
        }
    }

    /// Compiles a single root module from source, runs Stage 3 move/drop elaboration
    /// and NLL borrow checking, and returns the verified Stage 3 `Program`.
    pub fn compile_source(src: &str) -> Result<Program, String> {
        Self::compile_package(&[("root", src)])
    }

    /// Compiles a multi-module package (`[(module_path, source_code), ...]`),
    /// enforcing module & `struct`-block visibility, specializing `comptime` types/functions,
    /// and running Stage 3 drop elaboration and NLL borrow checking.
    pub fn compile_package(sources: &[(&str, &str)]) -> Result<Program, String> {
        let mut compiler = Self::new();
        for &(mod_path, src) in sources {
            let ast = SurfaceParser::parse_module(src)
                .map_err(|e| format!("In module '{mod_path}': {e}"))?;
            compiler.modules.insert(mod_path.to_string(), ast);
        }
        compiler.compile_all()?;
        elaborate_drops(&mut compiler.program)?;
        check_borrows(&compiler.program)?;
        Ok(compiler.program)
    }

    fn intern_type(&mut self, ty: Type) -> TypeId {
        if let Some(idx) = self.program.types.iter().position(|t| *t == ty) {
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

    fn compile_all(&mut self) -> Result<(), String> {
        let mod_names: Vec<String> = self.modules.keys().cloned().collect();

        // 1. Register extern functions
        for mod_path in &mod_names {
            let items = self.modules[mod_path].items.clone();
            for item in items {
                if let Item::ExternFunc(ext) = item {
                    self.register_extern(mod_path, &ext)?;
                }
            }
        }

        // 2. Register concrete top-level types (`record`, `struct`, `type`)
        for mod_path in &mod_names {
            let items = self.modules[mod_path].items.clone();
            for item in items {
                if let Item::TypeDecl { name, .. } = item {
                    let _ = self.resolve_named_type(mod_path, &name)?;
                }
            }
        }

        // 3. Register non-comptime top-level functions
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
    ) -> Result<Option<(Item, Visibility)>, String> {
        let Some(ast) = self.modules.get(target_mod) else {
            return Err(format!("Undefined module '{target_mod}'"));
        };
        for item in &ast.items {
            match item {
                Item::Func(f) if f.name == name => {
                    self.check_item_visibility(from_mod, target_mod, name, f.vis)?;
                    return Ok(Some((item.clone(), f.vis)));
                }
                Item::ExternFunc(e) if e.name == name => {
                    self.check_item_visibility(from_mod, target_mod, name, e.vis)?;
                    return Ok(Some((item.clone(), e.vis)));
                }
                Item::TypeDecl {
                    vis,
                    name: tname,
                    ..
                } if tname == name => {
                    self.check_item_visibility(from_mod, target_mod, name, *vis)?;
                    return Ok(Some((item.clone(), *vis)));
                }
                _ => {}
            }
        }
        // Check `pub import` re-exports
        for imp in &ast.imports {
            if from_mod != target_mod && imp.vis == Visibility::Private {
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
                ImportTargets::Module(_) => {}
            }
        }
        Ok(None)
    }

    fn resolve_path(&self, cur_mod: &str, path: &[String]) -> Result<ResolvedItem, String> {
        if path.len() == 1 {
            let name = &path[0];
            // 1. Local module item
            if let Some((item, _)) = self.find_item_in_module(cur_mod, cur_mod, name)? {
                return Ok(match item {
                    Item::Func(_) => ResolvedItem::Func(cur_mod.to_string(), name.clone()),
                    Item::ExternFunc(_) => {
                        ResolvedItem::ExternFunc(cur_mod.to_string(), name.clone())
                    }
                    Item::TypeDecl { .. } => ResolvedItem::Type(cur_mod.to_string(), name.clone()),
                });
            }
            // 2. Imported item or module
            let ast = &self.modules[cur_mod];
            for imp in &ast.imports {
                let target_mod = imp.path.join("::");
                match &imp.targets {
                    ImportTargets::Module(alias) => {
                        let bound = alias
                            .as_deref()
                            .unwrap_or_else(|| imp.path.last().map(String::as_str).unwrap_or(""));
                        if bound == name {
                            return Ok(ResolvedItem::Module(target_mod));
                        }
                    }
                    ImportTargets::Items(list) => {
                        for (orig, alias) in list {
                            let bound = alias.as_deref().unwrap_or(orig);
                            if bound == name {
                                let Some((item, _)) =
                                    self.find_item_in_module(cur_mod, &target_mod, orig)?
                                else {
                                    return Err(format!(
                                        "Item '{orig}' not found in module '{target_mod}'"
                                    ));
                                };
                                return Ok(match item {
                                    Item::Func(_) => ResolvedItem::Func(target_mod, orig.clone()),
                                    Item::ExternFunc(_) => {
                                        ResolvedItem::ExternFunc(target_mod, orig.clone())
                                    }
                                    Item::TypeDecl { .. } => {
                                        ResolvedItem::Type(target_mod, orig.clone())
                                    }
                                });
                            }
                        }
                    }
                    ImportTargets::Glob => {
                        if let Some((item, _)) =
                            self.find_item_in_module(cur_mod, &target_mod, name)?
                        {
                            return Ok(match item {
                                Item::Func(_) => ResolvedItem::Func(target_mod, name.clone()),
                                Item::ExternFunc(_) => {
                                    ResolvedItem::ExternFunc(target_mod, name.clone())
                                }
                                Item::TypeDecl { .. } => {
                                    ResolvedItem::Type(target_mod, name.clone())
                                }
                            });
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
            let Some((item, _)) = self.find_item_in_module(cur_mod, &target_mod, item_name)?
            else {
                return Err(format!(
                    "Item '{item_name}' not found in module '{target_mod}'"
                ));
            };
            Ok(match item {
                Item::Func(_) => ResolvedItem::Func(target_mod, item_name.clone()),
                Item::ExternFunc(_) => ResolvedItem::ExternFunc(target_mod, item_name.clone()),
                Item::TypeDecl { .. } => ResolvedItem::Type(target_mod, item_name.clone()),
            })
        }
    }

    fn resolve_named_type(&mut self, mod_path: &str, name: &str) -> Result<TypeId, String> {
        let key = (mod_path.to_string(), name.to_string());
        if let Some(&id) = self.named_types.get(&key) {
            return Ok(id);
        }
        let Some((Item::TypeDecl { ty, .. }, _)) =
            self.find_item_in_module(mod_path, mod_path, name)?
        else {
            return Err(format!("Type '{name}' not found in '{mod_path}'"));
        };
        let env = HashMap::new();
        let ty_id = self.instantiate_type_decl(mod_path, name, &env, &ty)?;
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
            TypeExpr::Record { fields, methods } => {
                self.instantiate_composite(mod_path, type_name, false, env, fields, methods, None, None, None)
            }
            TypeExpr::Struct {
                fields,
                methods,
                default_hook,
                clone_hook,
                drop_hook,
            } => self.instantiate_composite(
                mod_path,
                type_name,
                true,
                env,
                fields,
                methods,
                default_hook.clone(),
                clone_hook.clone(),
                drop_hook.clone(),
            ),
            other => self.resolve_type_expr(mod_path, None, env, other),
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn instantiate_composite(
        &mut self,
        mod_path: &str,
        type_name: &str,
        is_struct: bool,
        env: &HashMap<String, ComptimeVal>,
        fields: &[FieldDecl],
        methods: &[FuncDecl],
        default_hook: Option<Block>,
        clone_hook: Option<(String, Block)>,
        drop_hook: Option<(String, Block)>,
    ) -> Result<TypeId, String> {
        let mut field_tys = Vec::with_capacity(fields.len());
        let mut field_infos = Vec::with_capacity(fields.len());
        for f in fields {
            let f_ty = self.resolve_type_expr(mod_path, None, env, &f.ty)?;
            field_tys.push(f_ty);
            field_infos.push((f.name.clone(), f_ty, f.vis, f.default_val.clone()));
        }

        // Every distinct record/struct declaration gets a distinct TypeId so its field names,
        // defaults, and methods in `self.composites` never collide (tuples use `intern_type`).
        let ty_id = self.alloc_distinct_type(Type::Struct(field_tys));

        let mut method_map = HashMap::new();
        for m in methods {
            method_map.insert(m.name.clone(), (m.vis, m.clone()));
        }

        let info = CompositeInfo {
            name: type_name.to_string(),
            is_struct,
            def_module: mod_path.to_string(),
            fields: field_infos,
            methods: method_map,
            method_fn_ids: HashMap::new(),
            default_fn: None,
            clone_fn: None,
            drop_fn: None,
        };
        self.composites.insert(ty_id, info);

        // Instantiate methods
        for m in methods {
            let fn_id = self.schedule_method(mod_path, ty_id, env, m)?;
            self.composites
                .get_mut(&ty_id)
                .unwrap()
                .method_fn_ids
                .insert(m.name.clone(), fn_id);
        }

        // Instantiate `default`, `clone`, `drop` lifecycle hooks on `struct`
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
        self.pending_funcs.push(PendingFunc {
            func_id: fn_id,
            module_path: mod_path.to_string(),
            owner_ty: Some(owner_ty),
            decl: decl.clone(),
            comptime_env: env.clone(),
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
        // Apply Section 5.1 Lifetime Elision rule for `pub` functions returning references:
        let ret_borrows = if vis == Visibility::Pub
            && matches!(self.program.types[ret_ty.0 as usize], Type::Ptr { .. })
            && !param_tys.is_empty()
            && matches!(self.program.types[param_tys[0].0 as usize], Type::Ptr { .. })
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
        let Some((Item::Func(decl), _)) = self.find_item_in_module(mod_path, mod_path, name)?
        else {
            return Err(format!("Function '{name}' not found in '{mod_path}'"));
        };
        let mut env = HashMap::new();
        let mut ct_idx = 0;
        for p in &decl.params {
            if p.is_comptime {
                let val = comptime_args
                    .get(ct_idx)
                    .ok_or_else(|| format!("Missing comptime argument for '{}' in '{}'", p.name, name))?
                    .clone();
                env.insert(p.name.clone(), val);
                ct_idx += 1;
            }
        }
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
            TypeExpr::MetaType => Ok(self.intern_type(Type::MetaType)),
            TypeExpr::SelfType => {
                self_ty.ok_or_else(|| "'Self' type used outside of a struct/record context".to_string())
            }
            TypeExpr::Ref { mutable, inner } | TypeExpr::Ptr { mutable, inner } => {
                let pointee = self.resolve_type_expr(mod_path, self_ty, env, inner)?;
                Ok(self.intern_type(Type::Ptr {
                    mutable: *mutable,
                    pointee,
                }))
            }
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
            TypeExpr::Record { fields, methods } => {
                self.instantiate_composite(mod_path, "<anon_record>", false, env, fields, methods, None, None, None)
            }
            TypeExpr::Struct {
                fields,
                methods,
                default_hook,
                clone_hook,
                drop_hook,
            } => self.instantiate_composite(
                mod_path,
                "<anon_struct>",
                true,
                env,
                fields,
                methods,
                default_hook.clone(),
                clone_hook.clone(),
                drop_hook.clone(),
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
        let Some((Item::Func(decl), _)) = self.find_item_in_module(mod_path, mod_path, fname)?
        else {
            return Err(format!("Comptime function '{fname}' not found in '{mod_path}'"));
        };
        if decl.params.len() != args.len() {
            return Err(format!(
                "Comptime function '{fname}' expects {} args, got {}",
                decl.params.len(),
                args.len()
            ));
        }
        let mut local_env = HashMap::new();
        for (p, arg) in decl.params.iter().zip(args.iter()) {
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
                        &local_env,
                        fields,
                        methods,
                        None,
                        None,
                        None,
                    )?;
                    return Ok(ComptimeVal::Type(ty_id));
                }
                Stmt::Return(Some(Expr::TypeVal(TypeExpr::Struct {
                    fields,
                    methods,
                    default_hook,
                    clone_hook,
                    drop_hook,
                }))) => {
                    let ty_id = self.instantiate_composite(
                        mod_path,
                        fname,
                        true,
                        &local_env,
                        fields,
                        methods,
                        default_hook.clone(),
                        clone_hook.clone(),
                        drop_hook.clone(),
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
    locals: Vec<TypeId>,
    blocks: Vec<BasicBlock>,
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
            locals: existing_locals,
            blocks: vec![BasicBlock {
                statements: Vec::new(),
                terminator: Terminator::Unreachable,
            }],
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
    }

    fn is_terminated(&self) -> bool {
        !matches!(
            self.blocks[self.cur_block.0 as usize].terminator,
            Terminator::Unreachable
        )
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

    fn emit_drop_and_dead(&mut self, local: LocalId) {
        let arg_count = self
            .decl
            .params
            .iter()
            .filter(|p| !p.is_comptime)
            .count() as u32;
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
        // Bind runtime parameters into root scope
        let mut arg_local_idx = 1u32;
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

        if !self.is_terminated() {
            let ret_ty = self.locals[0];
            if matches!(self.compiler.program.types[ret_ty.0 as usize], Type::Void) {
                self.emit(Statement::Assign(
                    Place::new(LocalId(0)),
                    Rvalue::Use(Operand::Const(ConstValue::Void)),
                ));
                self.cleanup_all_scopes();
                self.terminate(Terminator::Return);
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
                let _ = self.lower_expr(expr, None)?;
                Ok(())
            }
        }
    }

    fn is_copy_type(&self, ty_id: TypeId) -> bool {
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
                let (local, ty) = self
                    .lookup_var(&p[0])
                    .ok_or_else(|| format!("Undefined local variable '{}'", p[0]))?;
                Ok((Place::new(local), ty))
            }
            Expr::Deref(inner) => {
                let (mut place, ty) = self.lower_place(inner, false)?;
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
                let (f_idx, f_ty) = self.check_field_access(base_ty, field)?;
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
                let elem_ty = match self.compiler.program.types[base_ty.0 as usize] {
                    Type::Array { elem, .. } | Type::Simd { elem, .. } => elem,
                    _ => return Err(format!("Cannot index non-array/simd type {base_ty}")),
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
                    if let Some(ComptimeVal::Int(n)) = self.comptime_env.get(&p[0]).cloned() {
                        let ty = expected_ty.unwrap_or_else(|| {
                            self.compiler.intern_type(Type::Int {
                                signed: true,
                                bits: 64,
                            })
                        });
                        return Ok((Operand::Const(ConstValue::I64(n)), ty));
                    }
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
                let (place, ty) = self.lower_place(expr, false)?;
                let op = if self.is_copy_type(ty) {
                    Operand::Copy(place)
                } else {
                    Operand::Move(place)
                };
                Ok((op, ty))
            }
            Expr::Ref { mutable, expr: inner } => {
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
                let (fb_op, _) = self.lower_expr(fallback, Some(payload_ty))?;
                self.emit(Statement::Assign(Place::new(res_local), Rvalue::Use(fb_op)));
                self.terminate(Terminator::Goto { target: join_bb });

                self.cur_block = join_bb;
                Ok((Operand::Move(Place::new(res_local)), payload_ty))
            }
            Expr::TupleLit(elems) => {
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
                let Type::Simd { elem, .. } = self.compiler.program.types[simd_ty.0 as usize]
                else {
                    return Err(format!("Expected SIMD type in SimdLit, got {simd_ty}"));
                };
                let mut ops = Vec::with_capacity(elems.len());
                for e in elems {
                    let (op, _) = self.lower_expr(e, Some(elem))?;
                    ops.push(op);
                }
                let tmp = self.alloc_temp(simd_ty);
                self.emit(Statement::Assign(
                    Place::new(tmp),
                    Rvalue::Aggregate(simd_ty, ops),
                ));
                Ok((Operand::Copy(Place::new(tmp)), simd_ty))
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
            Expr::UnsafeBlock(blk) => {
                self.lower_scoped_block(blk)?;
                let void_ty = self.compiler.intern_type(Type::Void);
                Ok((Operand::Const(ConstValue::Void), void_ty))
            }
            Expr::Call { callee, args } => self.lower_call(callee, args),
            Expr::MethodCall {
                receiver,
                method,
                args,
            } => self.lower_method_call(receiver, method, args),
        }
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

    fn lower_call(&mut self, callee: &Expr, args: &[Expr]) -> Result<(Operand, TypeId), String> {
        let Expr::Path(path) = callee else {
            return Err(format!("Unsupported callee expression {callee:?}"));
        };

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
                let fn_id = self.compiler.resolved_externs[&(emod, ename)];
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
                Ok((Operand::Move(Place::new(dst)), ret_ty))
            }
            ResolvedItem::Func(fmod, fname) => {
                let Some((Item::Func(decl), _)) =
                    self.compiler.find_item_in_module(&self.mod_path, &fmod, &fname)?
                else {
                    return Err(format!("Function '{fname}' not found in '{fmod}'"));
                };
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
        Ok((Operand::Move(Place::new(dst)), ret_ty))
    }

    fn lower_method_call(
        &mut self,
        receiver: &Expr,
        method_name: &str,
        args: &[Expr],
    ) -> Result<(Operand, TypeId), String> {
        let (recv_place, recv_ty) = self.lower_place(receiver, false)?;
        let comp_ty = if let Type::Ptr { pointee, .. } =
            self.compiler.program.types[recv_ty.0 as usize]
        {
            pointee
        } else {
            recv_ty
        };
        let Some(comp) = self.compiler.composites.get(&comp_ty).cloned() else {
            return Err(format!("Type {comp_ty} has no method '{method_name}'"));
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

        let mut lowered_args = Vec::with_capacity(args.len() + 1);
        lowered_args.push(self_arg);
        for (i, arg) in args.iter().enumerate() {
            let exp = param_tys.get(i + 1).copied();
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
        Ok((Operand::Move(Place::new(dst)), ret_ty))
    }
}
