mod expr;
mod lexer;

pub use lexer::{SurfToken, SurfTokenKind, SurfaceLexer};

use crate::ast::{
    BindMode, Block, BorrowContractItem, CIntKind, CloneHookDecl, ConstDecl, DropHookDecl, Expr,
    ExternFuncDecl, FieldDecl, FmtSegment, ForIter, FuncDecl, ImplDecl, ImportDecl, ImportTargets,
    Item, MatchPat, ModuleAst, OpaqueBody, OpaqueOwnership, Param, PtrKind, SelectArm, SelectOp,
    StaticDecl, Stmt, ThreadDecl, TraitMethodDecl, TypeConstraint, TypeExpr, Visibility,
    WherePredicate,
};
use crate::ir::{BinOp, UnOp};

/// Whether `s` is a positional parameter name (`_1`, `_2`, ...) as used in function-type contracts.
pub(crate) fn is_positional_param(s: &str) -> bool {
    s.strip_prefix('_')
        .is_some_and(|d| !d.is_empty() && d.bytes().all(|b| b.is_ascii_digit()))
}

/// Modifiers parsed from `opaque(...)`: ownership discipline, `unsafe sync`, and owned type parameters.
struct OpaqueMods {
    ownership: OpaqueOwnership,
    threads: ThreadDecl,
    owns: Vec<String>,
    borrows: Vec<String>,
}

impl OpaqueMods {
    /// `unsafe_sync` is the legacy `unsafe sync opaque` spelling of `opaque(unsafe sync)`.
    fn new(ownership: OpaqueOwnership, unsafe_sync: bool) -> Self {
        Self {
            ownership,
            threads: ThreadDecl {
                unsafe_sync,
                ..ThreadDecl::default()
            },
            owns: Vec::new(),
            borrows: Vec::new(),
        }
    }
}

pub struct SurfaceParser {
    tokens: Vec<SurfToken>,
    pos: usize,
    current_type_name: Option<String>,
    extra_items: Vec<Item>,
    /// Negative bounds from the comptime parameters being parsed (`[T: !sync]`), which the
    /// enclosing declaration takes as `where` clauses.
    pending_where: Vec<WherePredicate>,
    /// Token position where the current `if` / `while` / `for` / `match` head began: there,
    /// outside parentheses and brackets, `name {}` is the name followed by an empty block rather
    /// than an empty struct literal.
    cond_start: Option<usize>,
}

impl SurfaceParser {
    pub fn parse_module(src: &str) -> Result<ModuleAst, String> {
        let tokens = SurfaceLexer::new(src).tokenize()?;
        let mut parser = Self {
            tokens,
            pos: 0,
            current_type_name: None,
            cond_start: None,
            extra_items: Vec::new(),
            pending_where: Vec::new(),
        };
        parser.parse_module_inner()
    }

    fn peek(&self) -> &SurfToken {
        &self.tokens[self.pos.min(self.tokens.len() - 1)]
    }

    fn peek_n(&self, n: usize) -> &SurfToken {
        &self.tokens[(self.pos + n).min(self.tokens.len() - 1)]
    }

    fn advance(&mut self) -> SurfToken {
        let tok = self.peek().clone();
        if self.pos + 1 < self.tokens.len() {
            self.pos += 1;
        }
        tok
    }

    fn expect(&mut self, expected: &SurfTokenKind) -> Result<SurfToken, String> {
        let tok = self.peek().clone();
        if &tok.kind == expected {
            self.advance();
            Ok(tok)
        } else {
            Err(format!(
                "Expected {:?}, found {:?} at {}:{}",
                expected, tok.kind, tok.line, tok.col
            ))
        }
    }

    fn expect_ident(&mut self) -> Result<String, String> {
        let tok = self.peek().clone();
        match tok.kind {
            SurfTokenKind::Ident(s) => {
                self.advance();
                Ok(s)
            }
            SurfTokenKind::Sync => {
                self.advance();
                Ok("sync".to_string())
            }
            _ => Err(format!(
                "Expected identifier, found {:?} at {}:{}",
                tok.kind, tok.line, tok.col
            )),
        }
    }

    fn parse_visibility(&mut self) -> Result<Visibility, String> {
        if self.peek().kind == SurfTokenKind::Pub {
            self.advance();
            if matches!(&self.peek().kind, SurfTokenKind::Ident(s) if s == "export") {
                let tok = self.peek();
                Err(format!(
                    "Write 'export', not 'pub export' (an export is already public), at {}:{}",
                    tok.line, tok.col
                ))
            } else if self.peek().kind == SurfTokenKind::LParen {
                self.advance();
                let tok = self.advance();
                match tok.kind {
                    SurfTokenKind::Ident(s) if s == "mod" => {}
                    SurfTokenKind::Ident(s) if s == "pkg" => {
                        return Err(format!(
                            "'pub(pkg)' was removed: the compiler has no packages yet, so it meant 'pub'; use 'pub', or 'pub(mod)' for a method visible to its module, at {}:{}",
                            tok.line, tok.col
                        ));
                    }
                    other => {
                        return Err(format!(
                            "Expected 'mod' in 'pub(...)', found {other:?} at {}:{}",
                            tok.line, tok.col
                        ));
                    }
                }
                self.expect(&SurfTokenKind::RParen)?;
                // Only methods take `pub(mod)`: a top-level item is already private to its module,
                // and fields of an `opaque` are private to its block.
                if self.peek().kind != SurfTokenKind::Fn {
                    let tok = self.peek();
                    return Err(format!(
                        "'pub(mod)' applies only to methods ('pub(mod) fn ...' inside a type's block), at {}:{}",
                        tok.line, tok.col
                    ));
                }
                Ok(Visibility::PubMod)
            } else {
                Ok(Visibility::Pub)
            }
        } else if matches!(&self.peek().kind, SurfTokenKind::Ident(s) if s == "export") {
            self.advance();
            Ok(Visibility::Export)
        } else {
            Ok(Visibility::Private)
        }
    }

    fn parse_module_inner(&mut self) -> Result<ModuleAst, String> {
        let mut imports = Vec::new();
        let mut items = Vec::new();

        while self.peek().kind != SurfTokenKind::Eof {
            let vis = self.parse_visibility()?;
            if vis == Visibility::PubMod {
                return Err(
                    "'pub(mod)' applies only to methods; a top-level item without 'pub' is already private to its module"
                        .to_string(),
                );
            }
            match &self.peek().kind {
                SurfTokenKind::Import => {
                    imports.push(self.parse_import(vis)?);
                }
                SurfTokenKind::Fn => {
                    items.push(Item::Func(self.parse_func_decl(vis)?));
                }
                SurfTokenKind::Unsafe if self.peek_n(1).kind == SurfTokenKind::Fn => {
                    items.push(Item::Func(self.parse_func_decl(vis)?));
                }
                SurfTokenKind::Ident(s) if s == "impl" => {
                    if vis != Visibility::Private {
                        return Err(
                            "'impl' blocks take no visibility modifier; trait methods are as visible as the trait and type"
                                .to_string(),
                        );
                    }
                    items.push(Item::Impl(self.parse_module_impl()?));
                }
                SurfTokenKind::Const | SurfTokenKind::Comptime => {
                    items.push(Item::Const(self.parse_const_decl(vis)?));
                }
                SurfTokenKind::Ident(s) if s == "static" => {
                    items.push(Item::Static(self.parse_static_decl(vis)?));
                }
                SurfTokenKind::Ident(s)
                    if s == "safe"
                        && self.peek_n(1).kind == SurfTokenKind::Extern
                        && self.peek_n(2).kind == SurfTokenKind::Fn =>
                {
                    self.advance(); // consume 'safe'
                    let mut ext = self.parse_extern_func(vis)?;
                    ext.is_safe = true;
                    items.push(Item::ExternFunc(ext));
                }
                SurfTokenKind::Extern => {
                    if matches!(&self.peek_n(1).kind, SurfTokenKind::Ident(s) if s == "opaque") {
                        self.advance(); // consume 'extern'
                        self.advance(); // consume 'opaque'
                        let name = self.expect_ident()?;
                        let methods = if self.peek().kind == SurfTokenKind::LBrace {
                            let m = self.parse_opaque_methods_body()?;
                            if self.peek().kind == SurfTokenKind::Semi {
                                self.advance();
                            }
                            m
                        } else {
                            self.expect(&SurfTokenKind::Semi)?;
                            Vec::new()
                        };
                        items.push(Item::TypeDecl {
                            vis,
                            name,
                            ty: TypeExpr::OpaqueDef { methods },
                            alias: false,
                        });
                    } else {
                        items.push(Item::ExternFunc(self.parse_extern_func(vis)?));
                    }
                }
                SurfTokenKind::Record => {
                    return Err(
                        "The 'record' keyword has been replaced by 'struct' for transparent product types"
                            .to_string(),
                    );
                }
                SurfTokenKind::Struct => {
                    self.advance();
                    if self.peek().kind == SurfTokenKind::LParen {
                        return Err(
                            "Ownership and synchronization modifiers ('struct(...)') are forbidden on transparent 'struct' types; use 'opaque(...)' for encapsulated types with custom ownership or synchronization"
                                .to_string(),
                        );
                    }
                    let name = self.expect_ident()?;
                    let prev_type_name = self.current_type_name.replace(name.clone());
                    let ty = self.parse_struct_body(false)?;
                    self.current_type_name = prev_type_name;
                    items.push(Item::TypeDecl {
                        vis,
                        name,
                        ty,
                        alias: false,
                    });
                }
                SurfTokenKind::Ident(s) if s == "packed" => {
                    self.advance();
                    if self.peek().kind == SurfTokenKind::Struct {
                        self.advance();
                        let name = self.expect_ident()?;
                        let ty = self.parse_struct_body(true)?;
                        items.push(Item::TypeDecl {
                            vis,
                            name,
                            ty,
                            alias: false,
                        });
                    } else if matches!(&self.peek().kind, SurfTokenKind::Ident(s2) if s2 == "opaque")
                    {
                        self.advance();
                        let mods = self.parse_opaque_modifiers()?;
                        let name = self.expect_ident()?;
                        let ty = self.parse_opaque_body(true, mods)?;
                        items.push(Item::TypeDecl {
                            vis,
                            name,
                            ty,
                            alias: false,
                        });
                    } else {
                        return Err(
                            "Expected 'struct' or 'opaque' after 'packed' in type declaration"
                                .to_string(),
                        );
                    }
                }
                SurfTokenKind::Linear => {
                    self.advance();
                    if self.peek().kind == SurfTokenKind::Sync {
                        return Err(
                            "Declaring a 'sync' opaque type asserts thread-safe synchronization and requires 'opaque(linear, unsafe sync)'"
                                .to_string(),
                        );
                    }
                    if matches!(&self.peek().kind, SurfTokenKind::Ident(s) if s == "opaque") {
                        self.advance();
                    } else {
                        return Err("Expected 'opaque' after 'linear' (prefer 'opaque(linear)')"
                            .to_string());
                    }
                    let name = self.expect_ident()?;
                    let ty = self.parse_opaque_body(
                        false,
                        OpaqueMods::new(OpaqueOwnership::Linear, false),
                    )?;
                    items.push(Item::TypeDecl {
                        vis,
                        name,
                        ty,
                        alias: false,
                    });
                }
                SurfTokenKind::Unsafe => {
                    self.advance();
                    let mut ownership = OpaqueOwnership::Default;
                    if self.peek().kind == SurfTokenKind::Linear {
                        self.advance();
                        ownership = OpaqueOwnership::Linear;
                    }
                    self.expect(&SurfTokenKind::Sync)?;
                    if self.peek().kind == SurfTokenKind::Linear {
                        self.advance();
                        ownership = OpaqueOwnership::Linear;
                    }
                    if matches!(&self.peek().kind, SurfTokenKind::Ident(s) if s == "opaque") {
                        self.advance();
                    } else {
                        return Err(
                            "Expected 'opaque' after 'unsafe sync' (prefer 'opaque(unsafe sync)')"
                                .to_string(),
                        );
                    }
                    let name = self.expect_ident()?;
                    let ty = self.parse_opaque_body(false, OpaqueMods::new(ownership, true))?;
                    items.push(Item::TypeDecl {
                        vis,
                        name,
                        ty,
                        alias: false,
                    });
                }
                SurfTokenKind::Sync => {
                    return Err(
                        "Declaring a 'sync' opaque type asserts thread-safe synchronization and requires 'opaque(unsafe sync)'"
                            .to_string(),
                    );
                }
                SurfTokenKind::Ident(s) if s == "enum" => {
                    self.advance();
                    let backing = if self.peek().kind == SurfTokenKind::LParen {
                        self.advance();
                        let b = self.parse_type_expr()?;
                        self.expect(&SurfTokenKind::RParen)?;
                        Some(Box::new(b))
                    } else {
                        None
                    };
                    let name = self.expect_ident()?;
                    let ty = self.parse_enum_body(backing)?;
                    items.push(Item::TypeDecl {
                        vis,
                        name,
                        ty,
                        alias: false,
                    });
                }
                SurfTokenKind::Ident(s) if s == "union" => {
                    self.advance();
                    let backing = if self.peek().kind == SurfTokenKind::LParen {
                        self.advance();
                        let t = self.parse_type_expr()?;
                        self.expect(&SurfTokenKind::RParen)?;
                        Some(Box::new(t))
                    } else {
                        None
                    };
                    let name = self.expect_ident()?;
                    let ty = self.parse_union_body(backing)?;
                    items.push(Item::TypeDecl {
                        vis,
                        name,
                        ty,
                        alias: false,
                    });
                }
                SurfTokenKind::Ident(s) if s == "overlay" => {
                    self.advance();
                    let name = self.expect_ident()?;
                    let ty = self.parse_overlay_body()?;
                    items.push(Item::TypeDecl {
                        vis,
                        name,
                        ty,
                        alias: false,
                    });
                }
                SurfTokenKind::Ident(s) if s == "error" => {
                    self.advance();
                    let backing = self.parse_error_header()?;
                    let name = self.expect_ident()?;
                    if self.peek().kind == SurfTokenKind::Eq {
                        self.advance();
                    }
                    let ty = self.parse_error_body(backing)?;
                    if self.peek().kind == SurfTokenKind::Semi {
                        self.advance();
                    }
                    items.push(Item::TypeDecl {
                        vis,
                        name,
                        ty,
                        alias: false,
                    });
                }
                SurfTokenKind::Ident(s) if s == "errorcode" => {
                    return Err(
                        "The 'errorcode' keyword has been unified into 'error'; write 'error Name { ... }' or 'export error Name { ... }' instead"
                            .to_string(),
                    );
                }
                SurfTokenKind::Ident(s) if s == "trait" => {
                    self.advance();
                    let name = self.expect_ident()?;
                    // `trait Name { ... }` declares a trait; `trait Name = <trait expr>;` aliases one.
                    let ty = if self.peek().kind == SurfTokenKind::Eq {
                        self.advance();
                        if matches!(&self.peek().kind, SurfTokenKind::Ident(s) if s == "trait")
                            && self.peek_n(1).kind == SurfTokenKind::LBrace
                        {
                            return Err(format!(
                                "Declare the trait directly: write 'trait {name} {{ ... }}' instead of 'trait {name} = trait {{ ... }};'"
                            ));
                        }
                        let t = self.parse_type_expr()?;
                        self.expect(&SurfTokenKind::Semi)?;
                        t
                    } else {
                        self.parse_trait_body()?
                    };
                    items.push(Item::TypeDecl {
                        vis,
                        name,
                        ty,
                        alias: false,
                    });
                }
                SurfTokenKind::Ident(s) if s == "opaque" => {
                    self.advance();
                    let mods = self.parse_opaque_modifiers()?;
                    let name = self.expect_ident()?;
                    let ty = if self.peek().kind == SurfTokenKind::Eq {
                        return Err(format!(
                            "'opaque {name} = ...' no longer declares a newtype; write 'type {name} = distinct ...;' for a distinct type with the same representation"
                        ));
                    } else if self.peek().kind == SurfTokenKind::LBrace {
                        let s_ty = self.parse_opaque_body(false, mods)?;
                        if self.peek().kind == SurfTokenKind::Semi {
                            self.advance();
                        }
                        s_ty
                    } else {
                        return Err(format!(
                            "Unsized foreign C handles must be declared with 'extern opaque {name};' (or use 'opaque {name} {{}}' for a zero-sized encapsulated type)"
                        ));
                    };
                    items.push(Item::TypeDecl {
                        vis,
                        name,
                        ty,
                        alias: false,
                    });
                }
                SurfTokenKind::Ident(s)
                    if s == "alias"
                        && matches!(self.peek_n(1).kind, SurfTokenKind::Ident(_))
                        && self.peek_n(2).kind == SurfTokenKind::Eq =>
                {
                    self.advance();
                    let name = self.expect_ident()?;
                    self.expect(&SurfTokenKind::Eq)?;
                    if vis.is_export() {
                        return Err(format!(
                            "'export alias {name}' is not supported: an alias names another type; export that type's declaration instead"
                        ));
                    }
                    let ty = self.parse_type_expr()?;
                    self.expect(&SurfTokenKind::Semi)?;
                    // An anonymous struct or overlay is structural, so it can be aliased; any
                    // other declaration makes a new type and belongs in `type`.
                    if ty.declares_type()
                        && !matches!(ty, TypeExpr::Struct { .. } | TypeExpr::Overlay(_))
                    {
                        return Err(format!(
                            "'alias {name} = ...' names an existing type, but its right-hand side declares a new one; write 'type {name} = ...;'"
                        ));
                    }
                    items.push(Item::TypeDecl {
                        vis,
                        name,
                        ty,
                        alias: true,
                    });
                }
                SurfTokenKind::TypeKw => {
                    self.advance();
                    let name = self.expect_ident()?;
                    self.expect(&SurfTokenKind::Eq)?;
                    // `type` declares only distinct types; every other kind has its own keyword
                    // (`struct N { ... }`, `opaque N { ... }`, `extern opaque N;`, ...), and
                    // naming an existing type is `alias`.
                    let kind = match &self.peek().kind {
                        SurfTokenKind::Extern => Some("extern opaque"),
                        SurfTokenKind::Struct => Some("struct"),
                        SurfTokenKind::Ident(s) => match s.as_str() {
                            "opaque" => Some("opaque"),
                            "enum" => Some("enum"),
                            "union" => Some("union"),
                            "error" => Some("error"),
                            "errorcode" => Some("errorcode"),
                            "overlay" => Some("overlay"),
                            "packed" => Some("packed struct"),
                            "trait" => Some("trait"),
                            _ => None,
                        },
                        _ => None,
                    };
                    let opaque_newtype = kind == Some("opaque")
                        && !matches!(
                            self.peek_n(1).kind,
                            SurfTokenKind::LParen | SurfTokenKind::LBrace
                        );
                    let ty = if opaque_newtype {
                        return Err(format!(
                            "'type {name} = opaque ...' no longer declares a newtype; write 'type {name} = distinct ...;' for a distinct type with the same representation"
                        ));
                    } else if let Some(kind) = kind {
                        return Err(format!(
                            "Declare the type with its own keyword: write '{kind} {name} ...' instead of 'type {name} = {kind} ...' ('type' declares distinct types: 'type {name} = distinct T;')"
                        ));
                    } else if matches!(&self.peek().kind, SurfTokenKind::Ident(s) if s == "distinct")
                    {
                        self.advance();
                        let underlying = self.parse_type_expr()?;
                        let methods = if self.peek().kind == SurfTokenKind::LBrace {
                            let m = self.parse_opaque_methods_body()?;
                            if self.peek().kind == SurfTokenKind::Semi {
                                self.advance();
                            }
                            m
                        } else {
                            self.expect(&SurfTokenKind::Semi)?;
                            Vec::new()
                        };
                        TypeExpr::Distinct {
                            underlying: Box::new(underlying),
                            methods,
                        }
                    } else {
                        return Err(format!(
                            "'type {name} = ...' declares a distinct type ('type {name} = distinct T;'); write 'alias {name} = ...;' to name an existing or structural type"
                        ));
                    };
                    items.push(Item::TypeDecl {
                        vis,
                        name,
                        ty,
                        alias: false,
                    });
                }
                _ => {
                    let tok = self.peek();
                    return Err(format!(
                        "Unexpected top-level token {:?} at {}:{}",
                        tok.kind, tok.line, tok.col
                    ));
                }
            }
        }

        items.extend(std::mem::take(&mut self.extra_items));
        Ok(ModuleAst { imports, items })
    }

    fn parse_import(&mut self, vis: Visibility) -> Result<ImportDecl, String> {
        self.expect(&SurfTokenKind::Import)?;
        let mut path = vec![self.expect_ident()?];
        let mut targets = ImportTargets::Module(None);

        while self.peek().kind == SurfTokenKind::ColonColon {
            self.advance();
            if self.peek().kind == SurfTokenKind::LBrace {
                self.advance();
                let mut list = Vec::new();
                while self.peek().kind != SurfTokenKind::RBrace {
                    let item = self.expect_ident()?;
                    let alias = if self.peek().kind == SurfTokenKind::As {
                        self.advance();
                        Some(self.expect_ident()?)
                    } else {
                        None
                    };
                    list.push((item, alias));
                    if self.peek().kind == SurfTokenKind::Comma {
                        self.advance();
                    } else {
                        break;
                    }
                }
                self.expect(&SurfTokenKind::RBrace)?;
                targets = ImportTargets::Items(list);
                break;
            } else if self.peek().kind == SurfTokenKind::Star {
                self.advance();
                targets = ImportTargets::Glob;
                break;
            } else {
                path.push(self.expect_ident()?);
            }
        }

        if matches!(targets, ImportTargets::Module(None)) && self.peek().kind == SurfTokenKind::As {
            self.advance();
            targets = ImportTargets::Module(Some(self.expect_ident()?));
        }

        self.expect(&SurfTokenKind::Semi)?;
        Ok(ImportDecl {
            vis,
            path,
            targets,
            is_prelude: false,
        })
    }

    fn parse_extern_func(&mut self, vis: Visibility) -> Result<ExternFuncDecl, String> {
        self.expect(&SurfTokenKind::Extern)?;
        self.expect(&SurfTokenKind::Fn)?;
        let name = self.expect_ident()?;
        self.expect(&SurfTokenKind::LParen)?;
        let mut params = Vec::new();
        while self.peek().kind != SurfTokenKind::RParen {
            let pname = self.expect_ident()?;
            self.expect(&SurfTokenKind::Colon)?;
            let pty = self.parse_type_expr()?;
            params.push((pname, pty));
            if self.peek().kind == SurfTokenKind::Comma {
                self.advance();
            } else {
                break;
            }
        }
        self.expect(&SurfTokenKind::RParen)?;
        let ret_ty = if self.peek().kind == SurfTokenKind::Arrow {
            self.advance();
            self.parse_type_expr()?
        } else {
            TypeExpr::Void
        };
        self.expect(&SurfTokenKind::Semi)?;
        Ok(ExternFuncDecl {
            vis,
            name,
            params,
            ret_ty,
            is_safe: false,
        })
    }

    /// Parses a comptime parameter list `[T, N: usize, K: Hash + Eq]`. A bare name is a type
    /// parameter (`T: type`).
    fn parse_comptime_params(&mut self) -> Result<Vec<Param>, String> {
        self.expect(&SurfTokenKind::LBracket)?;
        let mut params = Vec::new();
        while self.peek().kind != SurfTokenKind::RBracket {
            if self.peek().kind == SurfTokenKind::Comptime {
                return Err(format!(
                    "Parameters in '[...]' are already comptime; remove 'comptime' at {}:{}",
                    self.peek().line,
                    self.peek().col
                ));
            }
            let name = self.expect_ident()?;
            let ty = if self.peek().kind == SurfTokenKind::Colon {
                self.advance();
                if self.peek().kind == SurfTokenKind::Bang {
                    // `[T: !sync]`: any type that does not satisfy the constraint.
                    self.advance();
                    let bound = self.parse_base_type_expr()?;
                    let Some(constraint) = bound.as_type_constraint() else {
                        return Err(format!(
                            "Expected a type constraint after '!' for comptime parameter '{name}', found {bound:?}"
                        ));
                    };
                    self.pending_where.push(WherePredicate {
                        type_param: name.clone(),
                        negated: true,
                        constraint,
                    });
                    TypeExpr::MetaType
                } else {
                    self.parse_type_expr()?
                }
            } else {
                TypeExpr::MetaType
            };
            let default = if self.peek().kind == SurfTokenKind::Eq {
                self.advance();
                Some(self.parse_expr_or_type()?)
            } else {
                if params.iter().any(|p: &Param| p.default.is_some()) {
                    return Err(format!(
                        "Comptime parameter '{name}' needs a default: parameters after a defaulted one must also have defaults"
                    ));
                }
                None
            };
            params.push(Param {
                is_comptime: true,
                is_mut: false,
                name,
                ty,
                default,
            });
            if self.peek().kind == SurfTokenKind::Comma {
                self.advance();
            } else {
                break;
            }
        }
        self.expect(&SurfTokenKind::RBracket)?;
        Ok(params)
    }

    /// Parses comptime arguments `[i32, 4]`.
    pub(super) fn parse_comptime_args(&mut self) -> Result<Vec<Expr>, String> {
        self.expect(&SurfTokenKind::LBracket)?;
        let mut args = Vec::new();
        while self.peek().kind != SurfTokenKind::RBracket {
            args.push(self.parse_expr_or_type()?);
            if self.peek().kind == SurfTokenKind::Comma {
                self.advance();
            } else {
                break;
            }
        }
        self.expect(&SurfTokenKind::RBracket)?;
        Ok(args)
    }

    /// Parses a function's parameters: an optional comptime list `[...]` followed by the runtime
    /// list `(...)`, which may be omitted when the comptime list is present (`fn Vec[T] -> type`).
    /// The comptime parameters come first in the result.
    fn parse_fn_params(&mut self, what: &str) -> Result<Vec<Param>, String> {
        let mut params = if self.peek().kind == SurfTokenKind::LBracket {
            self.parse_comptime_params()?
        } else {
            Vec::new()
        };
        if !params.is_empty() && self.peek().kind != SurfTokenKind::LParen {
            return Ok(params);
        }
        self.expect(&SurfTokenKind::LParen)?;
        while self.peek().kind != SurfTokenKind::RParen {
            if self.peek().kind == SurfTokenKind::Comptime {
                return Err(format!(
                    "Comptime parameters are declared in brackets before the runtime parameters ('fn f[T: type, N: usize](x: T)'), not with 'comptime' at {}:{}",
                    self.peek().line,
                    self.peek().col
                ));
            }
            let _is_move = if self.peek().kind == SurfTokenKind::Move {
                self.advance();
                true
            } else {
                false
            };
            let is_mut = if self.peek().kind == SurfTokenKind::Mut {
                self.advance();
                true
            } else {
                false
            };
            let pname = self.expect_ident()?;
            let pty = if self.peek().kind == SurfTokenKind::Colon {
                self.advance();
                self.parse_type_expr()?
            } else if pname == "self" {
                TypeExpr::SelfType
            } else {
                return Err(format!(
                    "Expected ':' and type annotation for {what} '{pname}' at {}:{}",
                    self.peek().line,
                    self.peek().col
                ));
            };
            params.push(Param {
                is_comptime: false,
                default: None,
                is_mut,
                name: pname,
                ty: pty,
            });
            if self.peek().kind == SurfTokenKind::Comma {
                self.advance();
            } else {
                break;
            }
        }
        self.expect(&SurfTokenKind::RParen)?;
        Ok(params)
    }

    /// Whether a function declaration (`fn` or `unsafe fn`) starts here.
    fn fn_ahead(&self) -> bool {
        self.peek().kind == SurfTokenKind::Fn
            || (self.peek().kind == SurfTokenKind::Unsafe
                && self.peek_n(1).kind == SurfTokenKind::Fn)
    }

    /// Consumes an optional `unsafe` before `fn`.
    fn parse_unsafe_fn_prefix(&mut self) -> bool {
        let is_unsafe = self.peek().kind == SurfTokenKind::Unsafe;
        if is_unsafe {
            self.advance();
        }
        is_unsafe
    }

    fn parse_func_decl(&mut self, vis: Visibility) -> Result<FuncDecl, String> {
        let is_unsafe = self.parse_unsafe_fn_prefix();
        self.expect(&SurfTokenKind::Fn)?;
        let name = self.expect_ident()?;
        let params = self.parse_fn_params("parameter")?;
        let ret_ty = if self.peek().kind == SurfTokenKind::Arrow {
            self.advance();
            self.parse_type_expr()?
        } else {
            TypeExpr::Void
        };
        let borrows = self.parse_borrows_clause()?;
        let mut where_clauses = std::mem::take(&mut self.pending_where);
        where_clauses.extend(self.parse_where_clauses()?);
        let body = self.parse_block()?;
        Ok(FuncDecl {
            vis,
            name,
            params,
            ret_ty,
            borrows,
            where_clauses,
            body,
            is_unsafe,
            impl_of: None,
        })
    }

    fn parse_borrows_clause(&mut self) -> Result<Option<Vec<BorrowContractItem>>, String> {
        if !matches!(&self.peek().kind, SurfTokenKind::Ident(s) if s == "borrows") {
            return Ok(None);
        }
        self.advance();
        self.expect(&SurfTokenKind::LParen)?;
        let mut items = Vec::new();
        while self.peek().kind != SurfTokenKind::RParen {
            let contents = self.peek().kind == SurfTokenKind::Star;
            if contents {
                self.advance();
            }
            let first = self.expect_ident()?;
            if !contents && self.peek().kind == SurfTokenKind::Colon {
                self.advance();
                let src = self.expect_ident()?;
                items.push(BorrowContractItem::ParamFlow { dst: first, src });
            } else {
                items.push(BorrowContractItem::Return {
                    name: first,
                    contents,
                });
            }
            if self.peek().kind == SurfTokenKind::Comma {
                self.advance();
            } else {
                break;
            }
        }
        self.expect(&SurfTokenKind::RParen)?;
        Ok(Some(items))
    }

    fn parse_where_clauses(&mut self) -> Result<Vec<WherePredicate>, String> {
        let mut clauses = Vec::new();
        while matches!(&self.peek().kind, SurfTokenKind::Ident(s) if s == "where") {
            self.advance();
            while self.peek().kind != SurfTokenKind::LBrace {
                let type_param = self.expect_ident()?;
                self.expect(&SurfTokenKind::Colon)?;
                let negated = if self.peek().kind == SurfTokenKind::Bang {
                    self.advance();
                    true
                } else {
                    false
                };
                let ty_expr = self.parse_base_type_expr()?;
                let Some(constraint) = ty_expr.as_type_constraint() else {
                    return Err(format!(
                        "Expected type constraint after ':' in 'where' clause for '{type_param}', found {ty_expr:?}"
                    ));
                };
                clauses.push(WherePredicate {
                    type_param,
                    negated,
                    constraint,
                });
                if self.peek().kind == SurfTokenKind::Comma {
                    self.advance();
                } else {
                    break;
                }
            }
        }
        Ok(clauses)
    }

    fn parse_struct_body(&mut self, is_packed: bool) -> Result<TypeExpr, String> {
        self.expect(&SurfTokenKind::LBrace)?;
        let mut fields = Vec::new();
        let mut methods = Vec::new();
        while self.peek().kind != SurfTokenKind::RBrace {
            let vis = self.parse_visibility()?;
            if let Some(hook_name) = self.lifecycle_hook_ahead() {
                return Err(format!(
                    "Lifecycle hook '{hook_name}' is forbidden on transparent 'struct' types; transparent types are always auto-synthesized structurally, and only 'opaque' types may define custom lifecycle hooks"
                ));
            }
            if self.fn_ahead() {
                methods.push(self.parse_func_decl(vis)?);
            } else if matches!(&self.peek().kind, SurfTokenKind::Ident(s) if s == "impl") {
                methods.extend(self.parse_inline_impl(vis)?);
            } else if matches!(&self.peek().kind, SurfTokenKind::Ident(s) if s == "enum") {
                self.advance();
                let backing = if self.peek().kind == SurfTokenKind::LParen {
                    self.advance();
                    let b = self.parse_type_expr()?;
                    self.expect(&SurfTokenKind::RParen)?;
                    Some(Box::new(b))
                } else {
                    None
                };
                let ename = self.expect_ident()?;
                let ety = self.parse_enum_body(backing)?;
                if let Some(parent) = &self.current_type_name {
                    self.extra_items.push(Item::TypeDecl {
                        vis,
                        name: format!("{parent}::{ename}"),
                        ty: ety.clone(),
                        alias: false,
                    });
                }
                self.extra_items.push(Item::TypeDecl {
                    vis,
                    name: ename,
                    ty: ety,
                    alias: false,
                });
            } else if matches!(
                self.peek().kind,
                SurfTokenKind::Const | SurfTokenKind::Comptime
            ) || matches!(&self.peek().kind, SurfTokenKind::Ident(s) if s == "static")
            {
                return Err(
                    "Associated 'static' or 'const'/'comptime' declarations are forbidden inside transparent 'struct' blocks; declare them at module scope or inside an 'opaque' block"
                        .to_string(),
                );
            } else {
                if matches!(&self.peek().kind, SurfTokenKind::Ident(c) if c == "cell")
                    && matches!(self.peek_n(1).kind, SurfTokenKind::Ident(_))
                    && self.peek_n(2).kind == SurfTokenKind::Colon
                {
                    return Err(
                        "Only 'opaque' fields may be 'cell': interior mutability needs the encapsulation a transparent 'struct' lacks"
                            .to_string(),
                    );
                }
                let fname = self.expect_ident()?;
                self.expect(&SurfTokenKind::Colon)?;
                let fty = self.parse_type_expr()?;
                let default_val = if self.peek().kind == SurfTokenKind::Eq {
                    self.advance();
                    Some(self.parse_expr_or_type()?)
                } else {
                    None
                };
                // Struct fields are public by default
                let field_vis = if vis == Visibility::Private {
                    Visibility::Pub
                } else {
                    vis
                };
                fields.push(FieldDecl {
                    vis: field_vis,
                    name: fname,
                    ty: fty,
                    is_cell: false,
                    default_val,
                });
                if self.peek().kind == SurfTokenKind::Comma {
                    self.advance();
                }
            }
        }
        self.expect(&SurfTokenKind::RBrace)?;
        Ok(TypeExpr::Struct {
            is_packed,
            fields,
            methods,
        })
    }

    fn parse_opaque_modifiers(&mut self) -> Result<OpaqueMods, String> {
        if self.peek().kind != SurfTokenKind::LParen {
            return Ok(OpaqueMods::new(OpaqueOwnership::Default, false));
        }
        self.advance(); // consume '('
        let mut ownership_opt: Option<OpaqueOwnership> = None;
        let mut threads = ThreadDecl::default();
        let mut owns: Vec<String> = Vec::new();
        let mut borrows: Vec<String> = Vec::new();

        while self.peek().kind != SurfTokenKind::RParen {
            match &self.peek().kind {
                SurfTokenKind::Ident(s) if s == "copy" => {
                    self.advance();
                    if ownership_opt.is_some() {
                        return Err(
                            "Conflicting ownership modifiers in 'opaque(...)' (choose at most one of 'copy', 'affine', or 'linear')"
                                .to_string(),
                        );
                    }
                    ownership_opt = Some(OpaqueOwnership::Copy);
                }
                SurfTokenKind::Ident(s) if s == "affine" => {
                    self.advance();
                    if ownership_opt.is_some() {
                        return Err(
                            "Conflicting ownership modifiers in 'opaque(...)' (choose at most one of 'copy', 'affine', or 'linear')"
                                .to_string(),
                        );
                    }
                    ownership_opt = Some(OpaqueOwnership::Affine);
                }
                SurfTokenKind::Linear => {
                    self.advance();
                    if ownership_opt.is_some() {
                        return Err(
                            "Conflicting ownership modifiers in 'opaque(...)' (choose at most one of 'copy', 'affine', or 'linear')"
                                .to_string(),
                        );
                    }
                    ownership_opt = Some(OpaqueOwnership::Linear);
                }
                SurfTokenKind::Unsafe => {
                    self.advance();
                    match &self.peek().kind {
                        SurfTokenKind::Sync => threads.unsafe_sync = true,
                        SurfTokenKind::Ident(t) if t == "send" => threads.unsafe_send = true,
                        _ => {
                            return Err(
                                "Expected 'send' or 'sync' after 'unsafe' in 'opaque(...)'".to_string()
                            );
                        }
                    }
                    self.advance();
                }
                SurfTokenKind::Bang => {
                    self.advance();
                    match &self.peek().kind {
                        SurfTokenKind::Sync => threads.not_sync = true,
                        SurfTokenKind::Ident(t) if t == "send" => threads.not_send = true,
                        _ => {
                            return Err("Expected 'send' or 'sync' after '!' in 'opaque(...)'".to_string());
                        }
                    }
                    self.advance();
                }
                SurfTokenKind::Ident(s) if s == "send" => {
                    return Err(
                        "Declaring a 'send' opaque type asserts it can move between threads and requires 'opaque(unsafe send)'"
                            .to_string(),
                    );
                }
                SurfTokenKind::Sync => {
                    return Err(
                        "Declaring a 'sync' opaque type asserts thread-safe synchronization and requires 'opaque(unsafe sync)'"
                            .to_string(),
                    );
                }
                SurfTokenKind::Ident(s) if s == "owns" || s == "borrows" => {
                    let modifier = s.clone();
                    self.advance();
                    let list = if modifier == "owns" { &mut owns } else { &mut borrows };
                    if !list.is_empty() {
                        return Err(format!("Duplicate '{modifier}' modifier in 'opaque(...)'"));
                    }
                    // `owns T` or `owns K, V`: parameter names continue until the next modifier keyword
                    list.push(self.expect_ident()?);
                    while self.peek().kind == SurfTokenKind::Comma
                        && matches!(&self.peek_n(1).kind, SurfTokenKind::Ident(n)
                            if !matches!(n.as_str(), "copy" | "affine" | "owns" | "borrows"))
                    {
                        self.advance();
                        list.push(self.expect_ident()?);
                    }
                }
                other => {
                    let tok = self.peek();
                    return Err(format!(
                        "Unknown opaque modifier {:?} at {}:{} (expected 'copy', 'affine', 'linear', 'owns T', 'borrows T', 'unsafe send', 'unsafe sync', '!send', or '!sync')",
                        other, tok.line, tok.col
                    ));
                }
            }
            if self.peek().kind == SurfTokenKind::Comma {
                self.advance();
            } else {
                break;
            }
        }
        self.expect(&SurfTokenKind::RParen)?;
        let ownership = ownership_opt.unwrap_or(OpaqueOwnership::Default);
        if ownership == OpaqueOwnership::Copy && !owns.is_empty() {
            return Err(
                "'opaque(copy, owns ...)' is invalid: an owning 'copy' type would duplicate the values it owns"
                    .to_string(),
            );
        }
        if (threads.unsafe_send && threads.not_send) || (threads.unsafe_sync && threads.not_sync) {
            return Err(
                "'opaque(...)' cannot both assert and withhold the same thread-safety trait".to_string()
            );
        }
        Ok(OpaqueMods {
            ownership,
            threads,
            owns,
            borrows,
        })
    }

    fn parse_static_decl(&mut self, vis: Visibility) -> Result<StaticDecl, String> {
        self.advance(); // consume 'static'
        let mutable = if self.peek().kind == SurfTokenKind::Mut {
            self.advance();
            true
        } else {
            false
        };
        let name = self.expect_ident()?;
        self.expect(&SurfTokenKind::Colon)?;
        let ty = self.parse_type_expr()?;
        self.expect(&SurfTokenKind::Eq)?;
        let init = self.parse_expr()?;
        self.expect(&SurfTokenKind::Semi)?;
        Ok(StaticDecl {
            vis,
            mutable,
            name,
            ty,
            init,
        })
    }

    fn parse_const_decl(&mut self, vis: Visibility) -> Result<ConstDecl, String> {
        self.advance(); // consume 'const' or 'comptime'
        let name = self.expect_ident()?;
        let ty = if self.peek().kind == SurfTokenKind::Colon {
            self.advance();
            Some(self.parse_type_expr()?)
        } else {
            None
        };
        self.expect(&SurfTokenKind::Eq)?;
        let init = self.parse_expr_or_type()?;
        self.expect(&SurfTokenKind::Semi)?;
        Ok(ConstDecl {
            vis,
            name,
            ty,
            init,
        })
    }

    fn parse_opaque_body(&mut self, is_packed: bool, mods: OpaqueMods) -> Result<TypeExpr, String> {
        let OpaqueMods {
            ownership,
            threads,
            owns,
            borrows,
        } = mods;
        self.expect(&SurfTokenKind::LBrace)?;
        let mut fields = Vec::new();
        let mut consts = Vec::new();
        let mut statics = Vec::new();
        let mut methods = Vec::new();
        let mut default_hook = None;
        let mut clone_hooks = Vec::new();
        let mut drop_hooks = Vec::new();
        let mut format_hook = None;

        while self.peek().kind != SurfTokenKind::RBrace {
            let vis = self.parse_visibility()?;
            if let Some(hook) = self.lifecycle_hook_ahead() {
                if vis != Visibility::Private {
                    return Err(format!(
                        "'impl {hook}' takes no visibility modifier; lifecycle hooks are always visible for the type"
                    ));
                }
                let is_unsafe = self.peek().kind == SurfTokenKind::Unsafe;
                if is_unsafe {
                    self.advance();
                }
                if !matches!(&self.peek().kind, SurfTokenKind::Ident(s) if s == "impl") {
                    return Err(format!(
                        "Declare the '{hook}' lifecycle hook as 'impl {hook} {{ fn {hook}(...) {{ ... }} }}'"
                    ));
                }
                let (f, may_dangle) = self.parse_lifecycle_impl(hook)?;
                if !is_unsafe && !may_dangle.is_empty() {
                    return Err(format!(
                        "'impl {hook}(may_dangle ...)' asserts what the hook does not read, which the compiler cannot check; write 'unsafe impl {hook}(may_dangle ...)'"
                    ));
                }
                if is_unsafe && may_dangle.is_empty() {
                    return Err(format!(
                        "'unsafe impl {hook}' asserts nothing; 'unsafe' is only for 'unsafe impl drop(may_dangle T)'"
                    ));
                }
                let self_name = |f: &FuncDecl| f.params.first().map(|p| p.name.clone());
                let arity = |n: usize, f: &FuncDecl| {
                    if f.params.len() == n {
                        Ok(())
                    } else {
                        Err(format!("'fn {hook}' takes {n} parameter(s), found {}", f.params.len()))
                    }
                };
                match hook {
                    "default" => {
                        arity(0, &f)?;
                        if default_hook.replace(f.body).is_some() {
                            return Err("Duplicate 'impl default'".to_string());
                        }
                    }
                    "clone" => {
                        arity(1, &f)?;
                        clone_hooks.push(CloneHookDecl {
                            self_name: self_name(&f).unwrap(),
                            where_clauses: f.where_clauses,
                            body: f.body,
                        });
                    }
                    "drop" => {
                        arity(1, &f)?;
                        drop_hooks.push(DropHookDecl {
                            self_name: self_name(&f).unwrap(),
                            where_clauses: f.where_clauses,
                            body: f.body,
                            may_dangle,
                        });
                    }
                    _ => {
                        if !(2..=3).contains(&f.params.len()) {
                            return Err(format!(
                                "'fn format' takes (self, formatter) or (self, formatter, spec), found {} parameter(s)",
                                f.params.len()
                            ));
                        }
                        let spec = f.params.get(2).map(|p| p.name.clone());
                        let names = (f.params[0].name.clone(), f.params[1].name.clone());
                        if format_hook.replace((names.0, names.1, spec, f.body)).is_some() {
                            return Err("Duplicate 'impl format'".to_string());
                        }
                    }
                }
                continue;
            }
            match &self.peek().kind {
                SurfTokenKind::Fn => {
                    methods.push(self.parse_func_decl(vis)?);
                }
                SurfTokenKind::Unsafe if self.peek_n(1).kind == SurfTokenKind::Fn => {
                    methods.push(self.parse_func_decl(vis)?);
                }
                SurfTokenKind::Ident(s) if s == "impl" => {
                    methods.extend(self.parse_inline_impl(vis)?);
                }
                SurfTokenKind::Const | SurfTokenKind::Comptime => {
                    consts.push(self.parse_const_decl(vis)?);
                }
                SurfTokenKind::Ident(s) if s == "static" => {
                    statics.push(self.parse_static_decl(vis)?);
                }
                _ => {
                    // `cell name: T`: a field that may be written through a shared reference.
                    let is_cell = matches!(&self.peek().kind, SurfTokenKind::Ident(c) if c == "cell")
                        && matches!(self.peek_n(1).kind, SurfTokenKind::Ident(_))
                        && self.peek_n(2).kind == SurfTokenKind::Colon;
                    if is_cell {
                        self.advance();
                    }
                    let fname = self.expect_ident()?;
                    if vis != Visibility::Private {
                        return Err(format!(
                            "Field '{fname}' of 'opaque' type cannot be declared 'pub'; all fields of an 'opaque' type are strictly private to its 'opaque {{ ... }}' block"
                        ));
                    }
                    self.expect(&SurfTokenKind::Colon)?;
                    let fty = self.parse_type_expr()?;
                    let default_val = if self.peek().kind == SurfTokenKind::Eq {
                        self.advance();
                        Some(self.parse_expr_or_type()?)
                    } else {
                        None
                    };
                    // Opaque fields are strictly private to the opaque block
                    fields.push(FieldDecl {
                        vis: Visibility::Private,
                        name: fname,
                        ty: fty,
                        default_val,
                        is_cell,
                    });
                    if self.peek().kind == SurfTokenKind::Comma {
                        self.advance();
                    }
                }
            }
        }
        self.expect(&SurfTokenKind::RBrace)?;
        Ok(TypeExpr::Opaque(Box::new(OpaqueBody {
            is_packed,
            ownership,
            threads,
            owns,
            borrows,
            fields,
            consts,
            statics,
            methods,
            default_hook,
            clone_hooks,
            drop_hooks,
            format_hook,
        })))
    }

    fn parse_enum_body(&mut self, backing: Option<Box<TypeExpr>>) -> Result<TypeExpr, String> {
        self.expect(&SurfTokenKind::LBrace)?;
        let mut variants = Vec::new();
        while self.peek().kind != SurfTokenKind::RBrace {
            let vname = self.expect_ident()?;
            let val = if self.peek().kind == SurfTokenKind::Eq {
                self.advance();
                let neg = if self.peek().kind == SurfTokenKind::Minus {
                    self.advance();
                    true
                } else {
                    false
                };
                let tok = self.advance();
                match tok.kind {
                    SurfTokenKind::Int(n) => Some(if neg { -n } else { n }),
                    _ => {
                        return Err(format!(
                            "Expected integer discriminant for enum variant '{vname}'"
                        ));
                    }
                }
            } else {
                None
            };
            variants.push((vname, val));
            if self.peek().kind == SurfTokenKind::Comma {
                self.advance();
            } else {
                break;
            }
        }
        self.expect(&SurfTokenKind::RBrace)?;
        Ok(TypeExpr::Enum { backing, variants })
    }

    fn parse_union_body(&mut self, backing: Option<Box<TypeExpr>>) -> Result<TypeExpr, String> {
        self.expect(&SurfTokenKind::LBrace)?;
        let mut variants = Vec::new();
        while self.peek().kind != SurfTokenKind::RBrace {
            let vname = self.expect_ident()?;
            let payload = if self.peek().kind == SurfTokenKind::Colon {
                self.advance();
                Some(self.parse_type_expr()?)
            } else if self.peek().kind == SurfTokenKind::LParen {
                self.advance();
                let ty = self.parse_type_expr()?;
                self.expect(&SurfTokenKind::RParen)?;
                Some(ty)
            } else {
                None
            };
            let value = if self.peek().kind == SurfTokenKind::Eq {
                self.advance();
                Some(self.parse_signed_int_lit(&format!("union variant '{vname}'"))?)
            } else {
                None
            };
            variants.push((vname, payload, value));
            if self.peek().kind == SurfTokenKind::Comma {
                self.advance();
            } else {
                break;
            }
        }
        self.expect(&SurfTokenKind::RBrace)?;
        Ok(TypeExpr::Union { backing, variants })
    }

    fn parse_overlay_body(&mut self) -> Result<TypeExpr, String> {
        self.expect(&SurfTokenKind::LBrace)?;
        let mut fields = Vec::new();
        while self.peek().kind != SurfTokenKind::RBrace {
            let has_named_field = self.peek().kind == SurfTokenKind::Pub
                || (matches!(self.peek().kind, SurfTokenKind::Ident(_))
                    && self.peek_n(1).kind == SurfTokenKind::Colon);
            if has_named_field {
                let _vis = self.parse_visibility()?;
                let fname = self.expect_ident()?;
                self.expect(&SurfTokenKind::Colon)?;
                let fty = self.parse_type_expr()?;
                fields.push((fname, fty));
            } else {
                let fty = self.parse_type_expr()?;
                fields.push((fields.len().to_string(), fty));
            }
            if matches!(self.peek().kind, SurfTokenKind::Comma | SurfTokenKind::Semi) {
                self.advance();
            } else {
                break;
            }
        }
        self.expect(&SurfTokenKind::RBrace)?;
        Ok(TypeExpr::Overlay(fields))
    }

    fn parse_signed_int_lit(&mut self, what: &str) -> Result<i128, String> {
        let neg = if self.peek().kind == SurfTokenKind::Minus {
            self.advance();
            true
        } else {
            false
        };
        let tok = self.advance();
        match tok.kind {
            SurfTokenKind::Int(n) => Ok(if neg { -n } else { n }),
            _ => Err(format!("Expected integer value for {what}")),
        }
    }

    /// `error(Int)`: the optional backing integer type (the success value is declared in the
    /// body, `ok Success = 0`).
    fn parse_error_header(&mut self) -> Result<Option<Box<TypeExpr>>, String> {
        if self.peek().kind != SurfTokenKind::LParen {
            return Ok(None);
        }
        self.advance();
        let moved = "The success value is declared in the body: \
                     write 'error(Int) Name { ok Success = 0, ... }'";
        if matches!(&self.peek().kind, SurfTokenKind::Ident(_))
            && self.peek_n(1).kind == SurfTokenKind::Eq
        {
            return Err(moved.to_string());
        }
        let b = self.parse_type_expr()?;
        if self.peek().kind == SurfTokenKind::Comma {
            return Err(moved.to_string());
        }
        self.expect(&SurfTokenKind::RParen)?;
        Ok(Some(Box::new(b)))
    }

    fn parse_error_body(&mut self, backing: Option<Box<TypeExpr>>) -> Result<TypeExpr, String> {
        self.expect(&SurfTokenKind::LBrace)?;
        let mut variants = Vec::new();
        let mut ok_flag: Option<(String, i128)> = None;
        while self.peek().kind != SurfTokenKind::RBrace {
            if matches!(&self.peek().kind, SurfTokenKind::Ident(s) if s == "ok")
                && matches!(self.peek_n(1).kind, SurfTokenKind::Ident(_))
            {
                self.advance();
                let ok_name = self.expect_ident()?;
                let ok_val = if self.peek().kind == SurfTokenKind::Eq {
                    self.advance();
                    self.parse_signed_int_lit(&format!("success value '{ok_name}'"))?
                } else {
                    0
                };
                if ok_flag.replace((ok_name, ok_val)).is_some() {
                    return Err("An 'error' declares at most one 'ok' success value".to_string());
                }
                if self.peek().kind == SurfTokenKind::Comma {
                    self.advance();
                }
                continue;
            }
            let mut vname = self.expect_ident()?;
            while self.peek().kind == SurfTokenKind::ColonColon {
                self.advance();
                let seg = self.expect_ident()?;
                vname.push_str("::");
                vname.push_str(&seg);
            }
            let payload = if self.peek().kind == SurfTokenKind::Colon {
                self.advance();
                Some(self.parse_type_expr()?)
            } else if self.peek().kind == SurfTokenKind::LParen {
                self.advance();
                let ty = self.parse_type_expr()?;
                self.expect(&SurfTokenKind::RParen)?;
                Some(ty)
            } else {
                None
            };
            let value = if self.peek().kind == SurfTokenKind::Eq {
                self.advance();
                Some(self.parse_signed_int_lit(&format!("error variant '{vname}'"))?)
            } else {
                None
            };
            variants.push((vname, payload, value));
            if self.peek().kind == SurfTokenKind::Comma {
                self.advance();
            } else {
                break;
            }
        }
        self.expect(&SurfTokenKind::RBrace)?;
        Ok(TypeExpr::Error {
            backing,
            ok_flag,
            variants,
        })
    }

    fn parse_trait_body(&mut self) -> Result<TypeExpr, String> {
        self.expect(&SurfTokenKind::LBrace)?;
        let mut methods = Vec::new();
        while self.peek().kind != SurfTokenKind::RBrace {
            if self.parse_visibility()? == Visibility::PubMod {
                return Err(
                    "Trait methods take no 'pub(mod)': they are as visible as the trait".to_string()
                );
            }
            let is_unsafe = self.parse_unsafe_fn_prefix();
            self.expect(&SurfTokenKind::Fn)?;
            let name = self.expect_ident()?;
            let params = self.parse_fn_params("trait method parameter")?;
            let ret_ty = if self.peek().kind == SurfTokenKind::Arrow {
                self.advance();
                self.parse_type_expr()?
            } else {
                TypeExpr::Void
            };
            let borrows = self.parse_borrows_clause()?;
            self.expect(&SurfTokenKind::Semi)?;
            methods.push(TraitMethodDecl {
                name,
                params,
                ret_ty,
                borrows,
                is_unsafe,
            });
        }
        self.expect(&SurfTokenKind::RBrace)?;
        Ok(TypeExpr::Trait(methods))
    }

    fn parse_opaque_methods_body(&mut self) -> Result<Vec<FuncDecl>, String> {
        self.expect(&SurfTokenKind::LBrace)?;
        let mut methods = Vec::new();
        while self.peek().kind != SurfTokenKind::RBrace {
            let m_vis = self.parse_visibility()?;
            if let Some(hook) = self.lifecycle_hook_ahead() {
                return Err(format!(
                    "Lifecycle hook '{hook}' is not permitted inside 'extern opaque' or 'distinct' type blocks; only 'opaque' types may define custom 'default', 'clone', 'drop', or 'format' hooks"
                ));
            }
            if matches!(&self.peek().kind, SurfTokenKind::Ident(s) if s == "impl") {
                methods.extend(self.parse_inline_impl(m_vis)?);
                continue;
            }
            if !self.fn_ahead() {
                return Err(format!(
                    "Expected 'fn' inside 'extern opaque' or distinct type method block, found {:?} at {}:{} (use 'opaque Name {{ ... }}' for a sized encapsulated type with fields or lifecycle hooks)",
                    self.peek().kind,
                    self.peek().line,
                    self.peek().col
                ));
            }
            methods.push(self.parse_func_decl(m_vis)?);
        }
        self.expect(&SurfTokenKind::RBrace)?;
        Ok(methods)
    }

    /// Parses `impl Tr { fn ... }` inside a type's own body. The methods implement `Tr` for the
    /// enclosing type and keep the body's private access.
    fn parse_inline_impl(&mut self, vis: Visibility) -> Result<Vec<FuncDecl>, String> {
        if vis != Visibility::Private {
            return Err(
                "'impl' blocks take no visibility modifier; trait methods are as visible as the trait and type"
                    .to_string(),
            );
        }
        self.advance(); // consume 'impl'
        let trait_expr = self.parse_type_expr()?;
        self.parse_impl_methods(&trait_expr)
    }

    /// Parses `impl[T: Bound, ...] Tr for Type { fn ... }` (brackets optional) at module level.
    fn parse_module_impl(&mut self) -> Result<ImplDecl, String> {
        self.advance(); // consume 'impl'
        if self.peek().kind == SurfTokenKind::LParen {
            return Err(
                "Generic 'impl' parameters go in brackets (e.g. 'impl[T: Hash] Hash for Pair[T]')"
                    .to_string(),
            );
        }
        let comptime_params = if self.peek().kind == SurfTokenKind::LBracket {
            self.parse_comptime_params()?
        } else {
            Vec::new()
        };
        if let Some(p) = comptime_params.iter().find(|p| p.default.is_some()) {
            return Err(format!(
                "Generic 'impl' parameter '{}' cannot have a default; it is matched against the type",
                p.name
            ));
        }
        if let SurfTokenKind::Ident(s) = &self.peek().kind
            && matches!(s.as_str(), "drop" | "clone" | "default" | "format")
        {
            return Err(format!(
                "Lifecycle hook '{s}' must be declared as 'impl {s} {{ fn {s}(...) {{ ... }} }}' inside the type's own 'opaque {{ ... }}' block, not at module level"
            ));
        }
        let trait_expr = self.parse_type_expr()?;
        if !matches!(&self.peek().kind, SurfTokenKind::Ident(s) if s == "for") {
            return Err(format!(
                "Expected 'for' in module-level 'impl' at {}:{} (write 'impl Trait for Type {{ ... }}', or put 'impl Trait {{ ... }}' inside the type's own body)",
                self.peek().line,
                self.peek().col
            ));
        }
        self.advance(); // consume 'for'
        let for_ty = self.parse_type_expr()?;
        let methods = self.parse_impl_methods(&trait_expr)?;
        Ok(ImplDecl {
            comptime_params,
            trait_expr,
            for_ty,
            methods,
        })
    }

    fn parse_impl_methods(&mut self, trait_expr: &TypeExpr) -> Result<Vec<FuncDecl>, String> {
        self.expect(&SurfTokenKind::LBrace)?;
        let mut methods = Vec::new();
        while self.peek().kind != SurfTokenKind::RBrace {
            if self.parse_visibility()? != Visibility::Private {
                return Err(
                    "Methods in an 'impl' block take their visibility from the trait; remove the visibility modifier"
                        .to_string(),
                );
            }
            if !self.fn_ahead() {
                return Err(format!(
                    "Expected 'fn' inside 'impl' block, found {:?} at {}:{}",
                    self.peek().kind,
                    self.peek().line,
                    self.peek().col
                ));
            }
            // Trait methods form a public interface: they follow `pub` contract rules.
            let mut m = self.parse_func_decl(Visibility::Pub)?;
            m.impl_of = Some(trait_expr.clone());
            methods.push(m);
        }
        self.expect(&SurfTokenKind::RBrace)?;
        Ok(methods)
    }

    /// The lifecycle hook a type-body member declares, if it is one: `impl drop { ... }` (also
    /// `impl clone`, `impl default`, `impl format`), or the former `drop(...) { ... }` form.
    fn lifecycle_hook_ahead(&self) -> Option<&'static str> {
        let hook = |k: &SurfTokenKind| match k {
            SurfTokenKind::Ident(s) => match s.as_str() {
                "drop" => Some("drop"),
                "clone" => Some("clone"),
                "default" => Some("default"),
                "format" => Some("format"),
                _ => None,
            },
            _ => None,
        };
        match &self.peek().kind {
            SurfTokenKind::Ident(s) if s == "impl" => hook(&self.peek_n(1).kind).filter(|_| {
                matches!(self.peek_n(2).kind, SurfTokenKind::LBrace | SurfTokenKind::LParen)
                    || matches!(&self.peek_n(2).kind, SurfTokenKind::Ident(w) if w == "where")
            }),
            // `unsafe impl drop(may_dangle T)`
            SurfTokenKind::Unsafe
                if matches!(&self.peek_n(1).kind, SurfTokenKind::Ident(s) if s == "impl")
                    && matches!(&self.peek_n(2).kind, SurfTokenKind::Ident(s) if s == "drop") =>
            {
                Some("drop")
            }
            k => hook(k).filter(|_| self.peek_n(1).kind == SurfTokenKind::LParen),
        }
    }

    /// `impl hook [(may_dangle T, ...)] [where ...] { fn hook(...) { ... } }`: the hook's one
    /// method, carrying the impl's `where` clauses, and the `may_dangle` parameters (only `drop`).
    fn parse_lifecycle_impl(&mut self, hook: &str) -> Result<(FuncDecl, Vec<String>), String> {
        self.advance(); // `impl`
        self.advance(); // the hook name
        let mut may_dangle = Vec::new();
        if self.peek().kind == SurfTokenKind::LParen {
            self.advance();
            if hook != "drop" || !matches!(&self.peek().kind, SurfTokenKind::Ident(s) if s == "may_dangle") {
                return Err(format!(
                    "Only 'drop' takes a parameter list, written 'unsafe impl drop(may_dangle T)'; found one on '{hook}'"
                ));
            }
            self.advance();
            while self.peek().kind != SurfTokenKind::RParen {
                may_dangle.push(self.expect_ident()?);
                if self.peek().kind == SurfTokenKind::Comma {
                    self.advance();
                } else {
                    break;
                }
            }
            self.expect(&SurfTokenKind::RParen)?;
        }
        let where_clauses = self.parse_where_clauses()?;
        self.expect(&SurfTokenKind::LBrace)?;
        if self.parse_visibility()? != Visibility::Private {
            return Err(format!(
                "'fn {hook}' inside 'impl {hook}' takes no visibility modifier"
            ));
        }
        let mut f = self.parse_func_decl(Visibility::Private)?;
        self.expect(&SurfTokenKind::RBrace)?;
        if f.name != hook {
            return Err(format!(
                "'impl {hook}' must contain exactly 'fn {hook}(...)', found 'fn {}'",
                f.name
            ));
        }
        f.where_clauses.extend(where_clauses);
        Ok((f, may_dangle))
    }

    fn is_composite_body_ahead(&self) -> bool {
        if self.peek().kind != SurfTokenKind::LBrace {
            return false;
        }
        match &self.peek_n(1).kind {
            SurfTokenKind::RBrace
            | SurfTokenKind::Pub
            | SurfTokenKind::Const
            | SurfTokenKind::Comptime => true,
            SurfTokenKind::Fn => matches!(self.peek_n(2).kind, SurfTokenKind::Ident(_)),
            SurfTokenKind::Unsafe => self.peek_n(2).kind == SurfTokenKind::Fn,
            SurfTokenKind::Ident(s) if s == "export" || s == "static" || s == "impl" => true,
            SurfTokenKind::Ident(s)
                if matches!(s.as_str(), "drop" | "clone" | "default" | "format")
                    && self.peek_n(2).kind == SurfTokenKind::LParen =>
            {
                true
            }
            SurfTokenKind::Ident(_) => self.peek_n(2).kind == SurfTokenKind::Colon,
            _ => false,
        }
    }

    pub fn parse_type_expr(&mut self) -> Result<TypeExpr, String> {
        let first = self.parse_base_type_expr()?;
        let base = if self.peek().kind == SurfTokenKind::Plus {
            let mut bounds = vec![first];
            while self.peek().kind == SurfTokenKind::Plus {
                self.advance();
                bounds.push(self.parse_base_type_expr()?);
            }
            TypeExpr::TraitBounds(bounds)
        } else if self.peek().kind == SurfTokenKind::PipePipe {
            let mut terms = vec![first];
            while self.peek().kind == SurfTokenKind::PipePipe {
                self.advance();
                terms.push(self.parse_base_type_expr()?);
            }
            TypeExpr::ErrorSetUnion(terms)
        } else {
            first
        };
        if self.peek().kind == SurfTokenKind::Bang {
            self.advance();
            let ok = self.parse_type_expr()?;
            return Ok(TypeExpr::Result {
                err: Box::new(base),
                ok: Box::new(ok),
            });
        }
        if self.peek().kind == SurfTokenKind::In {
            self.advance();
            let mut ranges = Vec::new();
            loop {
                let lo = self.parse_additive_expr()?;
                self.expect(&SurfTokenKind::DotDotEq)?;
                let hi = self.parse_additive_expr()?;
                ranges.push((lo, hi));
                if self.peek().kind == SurfTokenKind::Pipe {
                    self.advance();
                } else {
                    break;
                }
            }
            Ok(TypeExpr::Pattern {
                base: Box::new(base),
                ranges,
            })
        } else {
            Ok(base)
        }
    }

    fn parse_base_type_expr(&mut self) -> Result<TypeExpr, String> {
        let tok = self.peek().clone();
        match tok.kind {
            SurfTokenKind::Void => {
                self.advance();
                Ok(TypeExpr::Void)
            }
            SurfTokenKind::Never => {
                self.advance();
                Ok(TypeExpr::Never)
            }
            SurfTokenKind::Bool => {
                self.advance();
                Ok(TypeExpr::Bool)
            }
            SurfTokenKind::RuneKw => {
                self.advance();
                Ok(TypeExpr::Rune)
            }
            SurfTokenKind::F32 => {
                self.advance();
                Ok(TypeExpr::F32)
            }
            SurfTokenKind::F64 => {
                self.advance();
                Ok(TypeExpr::F64)
            }
            SurfTokenKind::Isize => {
                self.advance();
                Ok(TypeExpr::Isize)
            }
            SurfTokenKind::Usize => {
                self.advance();
                Ok(TypeExpr::Usize)
            }
            SurfTokenKind::IntType { signed, bits } => {
                self.advance();
                Ok(TypeExpr::Int { signed, bits })
            }
            SurfTokenKind::AtInt => {
                self.advance();
                self.expect(&SurfTokenKind::LParen)?;
                let signed = if self.peek().kind == SurfTokenKind::Dot {
                    self.advance();
                    let tag = match &self.peek().kind {
                        SurfTokenKind::Ident(s) => s.clone(),
                        _ => {
                            return Err(format!(
                                "Expected '.signed' or '.unsigned' in '@Int(...)' at {}:{}",
                                self.peek().line,
                                self.peek().col
                            ));
                        }
                    };
                    self.advance();
                    match tag.as_str() {
                        "signed" => Expr::Bool(true),
                        "unsigned" => Expr::Bool(false),
                        other => {
                            return Err(format!(
                                "Expected '.signed' or '.unsigned' as first argument to '@Int', found '.{other}'"
                            ));
                        }
                    }
                } else {
                    self.parse_expr()?
                };
                self.expect(&SurfTokenKind::Comma)?;
                let bits = self.parse_expr()?;
                self.expect(&SurfTokenKind::RParen)?;
                Ok(TypeExpr::ComputedInt {
                    signed: Box::new(signed),
                    bits: Box::new(bits),
                })
            }
            SurfTokenKind::AtBackingType => {
                self.advance();
                self.expect(&SurfTokenKind::LParen)?;
                let inner = self.parse_type_expr()?;
                self.expect(&SurfTokenKind::RParen)?;
                Ok(TypeExpr::BackingType(Box::new(inner)))
            }
            SurfTokenKind::AtStruct | SurfTokenKind::AtPackedStruct => {
                let is_packed = tok.kind == SurfTokenKind::AtPackedStruct;
                self.advance();
                self.expect(&SurfTokenKind::LParen)?;
                let fields = self.parse_expr()?;
                self.expect(&SurfTokenKind::RParen)?;
                Ok(TypeExpr::SynthesizedStruct {
                    is_packed,
                    fields: Box::new(fields),
                })
            }
            SurfTokenKind::AtTuple => {
                self.advance();
                self.expect(&SurfTokenKind::LParen)?;
                let elems = self.parse_expr()?;
                self.expect(&SurfTokenKind::RParen)?;
                Ok(TypeExpr::SynthesizedTuple(Box::new(elems)))
            }
            SurfTokenKind::AtEnum => {
                self.advance();
                self.expect(&SurfTokenKind::LParen)?;
                let backing = self.parse_type_expr()?;
                self.expect(&SurfTokenKind::Comma)?;
                let variants = self.parse_expr()?;
                self.expect(&SurfTokenKind::RParen)?;
                Ok(TypeExpr::SynthesizedEnum {
                    backing: Box::new(backing),
                    variants: Box::new(variants),
                })
            }
            SurfTokenKind::AtUnion => {
                self.advance();
                self.expect(&SurfTokenKind::LParen)?;
                let backing = if self.peek().kind == SurfTokenKind::Null {
                    self.advance();
                    None
                } else {
                    Some(Box::new(self.parse_type_expr()?))
                };
                self.expect(&SurfTokenKind::Comma)?;
                let variants = self.parse_expr()?;
                self.expect(&SurfTokenKind::RParen)?;
                Ok(TypeExpr::SynthesizedUnion {
                    backing,
                    variants: Box::new(variants),
                })
            }
            SurfTokenKind::AtError => {
                self.advance();
                self.expect(&SurfTokenKind::LParen)?;
                let variants = self.parse_expr()?;
                self.expect(&SurfTokenKind::RParen)?;
                Ok(TypeExpr::SynthesizedError(Box::new(variants)))
            }
            SurfTokenKind::TypeKw => {
                self.advance();
                Ok(TypeExpr::MetaType)
            }
            SurfTokenKind::SelfType => {
                self.advance();
                Ok(TypeExpr::SelfType)
            }
            SurfTokenKind::Amp | SurfTokenKind::AmpAmp => {
                if tok.kind == SurfTokenKind::AmpAmp {
                    self.tokens[self.pos].kind = SurfTokenKind::Amp;
                } else {
                    self.advance();
                }
                if self.peek().kind == SurfTokenKind::Rel {
                    self.advance();
                    if self.peek().kind == SurfTokenKind::Mut {
                        return Err(
                            "'&rel' relative references do not take a 'mut' modifier; mutability is inherited from 'self' (&Self vs &mut Self)"
                                .to_string(),
                        );
                    }
                    if self.peek().kind == SurfTokenKind::LBracket {
                        self.advance();
                        let elem = self.parse_type_expr()?;
                        self.expect(&SurfTokenKind::RBracket)?;
                        return Ok(TypeExpr::RelSlice(Box::new(elem)));
                    }
                    if matches!(&self.peek().kind, SurfTokenKind::Ident(s) if s == "str") {
                        self.advance();
                        return Ok(TypeExpr::RelStr);
                    }
                    let inner = self.parse_type_expr()?;
                    return Ok(TypeExpr::RelRef(Box::new(inner)));
                }
                let mutable = if self.peek().kind == SurfTokenKind::Mut {
                    self.advance();
                    true
                } else {
                    false
                };
                if !mutable
                    && matches!(&self.peek().kind, SurfTokenKind::Ident(s) if s == "str")
                    && self.peek_n(1).kind != SurfTokenKind::ColonColon
                    && self.peek_n(1).kind != SurfTokenKind::LParen
                {
                    self.advance();
                    return Ok(TypeExpr::StrRef);
                }
                if self.peek().kind == SurfTokenKind::LBracket {
                    self.advance();
                    let elem = self.parse_type_expr()?;
                    if self.peek().kind == SurfTokenKind::RBracket {
                        self.advance();
                        return Ok(TypeExpr::Slice {
                            mutable,
                            elem: Box::new(elem),
                        });
                    }
                    self.expect(&SurfTokenKind::Semi)?;
                    let len = self.parse_expr()?;
                    self.expect(&SurfTokenKind::RBracket)?;
                    return Ok(TypeExpr::Ref {
                        mutable,
                        inner: Box::new(TypeExpr::Array {
                            elem: Box::new(elem),
                            len: Box::new(len),
                        }),
                    });
                }
                let inner = self.parse_type_expr()?;
                Ok(TypeExpr::Ref {
                    mutable,
                    inner: Box::new(inner),
                })
            }
            SurfTokenKind::Star => {
                self.advance();
                let (kind, mutable) = match &self.peek().kind {
                    SurfTokenKind::Mut => {
                        self.advance();
                        (PtrKind::Raw, true)
                    }
                    SurfTokenKind::Const => {
                        self.advance();
                        (PtrKind::Raw, false)
                    }
                    SurfTokenKind::Ident(s) if s == "own" => {
                        self.advance();
                        (PtrKind::Own, true)
                    }
                    SurfTokenKind::Ident(s) if s == "ref" => {
                        self.advance();
                        let mutable = self.peek().kind == SurfTokenKind::Mut;
                        if mutable {
                            self.advance();
                        }
                        (PtrKind::View, mutable)
                    }
                    _ => (PtrKind::Raw, false),
                };
                let inner = self.parse_type_expr()?;
                Ok(TypeExpr::Ptr {
                    mutable,
                    inner: Box::new(inner),
                    kind,
                })
            }
            SurfTokenKind::Question => {
                self.advance();
                let inner = self.parse_type_expr()?;
                Ok(TypeExpr::Optional(Box::new(inner)))
            }
            SurfTokenKind::LBracket => {
                self.advance();
                let elem = self.parse_type_expr()?;
                self.expect(&SurfTokenKind::Semi)?;
                let len = self.parse_expr()?;
                self.expect(&SurfTokenKind::RBracket)?;
                Ok(TypeExpr::Array {
                    elem: Box::new(elem),
                    len: Box::new(len),
                })
            }
            SurfTokenKind::Simd => {
                self.advance();
                if self.peek().kind != SurfTokenKind::LBracket {
                    return Ok(TypeExpr::Constraint(TypeConstraint::Simd));
                }
                self.expect(&SurfTokenKind::LBracket)?;
                let elem = self.parse_type_expr()?;
                self.expect(&SurfTokenKind::Semi)?;
                let len = self.parse_expr()?;
                self.expect(&SurfTokenKind::RBracket)?;
                Ok(TypeExpr::Simd {
                    elem: Box::new(elem),
                    len: Box::new(len),
                })
            }
            SurfTokenKind::Fn => {
                self.advance();
                if self.peek().kind != SurfTokenKind::LParen {
                    return Ok(TypeExpr::Constraint(TypeConstraint::FnPtr));
                }
                self.expect(&SurfTokenKind::LParen)?;
                let mut params = Vec::new();
                while self.peek().kind != SurfTokenKind::RParen {
                    params.push(self.parse_type_expr()?);
                    if self.peek().kind == SurfTokenKind::Comma {
                        self.advance();
                    } else {
                        break;
                    }
                }
                self.expect(&SurfTokenKind::RParen)?;
                let ret = if self.peek().kind == SurfTokenKind::Arrow {
                    self.advance();
                    self.parse_type_expr()?
                } else {
                    TypeExpr::Void
                };
                // A function type's own contract names parameters positionally (`_1`, `_2`, ...),
                // which distinguishes it from the enclosing function's `borrows(name)` clause.
                let borrows = if matches!(&self.peek().kind, SurfTokenKind::Ident(s) if s == "borrows")
                    && self.peek_n(1).kind == SurfTokenKind::LParen
                    && (matches!(&self.peek_n(2).kind, SurfTokenKind::Ident(s) if is_positional_param(s))
                        || (self.peek_n(2).kind == SurfTokenKind::Star
                            && matches!(&self.peek_n(3).kind, SurfTokenKind::Ident(s) if is_positional_param(s))))
                {
                    self.parse_borrows_clause()?
                } else {
                    None
                };
                Ok(TypeExpr::FnPtr {
                    params,
                    ret: Box::new(ret),
                    borrows,
                    is_unsafe: false,
                })
            }
            SurfTokenKind::Tuple => {
                self.advance();
                if self.peek().kind != SurfTokenKind::LBrace {
                    return Ok(TypeExpr::Constraint(TypeConstraint::Tuple));
                }
                self.expect(&SurfTokenKind::LBrace)?;
                let mut elems = Vec::new();
                while self.peek().kind != SurfTokenKind::RBrace {
                    elems.push(self.parse_type_expr()?);
                    if self.peek().kind == SurfTokenKind::Comma {
                        self.advance();
                    } else {
                        break;
                    }
                }
                self.expect(&SurfTokenKind::RBrace)?;
                if elems.is_empty() {
                    return Err(
                        "Empty 'tuple {}' is not a type; use 'void' for the unit type".to_string()
                    );
                }
                Ok(TypeExpr::Tuple(elems))
            }
            SurfTokenKind::Unsafe
                if matches!(self.peek_n(1).kind, SurfTokenKind::Fn | SurfTokenKind::Extern) =>
            {
                self.advance();
                match self.parse_base_type_expr()? {
                    TypeExpr::FnPtr {
                        params,
                        ret,
                        borrows,
                        ..
                    } => Ok(TypeExpr::FnPtr {
                        params,
                        ret,
                        borrows,
                        is_unsafe: true,
                    }),
                    TypeExpr::CFnPtr { params, ret, .. } => Ok(TypeExpr::CFnPtr {
                        params,
                        ret,
                        is_unsafe: true,
                    }),
                    _ => Err("Expected 'fn(...)' after 'unsafe' in type expression".to_string()),
                }
            }
            SurfTokenKind::Extern if self.peek_n(1).kind == SurfTokenKind::Fn => {
                self.advance();
                match self.parse_base_type_expr()? {
                    TypeExpr::FnPtr {
                        params,
                        ret,
                        borrows: None,
                        ..
                    } => Ok(TypeExpr::CFnPtr {
                        params,
                        ret,
                        is_unsafe: false,
                    }),
                    TypeExpr::FnPtr { .. } => Err(
                        "A C function pointer 'extern fn(...)' cannot carry a borrow contract"
                            .to_string(),
                    ),
                    _ => Err("Expected 'fn(...)' after 'extern' in type expression".to_string()),
                }
            }
            SurfTokenKind::Extern => {
                self.advance();
                if matches!(&self.peek().kind, SurfTokenKind::Ident(s) if s == "opaque") {
                    self.advance();
                    let methods = if self.is_composite_body_ahead() {
                        self.parse_opaque_methods_body()?
                    } else {
                        Vec::new()
                    };
                    Ok(TypeExpr::OpaqueDef { methods })
                } else {
                    Err("Expected 'opaque' after 'extern' in type expression".to_string())
                }
            }
            SurfTokenKind::Record => Err(
                "The 'record' keyword has been replaced by 'struct' for transparent product types"
                    .to_string(),
            ),
            SurfTokenKind::Struct => {
                self.advance();
                if self.peek().kind == SurfTokenKind::LParen {
                    return Err(
                        "Ownership and synchronization modifiers ('struct(...)') are forbidden on transparent 'struct' types; use 'opaque(...)' for encapsulated types with custom ownership or synchronization"
                            .to_string(),
                    );
                }
                if !self.is_composite_body_ahead() {
                    return Ok(TypeExpr::Constraint(TypeConstraint::Struct));
                }
                self.parse_struct_body(false)
            }
            SurfTokenKind::Linear => {
                self.advance();
                if self.peek().kind == SurfTokenKind::Sync {
                    Err(
                        "Declaring a 'sync' opaque type asserts thread-safe synchronization and requires 'opaque(linear, unsafe sync)'"
                            .to_string(),
                    )
                } else if matches!(&self.peek().kind, SurfTokenKind::Ident(s) if s == "opaque") {
                    self.advance();
                    self.parse_opaque_body(false, OpaqueMods::new(OpaqueOwnership::Linear, false))
                } else {
                    Ok(TypeExpr::Constraint(TypeConstraint::Linear))
                }
            }
            SurfTokenKind::Unsafe => {
                self.advance();
                let mut ownership = OpaqueOwnership::Default;
                if self.peek().kind == SurfTokenKind::Linear {
                    self.advance();
                    ownership = OpaqueOwnership::Linear;
                }
                self.expect(&SurfTokenKind::Sync)?;
                if self.peek().kind == SurfTokenKind::Linear {
                    self.advance();
                    ownership = OpaqueOwnership::Linear;
                }
                if matches!(&self.peek().kind, SurfTokenKind::Ident(s) if s == "opaque") {
                    self.advance();
                } else {
                    return Err(
                        "Expected 'opaque' after 'unsafe sync' (prefer 'opaque(unsafe sync)')"
                            .to_string(),
                    );
                }
                self.parse_opaque_body(false, OpaqueMods::new(ownership, true))
            }
            SurfTokenKind::Sync if self.peek_n(1).kind != SurfTokenKind::ColonColon => {
                self.advance();
                if self.peek().kind == SurfTokenKind::Linear
                    || matches!(&self.peek().kind, SurfTokenKind::Ident(s) if s == "opaque")
                {
                    return Err(
                        "Declaring a 'sync' opaque type asserts thread-safe synchronization and requires 'opaque(unsafe sync)'"
                            .to_string(),
                    );
                }
                Ok(TypeExpr::Constraint(TypeConstraint::Sync))
            }
            SurfTokenKind::LParen => {
                self.advance();
                let inner = self.parse_type_expr()?;
                self.expect(&SurfTokenKind::RParen)?;
                Ok(inner)
            }
            SurfTokenKind::Ident(_) | SurfTokenKind::Sync => {
                let mut path = vec![self.expect_ident()?];
                while self.peek().kind == SurfTokenKind::ColonColon
                    || (self.peek().kind == SurfTokenKind::Dot
                        && matches!(self.peek_n(1).kind, SurfTokenKind::Ident(_))
                        && self.peek_n(2).kind != SurfTokenKind::LParen)
                {
                    self.advance();
                    path.push(self.expect_ident()?);
                }
                if path.len() == 1 && path[0] == "packed" {
                    if self.peek().kind == SurfTokenKind::Struct {
                        self.advance();
                        return self.parse_struct_body(true);
                    } else if matches!(&self.peek().kind, SurfTokenKind::Ident(s) if s == "opaque")
                    {
                        self.advance();
                        let mods = self.parse_opaque_modifiers()?;
                        return self.parse_opaque_body(true, mods);
                    }
                }
                if path.len() == 1 && path[0] == "opaque" {
                    if self.peek().kind == SurfTokenKind::LParen || self.is_composite_body_ahead() {
                        let mods = self.parse_opaque_modifiers()?;
                        return self.parse_opaque_body(false, mods);
                    } else if self.is_explicit_type_start()
                        || matches!(self.peek().kind, SurfTokenKind::Ident(_))
                    {
                        let bound = self.parse_type_expr()?;
                        return Ok(TypeExpr::OpaqueTrait(Box::new(bound)));
                    } else {
                        return Ok(TypeExpr::BareOpaque);
                    }
                }
                if path.len() == 1 && path[0] == "uninit" {
                    let inner = self.parse_type_expr()?;
                    return Ok(TypeExpr::Uninit(Box::new(inner)));
                }
                if path.len() == 1 && path[0] == "enum" && self.peek().kind == SurfTokenKind::LParen
                {
                    self.advance();
                    let b = self.parse_type_expr()?;
                    self.expect(&SurfTokenKind::RParen)?;
                    if self.peek().kind == SurfTokenKind::LBrace {
                        return self.parse_enum_body(Some(Box::new(b)));
                    } else {
                        return Err("Expected '{' after 'enum(...)'".to_string());
                    }
                }
                if path.len() == 1 && path[0] == "union" && self.peek().kind == SurfTokenKind::LParen
                {
                    self.advance();
                    let b = self.parse_type_expr()?;
                    self.expect(&SurfTokenKind::RParen)?;
                    if self.peek().kind == SurfTokenKind::LBrace {
                        return self.parse_union_body(Some(Box::new(b)));
                    } else {
                        return Err("Expected '{' after 'union(...)'".to_string());
                    }
                }
                if path.len() == 1
                    && path[0] == "error"
                    && matches!(
                        self.peek().kind,
                        SurfTokenKind::LParen | SurfTokenKind::LBrace
                    )
                {
                    let backing = self.parse_error_header()?;
                    return self.parse_error_body(backing);
                }
                if path.len() == 1 && path[0] == "errorcode" {
                    return Err(
                        "The 'errorcode' keyword has been unified into 'error'; use 'error' instead"
                            .to_string(),
                    );
                }
                if path.len() == 1 && self.peek().kind == SurfTokenKind::LBrace {
                    match path[0].as_str() {
                        "enum" => return self.parse_enum_body(None),
                        "union" => return self.parse_union_body(None),
                        "overlay" => return self.parse_overlay_body(),
                        "trait"
                            if matches!(
                                self.peek_n(1).kind,
                                SurfTokenKind::Fn | SurfTokenKind::RBrace
                            ) =>
                        {
                            return self.parse_trait_body();
                        }
                        _ => {}
                    }
                }
                if path.len() == 1
                    && path[0] == "map"
                    && self.peek().kind == SurfTokenKind::LBracket
                {
                    self.advance();
                    let key = self.parse_type_expr()?;
                    self.expect(&SurfTokenKind::Comma)?;
                    let val = self.parse_type_expr()?;
                    self.expect(&SurfTokenKind::RBracket)?;
                    return Ok(TypeExpr::Map {
                        key: Box::new(key),
                        val: Box::new(val),
                    });
                }
                if self.peek().kind == SurfTokenKind::LParen
                    && self.peek_n(1).kind == SurfTokenKind::RParen
                {
                    // `F()`: a type function without parameters.
                    self.advance();
                    self.advance();
                    return Ok(TypeExpr::TypeCall {
                        path,
                        args: Vec::new(),
                    });
                }
                if self.peek().kind == SurfTokenKind::LParen {
                    return Err(format!(
                        "Type function arguments go in brackets: write '{}[...]' at {}:{}",
                        path.join("::"),
                        self.peek().line,
                        self.peek().col
                    ));
                }
                if self.peek().kind == SurfTokenKind::LBracket {
                    let args = self.parse_comptime_args()?;
                    Ok(TypeExpr::TypeCall { path, args })
                } else if path.len() == 1 {
                    if let Some(ck) = CIntKind::from_ident(path[0].as_str()) {
                        return Ok(TypeExpr::CInt(ck));
                    }
                    match path[0].as_str() {
                        "f128" => Err(
                            "Type 'f128' is reserved for future IEEE 754 quadruple-precision floating-point support"
                                .to_string(),
                        ),
                        "c_longdouble" => Err(
                            "Type 'c_longdouble' is reserved for future C ABI extended floating-point support"
                                .to_string(),
                        ),
                        "trait" => Ok(TypeExpr::MetaType),
                        "module" => Ok(TypeExpr::Constraint(TypeConstraint::Module)),
                        "scalar" => Ok(TypeExpr::Constraint(TypeConstraint::Scalar)),
                        "callable" => Ok(TypeExpr::Constraint(TypeConstraint::Callable)),
                        "closure" => Ok(TypeExpr::Constraint(TypeConstraint::Closure)),
                        "number" => Ok(TypeExpr::Constraint(TypeConstraint::Number)),
                        "integer" => Ok(TypeExpr::Constraint(TypeConstraint::Integer)),
                        "signed" => Ok(TypeExpr::Constraint(TypeConstraint::Signed)),
                        "unsigned" => Ok(TypeExpr::Constraint(TypeConstraint::Unsigned)),
                        "float" => Ok(TypeExpr::Constraint(TypeConstraint::Float)),
                        "aggregate" => Ok(TypeExpr::Constraint(TypeConstraint::Aggregate)),
                        "discriminated" => Ok(TypeExpr::Constraint(TypeConstraint::Discriminated)),
                        "enum" => Ok(TypeExpr::Constraint(TypeConstraint::Enum)),
                        "union" => Ok(TypeExpr::Constraint(TypeConstraint::Union)),
                        "overlay" => Ok(TypeExpr::Constraint(TypeConstraint::Overlay)),
                        "error" => Ok(TypeExpr::Constraint(TypeConstraint::Error)),
                        "sequence" => Ok(TypeExpr::Constraint(TypeConstraint::Sequence)),
                        "array" => Ok(TypeExpr::Constraint(TypeConstraint::Array)),
                        "slice" => Ok(TypeExpr::Constraint(TypeConstraint::Slice)),
                        "send" => Ok(TypeExpr::Constraint(TypeConstraint::Send)),
                        "format" => Ok(TypeExpr::Constraint(TypeConstraint::Format)),
                        "copy" => Ok(TypeExpr::Constraint(TypeConstraint::Copy)),
                        "clone" => Ok(TypeExpr::Constraint(TypeConstraint::Clone)),
                        "default" => Ok(TypeExpr::Constraint(TypeConstraint::Default)),
                        "affine" => Ok(TypeExpr::Constraint(TypeConstraint::Affine)),
                        _ => Ok(TypeExpr::Named(path)),
                    }
                } else {
                    Ok(TypeExpr::Named(path))
                }
            }
            _ => Err(format!(
                "Expected type expression, found {:?} at {}:{}",
                tok.kind, tok.line, tok.col
            )),
        }
    }

    fn is_explicit_type_start(&self) -> bool {
        if matches!(
            self.peek().kind,
            SurfTokenKind::Bool
                | SurfTokenKind::RuneKw
                | SurfTokenKind::F32
                | SurfTokenKind::F64
                | SurfTokenKind::Isize
                | SurfTokenKind::Usize
                | SurfTokenKind::IntType { .. }
        ) && matches!(
            self.peek_n(1).kind,
            SurfTokenKind::ColonColon | SurfTokenKind::Dot
        ) {
            return false;
        }
        matches!(
            self.peek().kind,
            SurfTokenKind::Void
                | SurfTokenKind::Never
                | SurfTokenKind::Bool
                | SurfTokenKind::RuneKw
                | SurfTokenKind::F32
                | SurfTokenKind::F64
                | SurfTokenKind::Isize
                | SurfTokenKind::Usize
                | SurfTokenKind::IntType { .. }
                | SurfTokenKind::AtInt
                | SurfTokenKind::AtBackingType
                | SurfTokenKind::AtStruct
                | SurfTokenKind::AtPackedStruct
                | SurfTokenKind::AtTuple
                | SurfTokenKind::AtEnum
                | SurfTokenKind::AtUnion
                | SurfTokenKind::AtError
                | SurfTokenKind::TypeKw
                | SurfTokenKind::Tuple
                | SurfTokenKind::Struct
                | SurfTokenKind::Extern
                | SurfTokenKind::Linear
                | SurfTokenKind::Sync
                | SurfTokenKind::Question
                | SurfTokenKind::LBracket
        ) || (self.peek().kind == SurfTokenKind::Unsafe
            && matches!(
                self.peek_n(1).kind,
                SurfTokenKind::Sync | SurfTokenKind::Linear | SurfTokenKind::Fn | SurfTokenKind::Extern
            ))
            || (self.peek().kind == SurfTokenKind::Simd
                && self.peek_n(1).kind == SurfTokenKind::LBracket)
            // `*mut T` / `*const T` / `*own T` / `*ref T`: a dereference is never followed by
            // `mut` or `const`, and `*own` / `*ref` are not expressions.
            || (self.peek().kind == SurfTokenKind::Star
                && (matches!(self.peek_n(1).kind, SurfTokenKind::Mut | SurfTokenKind::Const)
                    || (matches!(&self.peek_n(1).kind, SurfTokenKind::Ident(s) if s == "own" || s == "ref")
                        && matches!(
                            self.peek_n(2).kind,
                            SurfTokenKind::Ident(_) | SurfTokenKind::Star | SurfTokenKind::Question | SurfTokenKind::Mut
                        ))))
            // Anonymous declarations (`enum { ... }`, `opaque(linear) { ... }`), which are never
            // expressions.
            || matches!(&self.peek().kind, SurfTokenKind::Ident(s)
                if matches!(s.as_str(), "enum" | "union" | "error" | "overlay" | "opaque")
                    && (self.peek_n(1).kind == SurfTokenKind::LBrace
                        || self.peek_n(1).kind == SurfTokenKind::LParen))
            || (matches!(&self.peek().kind, SurfTokenKind::Ident(s) if s == "map")
                && self.peek_n(1).kind == SurfTokenKind::LBracket)
            || (self.peek().kind == SurfTokenKind::Amp
                && ((self.peek_n(1).kind == SurfTokenKind::LBracket
                    && self.is_slice_type_ahead(1))
                    || matches!(&self.peek_n(1).kind, SurfTokenKind::Ident(s) if s == "str")
                    || (self.peek_n(1).kind == SurfTokenKind::Mut
                        && self.peek_n(2).kind == SurfTokenKind::LBracket
                        && self.is_slice_type_ahead(2))))
            || self.is_fn_type_ahead()
            || (matches!(
                &self.peek().kind,
                SurfTokenKind::Ident(s)
                    if (s == "opaque"
                        || CIntKind::from_ident(s).is_some())
                        && !matches!(
                            self.peek_n(1).kind,
                            SurfTokenKind::ColonColon | SurfTokenKind::Dot
                        )
            ))
            || (matches!(&self.peek().kind, SurfTokenKind::Ident(s) if s == "packed")
                && (self.peek_n(1).kind == SurfTokenKind::Struct
                    || matches!(&self.peek_n(1).kind, SurfTokenKind::Ident(s2) if s2 == "opaque")))
            || (matches!(
                &self.peek().kind,
                SurfTokenKind::Ident(s)
                    if s == "enum" || s == "union" || s == "overlay" || s == "error" || s == "trait"
            ) && (self.peek_n(1).kind == SurfTokenKind::LBrace
                || (matches!(&self.peek().kind, SurfTokenKind::Ident(s) if s == "enum" || s == "union" || s == "error")
                    && self.peek_n(1).kind == SurfTokenKind::LParen)))
            || (matches!(&self.peek().kind, SurfTokenKind::Ident(s) if s == "uninit")
                && !matches!(
                    self.peek_n(1).kind,
                    SurfTokenKind::LParen
                        | SurfTokenKind::Semi
                        | SurfTokenKind::Comma
                        | SurfTokenKind::RParen
                        | SurfTokenKind::RBrace
                        | SurfTokenKind::RBracket
                ))
    }

    fn is_slice_type_ahead(&self, bracket_offset: usize) -> bool {
        let k = bracket_offset + 1;
        // Scan to matching `]` at depth 0; a top-level `,` or struct literal `{` means a slice literal `&[...]`.
        let mut depth = 0usize;
        let mut scan = k;
        loop {
            match &self.peek_n(scan).kind {
                SurfTokenKind::Eof | SurfTokenKind::Semi if depth == 0 => break,
                SurfTokenKind::RBracket if depth == 0 => break,
                SurfTokenKind::Comma if depth == 0 => return false,
                SurfTokenKind::LParen | SurfTokenKind::LBracket | SurfTokenKind::LBrace => {
                    depth += 1;
                }
                SurfTokenKind::RParen | SurfTokenKind::RBracket | SurfTokenKind::RBrace => {
                    depth = depth.saturating_sub(1);
                }
                _ => {}
            }
            scan += 1;
        }
        match &self.peek_n(k).kind {
            SurfTokenKind::RBracket
            | SurfTokenKind::Int(_)
            | SurfTokenKind::Float(_)
            | SurfTokenKind::True
            | SurfTokenKind::False
            | SurfTokenKind::RuneLit(_)
            | SurfTokenKind::Str(_)
            | SurfTokenKind::FStr(_)
            | SurfTokenKind::Null
            | SurfTokenKind::LBrace => false,
            SurfTokenKind::Ident(_) => {
                let mut idx = k + 1;
                while self.peek_n(idx).kind == SurfTokenKind::ColonColon {
                    idx += 2;
                }
                matches!(
                    self.peek_n(idx).kind,
                    SurfTokenKind::RBracket
                        | SurfTokenKind::Semi
                        | SurfTokenKind::LParen
                        | SurfTokenKind::LBracket
                )
            }
            _ => true,
        }
    }

    fn is_fn_type_ahead(&self) -> bool {
        if self.peek().kind != SurfTokenKind::Fn || self.peek_n(1).kind != SurfTokenKind::LParen {
            return false;
        }
        // In a lambda `fn(x: T)` or `fn(mut x: T)`, the first parameter starts with `mut` or `ident :`.
        if self.peek_n(2).kind == SurfTokenKind::Mut
            || (matches!(self.peek_n(2).kind, SurfTokenKind::Ident(_))
                && self.peek_n(3).kind == SurfTokenKind::Colon)
        {
            return false;
        }
        // For `fn() ...`, scan to matching `)` and check if `{` follows (or `-> RetTy {`).
        if self.peek_n(2).kind == SurfTokenKind::RParen {
            if self.peek_n(3).kind == SurfTokenKind::LBrace {
                return false;
            }
            if self.peek_n(3).kind == SurfTokenKind::Arrow {
                let mut k = 4;
                while !matches!(
                    self.peek_n(k).kind,
                    SurfTokenKind::LBrace
                        | SurfTokenKind::Comma
                        | SurfTokenKind::RParen
                        | SurfTokenKind::Semi
                        | SurfTokenKind::Eof
                ) {
                    k += 1;
                }
                if self.peek_n(k).kind == SurfTokenKind::LBrace {
                    return false;
                }
            }
        }
        true
    }

    fn expr_as_type_expr(expr: &Expr) -> Option<TypeExpr> {
        match expr {
            Expr::Path(p) => Some(TypeExpr::Named(p.clone())),
            Expr::Field { base, field } => {
                if let Expr::Path(mut p) = (**base).clone() {
                    p.push(field.clone());
                    Some(TypeExpr::Named(p))
                } else {
                    None
                }
            }
            Expr::TypeVal(te) => Some(te.clone()),
            Expr::Index { base, index } => {
                if let Expr::Path(path) = base.as_ref() {
                    Some(TypeExpr::TypeCall {
                        path: path.clone(),
                        args: vec![(**index).clone()],
                    })
                } else {
                    None
                }
            }
            Expr::LogicalOr(a, b) => {
                let mut terms = Vec::new();
                match Self::expr_as_type_expr(a)? {
                    TypeExpr::ErrorSetUnion(sub) => terms.extend(sub),
                    other => terms.push(other),
                }
                match Self::expr_as_type_expr(b)? {
                    TypeExpr::ErrorSetUnion(sub) => terms.extend(sub),
                    other => terms.push(other),
                }
                Some(TypeExpr::ErrorSetUnion(terms))
            }
            _ => None,
        }
    }

    fn parse_expr_or_type(&mut self) -> Result<Expr, String> {
        if self.is_explicit_type_start() {
            let ty = self.parse_type_expr()?;
            if self.peek().kind == SurfTokenKind::LBrace {
                if matches!(ty, TypeExpr::Simd { .. } | TypeExpr::Array { .. }) {
                    self.advance();
                    let mut elems = Vec::new();
                    while self.peek().kind != SurfTokenKind::RBrace {
                        elems.push(self.parse_expr()?);
                        if self.peek().kind == SurfTokenKind::Comma {
                            self.advance();
                        } else {
                            break;
                        }
                    }
                    self.expect(&SurfTokenKind::RBrace)?;
                    return Ok(Expr::SimdLit { ty, elems });
                }
                if matches!(
                    ty,
                    TypeExpr::Struct { .. }
                        | TypeExpr::Opaque { .. }
                        | TypeExpr::Overlay(_)
                        | TypeExpr::SynthesizedStruct { .. }
                ) {
                    return self.parse_struct_lit_fields(ty);
                }
            }
            let mut expr = Expr::TypeVal(ty);
            while matches!(
                self.peek().kind,
                SurfTokenKind::ColonColon | SurfTokenKind::Dot
            ) {
                self.advance();
                let name = self.expect_ident()?;
                expr = Expr::Field {
                    base: Box::new(expr),
                    field: name,
                };
            }
            Ok(expr)
        } else {
            let expr = self.parse_expr()?;
            if self.peek().kind == SurfTokenKind::Bang
                && let Some(err_ty) = Self::expr_as_type_expr(&expr)
            {
                self.advance();
                let ok_ty = self.parse_type_expr()?;
                return Ok(Expr::TypeVal(TypeExpr::Result {
                    err: Box::new(err_ty),
                    ok: Box::new(ok_ty),
                }));
            }
            if self.peek().kind == SurfTokenKind::In
                && let Expr::Path(path) = expr
            {
                self.advance();
                let mut ranges = Vec::new();
                loop {
                    let lo = self.parse_additive_expr()?;
                    self.expect(&SurfTokenKind::DotDotEq)?;
                    let hi = self.parse_additive_expr()?;
                    ranges.push((lo, hi));
                    if self.peek().kind == SurfTokenKind::Pipe {
                        self.advance();
                    } else {
                        break;
                    }
                }
                return Ok(Expr::TypeVal(TypeExpr::Pattern {
                    base: Box::new(TypeExpr::Named(path)),
                    ranges,
                }));
            }
            Ok(expr)
        }
    }
}
