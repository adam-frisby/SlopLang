mod expr;
mod lexer;

pub use lexer::{SurfToken, SurfTokenKind, SurfaceLexer};

use crate::ast::{
    BindMode, Block, BorrowContractItem, CIntKind, CloneHookDecl, ConstDecl, DropHookDecl, Expr,
    ExternFuncDecl, FieldDecl, FmtSegment, FuncDecl, ImplDecl, ImportDecl, ImportTargets, Item,
    MatchPat, ModuleAst, Param, SelectArm, SelectOp, StaticDecl, Stmt, StructOwnership,
    TraitMethodDecl, TypeConstraint, TypeExpr, Visibility, WherePredicate,
};
use crate::ir::{BinOp, UnOp};

/// Whether `s` is a positional parameter name (`_1`, `_2`, ...) as used in function-type contracts.
pub(crate) fn is_positional_param(s: &str) -> bool {
    s.strip_prefix('_')
        .is_some_and(|d| !d.is_empty() && d.bytes().all(|b| b.is_ascii_digit()))
}

/// Modifiers parsed from `opaque(...)`: ownership discipline, `unsafe sync`, and owned type parameters.
struct StructMods {
    ownership: StructOwnership,
    is_sync: bool,
    owns: Vec<String>,
}

impl StructMods {
    fn new(ownership: StructOwnership, is_sync: bool) -> Self {
        Self {
            ownership,
            is_sync,
            owns: Vec::new(),
        }
    }
}

pub struct SurfaceParser {
    tokens: Vec<SurfToken>,
    pos: usize,
    current_type_name: Option<String>,
    extra_items: Vec<Item>,
}

impl SurfaceParser {
    pub fn parse_module(src: &str) -> Result<ModuleAst, String> {
        let tokens = SurfaceLexer::new(src).tokenize()?;
        let mut parser = Self {
            tokens,
            pos: 0,
            current_type_name: None,
            extra_items: Vec::new(),
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
                self.advance();
                Ok(Visibility::Export)
            } else if self.peek().kind == SurfTokenKind::LParen {
                self.advance();
                self.expect(&SurfTokenKind::Pkg)?;
                self.expect(&SurfTokenKind::RParen)?;
                Ok(Visibility::PubPkg)
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
            match &self.peek().kind {
                SurfTokenKind::Import => {
                    imports.push(self.parse_import(vis)?);
                }
                SurfTokenKind::Fn => {
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
                    let ty = self.parse_record_body(false)?;
                    self.current_type_name = prev_type_name;
                    items.push(Item::TypeDecl { vis, name, ty });
                }
                SurfTokenKind::Ident(s) if s == "packed" => {
                    self.advance();
                    if self.peek().kind == SurfTokenKind::Struct {
                        self.advance();
                        let name = self.expect_ident()?;
                        let ty = self.parse_record_body(true)?;
                        items.push(Item::TypeDecl { vis, name, ty });
                    } else if matches!(&self.peek().kind, SurfTokenKind::Ident(s2) if s2 == "opaque")
                    {
                        self.advance();
                        let mods = self.parse_struct_modifiers()?;
                        let name = self.expect_ident()?;
                        let ty = self.parse_struct_body(true, mods)?;
                        items.push(Item::TypeDecl { vis, name, ty });
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
                    let ty = self.parse_struct_body(
                        false,
                        StructMods::new(StructOwnership::Linear, false),
                    )?;
                    items.push(Item::TypeDecl { vis, name, ty });
                }
                SurfTokenKind::Unsafe => {
                    self.advance();
                    let mut ownership = StructOwnership::Affine;
                    if self.peek().kind == SurfTokenKind::Linear {
                        self.advance();
                        ownership = StructOwnership::Linear;
                    }
                    self.expect(&SurfTokenKind::Sync)?;
                    if self.peek().kind == SurfTokenKind::Linear {
                        self.advance();
                        ownership = StructOwnership::Linear;
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
                    let ty = self.parse_struct_body(false, StructMods::new(ownership, true))?;
                    items.push(Item::TypeDecl { vis, name, ty });
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
                    items.push(Item::TypeDecl { vis, name, ty });
                }
                SurfTokenKind::Ident(s) if s == "union" => {
                    self.advance();
                    // `union(Opcode) Message { ... }` links the tag to an explicit enum.
                    let tag_enum = if self.peek().kind == SurfTokenKind::LParen {
                        self.advance();
                        let t = self.parse_type_expr()?;
                        self.expect(&SurfTokenKind::RParen)?;
                        Some(Box::new(t))
                    } else {
                        None
                    };
                    let name = self.expect_ident()?;
                    let mut ty = self.parse_union_body()?;
                    if let TypeExpr::Union { tag_enum: slot, .. } = &mut ty {
                        *slot = tag_enum;
                    }
                    items.push(Item::TypeDecl { vis, name, ty });
                }
                SurfTokenKind::Ident(s) if s == "overlay" => {
                    self.advance();
                    let name = self.expect_ident()?;
                    let ty = self.parse_overlay_body()?;
                    items.push(Item::TypeDecl { vis, name, ty });
                }
                SurfTokenKind::Ident(s) if s == "error" => {
                    self.advance();
                    if self.peek().kind == SurfTokenKind::LParen {
                        return Err(
                            "Explicit backing integer types ('error(...)') are forbidden on 'error' declarations; 'error' is a unified sum type"
                                .to_string(),
                        );
                    }
                    let name = self.expect_ident()?;
                    let ty = self.parse_error_body()?;
                    items.push(Item::TypeDecl { vis, name, ty });
                }
                SurfTokenKind::Ident(s) if s == "trait" => {
                    self.advance();
                    let name = self.expect_ident()?;
                    // `trait Name { ... }` declares a trait; `trait Name = <trait expr>;` aliases one.
                    let ty = if self.peek().kind == SurfTokenKind::Eq {
                        self.advance();
                        let t = self.parse_type_expr()?;
                        self.expect(&SurfTokenKind::Semi)?;
                        t
                    } else {
                        self.parse_trait_body()?
                    };
                    items.push(Item::TypeDecl { vis, name, ty });
                }
                SurfTokenKind::Ident(s) if s == "opaque" => {
                    self.advance();
                    let has_modifiers = self.peek().kind == SurfTokenKind::LParen;
                    let mods = self.parse_struct_modifiers()?;
                    let name = self.expect_ident()?;
                    let ty = if self.peek().kind == SurfTokenKind::Eq {
                        if has_modifiers {
                            return Err(format!(
                                "Single-value opaque newtype '{name}' inherits ownership and synchronization from its underlying type; use 'opaque(...) {name} {{ ... }}' for custom modifiers"
                            ));
                        }
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
                        TypeExpr::OpaqueNewtype {
                            underlying: Box::new(underlying),
                            methods,
                        }
                    } else if self.peek().kind == SurfTokenKind::LBrace {
                        let s_ty = self.parse_struct_body(false, mods)?;
                        if self.peek().kind == SurfTokenKind::Semi {
                            self.advance();
                        }
                        s_ty
                    } else {
                        return Err(format!(
                            "Unsized foreign C handles must be declared with 'extern opaque {name};' (or use 'opaque {name} {{}}' for a zero-sized encapsulated type)"
                        ));
                    };
                    items.push(Item::TypeDecl { vis, name, ty });
                }
                SurfTokenKind::TypeKw => {
                    self.advance();
                    let name = self.expect_ident()?;
                    self.expect(&SurfTokenKind::Eq)?;
                    if matches!(&self.peek().kind, SurfTokenKind::Ident(s) if s == "trait")
                        && self.peek_n(1).kind == SurfTokenKind::LBrace
                    {
                        return Err(format!(
                            "Traits are not types: declare the alias with 'trait {name} = trait {{ ... }};' instead of 'type {name} = trait {{ ... }};'"
                        ));
                    }
                    let ty = if self.peek().kind == SurfTokenKind::Extern
                        && matches!(&self.peek_n(1).kind, SurfTokenKind::Ident(s) if s == "opaque")
                    {
                        self.advance();
                        self.advance();
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
                        TypeExpr::OpaqueDef { methods }
                    } else if matches!(&self.peek().kind, SurfTokenKind::Ident(s) if s == "opaque")
                        && self.peek_n(1).kind != SurfTokenKind::LParen
                        && self.peek_n(1).kind != SurfTokenKind::LBrace
                    {
                        self.advance();
                        if self.peek().kind == SurfTokenKind::Semi {
                            return Err(format!(
                                "Unsized foreign C handles must be declared with 'extern opaque {name};' or 'type {name} = extern opaque;'"
                            ));
                        }
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
                        TypeExpr::OpaqueNewtype {
                            underlying: Box::new(underlying),
                            methods,
                        }
                    } else {
                        let ty = self.parse_type_expr()?;
                        self.expect(&SurfTokenKind::Semi)?;
                        ty
                    };
                    items.push(Item::TypeDecl { vis, name, ty });
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
        })
    }

    fn parse_func_decl(&mut self, vis: Visibility) -> Result<FuncDecl, String> {
        self.expect(&SurfTokenKind::Fn)?;
        let name = self.expect_ident()?;
        self.expect(&SurfTokenKind::LParen)?;
        let mut params = Vec::new();
        while self.peek().kind != SurfTokenKind::RParen {
            let is_comptime = if self.peek().kind == SurfTokenKind::Comptime {
                self.advance();
                true
            } else {
                false
            };
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
                    "Expected ':' and type annotation for parameter '{pname}' at {}:{}",
                    self.peek().line,
                    self.peek().col
                ));
            };
            params.push(Param {
                is_comptime,
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
        let ret_ty = if self.peek().kind == SurfTokenKind::Arrow {
            self.advance();
            self.parse_type_expr()?
        } else {
            TypeExpr::Void
        };
        let borrows = self.parse_borrows_clause()?;
        let where_clauses = self.parse_where_clauses()?;
        let body = self.parse_block()?;
        Ok(FuncDecl {
            vis,
            name,
            params,
            ret_ty,
            borrows,
            where_clauses,
            body,
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
            let first = self.expect_ident()?;
            if self.peek().kind == SurfTokenKind::Colon {
                self.advance();
                let src = self.expect_ident()?;
                items.push(BorrowContractItem::ParamFlow { dst: first, src });
            } else {
                items.push(BorrowContractItem::Return(first));
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

    fn parse_record_body(&mut self, is_packed: bool) -> Result<TypeExpr, String> {
        self.expect(&SurfTokenKind::LBrace)?;
        let mut fields = Vec::new();
        let mut methods = Vec::new();
        while self.peek().kind != SurfTokenKind::RBrace {
            let vis = self.parse_visibility()?;
            if self.peek().kind == SurfTokenKind::Fn {
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
                    });
                }
                self.extra_items.push(Item::TypeDecl {
                    vis,
                    name: ename,
                    ty: ety,
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
            } else if matches!(
                self.peek().kind,
                SurfTokenKind::DefaultKw | SurfTokenKind::CloneKw | SurfTokenKind::DropKw
            ) || (matches!(&self.peek().kind, SurfTokenKind::Ident(s) if s == "format")
                && self.peek_n(1).kind == SurfTokenKind::LParen)
            {
                let hook_name = match &self.peek().kind {
                    SurfTokenKind::DefaultKw => "default",
                    SurfTokenKind::CloneKw => "clone",
                    SurfTokenKind::DropKw => "drop",
                    _ => "format",
                };
                return Err(format!(
                    "Lifecycle hook '{hook_name}' is forbidden on transparent 'struct' types; transparent types are always auto-synthesized structurally, and only 'opaque' types may define custom lifecycle hooks"
                ));
            } else {
                let fname = self.expect_ident()?;
                self.expect(&SurfTokenKind::Colon)?;
                let fty = self.parse_type_expr()?;
                let default_val = if self.peek().kind == SurfTokenKind::Eq {
                    self.advance();
                    Some(self.parse_expr()?)
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
                    default_val,
                });
                if self.peek().kind == SurfTokenKind::Comma {
                    self.advance();
                }
            }
        }
        self.expect(&SurfTokenKind::RBrace)?;
        Ok(TypeExpr::Record {
            is_packed,
            fields,
            methods,
        })
    }

    fn parse_struct_modifiers(&mut self) -> Result<StructMods, String> {
        if self.peek().kind != SurfTokenKind::LParen {
            return Ok(StructMods::new(StructOwnership::Affine, false));
        }
        self.advance(); // consume '('
        let mut ownership_opt: Option<StructOwnership> = None;
        let mut is_sync = false;
        let mut owns: Vec<String> = Vec::new();

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
                    ownership_opt = Some(StructOwnership::Copy);
                }
                SurfTokenKind::Ident(s) if s == "affine" => {
                    self.advance();
                    if ownership_opt.is_some() {
                        return Err(
                            "Conflicting ownership modifiers in 'opaque(...)' (choose at most one of 'copy', 'affine', or 'linear')"
                                .to_string(),
                        );
                    }
                    ownership_opt = Some(StructOwnership::Affine);
                }
                SurfTokenKind::Linear => {
                    self.advance();
                    if ownership_opt.is_some() {
                        return Err(
                            "Conflicting ownership modifiers in 'opaque(...)' (choose at most one of 'copy', 'affine', or 'linear')"
                                .to_string(),
                        );
                    }
                    ownership_opt = Some(StructOwnership::Linear);
                }
                SurfTokenKind::Unsafe => {
                    self.advance();
                    self.expect(&SurfTokenKind::Sync)?;
                    is_sync = true;
                }
                SurfTokenKind::Sync => {
                    return Err(
                        "Declaring a 'sync' opaque type asserts thread-safe synchronization and requires 'opaque(unsafe sync)'"
                            .to_string(),
                    );
                }
                SurfTokenKind::Ident(s) if s == "owns" => {
                    self.advance();
                    if !owns.is_empty() {
                        return Err("Duplicate 'owns' modifier in 'opaque(...)'".to_string());
                    }
                    // `owns T` or `owns K, V`: parameter names continue until the next modifier keyword
                    owns.push(self.expect_ident()?);
                    while self.peek().kind == SurfTokenKind::Comma
                        && matches!(&self.peek_n(1).kind, SurfTokenKind::Ident(n)
                            if !matches!(n.as_str(), "copy" | "affine" | "owns"))
                    {
                        self.advance();
                        owns.push(self.expect_ident()?);
                    }
                }
                other => {
                    let tok = self.peek();
                    return Err(format!(
                        "Unknown opaque modifier {:?} at {}:{} (expected 'copy', 'affine', 'linear', 'owns T', or 'unsafe sync')",
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
        let ownership = ownership_opt.unwrap_or(StructOwnership::Affine);
        if ownership == StructOwnership::Copy && !owns.is_empty() {
            return Err(
                "'opaque(copy, owns ...)' is invalid: an owning 'copy' type would duplicate the values it owns"
                    .to_string(),
            );
        }
        Ok(StructMods {
            ownership,
            is_sync,
            owns,
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

    fn parse_struct_body(&mut self, is_packed: bool, mods: StructMods) -> Result<TypeExpr, String> {
        let StructMods {
            ownership,
            is_sync,
            owns,
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
            match &self.peek().kind {
                SurfTokenKind::Fn => {
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
                SurfTokenKind::DefaultKw => {
                    self.advance();
                    self.expect(&SurfTokenKind::LParen)?;
                    self.expect(&SurfTokenKind::RParen)?;
                    self.expect(&SurfTokenKind::Arrow)?;
                    let _ = self.parse_type_expr()?;
                    default_hook = Some(self.parse_block()?);
                }
                SurfTokenKind::CloneKw => {
                    self.advance();
                    self.expect(&SurfTokenKind::LParen)?;
                    let self_name = self.expect_ident()?;
                    self.expect(&SurfTokenKind::Colon)?;
                    let _ = self.parse_type_expr()?;
                    self.expect(&SurfTokenKind::RParen)?;
                    self.expect(&SurfTokenKind::Arrow)?;
                    let _ = self.parse_type_expr()?;
                    let where_clauses = self.parse_where_clauses()?;
                    clone_hooks.push(CloneHookDecl {
                        self_name,
                        where_clauses,
                        body: self.parse_block()?,
                    });
                }
                SurfTokenKind::DropKw => {
                    self.advance();
                    self.expect(&SurfTokenKind::LParen)?;
                    let self_name = self.expect_ident()?;
                    self.expect(&SurfTokenKind::Colon)?;
                    let _ = self.parse_type_expr()?;
                    self.expect(&SurfTokenKind::RParen)?;
                    let where_clauses = self.parse_where_clauses()?;
                    drop_hooks.push(DropHookDecl {
                        self_name,
                        where_clauses,
                        body: self.parse_block()?,
                    });
                }
                SurfTokenKind::Ident(s)
                    if s == "format" && self.peek_n(1).kind == SurfTokenKind::LParen =>
                {
                    self.advance();
                    self.expect(&SurfTokenKind::LParen)?;
                    let self_name = self.expect_ident()?;
                    self.expect(&SurfTokenKind::Colon)?;
                    let _ = self.parse_type_expr()?;
                    self.expect(&SurfTokenKind::Comma)?;
                    let fmt_name = self.expect_ident()?;
                    self.expect(&SurfTokenKind::Colon)?;
                    let _ = self.parse_type_expr()?;
                    let opt_spec_name = if self.peek().kind == SurfTokenKind::Comma {
                        self.advance();
                        if self.peek().kind != SurfTokenKind::RParen {
                            let sname = self.expect_ident()?;
                            self.expect(&SurfTokenKind::Colon)?;
                            let _ = self.parse_type_expr()?;
                            Some(sname)
                        } else {
                            None
                        }
                    } else {
                        None
                    };
                    self.expect(&SurfTokenKind::RParen)?;
                    format_hook = Some((self_name, fmt_name, opt_spec_name, self.parse_block()?));
                }
                _ => {
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
                        Some(self.parse_expr()?)
                    } else {
                        None
                    };
                    // Opaque fields are strictly private to the opaque block
                    fields.push(FieldDecl {
                        vis: Visibility::Private,
                        name: fname,
                        ty: fty,
                        default_val,
                    });
                    if self.peek().kind == SurfTokenKind::Comma {
                        self.advance();
                    }
                }
            }
        }
        self.expect(&SurfTokenKind::RBrace)?;
        Ok(TypeExpr::Struct {
            is_packed,
            ownership,
            is_sync,
            owns,
            fields,
            consts,
            statics,
            methods,
            default_hook,
            clone_hooks,
            drop_hooks,
            format_hook,
        })
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

    fn parse_union_body(&mut self) -> Result<TypeExpr, String> {
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
            variants.push((vname, payload));
            if self.peek().kind == SurfTokenKind::Comma {
                self.advance();
            } else {
                break;
            }
        }
        self.expect(&SurfTokenKind::RBrace)?;
        Ok(TypeExpr::Union {
            tag_enum: None,
            variants,
        })
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

    fn parse_error_body(&mut self) -> Result<TypeExpr, String> {
        if self.peek().kind == SurfTokenKind::LParen {
            return Err(
                "Explicit backing integer types ('error(...)') are forbidden on 'error' declarations; 'error' is a unified sum type"
                    .to_string(),
            );
        }
        self.expect(&SurfTokenKind::LBrace)?;
        let mut variants = Vec::new();
        while self.peek().kind != SurfTokenKind::RBrace {
            let mut vname = self.expect_ident()?;
            while self.peek().kind == SurfTokenKind::ColonColon {
                self.advance();
                let seg = self.expect_ident()?;
                vname.push_str("::");
                vname.push_str(&seg);
            }
            if self.peek().kind == SurfTokenKind::Eq {
                return Err(format!(
                    "Explicit integer discriminants ('= N') are forbidden on 'error' variant '{vname}'; error tags are compiler-managed"
                ));
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
            variants.push((vname, payload));
            if self.peek().kind == SurfTokenKind::Comma {
                self.advance();
            } else {
                break;
            }
        }
        self.expect(&SurfTokenKind::RBrace)?;
        Ok(TypeExpr::Error(variants))
    }

    fn parse_trait_body(&mut self) -> Result<TypeExpr, String> {
        self.expect(&SurfTokenKind::LBrace)?;
        let mut methods = Vec::new();
        while self.peek().kind != SurfTokenKind::RBrace {
            let _vis = self.parse_visibility()?;
            self.expect(&SurfTokenKind::Fn)?;
            let name = self.expect_ident()?;
            self.expect(&SurfTokenKind::LParen)?;
            let mut params = Vec::new();
            while self.peek().kind != SurfTokenKind::RParen {
                let is_comptime = if self.peek().kind == SurfTokenKind::Comptime {
                    self.advance();
                    true
                } else {
                    false
                };
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
                        "Expected ':' and type annotation for trait method parameter '{pname}' at {}:{}",
                        self.peek().line,
                        self.peek().col
                    ));
                };
                params.push(Param {
                    is_comptime,
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
            if matches!(&self.peek().kind, SurfTokenKind::Ident(s) if s == "impl") {
                methods.extend(self.parse_inline_impl(m_vis)?);
                continue;
            }
            if self.peek().kind != SurfTokenKind::Fn {
                return Err(format!(
                    "Expected 'fn' inside 'extern opaque' or opaque newtype method block, found {:?} at {}:{} (use 'opaque Name {{ ... }}' for a sized encapsulated type with fields or lifecycle hooks)",
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

    /// Parses `impl [(comptime T: Bound, ...)] Tr for Type { fn ... }` at module level.
    fn parse_module_impl(&mut self) -> Result<ImplDecl, String> {
        self.advance(); // consume 'impl'
        let mut comptime_params = Vec::new();
        if self.peek().kind == SurfTokenKind::LParen {
            self.advance();
            while self.peek().kind != SurfTokenKind::RParen {
                if self.peek().kind != SurfTokenKind::Comptime {
                    return Err(
                        "Generic 'impl(...)' parameters must be 'comptime' type parameters (e.g. 'impl(comptime T: Hash) Hash for Pair(T)')"
                            .to_string(),
                    );
                }
                self.advance();
                let name = self.expect_ident()?;
                self.expect(&SurfTokenKind::Colon)?;
                let ty = self.parse_type_expr()?;
                comptime_params.push(Param {
                    is_comptime: true,
                    is_mut: false,
                    name,
                    ty,
                });
                if self.peek().kind == SurfTokenKind::Comma {
                    self.advance();
                } else {
                    break;
                }
            }
            self.expect(&SurfTokenKind::RParen)?;
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
            if self.peek().kind != SurfTokenKind::Fn {
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

    fn is_composite_body_ahead(&self) -> bool {
        if self.peek().kind != SurfTokenKind::LBrace {
            return false;
        }
        match &self.peek_n(1).kind {
            SurfTokenKind::RBrace
            | SurfTokenKind::Pub
            | SurfTokenKind::Const
            | SurfTokenKind::Comptime
            | SurfTokenKind::DefaultKw
            | SurfTokenKind::CloneKw
            | SurfTokenKind::DropKw => true,
            SurfTokenKind::Fn => matches!(self.peek_n(2).kind, SurfTokenKind::Ident(_)),
            SurfTokenKind::Ident(s) if s == "export" || s == "static" => true,
            SurfTokenKind::Ident(s)
                if s == "format" && self.peek_n(2).kind == SurfTokenKind::LParen =>
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
            SurfTokenKind::TypeKw => {
                self.advance();
                Ok(TypeExpr::MetaType)
            }
            SurfTokenKind::CloneKw => {
                self.advance();
                Ok(TypeExpr::Constraint(TypeConstraint::Clone))
            }
            SurfTokenKind::DefaultKw => {
                self.advance();
                Ok(TypeExpr::Constraint(TypeConstraint::Default))
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
                let mutable = match self.peek().kind {
                    SurfTokenKind::Mut => {
                        self.advance();
                        true
                    }
                    SurfTokenKind::Const => {
                        self.advance();
                        false
                    }
                    _ => false,
                };
                let inner = self.parse_type_expr()?;
                Ok(TypeExpr::Ptr {
                    mutable,
                    inner: Box::new(inner),
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
                    && matches!(&self.peek_n(2).kind, SurfTokenKind::Ident(s) if is_positional_param(s))
                {
                    self.parse_borrows_clause()?
                } else {
                    None
                };
                Ok(TypeExpr::FnPtr {
                    params,
                    ret: Box::new(ret),
                    borrows,
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
                    return Ok(TypeExpr::Constraint(TypeConstraint::Record));
                }
                self.parse_record_body(false)
            }
            SurfTokenKind::Linear => {
                self.advance();
                if self.peek().kind == SurfTokenKind::Sync {
                    return Err(
                        "Declaring a 'sync' opaque type asserts thread-safe synchronization and requires 'opaque(linear, unsafe sync)'"
                            .to_string(),
                    );
                } else if matches!(&self.peek().kind, SurfTokenKind::Ident(s) if s == "opaque") {
                    self.advance();
                    self.parse_struct_body(false, StructMods::new(StructOwnership::Linear, false))
                } else {
                    Ok(TypeExpr::Constraint(TypeConstraint::Linear))
                }
            }
            SurfTokenKind::Unsafe => {
                self.advance();
                let mut ownership = StructOwnership::Affine;
                if self.peek().kind == SurfTokenKind::Linear {
                    self.advance();
                    ownership = StructOwnership::Linear;
                }
                self.expect(&SurfTokenKind::Sync)?;
                if self.peek().kind == SurfTokenKind::Linear {
                    self.advance();
                    ownership = StructOwnership::Linear;
                }
                if matches!(&self.peek().kind, SurfTokenKind::Ident(s) if s == "opaque") {
                    self.advance();
                } else {
                    return Err(
                        "Expected 'opaque' after 'unsafe sync' (prefer 'opaque(unsafe sync)')"
                            .to_string(),
                    );
                }
                self.parse_struct_body(false, StructMods::new(ownership, true))
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
                while self.peek().kind == SurfTokenKind::ColonColon {
                    self.advance();
                    path.push(self.expect_ident()?);
                }
                if path.len() == 1 && path[0] == "packed" {
                    if self.peek().kind == SurfTokenKind::Struct {
                        self.advance();
                        return self.parse_record_body(true);
                    } else if matches!(&self.peek().kind, SurfTokenKind::Ident(s) if s == "opaque")
                    {
                        self.advance();
                        let mods = self.parse_struct_modifiers()?;
                        return self.parse_struct_body(true, mods);
                    }
                }
                if path.len() == 1 && path[0] == "opaque" {
                    if self.peek().kind == SurfTokenKind::LParen || self.is_composite_body_ahead() {
                        let mods = self.parse_struct_modifiers()?;
                        return self.parse_struct_body(false, mods);
                    } else if self.is_explicit_type_start()
                        || matches!(self.peek().kind, SurfTokenKind::Ident(_))
                    {
                        let bound = self.parse_type_expr()?;
                        return Ok(TypeExpr::OpaqueTrait(Box::new(bound)));
                    } else {
                        return Ok(TypeExpr::Opaque);
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
                if path.len() == 1 && self.peek().kind == SurfTokenKind::LBrace {
                    match path[0].as_str() {
                        "enum" => return self.parse_enum_body(None),
                        "union" => return self.parse_union_body(),
                        "overlay" => return self.parse_overlay_body(),
                        "error" => return self.parse_error_body(),
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
                    && path[0] == "error"
                    && self.peek().kind == SurfTokenKind::LParen
                {
                    return Err(
                        "Explicit backing integer types ('error(...)') are forbidden on 'error' declarations; 'error' is a unified sum type"
                            .to_string(),
                    );
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
                if self.peek().kind == SurfTokenKind::LBracket {
                    self.advance();
                    let index = self.parse_expr_or_type()?;
                    self.expect(&SurfTokenKind::RBracket)?;
                    return Ok(TypeExpr::TypeIndex {
                        path,
                        index: Box::new(index),
                    });
                }
                if self.peek().kind == SurfTokenKind::LParen {
                    self.advance();
                    let mut args = Vec::new();
                    while self.peek().kind != SurfTokenKind::RParen {
                        args.push(self.parse_expr_or_type()?);
                        if self.peek().kind == SurfTokenKind::Comma {
                            self.advance();
                        } else {
                            break;
                        }
                    }
                    self.expect(&SurfTokenKind::RParen)?;
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
                SurfTokenKind::Sync | SurfTokenKind::Linear
            ))
            || (self.peek().kind == SurfTokenKind::Simd
                && self.peek_n(1).kind == SurfTokenKind::LBracket)
            || (matches!(&self.peek().kind, SurfTokenKind::Ident(s) if s == "map")
                && self.peek_n(1).kind == SurfTokenKind::LBracket)
            || (self.peek().kind == SurfTokenKind::Amp
                && ((self.peek_n(1).kind == SurfTokenKind::LBracket
                    && self.is_slice_type_ahead(1))
                    || self.peek_n(1).kind == SurfTokenKind::Rel
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
                || (matches!(&self.peek().kind, SurfTokenKind::Ident(s) if s == "enum")
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
            Expr::TypeVal(te) => Some(te.clone()),
            Expr::Index { base, index } => {
                if let Expr::Path(path) = base.as_ref() {
                    Some(TypeExpr::TypeIndex {
                        path: path.clone(),
                        index: index.clone(),
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
                    TypeExpr::Record { .. } | TypeExpr::Struct { .. } | TypeExpr::Overlay(_)
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
