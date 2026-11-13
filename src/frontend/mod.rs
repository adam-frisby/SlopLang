mod expr;
mod lexer;

pub use lexer::{SurfToken, SurfTokenKind, SurfaceLexer};

use crate::ast::{
    At,
    BindMode, Block, BorrowContractItem, CIntKind, CloneHookDecl, ConstDecl, DropHookDecl, Expr,
    ExternFuncDecl, FieldDecl, FmtSegment, ForIter, FuncDecl, ImplDecl, ImportDecl, ImportTargets,
    Item, MatchPat, ModuleAst, OpaqueBody, OpaqueOwnership, Param, PtrKind, SelectArm, SelectOp,
    StaticDecl, Stmt, ThreadDecl, AssocItem, TraitKind, TraitMethodDecl, TypeConstraint, TypeExpr,
    Visibility, WherePredicate,
};
use crate::ir::{BinOp, Pos, UnOp};

/// Whether `@name` is a type-level intrinsic (`@Int`, `@Struct`, `@type_of`, ...).
pub(super) fn is_type_intrinsic(name: &str) -> bool {
    matches!(
        name,
        "Int"
            | "backing_type"
            | "type_of"
            | "Struct"
            | "PackedStruct"
            | "Tuple"
            | "Enum"
            | "Union"
            | "Error"
    )
}

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
    /// The source, line by line, for what an `@assert` quotes of its condition.
    lines: Vec<Vec<char>>,
}

impl SurfaceParser {
    /// The source text from `from` up to `to`, on one line.
    fn source_between(&self, from: Pos, to: Pos) -> String {
        let mut text = String::new();
        for line in from.line..=to.line {
            let Some(chars) = self.lines.get(line as usize - 1) else { break };
            let start = if line == from.line { from.col as usize - 1 } else { 0 };
            let end = if line == to.line { (to.col as usize - 1).min(chars.len()) } else { chars.len() };
            if start < end {
                text.extend(&chars[start..end]);
            }
            text.push(' ');
        }
        text.split_whitespace().collect::<Vec<_>>().join(" ")
    }

    pub fn parse_module(src: &str) -> Result<ModuleAst, String> {
        let tokens = SurfaceLexer::new(src).tokenize()?;
        let mut parser = Self {
            tokens,
            pos: 0,
            current_type_name: None,
            cond_start: None,
            extra_items: Vec::new(),
            pending_where: Vec::new(),
            lines: src.lines().map(|l| l.chars().collect()).collect(),
        };
        // An error that does not say where it is is where the parser stopped.
        parser.parse_module_inner().map_err(|e| {
            if e.contains("(line ") {
                e
            } else {
                format!("{e} ({})", parser.src_pos())
            }
        })
    }

    fn peek(&self) -> &SurfToken {
        &self.tokens[self.pos.min(self.tokens.len() - 1)]
    }

    /// Where the next token starts.
    fn src_pos(&self) -> Pos {
        let t = self.peek();
        Pos {
            line: t.line as u32,
            col: t.col as u32,
        }
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
                "Expected {}, found {} (line {}, column {})",
                expected.describe(), tok.kind.describe(), tok.line, tok.col
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
                "Expected identifier, found {} (line {}, column {})",
                tok.kind.describe(), tok.line, tok.col
            )),
        }
    }

    fn parse_visibility(&mut self) -> Result<Visibility, String> {
        if self.peek().kind == SurfTokenKind::Pub {
            self.advance();
            if matches!(&self.peek().kind, SurfTokenKind::Ident(s) if s == "export") {
                let tok = self.peek();
                Err(format!(
                    "Write 'export', not 'pub export' (an export is already public) (line {}, column {})",
                    tok.line, tok.col
                ))
            } else if self.peek().kind == SurfTokenKind::LParen {
                self.advance();
                let tok = self.advance();
                match tok.kind {
                    SurfTokenKind::Ident(s) if s == "mod" => {}
                    SurfTokenKind::Ident(s) if s == "pkg" => {
                        return Err(format!(
                            "'pub(pkg)' was removed: the compiler has no packages yet, so it meant 'pub'; use 'pub', or 'pub(mod)' for a method visible to its module (line {}, column {})",
                            tok.line, tok.col
                        ));
                    }
                    other => {
                        return Err(format!(
                            "Expected 'mod' in 'pub(...)', found {other:?} (line {}, column {})",
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
                        "'pub(mod)' applies only to methods ('pub(mod) fn ...' inside a type's block) (line {}, column {})",
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
                SurfTokenKind::Ident(s) if s == "thread_local" => {
                    let tok = self.peek().clone();
                    self.advance();
                    let mut decl = self.parse_static_decl(vis)?;
                    if !decl.mutable {
                        return Err(format!(
                            "'thread_local' needs 'static mut': an immutable static is already the same in every thread (line {}, column {})",
                            tok.line, tok.col
                        ));
                    }
                    decl.thread_local = true;
                    items.push(Item::Static(decl));
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
                SurfTokenKind::Struct => {
                    self.advance();
                    if self.peek().kind == SurfTokenKind::LParen {
                        return Err(
                            "Ownership and synchronization modifiers ('struct(...)') are forbidden on transparent 'struct' types; use 'opaque(...)' for encapsulated types with custom ownership or synchronization"
                                .to_string(),
                        );
                    }
                    let name = self.expect_ident()?;
                    let generic = self.parse_generic_header()?;
                    let prev_type_name = self.current_type_name.replace(name.clone());
                    let ty = self.parse_struct_body(false)?;
                    self.current_type_name = prev_type_name;
                    items.push(Self::type_decl(vis, name, generic, ty)?);
                }
                SurfTokenKind::Ident(s) if s == "packed" => {
                    self.advance();
                    if self.peek().kind == SurfTokenKind::Struct {
                        self.advance();
                        let name = self.expect_ident()?;
                        let generic = self.parse_generic_header()?;
                        let ty = self.parse_struct_body(true)?;
                        items.push(Self::type_decl(vis, name, generic, ty)?);
                    } else if matches!(&self.peek().kind, SurfTokenKind::Ident(s2) if s2 == "opaque")
                    {
                        self.advance();
                        let mods = self.parse_opaque_modifiers()?;
                        let name = self.expect_ident()?;
                        let generic = self.parse_generic_header()?;
                        let ty = self.parse_opaque_body(true, mods)?;
                        items.push(Self::type_decl(vis, name, generic, ty)?);
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
                    let generic = self.parse_generic_header()?;
                    let ty = self.parse_opaque_body(
                        false,
                        OpaqueMods::new(OpaqueOwnership::Linear, false),
                    )?;
                    items.push(Self::type_decl(vis, name, generic, ty)?);
                }
                SurfTokenKind::Unsafe
                    if matches!(&self.peek_n(1).kind, SurfTokenKind::Ident(s) if s == "impl") =>
                {
                    if vis != Visibility::Private {
                        return Err("'impl' blocks take no visibility modifier".to_string());
                    }
                    self.advance();
                    let mut decl = self.parse_module_impl()?;
                    decl.is_unsafe = true;
                    items.push(Item::Impl(decl));
                }
                SurfTokenKind::Unsafe
                    if matches!(&self.peek_n(1).kind, SurfTokenKind::Ident(s) if s == "trait") =>
                {
                    self.advance();
                    self.advance();
                    let name = self.expect_ident()?;
                    let generic = self.parse_generic_header()?;
                    let TypeExpr::Trait(methods, _, assoc) = self.parse_trait_body()? else {
                        unreachable!("a trait body is a trait");
                    };
                    let ty = TypeExpr::Trait(methods, TraitKind::Unsafe, assoc);
                    items.push(Self::type_decl(vis, name, generic, ty)?);
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
                    let generic = self.parse_generic_header()?;
                    let ty = self.parse_opaque_body(false, OpaqueMods::new(ownership, true))?;
                    items.push(Self::type_decl(vis, name, generic, ty)?);
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
                    let generic = self.parse_generic_header()?;
                    let ty = self.parse_union_body(backing)?;
                    items.push(Self::type_decl(vis, name, generic, ty)?);
                }
                SurfTokenKind::Ident(s) if s == "overlay" => {
                    self.advance();
                    let name = self.expect_ident()?;
                    let generic = self.parse_generic_header()?;
                    let ty = self.parse_overlay_body()?;
                    items.push(Self::type_decl(vis, name, generic, ty)?);
                }
                SurfTokenKind::Ident(s) if s == "error" => {
                    self.advance();
                    let backing = self.parse_error_header()?;
                    let name = self.expect_ident()?;
                    let generic = self.parse_generic_header()?;
                    if self.peek().kind == SurfTokenKind::Eq {
                        self.advance();
                    }
                    let ty = self.parse_error_body(backing)?;
                    if self.peek().kind == SurfTokenKind::Semi {
                        self.advance();
                    }
                    items.push(Self::type_decl(vis, name, generic, ty)?);
                }
                SurfTokenKind::Ident(s) if s == "errorcode" => {
                    return Err(
                        "The 'errorcode' keyword has been unified into 'error'; write 'error Name { ... }' or 'export error Name { ... }' instead"
                            .to_string(),
                    );
                }
                SurfTokenKind::Ident(s)
                    if s == "test" && matches!(self.peek_n(1).kind, SurfTokenKind::Str(_)) =>
                {
                    if vis != Visibility::Private {
                        return Err("A 'test' block takes no visibility modifier".to_string());
                    }
                    self.advance();
                    let SurfTokenKind::Str(name) = self.advance().kind else {
                        unreachable!("a string follows 'test'");
                    };
                    let body = self.parse_block()?;
                    items.push(Item::Test { name, body });
                }
                SurfTokenKind::Ident(s) if s == "trait" => {
                    self.advance();
                    let structural = self.peek().kind == SurfTokenKind::LParen;
                    if structural {
                        self.advance();
                        match &self.peek().kind {
                            SurfTokenKind::Ident(m) if m == "structural" => self.advance(),
                            other => {
                                return Err(format!(
                                    "Expected 'structural' in 'trait(...)', found {other:?}"
                                ));
                            }
                        };
                        self.expect(&SurfTokenKind::RParen)?;
                    }
                    let name = self.expect_ident()?;
                    let generic = self.parse_generic_header()?;
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
                        match self.parse_trait_body()? {
                            TypeExpr::Trait(methods, _, assoc) if structural => {
                                if let Some(m) = methods.iter().find(|m| m.default_body.is_some()) {
                                    return Err(format!(
                                        "Method '{}' of 'trait(structural) {name}' has a body, but a structural trait is met by the type's own methods, and has no impl for a default to fill",
                                        m.name
                                    ));
                                }
                                TypeExpr::Trait(methods, TraitKind::Structural, assoc)
                            }
                            t => t,
                        }
                    };
                    if structural && !matches!(ty, TypeExpr::Trait(..)) {
                        return Err(format!(
                            "'trait(structural) {name}' declares a trait: write its methods in braces"
                        ));
                    }
                    items.push(Self::type_decl(vis, name, generic, ty)?);
                }
                SurfTokenKind::Ident(s) if s == "opaque" => {
                    self.advance();
                    let mods = self.parse_opaque_modifiers()?;
                    let name = self.expect_ident()?;
                    let generic = self.parse_generic_header()?;
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
                    items.push(Self::type_decl(vis, name, generic, ty)?);
                }
                SurfTokenKind::Ident(s)
                    if s == "alias"
                        && matches!(self.peek_n(1).kind, SurfTokenKind::Ident(_))
                        && matches!(self.peek_n(2).kind, SurfTokenKind::Eq | SurfTokenKind::LBracket) =>
                {
                    self.advance();
                    let name = self.expect_ident()?;
                    let generic = self.parse_generic_header()?;
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
                    if let Some(params) = generic {
                        // A struct literal from a type function is a type of its own.
                        if matches!(ty, TypeExpr::Struct { .. } | TypeExpr::Overlay(_)) {
                            return Err(format!(
                                "A generic 'alias {name}[...]' cannot name an anonymous struct or overlay, as each instance would be a type of its own; declare 'struct {name}[...]' instead"
                            ));
                        }
                        // `alias Grid[T] = Vec[Vec[T]];` is the type function returning that type.
                        items.push(Self::type_decl(vis, name, Some(params), ty)?);
                    } else {
                        items.push(Item::TypeDecl {
                            vis,
                            name,
                            ty,
                            alias: true,
                        });
                    }
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
                        "Unexpected top-level token {:?} (line {}, column {})",
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

    /// The parameters of a generic type declaration (`struct Pair[T] { ... }`), if it has any.
    fn parse_generic_header(&mut self) -> Result<Option<Vec<Param>>, String> {
        if self.peek().kind != SurfTokenKind::LBracket {
            return Ok(None);
        }
        Ok(Some(self.parse_comptime_params()?))
    }

    /// A type declaration. With parameters it is the type function it stands for:
    /// `struct Pair[T] { ... }` is `fn Pair[T]() -> type { return struct { ... }; }`.
    fn type_decl(
        vis: Visibility,
        name: String,
        generic: Option<Vec<Param>>,
        ty: TypeExpr,
    ) -> Result<Item, String> {
        let Some(params) = generic else {
            return Ok(Item::TypeDecl {
                vis,
                name,
                ty,
                alias: false,
            });
        };
        if vis.is_export() {
            return Err(format!(
                "Generic type '{name}' cannot be exported: C sees only types with every parameter given"
            ));
        }
        Ok(Item::Func(FuncDecl {
            vis,
            name,
            params,
            ret_ty: TypeExpr::MetaType,
            borrows: None,
            where_clauses: Vec::new(),
            body: Block {
                stmts: vec![Stmt::Return(Some(Expr::TypeVal(ty)))],
                lines: Vec::new(),
            },
            is_unsafe: false,
            impl_of: None,
            is_unsafe_impl: false,
            discardable: false,
        }))
    }

    /// Parses a comptime parameter list `[T, N: usize, K: Hash + Eq]`. A bare name is a type
    /// parameter (`T: type`).
    fn parse_comptime_params(&mut self) -> Result<Vec<Param>, String> {
        self.expect(&SurfTokenKind::LBracket)?;
        let mut params = Vec::new();
        while self.peek().kind != SurfTokenKind::RBracket {
            if self.peek().kind == SurfTokenKind::Comptime {
                return Err(format!(
                    "Parameters in '[...]' are already comptime; remove 'comptime' (line {}, column {})",
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
                    maybe_linear(self.parse_type_expr()?)
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
    /// list `(...)`, written even when empty (`fn Vec[T]() -> type`).
    /// The comptime parameters come first in the result.
    fn parse_fn_params(&mut self, what: &str) -> Result<Vec<Param>, String> {
        let mut params = if self.peek().kind == SurfTokenKind::LBracket {
            self.parse_comptime_params()?
        } else {
            Vec::new()
        };
        if !params.is_empty() && self.peek().kind != SurfTokenKind::LParen {
            // `fn Pair[T]() -> type`, from before a type function wrote its `()`.
            let close = &self.tokens[self.pos.saturating_sub(1)];
            return Err(format!(
                "A function's parameter list is written even when it is empty: 'fn Name[...]() -> ...' (line {}, column {})",
                close.line,
                close.col + 1
            ));
        }
        self.expect(&SurfTokenKind::LParen)?;
        while self.peek().kind != SurfTokenKind::RParen {
            if self.peek().kind == SurfTokenKind::Comptime {
                return Err(format!(
                    "Comptime parameters are declared in brackets before the runtime parameters ('fn f[T: type, N: usize](x: T)'), not with 'comptime' (line {}, column {})",
                    self.peek().line,
                    self.peek().col
                ));
            }
            if self.peek().kind == SurfTokenKind::Amp {
                let amp_tok = self.advance();
                let ref_mut = if self.peek().kind == SurfTokenKind::Mut {
                    self.advance();
                    true
                } else {
                    false
                };
                let mut_kw = if ref_mut { "mut " } else { "" };
                let pname = self.expect_ident()?;
                if pname != "self" {
                    return Err(format!(
                        "Receiver shorthand '&{mut_kw}{pname}' is only valid for 'self'; write '{pname}: &{mut_kw}T' (line {}, column {})",
                        amp_tok.line, amp_tok.col
                    ));
                }
                if self.peek().kind == SurfTokenKind::Colon {
                    return Err(format!(
                        "Unexpected ':' after '&{mut_kw}self'; '&{mut_kw}self' says its type (line {}, column {})",
                        self.peek().line,
                        self.peek().col
                    ));
                }
                params.push(Param {
                    is_comptime: false,
                    default: None,
                    is_mut: false,
                    name: pname,
                    ty: TypeExpr::Ref {
                        mutable: ref_mut,
                        inner: Box::new(TypeExpr::SelfType),
                    },
                });
                if self.peek().kind == SurfTokenKind::Comma {
                    self.advance();
                } else {
                    break;
                }
                continue;
            }
            if self.peek().kind == SurfTokenKind::Move {
                let tok = self.peek().clone();
                let fix = match &self.peek_n(1).kind {
                    SurfTokenKind::Ident(s) if s == "self" => "write 'self', which takes the value".to_string(),
                    SurfTokenKind::Mut => "write 'mut self' or 'mut name: T'".to_string(),
                    _ => "remove 'move': a parameter that is not a reference takes its argument's value already".to_string(),
                };
                return Err(format!(
                    "'move' on a {what} changes nothing; {fix} (line {}, column {})",
                    tok.line, tok.col
                ));
            }
            let mut is_mut = if self.peek().kind == SurfTokenKind::Mut {
                self.advance();
                true
            } else {
                false
            };
            let name_tok = self.peek().clone();
            let pname = self.expect_ident()?;
            let pty = if self.peek().kind == SurfTokenKind::Colon {
                self.advance();
                if self.peek().kind == SurfTokenKind::Mut {
                    self.advance();
                    is_mut = true;
                }
                let at = self.peek().clone();
                let ty = self.parse_type_expr()?;
                if pname == "self" && matches!(ty, TypeExpr::SelfType) {
                    return Err(format!(
                        "Write 'self' for a receiver that takes the value, not 'self: Self' (line {}, column {})",
                        at.line, at.col
                    ));
                }
                if pname == "self"
                    && !is_mut
                    && let TypeExpr::Ref { mutable, inner } = &ty
                    && matches!(**inner, TypeExpr::SelfType)
                {
                    let short = if *mutable { "&mut self" } else { "&self" };
                    let long = if *mutable { "self: &mut Self" } else { "self: &Self" };
                    return Err(format!(
                        "Write '{short}', not '{long}' (line {}, column {})",
                        name_tok.line, name_tok.col
                    ));
                }
                ty
            } else if pname == "self" {
                TypeExpr::SelfType
            } else {
                return Err(format!(
                    "Expected ':' and type annotation for {what} '{pname}' (line {}, column {})",
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
        let (ret_ty, gen_item) = self.parse_ret_type()?;
        let discardable = matches!(&self.peek().kind, SurfTokenKind::Ident(s) if s == "discardable");
        if discardable {
            self.advance();
        }
        let borrows = self.parse_borrows_clause()?;
        let mut where_clauses = std::mem::take(&mut self.pending_where);
        where_clauses.extend(self.parse_where_clauses()?);
        let body = self.parse_block()?;
        let mut params = params;
        let (ret_ty, borrows, body) = match gen_item {
            Some(item) => {
                if borrows.is_some() {
                    return Err(format!(
                        "Generator '{name}' borrows what each of its parameters does, so it takes no 'borrows(...)' clause"
                    ));
                }
                // A hidden last comptime parameter makes `@try_gen(g(x))`'s instance, which
                // gives an `AllocError` for want of memory for its frame instead of trapping.
                params.push(Param {
                    is_comptime: true,
                    is_mut: false,
                    name: GEN_FALLIBLE.to_string(),
                    ty: TypeExpr::Bool,
                    default: Some(Expr::Bool(false)),
                });
                let (ret, borrows, body) = generator_parts(&params, item, Some(body));
                (ret, borrows, body.unwrap())
            }
            None => (ret_ty, borrows, body),
        };
        admit_linear_when_value_free(&mut params, &ret_ty);
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
            is_unsafe_impl: false,
            discardable,
        })
    }

    /// `-> T`, `-> gen T` (a generator of `T`s: the second part), or nothing (`void`).
    fn parse_ret_type(&mut self) -> Result<(TypeExpr, Option<TypeExpr>), String> {
        if self.peek().kind != SurfTokenKind::Arrow {
            return Ok((TypeExpr::Void, None));
        }
        self.advance();
        if matches!(&self.peek().kind, SurfTokenKind::Ident(s) if s == "gen")
            && !matches!(self.peek_n(1).kind, SurfTokenKind::LBrace | SurfTokenKind::LBracket | SurfTokenKind::ColonColon)
        {
            self.advance();
            return Ok((TypeExpr::Void, Some(self.parse_type_expr()?)));
        }
        Ok((self.parse_type_expr()?, None))
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
                let src_contents = self.peek().kind == SurfTokenKind::Star;
                if src_contents {
                    self.advance();
                }
                let src = self.expect_ident()?;
                items.push(BorrowContractItem::ParamFlow { dst: first, src, contents: src_contents });
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
            while !matches!(self.peek().kind, SurfTokenKind::LBrace | SurfTokenKind::Semi) {
                // A parameter, or an associated item of a trait's implementing type (`Self::Item`).
                let type_param = if self.peek().kind == SurfTokenKind::SelfType
                    && self.peek_n(1).kind == SurfTokenKind::ColonColon
                {
                    self.advance();
                    self.advance();
                    format!("Self::{}", self.expect_ident()?)
                } else {
                    self.expect_ident()?
                };
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
            } else if matches!(&self.peek().kind, SurfTokenKind::Ident(s) if s == "impl")
                || (self.peek().kind == SurfTokenKind::Unsafe
                    && matches!(&self.peek_n(1).kind, SurfTokenKind::Ident(s) if s == "impl"))
            {
                methods.extend(self.parse_inline_impl_methods(vis)?);
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
                        SurfTokenKind::Ident(t) if t == "zeroinit" => threads.unsafe_zeroinit = true,
                        _ => {
                            return Err(
                                "Expected 'send', 'sync', or 'zeroinit' after 'unsafe' in 'opaque(...)'".to_string()
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
                        "Unknown opaque modifier {:?} (line {}, column {}; expected 'copy', 'affine', 'linear', 'owns T', 'borrows T', 'unsafe send', 'unsafe sync', '!send', or '!sync')",
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
            thread_local: false,
            mutable,
            name,
            ty,
            init,
        })
    }

    fn parse_const_decl(&mut self, vis: Visibility) -> Result<ConstDecl, String> {
        if self.peek().kind == SurfTokenKind::Comptime {
            let tok = self.peek();
            return Err(format!(
                "Bare 'comptime NAME = ...;' has been removed; write 'const NAME = ...;' to declare a constant (line {}, column {})",
                tok.line, tok.col
            ));
        }
        self.advance(); // consume 'const'
        if self.peek().kind == SurfTokenKind::Mut {
            let tok = self.peek();
            return Err(format!(
                "Constants are always immutable; 'const mut' is invalid (line {}, column {})",
                tok.line, tok.col
            ));
        }
        let name = self.expect_ident()?;
        let ty = if self.peek().kind == SurfTokenKind::Colon {
            self.advance();
            Some(self.parse_type_expr()?)
        } else {
            None
        };
        self.expect(&SurfTokenKind::Eq)?;
        // A constant whose type is `type`, or a bound on one (`const Handle: copy = *own u8;`),
        // holds a type (`*own u8`, which reads as an expression).
        let is_type_bound = match &ty {
            Some(TypeExpr::MetaType | TypeExpr::TraitBounds(_)) => true,
            Some(TypeExpr::Constraint(c)) => *c != TypeConstraint::Module,
            _ => false,
        };
        let init = if is_type_bound
            && !matches!(self.peek().kind, SurfTokenKind::If | SurfTokenKind::Match)
        {
            Expr::TypeVal(self.parse_type_expr()?)
        } else {
            self.parse_expr_or_type()?
        };
        self.expect(&SurfTokenKind::Semi)?;
        Ok(ConstDecl {
            vis,
            name,
            ty,
            init,
            field: false,
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
                        if default_hook.replace((f.where_clauses, f.body)).is_some() {
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
                        if format_hook.replace((f.where_clauses, names.0, names.1, spec, f.body)).is_some() {
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
                    let (m, c) = self.parse_inline_impl(vis)?;
                    methods.extend(m);
                    consts.extend(c);
                }
                SurfTokenKind::Unsafe
                    if matches!(&self.peek_n(1).kind, SurfTokenKind::Ident(s) if s == "impl") =>
                {
                    let (m, c) = self.parse_inline_impl(vis)?;
                    methods.extend(m);
                    consts.extend(c);
                }
                // `const N: T = v;` in a type: a compile-time field, known by its name inside it.
                SurfTokenKind::Const | SurfTokenKind::Comptime => {
                    let mut c = self.parse_const_decl(vis)?;
                    c.field = true;
                    consts.push(c);
                }
                SurfTokenKind::LBracket => return Err(Self::bracket_field_error()),
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
                if matches!(self.peek().kind, SurfTokenKind::IntSuffix(_)) {
                    self.advance();
                }
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
                let tok = self.peek();
                return Err(format!(
                    "A union variant's payload goes in parentheses: write '{vname}(T)', not '{vname}: T' (line {}, column {})",
                    tok.line, tok.col
                ));
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
        if matches!(self.peek().kind, SurfTokenKind::IntSuffix(_)) {
            self.advance();
        }
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
                let tok = self.peek();
                return Err(format!(
                    "An error variant's payload goes in parentheses: write '{vname}(T)', not '{vname}: T' (line {}, column {})",
                    tok.line, tok.col
                ));
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
        let mut assoc = Vec::new();
        while self.peek().kind != SurfTokenKind::RBrace {
            if self.peek().kind == SurfTokenKind::LBracket {
                return Err(Self::bracket_field_error());
            }
            if self.peek().kind == SurfTokenKind::Comptime {
                let tok = self.peek();
                return Err(format!(
                    "Associated constants use 'const', not 'comptime': write 'const NAME: bound;' (line {}, column {})",
                    tok.line, tok.col
                ));
            }
            // `const Item: bound;`: an associated item each implementation gives.
            if self.peek().kind == SurfTokenKind::Const {
                self.advance();
                let name = self.expect_ident()?;
                self.expect(&SurfTokenKind::Colon)?;
                let bound = self.parse_type_expr()?;
                if self.peek().kind == SurfTokenKind::Eq {
                    return Err(format!(
                        "A trait asks for 'const {name}' and each implementation gives its value; remove '= ...'"
                    ));
                }
                self.expect(&SurfTokenKind::Semi)?;
                assoc.push(AssocItem { name, bound });
                continue;
            }
            if self.parse_visibility()? == Visibility::PubMod {
                return Err(
                    "Trait methods take no 'pub(mod)': they are as visible as the trait".to_string()
                );
            }
            let is_unsafe = self.parse_unsafe_fn_prefix();
            self.expect(&SurfTokenKind::Fn)?;
            let name = self.expect_ident()?;
            let params = self.parse_fn_params("trait method parameter")?;
            let (ret_ty, gen_item) = self.parse_ret_type()?;
            let borrows = self.parse_borrows_clause()?;
            let where_clauses = self.parse_where_clauses()?;
            // A body is what an implementation that leaves the method out does.
            let default_body = if self.peek().kind == SurfTokenKind::LBrace {
                Some(self.parse_block()?)
            } else {
                self.expect(&SurfTokenKind::Semi)?;
                None
            };
            let (ret_ty, borrows, default_body) = match gen_item {
                Some(item) => {
                    if borrows.is_some() {
                        return Err(format!(
                            "Generator '{name}' borrows what each of its parameters does, so it takes no 'borrows(...)' clause"
                        ));
                    }
                    generator_parts(&params, item, default_body)
                }
                None => (ret_ty, borrows, default_body),
            };
            methods.push(TraitMethodDecl {
                name,
                params,
                ret_ty,
                borrows,
                is_unsafe,
                default_body,
                where_clauses,
            });
        }
        self.expect(&SurfTokenKind::RBrace)?;
        Ok(TypeExpr::Trait(methods, TraitKind::Nominal, assoc))
    }

    /// A bracketed member (`[Name: T = value]`), which compile-time fields used to be.
    fn bracket_field_error() -> String {
        "A compile-time field is a constant: write 'const Name: T = value;' (or, in a trait, 'const Name: bound;')"
            .to_string()
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
                methods.extend(self.parse_inline_impl_methods(m_vis)?);
                continue;
            }
            if !self.fn_ahead() {
                return Err(format!(
                    "Expected 'fn' inside 'extern opaque' or distinct type method block, found {} (line {}, column {}; use 'opaque Name {{ ... }}' for a sized encapsulated type with fields or lifecycle hooks)",
                    self.peek().kind.describe(),
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

    /// `impl Tr { ... }` in a type's body: its methods, and the associated items it gives, which
    /// are the type's own compile-time fields.
    fn parse_inline_impl(&mut self, vis: Visibility) -> Result<(Vec<FuncDecl>, Vec<ConstDecl>), String> {
        let is_unsafe = self.peek().kind == SurfTokenKind::Unsafe;
        if is_unsafe {
            self.advance();
        }
        let (mut methods, consts) = self.parse_inline_impl_after(vis)?;
        for m in &mut methods {
            m.is_unsafe_impl = is_unsafe;
        }
        Ok((methods, consts))
    }

    /// `parse_inline_impl` in a body that holds no compile-time fields.
    fn parse_inline_impl_methods(&mut self, vis: Visibility) -> Result<Vec<FuncDecl>, String> {
        let (methods, consts) = self.parse_inline_impl(vis)?;
        if let Some(c) = consts.first() {
            return Err(format!(
                "'const {}' goes in an 'opaque' body or a module-level 'impl', not in this type's body",
                c.name
            ));
        }
        Ok(methods)
    }

    fn parse_inline_impl_after(&mut self, vis: Visibility) -> Result<(Vec<FuncDecl>, Vec<ConstDecl>), String> {
        if vis != Visibility::Private {
            return Err(
                "'impl' blocks take no visibility modifier; trait methods are as visible as the trait and type"
                    .to_string(),
            );
        }
        self.advance(); // consume 'impl'
        let trait_expr = self.parse_type_expr()?;
        let (mut methods, consts) = self.parse_impl_methods(&trait_expr)?;
        // An impl with no methods (of a marker trait) is kept by a stand-in member.
        if methods.is_empty() {
            methods.push(FuncDecl::impl_marker(trait_expr));
        }
        Ok((methods, consts))
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
                "Expected 'for' in module-level 'impl' (line {}, column {}; write 'impl Trait for Type {{ ... }}', or put 'impl Trait {{ ... }}' inside the type's own body)",
                self.peek().line,
                self.peek().col
            ));
        }
        self.advance(); // consume 'for'
        let for_ty = self.parse_type_expr()?;
        let (methods, consts) = self.parse_impl_methods(&trait_expr)?;
        Ok(ImplDecl {
            is_unsafe: false,
            comptime_params,
            trait_expr,
            for_ty,
            methods,
            consts,
        })
    }

    fn parse_impl_methods(&mut self, trait_expr: &TypeExpr) -> Result<(Vec<FuncDecl>, Vec<ConstDecl>), String> {
        self.expect(&SurfTokenKind::LBrace)?;
        let mut methods = Vec::new();
        let mut consts = Vec::new();
        while self.peek().kind != SurfTokenKind::RBrace {
            if self.peek().kind == SurfTokenKind::LBracket {
                return Err(Self::bracket_field_error());
            }
            if self.peek().kind == SurfTokenKind::Comptime {
                let tok = self.peek();
                return Err(format!(
                    "Associated constants use 'const', not 'comptime': write 'const NAME = ...;' (line {}, column {})",
                    tok.line, tok.col
                ));
            }
            // What an impl gives its trait (`const Item: copy = u32;`) is as visible as the trait.
            if self.peek().kind == SurfTokenKind::Const {
                let mut c = self.parse_const_decl(Visibility::Pub)?;
                c.field = true;
                consts.push(c);
                continue;
            }
            if self.parse_visibility()? != Visibility::Private {
                return Err(
                    "Methods in an 'impl' block take their visibility from the trait; remove the visibility modifier"
                        .to_string(),
                );
            }
            if !self.fn_ahead() {
                return Err(format!(
                    "Expected 'fn' inside 'impl' block, found {} (line {}, column {})",
                    self.peek().kind.describe(),
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
        Ok((methods, consts))
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
            SurfTokenKind::Intrinsic(ref intr) if is_type_intrinsic(intr) => {
                let intr = intr.clone();
                match intr.as_str() {
                    "Int" => {
                        self.advance();
                        self.expect(&SurfTokenKind::LParen)?;
                        let signed = if self.peek().kind == SurfTokenKind::Dot {
                            self.advance();
                            let tag = match &self.peek().kind {
                                SurfTokenKind::Ident(s) => s.clone(),
                                _ => {
                                    return Err(format!(
                                        "Expected '.signed' or '.unsigned' in '@Int(...)' (line {}, column {})",
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
                    "backing_type" => {
                        self.advance();
                        self.expect(&SurfTokenKind::LParen)?;
                        let inner = self.parse_type_expr()?;
                        self.expect(&SurfTokenKind::RParen)?;
                        Ok(TypeExpr::BackingType(Box::new(inner)))
                    }
                    "type_of" => {
                        self.advance();
                        self.expect(&SurfTokenKind::LParen)?;
                        let inner = self.parse_expr()?;
                        self.expect(&SurfTokenKind::RParen)?;
                        Ok(TypeExpr::TypeOf(Box::new(inner)))
                    }
                    "Struct" | "PackedStruct" => {
                        let is_packed = intr == "PackedStruct";
                        self.advance();
                        self.expect(&SurfTokenKind::LParen)?;
                        let fields = self.parse_expr()?;
                        self.expect(&SurfTokenKind::RParen)?;
                        Ok(TypeExpr::SynthesizedStruct {
                            is_packed,
                            fields: Box::new(fields),
                        })
                    }
                    "Tuple" => {
                        self.advance();
                        self.expect(&SurfTokenKind::LParen)?;
                        let elems = self.parse_expr()?;
                        self.expect(&SurfTokenKind::RParen)?;
                        Ok(TypeExpr::SynthesizedTuple(Box::new(elems)))
                    }
                    "Enum" => {
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
                    "Union" => {
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
                    "Error" => {
                        self.advance();
                        self.expect(&SurfTokenKind::LParen)?;
                        let variants = self.parse_expr()?;
                        self.expect(&SurfTokenKind::RParen)?;
                        Ok(TypeExpr::SynthesizedError(Box::new(variants)))
                    }
                    _ => unreachable!(),
                }
            }
            SurfTokenKind::TypeKw => {
                self.advance();
                Ok(TypeExpr::MetaType)
            }
            SurfTokenKind::SelfType => {
                self.advance();
                // `Self::Handle`: an associated type of `Self`.
                if self.peek().kind == SurfTokenKind::ColonColon {
                    let mut path = vec!["Self".to_string()];
                    while self.peek().kind == SurfTokenKind::ColonColon {
                        self.advance();
                        path.push(self.expect_ident()?);
                    }
                    return Ok(TypeExpr::Named(path));
                }
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
                    let mut_kw = if mutable { "mut " } else { "" };
                    return Err(format!(
                        "Slice types are written '&{mut_kw}slice[T]' and array references '&{mut_kw}array[T; N]', not '&{mut_kw}[...]' (line {}, column {})",
                        self.peek().line,
                        self.peek().col
                    ));
                }
                if matches!(&self.peek().kind, SurfTokenKind::Ident(s) if s == "slice")
                    && self.peek_n(1).kind == SurfTokenKind::LBracket
                {
                    self.advance();
                    self.advance();
                    let elem = self.parse_type_expr()?;
                    self.expect(&SurfTokenKind::RBracket)?;
                    return Ok(TypeExpr::Slice {
                        mutable,
                        elem: Box::new(elem),
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
                return Err(format!(
                    "Array types are written 'array[T; N]', not '[T; N]' (line {}, column {})",
                    self.peek().line,
                    self.peek().col
                ));
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
                    && path != ["callable"]
                {
                    // `F()`: a type function without parameters.
                    self.advance();
                    self.advance();
                    return Ok(TypeExpr::TypeCall {
                        path,
                        args: Vec::new(),
                    });
                }
                // `callable(T) -> R` is a bound with a signature, not a call.
                if self.peek().kind == SurfTokenKind::LParen && path != ["callable"] {
                    return Err(format!(
                        "Type function arguments go in brackets: write '{}[...]' (line {}, column {})",
                        path.join("::"),
                        self.peek().line,
                        self.peek().col
                    ));
                }
                if self.peek().kind == SurfTokenKind::LBracket {
                    if path.len() == 1 && path[0] == "array" {
                        self.advance();
                        let elem = self.parse_type_expr()?;
                        self.expect(&SurfTokenKind::Semi)?;
                        let len = self.parse_expr()?;
                        self.expect(&SurfTokenKind::RBracket)?;
                        return Ok(TypeExpr::Array {
                            elem: Box::new(elem),
                            len: Box::new(len),
                        });
                    }
                    if path.len() == 1 && path[0] == "slice" {
                        return Err(format!(
                            "Slice types require '&': write '&slice[T]' or '&mut slice[T]' (line {}, column {})",
                            self.peek().line,
                            self.peek().col
                        ));
                    }
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
                        "callable" if self.peek().kind == SurfTokenKind::LParen => {
                            self.advance();
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
                            Ok(TypeExpr::CallableSig { params, ret: Box::new(ret) })
                        }
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
                        "recursive" => Ok(TypeExpr::Constraint(TypeConstraint::Recursive)),
                        "unchecked" => Ok(TypeExpr::Constraint(TypeConstraint::Unchecked)),
                        "format" => Ok(TypeExpr::Constraint(TypeConstraint::Format)),
                        "copy" => Ok(TypeExpr::Constraint(TypeConstraint::Copy)),
                        "clone" => Ok(TypeExpr::Constraint(TypeConstraint::Clone)),
                        "try_clone" => Ok(TypeExpr::Constraint(TypeConstraint::TryClone)),
                        "default" => Ok(TypeExpr::Constraint(TypeConstraint::Default)),
                        "zeroinit" => Ok(TypeExpr::Constraint(TypeConstraint::ZeroInit)),
                        "affine" => Ok(TypeExpr::Constraint(TypeConstraint::Affine)),
                        _ => Ok(TypeExpr::Named(path)),
                    }
                } else {
                    Ok(TypeExpr::Named(path))
                }
            }
            _ => Err(format!(
                "Expected type expression, found {} (line {}, column {})",
                tok.kind.describe(), tok.line, tok.col
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
                | SurfTokenKind::TypeKw
                | SurfTokenKind::Tuple
                | SurfTokenKind::Struct
                | SurfTokenKind::Extern
                | SurfTokenKind::Linear
                | SurfTokenKind::Sync
                | SurfTokenKind::Question
        ) || matches!(&self.peek().kind, SurfTokenKind::Intrinsic(s) if is_type_intrinsic(s))
            || (self.peek().kind == SurfTokenKind::Unsafe
            && matches!(
                self.peek_n(1).kind,
                SurfTokenKind::Sync | SurfTokenKind::Linear | SurfTokenKind::Fn | SurfTokenKind::Extern
            ))
            || (self.peek().kind == SurfTokenKind::Simd
                && self.peek_n(1).kind == SurfTokenKind::LBracket)
            || (matches!(&self.peek().kind, SurfTokenKind::Ident(s) if s == "array")
                && self.peek_n(1).kind == SurfTokenKind::LBracket
                && self.has_top_level_semi_in_brackets(1))
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
                && ({
                    let at = if self.peek_n(1).kind == SurfTokenKind::Mut { 2 } else { 1 };
                    matches!(&self.peek_n(at).kind, SurfTokenKind::Ident(s) if s == "str")
                        || (matches!(&self.peek_n(at).kind, SurfTokenKind::Ident(s) if s == "slice")
                            && self.peek_n(at + 1).kind == SurfTokenKind::LBracket)
                        || (matches!(&self.peek_n(at).kind, SurfTokenKind::Ident(s) if s == "array")
                            && self.peek_n(at + 1).kind == SurfTokenKind::LBracket
                            && self.has_top_level_semi_in_brackets(at + 1))
                }))
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

    /// Whether the `[` at `bracket_offset` contains a top-level `;` (distinguishing `array[T; N]`
    /// from indexing `array[i]`).
    pub(super) fn has_top_level_semi_in_brackets(&self, bracket_offset: usize) -> bool {
        if self.peek_n(bracket_offset).kind != SurfTokenKind::LBracket {
            return false;
        }
        let mut depth = 0usize;
        let mut scan = bracket_offset + 1;
        loop {
            match &self.peek_n(scan).kind {
                SurfTokenKind::Eof => return false,
                SurfTokenKind::RBracket if depth == 0 => return false,
                SurfTokenKind::Semi if depth == 0 => return true,
                SurfTokenKind::LParen | SurfTokenKind::LBracket | SurfTokenKind::LBrace => depth += 1,
                SurfTokenKind::RParen | SurfTokenKind::RBracket | SurfTokenKind::RBrace => {
                    depth = depth.saturating_sub(1);
                }
                _ => {}
            }
            scan += 1;
        }
    }

    fn is_fn_type_ahead(&self) -> bool {
        if self.peek().kind != SurfTokenKind::Fn || self.peek_n(1).kind != SurfTokenKind::LParen {
            return false;
        }
        // Scan `( ... )` parameters:
        // - `mut ...` or `ident : ...` is unambiguously a lambda (`false`).
        // - Bare `ident` separated by `,` up to `)` (or empty `()`) could be either untyped lambda
        //   parameters or single-identifier parameter types (`fn(Point)`), decided by what follows `)`.
        // - Anything else (`i32`, `&T`, `*T`, `Foo::Bar`, `Vec[T]`, ...) cannot be a lambda (`true`).
        let mut k = 2;
        if self.peek_n(k).kind != SurfTokenKind::RParen {
            loop {
                if self.peek_n(k).kind == SurfTokenKind::Mut
                    || (matches!(self.peek_n(k).kind, SurfTokenKind::Ident(_))
                        && self.peek_n(k + 1).kind == SurfTokenKind::Colon)
                {
                    return false;
                }
                if !matches!(self.peek_n(k).kind, SurfTokenKind::Ident(_)) {
                    return true;
                }
                k += 1;
                if self.peek_n(k).kind == SurfTokenKind::Comma {
                    k += 1;
                    if self.peek_n(k).kind == SurfTokenKind::RParen {
                        break;
                    }
                } else if self.peek_n(k).kind == SurfTokenKind::RParen {
                    break;
                } else {
                    return true;
                }
            }
        }
        let after = k + 1;
        let brace_ok = self.empty_struct_lit_allowed();
        if self.peek_n(after).kind == SurfTokenKind::FatArrow
            || (brace_ok && self.peek_n(after).kind == SurfTokenKind::LBrace)
        {
            return false;
        }
        if self.peek_n(after).kind == SurfTokenKind::Arrow {
            // A comma inside `Vec[i32, A]` or `{ ... }` inside `tuple { i32, i32 }` does not end
            // the return type.
            let mut m = after + 1;
            let mut depth = 0;
            let mut composite_paren = false;
            let is_composite_kw = |kind: &SurfTokenKind| match kind {
                SurfTokenKind::Tuple | SurfTokenKind::Struct => true,
                SurfTokenKind::Ident(s) => matches!(
                    s.as_str(),
                    "enum" | "union" | "error" | "opaque" | "overlay" | "trait"
                ),
                _ => false,
            };
            loop {
                match &self.peek_n(m).kind {
                    SurfTokenKind::LParen => {
                        if depth == 0 && is_composite_kw(&self.peek_n(m.saturating_sub(1)).kind) {
                            composite_paren = true;
                        }
                        depth += 1;
                    }
                    SurfTokenKind::LBracket => depth += 1,
                    SurfTokenKind::RBracket if depth > 0 => depth -= 1,
                    SurfTokenKind::RParen if depth > 0 => {
                        depth -= 1;
                    }
                    SurfTokenKind::LBrace
                        if depth == 0
                            && (is_composite_kw(&self.peek_n(m.saturating_sub(1)).kind)
                                || (composite_paren
                                    && self.peek_n(m.saturating_sub(1)).kind
                                        == SurfTokenKind::RParen)) =>
                    {
                        composite_paren = false;
                        let mut bdepth = 1;
                        m += 1;
                        while bdepth > 0 && self.peek_n(m).kind != SurfTokenKind::Eof {
                            match self.peek_n(m).kind {
                                SurfTokenKind::LBrace => bdepth += 1,
                                SurfTokenKind::RBrace => bdepth -= 1,
                                _ => {}
                            }
                            m += 1;
                        }
                        continue;
                    }
                    SurfTokenKind::FatArrow
                    | SurfTokenKind::LBrace
                    | SurfTokenKind::Semi
                    | SurfTokenKind::Eof => break,
                    SurfTokenKind::Comma | SurfTokenKind::RParen | SurfTokenKind::RBracket
                        if depth == 0 =>
                    {
                        break;
                    }
                    _ => {}
                }
                m += 1;
            }
            if self.peek_n(m).kind == SurfTokenKind::FatArrow
                || (brace_ok && self.peek_n(m).kind == SurfTokenKind::LBrace)
            {
                return false;
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

    pub(super) fn parse_typed_array_or_simd_brace(&mut self, ty: TypeExpr) -> Result<Expr, String> {
        if matches!(ty, TypeExpr::Array { .. }) {
            let tok = self.peek();
            return Err(format!(
                "An array literal is written '[a, b]' or '[v; N]'; give its type where it goes ('let a: array[u8; 4] = [1, 2, 3, 4];') (line {}, column {})",
                tok.line, tok.col
            ));
        }
        self.expect(&SurfTokenKind::LBrace)?;
        if self.peek().kind == SurfTokenKind::RBrace {
            self.advance();
            return Ok(Expr::SimdLit {
                ty,
                elems: Vec::new(),
            });
        }
        let first = self.parse_expr()?;
        if self.peek().kind == SurfTokenKind::Semi {
            self.advance();
            let len = self.parse_expr()?;
            self.expect(&SurfTokenKind::RBrace)?;
            return Ok(Expr::ArrayRepeat {
                ty: Some(ty),
                elem: Box::new(first),
                len: Box::new(len),
            });
        }
        let mut elems = vec![first];
        if self.peek().kind == SurfTokenKind::Comma {
            self.advance();
            while self.peek().kind != SurfTokenKind::RBrace {
                elems.push(self.parse_expr()?);
                if self.peek().kind == SurfTokenKind::Comma {
                    self.advance();
                } else {
                    break;
                }
            }
        }
        self.expect(&SurfTokenKind::RBrace)?;
        Ok(Expr::SimdLit { ty, elems })
    }

    fn parse_expr_or_type(&mut self) -> Result<Expr, String> {
        if self.is_explicit_type_start() {
            let ty = self.parse_type_expr()?;
            if self.peek().kind == SurfTokenKind::LBrace {
                if matches!(ty, TypeExpr::Simd { .. } | TypeExpr::Array { .. }) {
                    return self.parse_typed_array_or_simd_brace(ty);
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

/// The constraint `?linear` or `?sized` would be with `bound` as what follows the `?`.
fn widened(bound: &TypeExpr) -> Option<TypeConstraint> {
    match bound {
        TypeExpr::Constraint(TypeConstraint::Linear) => Some(TypeConstraint::MaybeLinear),
        TypeExpr::Named(path) if path.len() == 1 && path[0] == "sized" => Some(TypeConstraint::MaybeSized),
        _ => None,
    }
}

/// A parameter's bound with `?linear` and `?sized`, which parse as optionals, as constraints.
fn maybe_linear(bound: TypeExpr) -> TypeExpr {
    match bound {
        TypeExpr::Optional(inner) if widened(&inner).is_some() => {
            TypeExpr::Constraint(widened(&inner).expect("checked"))
        }
        // `?linear + Foo` parses as an optional `linear + Foo`.
        TypeExpr::Optional(inner)
            if matches!(&*inner, TypeExpr::TraitBounds(b) if b.first().and_then(widened).is_some()) =>
        {
            let TypeExpr::TraitBounds(mut bounds) = *inner else { unreachable!() };
            bounds[0] = TypeExpr::Constraint(widened(&bounds[0]).expect("checked"));
            TypeExpr::TraitBounds(bounds.into_iter().map(maybe_linear).collect())
        }
        TypeExpr::TraitBounds(bounds) => TypeExpr::TraitBounds(bounds.into_iter().map(maybe_linear).collect()),
        other => other,
    }
}

/// A function's type parameter that its signature holds no value of (`[T](x: &T)`,
/// `[T: sync]()`) cannot be given a `T` to drop, so it takes linear types as if it said
/// `?linear`, and is checked as if given one. Only for bounds of properties that a linear type
/// may have (`send`, `sync`, `format`), as a named bound may be a value's type rather than a
/// trait.
fn admit_linear_when_value_free(params: &mut [Param], ret_ty: &TypeExpr) {
    // A type function's (`-> type`, `-> trait`) parameters go into what it makes.
    if *ret_ty == TypeExpr::MetaType {
        return;
    }
    let names: Vec<String> = params
        .iter()
        .filter(|p| p.is_comptime && p.default.is_none() && implicitly_widened(&p.ty))
        .map(|p| p.name.clone())
        .collect();
    for name in names {
        let held = params.iter().filter(|p| !p.is_comptime).any(|p| holds_by_value(&p.ty, &name))
            || holds_by_value(ret_ty, &name);
        if held {
            continue;
        }
        let p = params.iter_mut().find(|p| p.is_comptime && p.name == name).expect("named above");
        let maybe = TypeExpr::Constraint(TypeConstraint::MaybeLinear);
        p.ty = match std::mem::replace(&mut p.ty, TypeExpr::MetaType) {
            TypeExpr::MetaType => maybe,
            TypeExpr::TraitBounds(mut bounds) => {
                bounds.push(maybe);
                TypeExpr::TraitBounds(bounds)
            }
            other => TypeExpr::TraitBounds(vec![other, maybe]),
        };
    }
}

/// Whether a parameter bounded by `bound` would take a linear type if it said `?linear`.
fn implicitly_widened(bound: &TypeExpr) -> bool {
    use TypeConstraint as C;
    match bound {
        TypeExpr::MetaType => true,
        TypeExpr::Constraint(C::Send | C::Sync | C::Format | C::AnyType) => true,
        TypeExpr::TraitBounds(parts) => parts.iter().all(implicitly_widened),
        _ => false,
    }
}

/// Whether a value of type `ty` may hold a `name` by value: not only behind a reference or a
/// pointer that owns nothing. A `name` given to a generic type (`&Tree[T]`) counts too, behind a
/// pointer or not, as that type may not take what `name` may be. Shapes not looked into count
/// if they mention it.
fn holds_by_value(ty: &TypeExpr, name: &str) -> bool {
    mentions(ty, name, false)
}

fn mentions(ty: &TypeExpr, name: &str, behind: bool) -> bool {
    match ty {
        TypeExpr::Ref { inner, .. } | TypeExpr::Ptr { kind: PtrKind::Raw | PtrKind::View, inner, .. } => {
            mentions(inner, name, true)
        }
        TypeExpr::Slice { elem, .. } => mentions(elem, name, true),
        TypeExpr::Optional(inner) => mentions(inner, name, behind),
        TypeExpr::Tuple(parts) => parts.iter().any(|t| mentions(t, name, behind)),
        TypeExpr::Array { elem, .. } => mentions(elem, name, behind),
        TypeExpr::Named(path) => !behind && path.first().is_some_and(|p| p == name),
        other => format!("{other:?}").contains(&format!("\"{name}\"")),
    }
}

/// What a generator `fn f(params) -> gen T { body }` is: a function returning `Gen[T, B]`, where
/// `B` is the tuple of the parameters' types, borrowing what each parameter does, whose body
/// starts `body` in a frame of its own. `body` becomes a function literal taking `__gen_out`, the
/// slot each `yield` fills, then the parameters, and starting with the point the constructor
/// runs it to.
/// With no body (a trait's required method), only the signature.
fn generator_parts(
    params: &[Param],
    item: TypeExpr,
    body: Option<Block>,
) -> (TypeExpr, Option<Vec<BorrowContractItem>>, Option<Block>) {
    let runtime: Vec<&Param> = params.iter().filter(|p| !p.is_comptime).collect();
    let held = TypeExpr::Tuple(runtime.iter().map(|p| p.ty.clone()).collect());
    let ret_ty = if params.iter().any(|p| p.name == GEN_FALLIBLE) {
        TypeExpr::TypeCall {
            path: vec!["std".to_string(), "mem".to_string(), "GenStartResult".to_string()],
            args: vec![Expr::Path(vec![GEN_FALLIBLE.to_string()]), Expr::TypeVal(item.clone()), Expr::TypeVal(held)],
        }
    } else {
        TypeExpr::TypeCall {
            path: vec!["std".to_string(), "mem".to_string(), "Gen".to_string()],
            args: vec![Expr::TypeVal(item.clone()), Expr::TypeVal(held)],
        }
    };
    let borrows = runtime
        .iter()
        .map(|p| BorrowContractItem::Return { name: p.name.clone(), contents: false })
        .collect();
    let Some(body) = body else {
        return (ret_ty, Some(borrows), None);
    };
    let start = body.lines.first().cloned().unwrap_or_default();
    let mut lambda_params = vec![(
        false,
        GEN_OUT.to_string(),
        Some(TypeExpr::Ref { mutable: true, inner: Box::new(TypeExpr::Optional(Box::new(item))) }),
    )];
    lambda_params.extend(runtime.iter().map(|p| (p.is_mut, p.name.clone(), Some(p.ty.clone()))));
    let mut stmts = vec![Stmt::Yield(None)];
    stmts.extend(body.stmts);
    let mut lines = vec![start.clone()];
    lines.extend(body.lines);
    let lambda = Expr::Lambda {
        is_move: false,
        params: lambda_params,
        ret_ty: Some(TypeExpr::Void),
        body: Block { stmts, lines },
        has_tail: false,
    };
    let start_expr = Expr::GenStart {
        body: Box::new(lambda),
        args: runtime.iter().map(|p| Expr::Path(vec![p.name.clone()])).collect(),
    };
    let end = start.clone();
    (
        ret_ty,
        Some(borrows),
        Some(Block { stmts: vec![Stmt::Return(Some(start_expr))], lines: vec![start, end] }),
    )
}

/// The parameter of a generator's body that each `yield` fills.
pub const GEN_OUT: &str = "__gen_out";

/// A generator's hidden comptime parameter: whether its constructor gives `AllocError!Gen`
/// (`@try_gen`) rather than trapping for want of memory for the frame.
pub const GEN_FALLIBLE: &str = "__gen_fallible";
