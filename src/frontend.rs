use crate::ast::{
    Block, Expr, ExternFuncDecl, FieldDecl, FuncDecl, ImportDecl, ImportTargets, Item, ModuleAst,
    Param, Stmt, TypeConstraint, TypeExpr, Visibility,
};
use crate::ir::{BinOp, UnOp};

#[derive(Debug, Clone, PartialEq)]
pub enum SurfTokenKind {
    // Keywords
    Import,
    Pub,
    Pkg,
    Fn,
    Extern,
    Record,
    Struct,
    Tuple,
    TypeKw,
    Comptime,
    Let,
    Mut,
    Const,
    If,
    Else,
    While,
    Return,
    Unsafe,
    Move,
    As,
    In,
    OrElse,
    DefaultKw,
    CloneKw,
    DropKw,
    Void,
    Never,
    Bool,
    RuneKw,
    F32,
    F64,
    Isize,
    Usize,
    SelfType,
    True,
    False,
    Null,
    Simd,
    IntType { signed: bool, bits: u16 },

    // Intrinsics
    AtDefault,
    AtClone,
    AtDrop,
    AtTrap,

    // Identifiers & Literals
    Ident(String),
    Int(i128),
    Float(u64),
    RuneLit(char),
    Str(String),

    // Punctuation & Operators
    LParen,
    RParen,
    LBrace,
    RBrace,
    LBracket,
    RBracket,
    Comma,
    Semi,
    Colon,
    ColonColon,
    Dot,
    DotDot,
    DotDotEq,
    Arrow,
    Question,
    Eq,
    PlusEq,
    MinusEq,
    StarEq,
    Plus,
    PlusPercent,
    PlusPipe,
    Minus,
    MinusPercent,
    MinusPipe,
    Star,
    StarPercent,
    StarPipe,
    Slash,
    Percent,
    Amp,
    AmpAmp,
    Pipe,
    PipePipe,
    Caret,
    Bang,
    Shl,
    Shr,
    EqEq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
    Eof,
}

#[derive(Debug, Clone)]
pub struct SurfToken {
    pub kind: SurfTokenKind,
    pub line: usize,
    pub col: usize,
}

pub struct SurfaceLexer<'a> {
    input: &'a str,
    pos: usize,
    line: usize,
    col: usize,
}

impl<'a> SurfaceLexer<'a> {
    pub fn new(input: &'a str) -> Self {
        Self {
            input,
            pos: 0,
            line: 1,
            col: 1,
        }
    }

    fn peek_char(&self) -> Option<char> {
        self.input[self.pos..].chars().next()
    }

    fn peek_char_n(&self, n: usize) -> Option<char> {
        self.input[self.pos..].chars().nth(n)
    }

    fn advance(&mut self) -> Option<char> {
        let ch = self.peek_char()?;
        self.pos += ch.len_utf8();
        if ch == '\n' {
            self.line += 1;
            self.col = 1;
        } else {
            self.col += 1;
        }
        Some(ch)
    }

    fn skip_whitespace_and_comments(&mut self) {
        while let Some(ch) = self.peek_char() {
            if ch.is_whitespace() {
                self.advance();
            } else if ch == '/' && self.peek_char_n(1) == Some('/') {
                while let Some(c) = self.peek_char() {
                    self.advance();
                    if c == '\n' {
                        break;
                    }
                }
            } else {
                break;
            }
        }
    }

    pub fn tokenize(mut self) -> Result<Vec<SurfToken>, String> {
        let mut tokens = Vec::new();
        loop {
            self.skip_whitespace_and_comments();
            let line = self.line;
            let col = self.col;
            let Some(ch) = self.peek_char() else {
                tokens.push(SurfToken {
                    kind: SurfTokenKind::Eof,
                    line,
                    col,
                });
                break;
            };

            let kind = match ch {
                '(' => {
                    self.advance();
                    SurfTokenKind::LParen
                }
                ')' => {
                    self.advance();
                    SurfTokenKind::RParen
                }
                '{' => {
                    self.advance();
                    SurfTokenKind::LBrace
                }
                '}' => {
                    self.advance();
                    SurfTokenKind::RBrace
                }
                '[' => {
                    self.advance();
                    SurfTokenKind::LBracket
                }
                ']' => {
                    self.advance();
                    SurfTokenKind::RBracket
                }
                ',' => {
                    self.advance();
                    SurfTokenKind::Comma
                }
                ';' => {
                    self.advance();
                    SurfTokenKind::Semi
                }
                '?' => {
                    self.advance();
                    SurfTokenKind::Question
                }
                '^' => {
                    self.advance();
                    SurfTokenKind::Caret
                }
                ':' => {
                    self.advance();
                    if self.peek_char() == Some(':') {
                        self.advance();
                        SurfTokenKind::ColonColon
                    } else {
                        SurfTokenKind::Colon
                    }
                }
                '.' => {
                    self.advance();
                    if self.peek_char() == Some('.') && self.peek_char_n(1) == Some('=') {
                        self.advance();
                        self.advance();
                        SurfTokenKind::DotDotEq
                    } else if self.peek_char() == Some('.') {
                        self.advance();
                        SurfTokenKind::DotDot
                    } else {
                        SurfTokenKind::Dot
                    }
                }
                '+' => {
                    self.advance();
                    match self.peek_char() {
                        Some('=') => {
                            self.advance();
                            SurfTokenKind::PlusEq
                        }
                        Some('%') => {
                            self.advance();
                            SurfTokenKind::PlusPercent
                        }
                        Some('|') => {
                            self.advance();
                            SurfTokenKind::PlusPipe
                        }
                        _ => SurfTokenKind::Plus,
                    }
                }
                '-' => {
                    self.advance();
                    match self.peek_char() {
                        Some('>') => {
                            self.advance();
                            SurfTokenKind::Arrow
                        }
                        Some('=') => {
                            self.advance();
                            SurfTokenKind::MinusEq
                        }
                        Some('%') => {
                            self.advance();
                            SurfTokenKind::MinusPercent
                        }
                        Some('|') => {
                            self.advance();
                            SurfTokenKind::MinusPipe
                        }
                        _ => SurfTokenKind::Minus,
                    }
                }
                '*' => {
                    self.advance();
                    match self.peek_char() {
                        Some('=') => {
                            self.advance();
                            SurfTokenKind::StarEq
                        }
                        Some('%') => {
                            self.advance();
                            SurfTokenKind::StarPercent
                        }
                        Some('|') => {
                            self.advance();
                            SurfTokenKind::StarPipe
                        }
                        _ => SurfTokenKind::Star,
                    }
                }
                '/' => {
                    self.advance();
                    SurfTokenKind::Slash
                }
                '%' => {
                    self.advance();
                    SurfTokenKind::Percent
                }
                '&' => {
                    self.advance();
                    if self.peek_char() == Some('&') {
                        self.advance();
                        SurfTokenKind::AmpAmp
                    } else {
                        SurfTokenKind::Amp
                    }
                }
                '|' => {
                    self.advance();
                    if self.peek_char() == Some('|') {
                        self.advance();
                        SurfTokenKind::PipePipe
                    } else {
                        SurfTokenKind::Pipe
                    }
                }
                '!' => {
                    self.advance();
                    if self.peek_char() == Some('=') {
                        self.advance();
                        SurfTokenKind::Ne
                    } else {
                        SurfTokenKind::Bang
                    }
                }
                '=' => {
                    self.advance();
                    if self.peek_char() == Some('=') {
                        self.advance();
                        SurfTokenKind::EqEq
                    } else {
                        SurfTokenKind::Eq
                    }
                }
                '<' => {
                    self.advance();
                    match self.peek_char() {
                        Some('=') => {
                            self.advance();
                            SurfTokenKind::Le
                        }
                        Some('<') => {
                            self.advance();
                            SurfTokenKind::Shl
                        }
                        _ => SurfTokenKind::Lt,
                    }
                }
                '>' => {
                    self.advance();
                    match self.peek_char() {
                        Some('=') => {
                            self.advance();
                            SurfTokenKind::Ge
                        }
                        Some('>') => {
                            self.advance();
                            SurfTokenKind::Shr
                        }
                        _ => SurfTokenKind::Gt,
                    }
                }
                '\'' => {
                    self.advance();
                    let c = self
                        .advance()
                        .ok_or_else(|| format!("Unterminated rune literal at {line}:{col}"))?;
                    let ch_val = if c == '\\' {
                        let esc = self
                            .advance()
                            .ok_or_else(|| format!("Unterminated escape at {line}:{col}"))?;
                        match esc {
                            'n' => '\n',
                            'r' => '\r',
                            't' => '\t',
                            '0' => '\0',
                            '\\' => '\\',
                            '\'' => '\'',
                            _ => return Err(format!("Unknown rune escape '\\{esc}' at {line}:{col}")),
                        }
                    } else {
                        c
                    };
                    if self.advance() != Some('\'') {
                        return Err(format!("Expected closing \"'\" for rune literal at {line}:{col}"));
                    }
                    SurfTokenKind::RuneLit(ch_val)
                }
                '"' => {
                    self.advance();
                    let mut s = String::new();
                    loop {
                        let c = self
                            .advance()
                            .ok_or_else(|| format!("Unterminated string literal at {line}:{col}"))?;
                        if c == '"' {
                            break;
                        } else if c == '\\' {
                            let esc = self
                                .advance()
                                .ok_or_else(|| format!("Unterminated escape at {line}:{col}"))?;
                            match esc {
                                'n' => s.push('\n'),
                                'r' => s.push('\r'),
                                't' => s.push('\t'),
                                '0' => s.push('\0'),
                                '\\' => s.push('\\'),
                                '"' => s.push('"'),
                                _ => {
                                    return Err(format!(
                                        "Unknown string escape '\\{esc}' at {line}:{col}"
                                    ))
                                }
                            }
                        } else {
                            s.push(c);
                        }
                    }
                    SurfTokenKind::Str(s)
                }
                '@' => {
                    self.advance();
                    let mut name = String::new();
                    while let Some(c) = self.peek_char() {
                        if c.is_ascii_alphanumeric() || c == '_' {
                            name.push(c);
                            self.advance();
                        } else {
                            break;
                        }
                    }
                    match name.as_str() {
                        "default" => SurfTokenKind::AtDefault,
                        "clone" => SurfTokenKind::AtClone,
                        "drop" => SurfTokenKind::AtDrop,
                        "trap" => SurfTokenKind::AtTrap,
                        _ => return Err(format!("Unknown intrinsic '@{name}' at {line}:{col}")),
                    }
                }
                c if c.is_ascii_digit() => {
                    if c == '0' && matches!(self.peek_char_n(1), Some('x' | 'X')) {
                        self.advance();
                        self.advance();
                        let mut hex = String::new();
                        while let Some(hc) = self.peek_char() {
                            if hc.is_ascii_hexdigit() || hc == '_' {
                                if hc != '_' {
                                    hex.push(hc);
                                }
                                self.advance();
                            } else {
                                break;
                            }
                        }
                        let val = i128::from_str_radix(&hex, 16)
                            .map_err(|e| format!("Invalid hex literal 0x{hex} at {line}:{col}: {e}"))?;
                        SurfTokenKind::Int(val)
                    } else {
                        let mut num = String::new();
                        let mut is_float = false;
                        while let Some(nc) = self.peek_char() {
                            if nc.is_ascii_digit() || nc == '_' {
                                if nc != '_' {
                                    num.push(nc);
                                }
                                self.advance();
                            } else if nc == '.'
                                && self.peek_char_n(1) != Some('.')
                                && self.peek_char_n(1).is_some_and(|d| d.is_ascii_digit())
                                && !is_float
                            {
                                is_float = true;
                                num.push('.');
                                self.advance();
                            } else {
                                break;
                            }
                        }
                        if is_float {
                            let f: f64 = num
                                .parse()
                                .map_err(|e| format!("Invalid float '{num}' at {line}:{col}: {e}"))?;
                            SurfTokenKind::Float(f.to_bits())
                        } else {
                            let n: i128 = num
                                .parse()
                                .map_err(|e| format!("Invalid int '{num}' at {line}:{col}: {e}"))?;
                            SurfTokenKind::Int(n)
                        }
                    }
                }
                c if c.is_ascii_alphabetic() || c == '_' => {
                    let mut ident = String::new();
                    while let Some(ic) = self.peek_char() {
                        if ic.is_ascii_alphanumeric() || ic == '_' {
                            ident.push(ic);
                            self.advance();
                        } else {
                            break;
                        }
                    }
                    match ident.as_str() {
                        "import" => SurfTokenKind::Import,
                        "pub" => SurfTokenKind::Pub,
                        "pkg" => SurfTokenKind::Pkg,
                        "fn" => SurfTokenKind::Fn,
                        "extern" => SurfTokenKind::Extern,
                        "record" => SurfTokenKind::Record,
                        "struct" => SurfTokenKind::Struct,
                        "tuple" => SurfTokenKind::Tuple,
                        "type" => SurfTokenKind::TypeKw,
                        "comptime" => SurfTokenKind::Comptime,
                        "let" => SurfTokenKind::Let,
                        "mut" => SurfTokenKind::Mut,
                        "const" => SurfTokenKind::Const,
                        "if" => SurfTokenKind::If,
                        "else" => SurfTokenKind::Else,
                        "while" => SurfTokenKind::While,
                        "return" => SurfTokenKind::Return,
                        "unsafe" => SurfTokenKind::Unsafe,
                        "move" => SurfTokenKind::Move,
                        "as" => SurfTokenKind::As,
                        "in" => SurfTokenKind::In,
                        "orelse" => SurfTokenKind::OrElse,
                        "default" => SurfTokenKind::DefaultKw,
                        "clone" => SurfTokenKind::CloneKw,
                        "drop" => SurfTokenKind::DropKw,
                        "void" => SurfTokenKind::Void,
                        "never" => SurfTokenKind::Never,
                        "bool" => SurfTokenKind::Bool,
                        "rune" => SurfTokenKind::RuneKw,
                        "f32" => SurfTokenKind::F32,
                        "f64" => SurfTokenKind::F64,
                        "isize" => SurfTokenKind::Isize,
                        "usize" => SurfTokenKind::Usize,
                        "Self" => SurfTokenKind::SelfType,
                        "true" => SurfTokenKind::True,
                        "false" => SurfTokenKind::False,
                        "null" => SurfTokenKind::Null,
                        "simd" => SurfTokenKind::Simd,
                        s => {
                            if let Some(rest) = s.strip_prefix('i').or_else(|| s.strip_prefix('u'))
                                && !rest.is_empty()
                                && rest.bytes().all(|b| b.is_ascii_digit())
                                && let Ok(bits) = rest.parse::<u16>()
                                && (1..=512).contains(&bits)
                            {
                                SurfTokenKind::IntType {
                                    signed: s.starts_with('i'),
                                    bits,
                                }
                            } else {
                                SurfTokenKind::Ident(ident)
                            }
                        }
                    }
                }
                _ => return Err(format!("Unexpected character '{ch}' at {line}:{col}")),
            };

            tokens.push(SurfToken { kind, line, col });
        }
        Ok(tokens)
    }
}

pub struct SurfaceParser {
    tokens: Vec<SurfToken>,
    pos: usize,
}

impl SurfaceParser {
    pub fn parse_module(src: &str) -> Result<ModuleAst, String> {
        let tokens = SurfaceLexer::new(src).tokenize()?;
        let mut parser = Self { tokens, pos: 0 };
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
            _ => Err(format!(
                "Expected identifier, found {:?} at {}:{}",
                tok.kind, tok.line, tok.col
            )),
        }
    }

    fn parse_visibility(&mut self) -> Result<Visibility, String> {
        if self.peek().kind == SurfTokenKind::Pub {
            self.advance();
            if self.peek().kind == SurfTokenKind::LParen {
                self.advance();
                self.expect(&SurfTokenKind::Pkg)?;
                self.expect(&SurfTokenKind::RParen)?;
                Ok(Visibility::PubPkg)
            } else {
                Ok(Visibility::Pub)
            }
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
                SurfTokenKind::Extern => {
                    items.push(Item::ExternFunc(self.parse_extern_func(vis)?));
                }
                SurfTokenKind::Record => {
                    self.advance();
                    let name = self.expect_ident()?;
                    let ty = self.parse_record_body()?;
                    items.push(Item::TypeDecl { vis, name, ty });
                }
                SurfTokenKind::Struct => {
                    self.advance();
                    let name = self.expect_ident()?;
                    let ty = self.parse_struct_body()?;
                    items.push(Item::TypeDecl { vis, name, ty });
                }
                SurfTokenKind::Ident(s) if s == "enum" => {
                    self.advance();
                    let name = self.expect_ident()?;
                    let ty = self.parse_enum_body()?;
                    items.push(Item::TypeDecl { vis, name, ty });
                }
                SurfTokenKind::TypeKw => {
                    self.advance();
                    let name = self.expect_ident()?;
                    self.expect(&SurfTokenKind::Eq)?;
                    let ty = self.parse_type_expr()?;
                    self.expect(&SurfTokenKind::Semi)?;
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
        Ok(ImportDecl { vis, path, targets })
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
            let is_mut = if self.peek().kind == SurfTokenKind::Mut {
                self.advance();
                true
            } else {
                false
            };
            let pname = self.expect_ident()?;
            self.expect(&SurfTokenKind::Colon)?;
            let pty = self.parse_type_expr()?;
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
        let body = self.parse_block()?;
        Ok(FuncDecl {
            vis,
            name,
            params,
            ret_ty,
            body,
        })
    }

    fn parse_record_body(&mut self) -> Result<TypeExpr, String> {
        self.expect(&SurfTokenKind::LBrace)?;
        let mut fields = Vec::new();
        let mut methods = Vec::new();
        while self.peek().kind != SurfTokenKind::RBrace {
            let vis = self.parse_visibility()?;
            if self.peek().kind == SurfTokenKind::Fn {
                methods.push(self.parse_func_decl(vis)?);
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
                // Record fields are public by default
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
        Ok(TypeExpr::Record { fields, methods })
    }

    fn parse_struct_body(&mut self) -> Result<TypeExpr, String> {
        self.expect(&SurfTokenKind::LBrace)?;
        let mut fields = Vec::new();
        let mut methods = Vec::new();
        let mut default_hook = None;
        let mut clone_hook = None;
        let mut drop_hook = None;

        while self.peek().kind != SurfTokenKind::RBrace {
            let vis = self.parse_visibility()?;
            match &self.peek().kind {
                SurfTokenKind::Fn => {
                    methods.push(self.parse_func_decl(vis)?);
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
                    clone_hook = Some((self_name, self.parse_block()?));
                }
                SurfTokenKind::DropKw => {
                    self.advance();
                    self.expect(&SurfTokenKind::LParen)?;
                    let self_name = self.expect_ident()?;
                    self.expect(&SurfTokenKind::Colon)?;
                    let _ = self.parse_type_expr()?;
                    self.expect(&SurfTokenKind::RParen)?;
                    drop_hook = Some((self_name, self.parse_block()?));
                }
                _ => {
                    let fname = self.expect_ident()?;
                    self.expect(&SurfTokenKind::Colon)?;
                    let fty = self.parse_type_expr()?;
                    let default_val = if self.peek().kind == SurfTokenKind::Eq {
                        self.advance();
                        Some(self.parse_expr()?)
                    } else {
                        None
                    };
                    // Struct fields are strictly private to the struct block by default!
                    fields.push(FieldDecl {
                        vis,
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
            fields,
            methods,
            default_hook,
            clone_hook,
            drop_hook,
        })
    }

    fn parse_enum_body(&mut self) -> Result<TypeExpr, String> {
        self.expect(&SurfTokenKind::LBrace)?;
        let mut variants = Vec::new();
        while self.peek().kind != SurfTokenKind::RBrace {
            let vname = self.expect_ident()?;
            let val = if self.peek().kind == SurfTokenKind::Eq {
                self.advance();
                let tok = self.advance();
                match tok.kind {
                    SurfTokenKind::Int(n) => Some(n),
                    _ => return Err(format!("Expected integer discriminant for enum variant '{vname}'")),
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
        Ok(TypeExpr::Enum(variants))
    }

    pub fn parse_type_expr(&mut self) -> Result<TypeExpr, String> {
        let base = self.parse_base_type_expr()?;
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
            SurfTokenKind::TypeKw => {
                self.advance();
                Ok(TypeExpr::MetaType)
            }
            SurfTokenKind::SelfType => {
                self.advance();
                Ok(TypeExpr::SelfType)
            }
            SurfTokenKind::Amp => {
                self.advance();
                let mutable = if self.peek().kind == SurfTokenKind::Mut {
                    self.advance();
                    true
                } else {
                    false
                };
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
                Ok(TypeExpr::FnPtr {
                    params,
                    ret: Box::new(ret),
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
            SurfTokenKind::Record => {
                self.advance();
                if self.peek().kind != SurfTokenKind::LBrace {
                    return Ok(TypeExpr::Constraint(TypeConstraint::Record));
                }
                self.parse_record_body()
            }
            SurfTokenKind::Struct => {
                self.advance();
                if self.peek().kind != SurfTokenKind::LBrace {
                    return Ok(TypeExpr::Constraint(TypeConstraint::Struct));
                }
                self.parse_struct_body()
            }
            SurfTokenKind::Ident(_) => {
                let mut path = vec![self.expect_ident()?];
                while self.peek().kind == SurfTokenKind::ColonColon {
                    self.advance();
                    path.push(self.expect_ident()?);
                }
                if path.len() == 1
                    && path[0] == "enum"
                    && self.peek().kind == SurfTokenKind::LBrace
                {
                    return self.parse_enum_body();
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
                    match path[0].as_str() {
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
                        "sequence" => Ok(TypeExpr::Constraint(TypeConstraint::Sequence)),
                        "array" => Ok(TypeExpr::Constraint(TypeConstraint::Array)),
                        "slice" => Ok(TypeExpr::Constraint(TypeConstraint::Slice)),
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
                | SurfTokenKind::Record
                | SurfTokenKind::Struct
                | SurfTokenKind::Question
                | SurfTokenKind::LBracket
        ) || (self.peek().kind == SurfTokenKind::Simd
            && self.peek_n(1).kind == SurfTokenKind::LBracket)
            || (self.peek().kind == SurfTokenKind::Amp
                && (self.peek_n(1).kind == SurfTokenKind::LBracket
                    || (self.peek_n(1).kind == SurfTokenKind::Mut
                        && self.peek_n(2).kind == SurfTokenKind::LBracket)))
            || self.is_fn_type_ahead()
            || (matches!(&self.peek().kind, SurfTokenKind::Ident(s) if s == "enum")
                && self.peek_n(1).kind == SurfTokenKind::LBrace)
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

    fn parse_expr_or_type(&mut self) -> Result<Expr, String> {
        if self.is_explicit_type_start() {
            let ty = self.parse_type_expr()?;
            if self.peek().kind == SurfTokenKind::LBrace
                && matches!(ty, TypeExpr::Simd { .. } | TypeExpr::Array { .. })
            {
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
            Ok(Expr::TypeVal(ty))
        } else {
            let expr = self.parse_expr()?;
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

    fn parse_block(&mut self) -> Result<Block, String> {
        self.expect(&SurfTokenKind::LBrace)?;
        let mut stmts = Vec::new();
        while self.peek().kind != SurfTokenKind::RBrace
            && self.peek().kind != SurfTokenKind::Eof
        {
            stmts.push(self.parse_stmt()?);
        }
        self.expect(&SurfTokenKind::RBrace)?;
        Ok(Block { stmts })
    }

    fn parse_stmt(&mut self) -> Result<Stmt, String> {
        match &self.peek().kind {
            SurfTokenKind::Let => {
                self.advance();
                let mutable = if self.peek().kind == SurfTokenKind::Mut {
                    self.advance();
                    true
                } else {
                    false
                };
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
                Ok(Stmt::Let {
                    mutable,
                    name,
                    ty,
                    init,
                })
            }
            SurfTokenKind::If => self.parse_if_stmt(),
            SurfTokenKind::While => {
                self.advance();
                let cond = self.parse_expr()?;
                let body = self.parse_block()?;
                Ok(Stmt::While { cond, body })
            }
            SurfTokenKind::Return => {
                self.advance();
                if self.peek().kind == SurfTokenKind::Semi {
                    self.advance();
                    Ok(Stmt::Return(None))
                } else {
                    let val = self.parse_expr_or_type()?;
                    self.expect(&SurfTokenKind::Semi)?;
                    Ok(Stmt::Return(Some(val)))
                }
            }
            SurfTokenKind::Unsafe => {
                self.advance();
                let blk = self.parse_block()?;
                Ok(Stmt::Unsafe(blk))
            }
            _ => {
                let expr = self.parse_expr()?;
                match &self.peek().kind {
                    SurfTokenKind::Eq => {
                        self.advance();
                        let value = self.parse_expr()?;
                        self.expect(&SurfTokenKind::Semi)?;
                        Ok(Stmt::Assign {
                            target: expr,
                            op: None,
                            value,
                        })
                    }
                    SurfTokenKind::PlusEq => {
                        self.advance();
                        let value = self.parse_expr()?;
                        self.expect(&SurfTokenKind::Semi)?;
                        Ok(Stmt::Assign {
                            target: expr,
                            op: Some(BinOp::Add),
                            value,
                        })
                    }
                    SurfTokenKind::MinusEq => {
                        self.advance();
                        let value = self.parse_expr()?;
                        self.expect(&SurfTokenKind::Semi)?;
                        Ok(Stmt::Assign {
                            target: expr,
                            op: Some(BinOp::Sub),
                            value,
                        })
                    }
                    SurfTokenKind::StarEq => {
                        self.advance();
                        let value = self.parse_expr()?;
                        self.expect(&SurfTokenKind::Semi)?;
                        Ok(Stmt::Assign {
                            target: expr,
                            op: Some(BinOp::Mul),
                            value,
                        })
                    }
                    _ => {
                        self.expect(&SurfTokenKind::Semi)?;
                        Ok(Stmt::Expr(expr))
                    }
                }
            }
        }
    }

    fn parse_if_stmt(&mut self) -> Result<Stmt, String> {
        self.expect(&SurfTokenKind::If)?;
        if self.peek().kind == SurfTokenKind::Let {
            self.advance();
            let var_name = self.expect_ident()?;
            self.expect(&SurfTokenKind::Eq)?;
            let opt_expr = self.parse_expr()?;
            let then_block = self.parse_block()?;
            let else_block = if self.peek().kind == SurfTokenKind::Else {
                self.advance();
                if self.peek().kind == SurfTokenKind::If {
                    Some(Block {
                        stmts: vec![self.parse_if_stmt()?],
                    })
                } else {
                    Some(self.parse_block()?)
                }
            } else {
                None
            };
            Ok(Stmt::IfLet {
                var_name,
                opt_expr,
                then_block,
                else_block,
            })
        } else {
            let cond = self.parse_expr()?;
            let then_block = self.parse_block()?;
            let else_block = if self.peek().kind == SurfTokenKind::Else {
                self.advance();
                if self.peek().kind == SurfTokenKind::If {
                    Some(Block {
                        stmts: vec![self.parse_if_stmt()?],
                    })
                } else {
                    Some(self.parse_block()?)
                }
            } else {
                None
            };
            Ok(Stmt::If {
                cond,
                then_block,
                else_block,
            })
        }
    }

    pub fn parse_expr(&mut self) -> Result<Expr, String> {
        self.parse_logical_or()
    }

    fn parse_logical_or(&mut self) -> Result<Expr, String> {
        let mut lhs = self.parse_logical_and()?;
        while self.peek().kind == SurfTokenKind::PipePipe {
            self.advance();
            let rhs = self.parse_logical_and()?;
            lhs = Expr::LogicalOr(Box::new(lhs), Box::new(rhs));
        }
        Ok(lhs)
    }

    fn parse_logical_and(&mut self) -> Result<Expr, String> {
        let mut lhs = self.parse_comparison()?;
        while self.peek().kind == SurfTokenKind::AmpAmp {
            self.advance();
            let rhs = self.parse_comparison()?;
            lhs = Expr::LogicalAnd(Box::new(lhs), Box::new(rhs));
        }
        Ok(lhs)
    }

    fn parse_comparison(&mut self) -> Result<Expr, String> {
        let mut lhs = self.parse_bitwise_or()?;
        loop {
            let op = match self.peek().kind {
                SurfTokenKind::EqEq => BinOp::Eq,
                SurfTokenKind::Ne => BinOp::Ne,
                SurfTokenKind::Lt => BinOp::Lt,
                SurfTokenKind::Le => BinOp::Le,
                SurfTokenKind::Gt => BinOp::Gt,
                SurfTokenKind::Ge => BinOp::Ge,
                _ => break,
            };
            self.advance();
            let rhs = self.parse_bitwise_or()?;
            lhs = Expr::Binary {
                op,
                lhs: Box::new(lhs),
                rhs: Box::new(rhs),
            };
        }
        Ok(lhs)
    }

    fn parse_bitwise_or(&mut self) -> Result<Expr, String> {
        let mut lhs = self.parse_bitwise_xor()?;
        while self.peek().kind == SurfTokenKind::Pipe {
            self.advance();
            let rhs = self.parse_bitwise_xor()?;
            lhs = Expr::Binary {
                op: BinOp::BitOr,
                lhs: Box::new(lhs),
                rhs: Box::new(rhs),
            };
        }
        Ok(lhs)
    }

    fn parse_bitwise_xor(&mut self) -> Result<Expr, String> {
        let mut lhs = self.parse_bitwise_and()?;
        while self.peek().kind == SurfTokenKind::Caret {
            self.advance();
            let rhs = self.parse_bitwise_and()?;
            lhs = Expr::Binary {
                op: BinOp::BitXor,
                lhs: Box::new(lhs),
                rhs: Box::new(rhs),
            };
        }
        Ok(lhs)
    }

    fn parse_bitwise_and(&mut self) -> Result<Expr, String> {
        let mut lhs = self.parse_shift()?;
        while self.peek().kind == SurfTokenKind::Amp {
            self.advance();
            let rhs = self.parse_shift()?;
            lhs = Expr::Binary {
                op: BinOp::BitAnd,
                lhs: Box::new(lhs),
                rhs: Box::new(rhs),
            };
        }
        Ok(lhs)
    }

    fn parse_shift(&mut self) -> Result<Expr, String> {
        let mut lhs = self.parse_additive_expr()?;
        loop {
            let op = match self.peek().kind {
                SurfTokenKind::Shl => BinOp::Shl,
                SurfTokenKind::Shr => BinOp::Shr,
                _ => break,
            };
            self.advance();
            let rhs = self.parse_additive_expr()?;
            lhs = Expr::Binary {
                op,
                lhs: Box::new(lhs),
                rhs: Box::new(rhs),
            };
        }
        Ok(lhs)
    }

    fn parse_additive_expr(&mut self) -> Result<Expr, String> {
        let mut lhs = self.parse_multiplicative_expr()?;
        loop {
            let op = match self.peek().kind {
                SurfTokenKind::Plus => BinOp::Add,
                SurfTokenKind::PlusPercent => BinOp::AddWrap,
                SurfTokenKind::PlusPipe => BinOp::AddSat,
                SurfTokenKind::Minus => BinOp::Sub,
                SurfTokenKind::MinusPercent => BinOp::SubWrap,
                SurfTokenKind::MinusPipe => BinOp::SubSat,
                _ => break,
            };
            self.advance();
            let rhs = self.parse_multiplicative_expr()?;
            lhs = Expr::Binary {
                op,
                lhs: Box::new(lhs),
                rhs: Box::new(rhs),
            };
        }
        Ok(lhs)
    }

    fn parse_multiplicative_expr(&mut self) -> Result<Expr, String> {
        let mut lhs = self.parse_cast_or_orelse()?;
        loop {
            let op = match self.peek().kind {
                SurfTokenKind::Star => BinOp::Mul,
                SurfTokenKind::StarPercent => BinOp::MulWrap,
                SurfTokenKind::StarPipe => BinOp::MulSat,
                SurfTokenKind::Slash => BinOp::Div,
                SurfTokenKind::Percent => BinOp::Rem,
                _ => break,
            };
            self.advance();
            let rhs = self.parse_cast_or_orelse()?;
            lhs = Expr::Binary {
                op,
                lhs: Box::new(lhs),
                rhs: Box::new(rhs),
            };
        }
        Ok(lhs)
    }

    fn parse_cast_or_orelse(&mut self) -> Result<Expr, String> {
        let mut expr = self.parse_unary()?;
        loop {
            if self.peek().kind == SurfTokenKind::As {
                self.advance();
                let ty = self.parse_type_expr()?;
                expr = Expr::Cast {
                    expr: Box::new(expr),
                    ty,
                };
            } else if self.peek().kind == SurfTokenKind::OrElse {
                self.advance();
                let fallback = self.parse_unary()?;
                expr = Expr::OrElse {
                    opt: Box::new(expr),
                    fallback: Box::new(fallback),
                };
            } else {
                break;
            }
        }
        Ok(expr)
    }

    fn parse_unary(&mut self) -> Result<Expr, String> {
        match &self.peek().kind {
            SurfTokenKind::Minus => {
                self.advance();
                let expr = self.parse_unary()?;
                Ok(Expr::Unary {
                    op: UnOp::Neg,
                    expr: Box::new(expr),
                })
            }
            SurfTokenKind::Bang => {
                self.advance();
                let expr = self.parse_unary()?;
                Ok(Expr::Unary {
                    op: UnOp::Not,
                    expr: Box::new(expr),
                })
            }
            SurfTokenKind::Amp => {
                self.advance();
                let mutable = if self.peek().kind == SurfTokenKind::Mut {
                    self.advance();
                    true
                } else {
                    false
                };
                let expr = self.parse_unary()?;
                Ok(Expr::Ref {
                    mutable,
                    expr: Box::new(expr),
                })
            }
            SurfTokenKind::Star => {
                self.advance();
                let expr = self.parse_unary()?;
                Ok(Expr::Deref(Box::new(expr)))
            }
            SurfTokenKind::Move => {
                self.advance();
                if self.peek().kind == SurfTokenKind::Fn {
                    return self.parse_lambda_expr(true);
                }
                let expr = self.parse_unary()?;
                Ok(Expr::Move(Box::new(expr)))
            }
            _ => self.parse_postfix(),
        }
    }

    fn parse_postfix(&mut self) -> Result<Expr, String> {
        let mut expr = self.parse_primary()?;
        loop {
            match &self.peek().kind {
                SurfTokenKind::Dot => {
                    self.advance();
                    match &self.peek().kind {
                        SurfTokenKind::Int(idx) => {
                            let idx = *idx as u32;
                            self.advance();
                            expr = Expr::TupleIndex {
                                base: Box::new(expr),
                                index: idx,
                            };
                        }
                        SurfTokenKind::Ident(_) => {
                            let name = self.expect_ident()?;
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
                                expr = Expr::MethodCall {
                                    receiver: Box::new(expr),
                                    method: name,
                                    args,
                                };
                            } else {
                                expr = Expr::Field {
                                    base: Box::new(expr),
                                    field: name,
                                };
                            }
                        }
                        _ => {
                            let tok = self.peek();
                            return Err(format!(
                                "Expected field name or tuple index after '.', found {:?} at {}:{}",
                                tok.kind, tok.line, tok.col
                            ));
                        }
                    }
                }
                SurfTokenKind::LBracket => {
                    self.advance();
                    let first = self.parse_expr()?;
                    if self.peek().kind == SurfTokenKind::DotDot {
                        self.advance();
                        let end = self.parse_expr()?;
                        self.expect(&SurfTokenKind::RBracket)?;
                        expr = Expr::Slice {
                            base: Box::new(expr),
                            start: Box::new(first),
                            end: Box::new(end),
                        };
                    } else {
                        self.expect(&SurfTokenKind::RBracket)?;
                        expr = Expr::Index {
                            base: Box::new(expr),
                            index: Box::new(first),
                        };
                    }
                }
                SurfTokenKind::LParen => {
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
                    // Check if `TypeCall(args) { field: val, ... }` struct literal!
                    if self.peek().kind == SurfTokenKind::LBrace
                        && matches!(self.peek_n(1).kind, SurfTokenKind::Ident(_))
                        && self.peek_n(2).kind == SurfTokenKind::Colon
                        && let Expr::Path(path) = expr
                    {
                        let ty = TypeExpr::TypeCall { path, args };
                        return self.parse_struct_lit_fields(ty);
                    }
                    expr = Expr::Call {
                        callee: Box::new(expr),
                        args,
                    };
                }
                _ => break,
            }
        }
        Ok(expr)
    }

    fn parse_struct_lit_fields(&mut self, ty: TypeExpr) -> Result<Expr, String> {
        self.expect(&SurfTokenKind::LBrace)?;
        let mut fields = Vec::new();
        while self.peek().kind != SurfTokenKind::RBrace {
            let fname = self.expect_ident()?;
            self.expect(&SurfTokenKind::Colon)?;
            let fval = self.parse_expr()?;
            fields.push((fname, fval));
            if self.peek().kind == SurfTokenKind::Comma {
                self.advance();
            } else {
                break;
            }
        }
        self.expect(&SurfTokenKind::RBrace)?;
        Ok(Expr::StructLit { ty, fields })
    }

    fn parse_lambda_expr(&mut self, is_move: bool) -> Result<Expr, String> {
        self.expect(&SurfTokenKind::Fn)?;
        self.expect(&SurfTokenKind::LParen)?;
        let mut params = Vec::new();
        while self.peek().kind != SurfTokenKind::RParen {
            let is_mut = if self.peek().kind == SurfTokenKind::Mut {
                self.advance();
                true
            } else {
                false
            };
            let pname = self.expect_ident()?;
            self.expect(&SurfTokenKind::Colon)?;
            let pty = self.parse_type_expr()?;
            params.push((is_mut, pname, pty));
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
        let body = self.parse_block()?;
        Ok(Expr::Lambda {
            is_move,
            params,
            ret_ty,
            body,
        })
    }

    fn parse_primary(&mut self) -> Result<Expr, String> {
        let tok = self.peek().clone();
        match tok.kind {
            SurfTokenKind::Int(n) => {
                self.advance();
                Ok(Expr::Int(n))
            }
            SurfTokenKind::Float(bits) => {
                self.advance();
                Ok(Expr::Float(bits))
            }
            SurfTokenKind::True => {
                self.advance();
                Ok(Expr::Bool(true))
            }
            SurfTokenKind::False => {
                self.advance();
                Ok(Expr::Bool(false))
            }
            SurfTokenKind::RuneLit(ch) => {
                self.advance();
                Ok(Expr::Rune(ch))
            }
            SurfTokenKind::Str(s) => {
                self.advance();
                Ok(Expr::Str(s))
            }
            SurfTokenKind::Null => {
                self.advance();
                Ok(Expr::Null)
            }
            SurfTokenKind::AtDefault => {
                self.advance();
                self.expect(&SurfTokenKind::LParen)?;
                let ty = self.parse_type_expr()?;
                self.expect(&SurfTokenKind::RParen)?;
                Ok(Expr::IntrinsicDefault(ty))
            }
            SurfTokenKind::AtClone => {
                self.advance();
                self.expect(&SurfTokenKind::LParen)?;
                let val = self.parse_expr()?;
                self.expect(&SurfTokenKind::RParen)?;
                Ok(Expr::IntrinsicClone(Box::new(val)))
            }
            SurfTokenKind::AtDrop => {
                self.advance();
                self.expect(&SurfTokenKind::LParen)?;
                let val = self.parse_expr()?;
                self.expect(&SurfTokenKind::RParen)?;
                Ok(Expr::IntrinsicDrop(Box::new(val)))
            }
            SurfTokenKind::AtTrap => {
                self.advance();
                self.expect(&SurfTokenKind::LParen)?;
                self.expect(&SurfTokenKind::RParen)?;
                Ok(Expr::IntrinsicTrap)
            }
            SurfTokenKind::Return => {
                self.advance();
                let val = if !matches!(
                    self.peek().kind,
                    SurfTokenKind::Semi
                        | SurfTokenKind::Comma
                        | SurfTokenKind::RParen
                        | SurfTokenKind::RBrace
                        | SurfTokenKind::RBracket
                ) {
                    Some(Box::new(self.parse_expr()?))
                } else {
                    None
                };
                Ok(Expr::Return(val))
            }
            SurfTokenKind::LParen => {
                self.advance();
                let inner = self.parse_expr()?;
                self.expect(&SurfTokenKind::RParen)?;
                Ok(inner)
            }
            SurfTokenKind::LBrace => {
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
                Ok(Expr::TupleLit(elems))
            }
            SurfTokenKind::Simd | SurfTokenKind::LBracket => {
                let ty = self.parse_type_expr()?;
                if self.peek().kind == SurfTokenKind::LBrace {
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
                    Ok(Expr::SimdLit { ty, elems })
                } else {
                    Ok(Expr::TypeVal(ty))
                }
            }
            SurfTokenKind::SelfType => {
                self.advance();
                if self.peek().kind == SurfTokenKind::ColonColon {
                    self.advance();
                    let method = self.expect_ident()?;
                    Ok(Expr::Path(vec!["Self".to_string(), method]))
                } else if self.peek().kind == SurfTokenKind::LBrace {
                    self.parse_struct_lit_fields(TypeExpr::SelfType)
                } else {
                    Ok(Expr::TypeVal(TypeExpr::SelfType))
                }
            }
            SurfTokenKind::Unsafe => {
                self.advance();
                let blk = self.parse_block()?;
                Ok(Expr::UnsafeBlock(blk))
            }
            SurfTokenKind::Fn => self.parse_lambda_expr(false),
            SurfTokenKind::Ident(_) => {
                let mut path = vec![self.expect_ident()?];
                while self.peek().kind == SurfTokenKind::ColonColon {
                    self.advance();
                    path.push(self.expect_ident()?);
                }
                // Check for `Type { field: val, ... }` struct/record literal
                if self.peek().kind == SurfTokenKind::LBrace
                    && (self.peek_n(1).kind == SurfTokenKind::RBrace
                        || (matches!(self.peek_n(1).kind, SurfTokenKind::Ident(_))
                            && self.peek_n(2).kind == SurfTokenKind::Colon))
                {
                    let ty = TypeExpr::Named(path);
                    self.parse_struct_lit_fields(ty)
                } else {
                    Ok(Expr::Path(path))
                }
            }
            _ => Err(format!(
                "Expected expression, found {:?} at {}:{}",
                tok.kind, tok.line, tok.col
            )),
        }
    }
}

