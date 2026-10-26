use crate::ir::{BinOp, BlockId, FuncId, GlobalId, LocalId, TypeId, UnOp};

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TokenKind {
    // Typed IDs
    Type(TypeId),     // ty0, ty1, ...
    Local(LocalId),   // _0, _1, ...
    Block(BlockId),   // bb0, bb1, ...
    Func(FuncId),     // fn0, fn1, ...
    Global(GlobalId), // gl0, gl1, ...
    Variant(u32),     // v0, v1, ...

    // Keywords
    Extern,
    GlobalKw,
    Drop,
    Borrows,
    Fn,
    Union,
    Overlay,
    Simd,
    In,
    Cast,
    Discriminant,
    IntType { signed: bool, bits: u16 },
    F32,
    F64,
    Void,
    Never,
    Bool,
    Rune,
    MetaType,
    Let,
    Copy,
    Move,
    Const,
    Mut,
    Aggregate,
    True,
    False,
    Goto,
    SwitchInt,
    Otherwise,
    Call,
    Return,
    Unreachable,
    StorageLive,
    StorageDead,
    UnOp(UnOp),
    BinOp(BinOp),

    // Literals
    Int(i128),
    /// An integer constant beyond `i128` (printed by `ConstValue::Wide`).
    WideInt(Box<crate::wide::Wide>),
    Float(u64),
    Str(String),

    // Punctuation
    LBrace,   // {
    RBrace,   // }
    LParen,   // (
    RParen,   // )
    LBracket, // [
    RBracket, // ]
    Colon,    // :
    Semi,     // ;
    Comma,    // ,
    Dot,      // .
    DotDotEq, // ..=
    Pipe,     // |
    Eq,       // =
    Amp,      // &
    Star,     // *
    Arrow,    // ->
    Eof,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Token {
    pub kind: TokenKind,
    pub line: usize,
    pub col: usize,
}

pub struct Lexer<'a> {
    input: &'a [u8],
    pos: usize,
    line: usize,
    col: usize,
    last_was_dot: bool,
}

impl<'a> Lexer<'a> {
    pub fn new(input: &'a str) -> Self {
        Self {
            input: input.as_bytes(),
            pos: 0,
            line: 1,
            col: 1,
            last_was_dot: false,
        }
    }

    pub fn tokenize(mut self) -> Result<Vec<Token>, String> {
        let mut tokens = Vec::new();
        loop {
            let tok = self.next_token()?;
            let is_eof = tok.kind == TokenKind::Eof;
            tokens.push(tok);
            if is_eof {
                break;
            }
        }
        Ok(tokens)
    }

    fn peek(&self) -> Option<u8> {
        self.input.get(self.pos).copied()
    }

    fn peek_next(&self) -> Option<u8> {
        self.input.get(self.pos + 1).copied()
    }

    fn advance(&mut self) -> Option<u8> {
        let b = self.peek()?;
        self.pos += 1;
        if b == b'\n' {
            self.line += 1;
            self.col = 1;
        } else {
            self.col += 1;
        }
        Some(b)
    }

    fn skip_whitespace_and_comments(&mut self) {
        while let Some(b) = self.peek() {
            if b.is_ascii_whitespace() {
                self.advance();
            } else if b == b'/' && self.peek_next() == Some(b'/') {
                while let Some(c) = self.peek() {
                    self.advance();
                    if c == b'\n' {
                        break;
                    }
                }
            } else {
                break;
            }
        }
    }

    fn next_token(&mut self) -> Result<Token, String> {
        self.skip_whitespace_and_comments();
        let line = self.line;
        let col = self.col;

        let Some(b) = self.peek() else {
            return Ok(Token {
                kind: TokenKind::Eof,
                line,
                col,
            });
        };

        let kind = match b {
            b'{' => {
                self.advance();
                TokenKind::LBrace
            }
            b'}' => {
                self.advance();
                TokenKind::RBrace
            }
            b'(' => {
                self.advance();
                TokenKind::LParen
            }
            b')' => {
                self.advance();
                TokenKind::RParen
            }
            b'[' => {
                self.advance();
                TokenKind::LBracket
            }
            b']' => {
                self.advance();
                TokenKind::RBracket
            }
            b':' => {
                self.advance();
                TokenKind::Colon
            }
            b';' => {
                self.advance();
                TokenKind::Semi
            }
            b',' => {
                self.advance();
                TokenKind::Comma
            }
            b'.' => {
                self.advance();
                if self.peek() == Some(b'.') && self.peek_next() == Some(b'=') {
                    self.advance();
                    self.advance();
                    TokenKind::DotDotEq
                } else {
                    TokenKind::Dot
                }
            }
            b'|' => {
                self.advance();
                TokenKind::Pipe
            }
            b'=' => {
                self.advance();
                TokenKind::Eq
            }
            b'&' => {
                self.advance();
                TokenKind::Amp
            }
            b'*' => {
                self.advance();
                TokenKind::Star
            }
            b'"' => {
                let s = self.read_string(line, col)?;
                TokenKind::Str(s)
            }
            b'-' => {
                self.advance();
                if self.peek() == Some(b'>') {
                    self.advance();
                    TokenKind::Arrow
                } else if self.peek().is_some_and(|c| c.is_ascii_digit()) {
                    self.read_number(true)?
                } else {
                    return Err(format!("Unexpected '-' at {line}:{col}"));
                }
            }
            c if c.is_ascii_digit() => self.read_number(false)?,
            c if c.is_ascii_alphabetic() || c == b'_' => {
                let word = self.read_word();
                if let Some(rest) = word.strip_prefix('_') {
                    let id = rest
                        .parse::<u32>()
                        .map_err(|_| format!("Invalid LocalId '{word}' at {line}:{col}"))?;
                    TokenKind::Local(LocalId(id))
                } else if let Some(rest) = word.strip_prefix("ty")
                    && !rest.is_empty()
                    && rest.bytes().all(|b| b.is_ascii_digit())
                {
                    let id = rest
                        .parse::<u32>()
                        .map_err(|_| format!("Invalid TypeId '{word}' at {line}:{col}"))?;
                    TokenKind::Type(TypeId(id))
                } else if let Some(rest) = word.strip_prefix("bb")
                    && !rest.is_empty()
                    && rest.bytes().all(|b| b.is_ascii_digit())
                {
                    let id = rest
                        .parse::<u32>()
                        .map_err(|_| format!("Invalid BlockId '{word}' at {line}:{col}"))?;
                    TokenKind::Block(BlockId(id))
                } else if let Some(rest) = word.strip_prefix("fn")
                    && !rest.is_empty()
                    && rest.bytes().all(|b| b.is_ascii_digit())
                {
                    let id = rest
                        .parse::<u32>()
                        .map_err(|_| format!("Invalid FuncId '{word}' at {line}:{col}"))?;
                    TokenKind::Func(FuncId(id))
                } else if let Some(rest) = word.strip_prefix("gl")
                    && !rest.is_empty()
                    && rest.bytes().all(|b| b.is_ascii_digit())
                {
                    let id = rest
                        .parse::<u32>()
                        .map_err(|_| format!("Invalid GlobalId '{word}' at {line}:{col}"))?;
                    TokenKind::Global(GlobalId(id))
                } else if let Some(rest) = word.strip_prefix('v')
                    && !rest.is_empty()
                    && rest.bytes().all(|b| b.is_ascii_digit())
                {
                    let id = rest
                        .parse::<u32>()
                        .map_err(|_| format!("Invalid Variant index '{word}' at {line}:{col}"))?;
                    TokenKind::Variant(id)
                } else if let Some(rest) = word.strip_prefix('i')
                    && !rest.is_empty()
                    && rest.bytes().all(|b| b.is_ascii_digit())
                {
                    let bits = rest.parse::<u16>().map_err(|_| {
                        format!("Invalid signed integer bit-width '{word}' at {line}:{col}")
                    })?;
                    if !(1..=512).contains(&bits) {
                        return Err(format!(
                            "Signed integer bit-width in '{word}' must be in 1..=512 at {line}:{col}"
                        ));
                    }
                    TokenKind::IntType { signed: true, bits }
                } else if let Some(rest) = word.strip_prefix('u')
                    && !rest.is_empty()
                    && rest.bytes().all(|b| b.is_ascii_digit())
                {
                    let bits = rest.parse::<u16>().map_err(|_| {
                        format!("Invalid unsigned integer bit-width '{word}' at {line}:{col}")
                    })?;
                    if !(1..=512).contains(&bits) {
                        return Err(format!(
                            "Unsigned integer bit-width in '{word}' must be in 1..=512 at {line}:{col}"
                        ));
                    }
                    TokenKind::IntType {
                        signed: false,
                        bits,
                    }
                } else {
                    match word.as_str() {
                        "extern" => TokenKind::Extern,
                        "global" => TokenKind::GlobalKw,
                        "drop" => TokenKind::Drop,
                        "borrows" => TokenKind::Borrows,
                        "fn" => TokenKind::Fn,
                        "union" => TokenKind::Union,
                        "overlay" => TokenKind::Overlay,
                        "simd" => TokenKind::Simd,
                        "in" => TokenKind::In,
                        "cast" => TokenKind::Cast,
                        "discriminant" => TokenKind::Discriminant,
                        "f32" => TokenKind::F32,
                        "f64" => TokenKind::F64,
                        "void" => TokenKind::Void,
                        "never" => TokenKind::Never,
                        "bool" => TokenKind::Bool,
                        "rune" => TokenKind::Rune,
                        "type" => TokenKind::MetaType,
                        "let" => TokenKind::Let,
                        "copy" => TokenKind::Copy,
                        "move" => TokenKind::Move,
                        "const" => TokenKind::Const,
                        "mut" => TokenKind::Mut,
                        "aggregate" => TokenKind::Aggregate,
                        "true" => TokenKind::True,
                        "false" => TokenKind::False,
                        "goto" => TokenKind::Goto,
                        "switchInt" => TokenKind::SwitchInt,
                        "otherwise" => TokenKind::Otherwise,
                        "call" => TokenKind::Call,
                        "return" => TokenKind::Return,
                        "unreachable" => TokenKind::Unreachable,
                        "StorageLive" => TokenKind::StorageLive,
                        "StorageDead" => TokenKind::StorageDead,
                        "neg" => TokenKind::UnOp(UnOp::Neg),
                        "not" => TokenKind::UnOp(UnOp::Not),
                        "bswap" => TokenKind::UnOp(UnOp::Bswap),
                        "add" => TokenKind::BinOp(BinOp::Add),
                        "sub" => TokenKind::BinOp(BinOp::Sub),
                        "mul" => TokenKind::BinOp(BinOp::Mul),
                        "add_wrap" => TokenKind::BinOp(BinOp::AddWrap),
                        "sub_wrap" => TokenKind::BinOp(BinOp::SubWrap),
                        "mul_wrap" => TokenKind::BinOp(BinOp::MulWrap),
                        "add_sat" => TokenKind::BinOp(BinOp::AddSat),
                        "sub_sat" => TokenKind::BinOp(BinOp::SubSat),
                        "mul_sat" => TokenKind::BinOp(BinOp::MulSat),
                        "add_checked" => TokenKind::BinOp(BinOp::AddChecked),
                        "sub_checked" => TokenKind::BinOp(BinOp::SubChecked),
                        "mul_checked" => TokenKind::BinOp(BinOp::MulChecked),
                        "add_unchecked" => TokenKind::BinOp(BinOp::AddUnchecked),
                        "sub_unchecked" => TokenKind::BinOp(BinOp::SubUnchecked),
                        "mul_unchecked" => TokenKind::BinOp(BinOp::MulUnchecked),
                        "div" => TokenKind::BinOp(BinOp::Div),
                        "rem" => TokenKind::BinOp(BinOp::Rem),
                        "bitand" => TokenKind::BinOp(BinOp::BitAnd),
                        "bitor" => TokenKind::BinOp(BinOp::BitOr),
                        "bitxor" => TokenKind::BinOp(BinOp::BitXor),
                        "shl" => TokenKind::BinOp(BinOp::Shl),
                        "shr" => TokenKind::BinOp(BinOp::Shr),
                        "eq" => TokenKind::BinOp(BinOp::Eq),
                        "ne" => TokenKind::BinOp(BinOp::Ne),
                        "lt" => TokenKind::BinOp(BinOp::Lt),
                        "le" => TokenKind::BinOp(BinOp::Le),
                        "gt" => TokenKind::BinOp(BinOp::Gt),
                        "ge" => TokenKind::BinOp(BinOp::Ge),
                        _ => {
                            return Err(format!(
                                "Unknown keyword or identifier '{word}' at {line}:{col}"
                            ));
                        }
                    }
                }
            }
            _ => {
                return Err(format!(
                    "Unexpected character '{}' at {line}:{col}",
                    b as char
                ));
            }
        };

        self.last_was_dot = kind == TokenKind::Dot;
        Ok(Token { kind, line, col })
    }

    fn read_string(&mut self, start_line: usize, start_col: usize) -> Result<String, String> {
        self.advance(); // consume opening '"'
        let mut s = String::new();
        while let Some(b) = self.advance() {
            match b {
                b'"' => return Ok(s),
                b'\\' => {
                    let Some(esc) = self.advance() else {
                        break;
                    };
                    match esc {
                        b'n' => s.push('\n'),
                        b'r' => s.push('\r'),
                        b't' => s.push('\t'),
                        b'\\' => s.push('\\'),
                        b'"' => s.push('"'),
                        b'0' => s.push('\0'),
                        _ => {
                            return Err(format!(
                                "Unknown escape sequence '\\{}' at {}:{}",
                                esc as char, self.line, self.col
                            ));
                        }
                    }
                }
                _ => s.push(b as char),
            }
        }
        Err(format!(
            "Unterminated string literal at {start_line}:{start_col}"
        ))
    }

    fn read_number(&mut self, negative: bool) -> Result<TokenKind, String> {
        let start = self.pos;
        while let Some(c) = self.peek() {
            if c.is_ascii_digit() {
                self.advance();
            } else {
                break;
            }
        }
        if !self.last_was_dot
            && self.peek() == Some(b'.')
            && self.peek_next().is_some_and(|c| c.is_ascii_digit())
        {
            self.advance(); // consume '.'
            while let Some(c) = self.peek() {
                if c.is_ascii_digit() {
                    self.advance();
                } else {
                    break;
                }
            }
            let s = std::str::from_utf8(&self.input[start..self.pos]).unwrap();
            let val: f64 = s.parse().map_err(|e| format!("Invalid float '{s}': {e}"))?;
            let val = if negative { -val } else { val };
            return Ok(TokenKind::Float(val.to_bits()));
        }
        let s = std::str::from_utf8(&self.input[start..self.pos]).unwrap();
        if let Ok(val) = s.parse::<i128>() {
            return Ok(TokenKind::Int(if negative { -val } else { val }));
        }
        let wide = crate::wide::Wide::from_str_radix(s, 10)
            .ok_or_else(|| format!("Invalid integer '{s}'"))?;
        let wide = if negative { wide.neg() } else { wide };
        Ok(match wide.to_i128() {
            Some(n) => TokenKind::Int(n),
            None => TokenKind::WideInt(Box::new(wide)),
        })
    }

    fn read_word(&mut self) -> String {
        let start = self.pos;
        while let Some(c) = self.peek() {
            if c.is_ascii_alphanumeric() || c == b'_' {
                self.advance();
            } else {
                break;
            }
        }
        String::from_utf8_lossy(&self.input[start..self.pos]).into_owned()
    }
}
