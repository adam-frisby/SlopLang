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
    Linear,
    Sync,
    Tuple,
    TypeKw,
    Comptime,
    Let,
    Mut,
    Rel,
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
    Try,
    Catch,
    Match,
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
    AtAlloc,
    AtRealloc,
    AtDealloc,
    AtMemcpy,
    AtMemmove,
    AtTransmute,
    AtForget,
    AtCAbi,
    AtAddUnchecked,
    AtSubUnchecked,
    AtMulUnchecked,
    AtBswap,
    AtInt,
    AtDefault,
    AtClone,
    AtDrop,
    AtFormat,
    AtTrap,
    AtSelect,
    AtInvert,
    AtDeclarations,

    // Identifiers & Literals
    Ident(String),
    Int(i128),
    Float(u64),
    RuneLit(char),
    Str(String),
    FStr(Vec<(String, Option<(String, String)>)>),

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
    FatArrow,
    Question,
    Eq,
    PlusEq,
    MinusEq,
    StarEq,
    Plus,
    PlusPercent,
    PlusPipe,
    PlusQuestion,
    Minus,
    MinusPercent,
    MinusPipe,
    MinusQuestion,
    Star,
    StarPercent,
    StarPipe,
    StarQuestion,
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

    fn consume_optional_int_suffix(&mut self) {
        if matches!(self.peek_char(), Some('i' | 'u')) {
            let saved_pos = self.pos;
            let saved_line = self.line;
            let saved_col = self.col;
            self.advance();
            let mut rest = String::new();
            while let Some(c) = self.peek_char() {
                if c.is_ascii_alphanumeric() || c == '_' {
                    rest.push(c);
                    self.advance();
                } else {
                    break;
                }
            }
            let valid = rest == "size"
                || (!rest.is_empty()
                    && rest.bytes().all(|b| b.is_ascii_digit())
                    && rest
                        .parse::<u16>()
                        .is_ok_and(|bits| (1..=512).contains(&bits)));
            if !valid {
                self.pos = saved_pos;
                self.line = saved_line;
                self.col = saved_col;
            }
        }
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
                        Some('?') => {
                            self.advance();
                            SurfTokenKind::PlusQuestion
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
                        Some('?') => {
                            self.advance();
                            SurfTokenKind::MinusQuestion
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
                        Some('?') => {
                            self.advance();
                            SurfTokenKind::StarQuestion
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
                    } else if self.peek_char() == Some('>') {
                        self.advance();
                        SurfTokenKind::FatArrow
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
                            _ => {
                                return Err(format!(
                                    "Unknown rune escape '\\{esc}' at {line}:{col}"
                                ));
                            }
                        }
                    } else {
                        c
                    };
                    if self.advance() != Some('\'') {
                        return Err(format!(
                            "Expected closing \"'\" for rune literal at {line}:{col}"
                        ));
                    }
                    SurfTokenKind::RuneLit(ch_val)
                }
                '"' => {
                    self.advance();
                    let mut s = String::new();
                    loop {
                        let c = self.advance().ok_or_else(|| {
                            format!("Unterminated string literal at {line}:{col}")
                        })?;
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
                                    ));
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
                        "alloc" => SurfTokenKind::AtAlloc,
                        "realloc" => SurfTokenKind::AtRealloc,
                        "dealloc" => SurfTokenKind::AtDealloc,
                        "memcpy" => SurfTokenKind::AtMemcpy,
                        "memmove" => SurfTokenKind::AtMemmove,
                        "transmute" => SurfTokenKind::AtTransmute,
                        "forget" => SurfTokenKind::AtForget,
                        "c_abi" => SurfTokenKind::AtCAbi,
                        "add_unchecked" => SurfTokenKind::AtAddUnchecked,
                        "sub_unchecked" => SurfTokenKind::AtSubUnchecked,
                        "mul_unchecked" => SurfTokenKind::AtMulUnchecked,
                        "bswap" => SurfTokenKind::AtBswap,
                        "Int" => SurfTokenKind::AtInt,
                        "default" => SurfTokenKind::AtDefault,
                        "clone" => SurfTokenKind::AtClone,
                        "drop" => SurfTokenKind::AtDrop,
                        "format" => SurfTokenKind::AtFormat,
                        "trap" => SurfTokenKind::AtTrap,
                        "select" => SurfTokenKind::AtSelect,
                        "invert" => SurfTokenKind::AtInvert,
                        "declarations" => SurfTokenKind::AtDeclarations,
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
                        self.consume_optional_int_suffix();
                        if hex.is_empty() {
                            return Err(format!("Invalid empty hex literal at {line}:{col}"));
                        }
                        let tail = if hex.len() > 32 {
                            &hex[hex.len() - 32..]
                        } else {
                            hex.as_str()
                        };
                        let val = u128::from_str_radix(tail, 16).map_err(|e| {
                            format!("Invalid hex literal 0x{hex} at {line}:{col}: {e}")
                        })? as i128;
                        SurfTokenKind::Int(val)
                    } else if c == '0' && matches!(self.peek_char_n(1), Some('b' | 'B')) {
                        self.advance();
                        self.advance();
                        let mut bin = String::new();
                        while let Some(bc) = self.peek_char() {
                            if bc == '0' || bc == '1' || bc == '_' {
                                if bc != '_' {
                                    bin.push(bc);
                                }
                                self.advance();
                            } else {
                                break;
                            }
                        }
                        self.consume_optional_int_suffix();
                        let val = u128::from_str_radix(&bin, 2).map_err(|e| {
                            format!("Invalid binary literal 0b{bin} at {line}:{col}: {e}")
                        })? as i128;
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
                            let f: f64 = num.parse().map_err(|e| {
                                format!("Invalid float '{num}' at {line}:{col}: {e}")
                            })?;
                            SurfTokenKind::Float(f.to_bits())
                        } else {
                            self.consume_optional_int_suffix();
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
                    if ident == "f" && self.peek_char() == Some('"') {
                        self.advance(); // consume opening '"'
                        let mut parts: Vec<(String, Option<(String, String)>)> = Vec::new();
                        let mut cur_lit = String::new();
                        loop {
                            let fc = self.advance().ok_or_else(|| {
                                format!("Unterminated f-string literal at {line}:{col}")
                            })?;
                            if fc == '"' {
                                break;
                            } else if fc == '\\' {
                                let esc = self.advance().ok_or_else(|| {
                                    format!("Unterminated escape in f-string at {line}:{col}")
                                })?;
                                match esc {
                                    'n' => cur_lit.push('\n'),
                                    'r' => cur_lit.push('\r'),
                                    't' => cur_lit.push('\t'),
                                    '0' => cur_lit.push('\0'),
                                    '\\' => cur_lit.push('\\'),
                                    '"' => cur_lit.push('"'),
                                    _ => {
                                        return Err(format!(
                                            "Unknown f-string escape '\\{esc}' at {line}:{col}"
                                        ));
                                    }
                                }
                            } else if fc == '{' {
                                if self.peek_char() == Some('{') {
                                    self.advance();
                                    cur_lit.push('{');
                                    continue;
                                }
                                if !cur_lit.is_empty() {
                                    parts.push((std::mem::take(&mut cur_lit), None));
                                }
                                let mut inner = String::new();
                                let mut depth = 0usize;
                                let mut split_colon_idx: Option<usize> = None;
                                loop {
                                    let ic = self.advance().ok_or_else(|| {
                                        format!(
                                            "Unterminated '{{...}}' in f-string at {line}:{col}"
                                        )
                                    })?;
                                    if ic == '}' && depth == 0 {
                                        break;
                                    }
                                    match ic {
                                        '(' | '[' | '{' => depth += 1,
                                        ')' | ']' | '}' => depth = depth.saturating_sub(1),
                                        ':' if depth == 0 && split_colon_idx.is_none() => {
                                            if self.peek_char() == Some(':') {
                                                inner.push(':');
                                                let next_c = self.advance().unwrap();
                                                inner.push(next_c);
                                                continue;
                                            } else {
                                                split_colon_idx = Some(inner.len());
                                                inner.push(':');
                                                continue;
                                            }
                                        }
                                        _ => {}
                                    }
                                    inner.push(ic);
                                }
                                let (expr_src, spec_src) = if let Some(idx) = split_colon_idx {
                                    (
                                        inner[..idx].trim().to_string(),
                                        inner[idx + 1..].trim().to_string(),
                                    )
                                } else {
                                    (inner.trim().to_string(), String::new())
                                };
                                parts.push((String::new(), Some((expr_src, spec_src))));
                            } else if fc == '}' {
                                if self.peek_char() == Some('}') {
                                    self.advance();
                                    cur_lit.push('}');
                                } else {
                                    return Err(format!(
                                        "Unmatched '}}' in f-string at {line}:{col} (use '}}}}' to escape)"
                                    ));
                                }
                            } else {
                                cur_lit.push(fc);
                            }
                        }
                        if !cur_lit.is_empty() || parts.is_empty() {
                            parts.push((cur_lit, None));
                        }
                        SurfTokenKind::FStr(parts)
                    } else {
                        match ident.as_str() {
                            "import" => SurfTokenKind::Import,
                            "pub" => SurfTokenKind::Pub,
                            "pkg" => SurfTokenKind::Pkg,
                            "fn" => SurfTokenKind::Fn,
                            "extern" => SurfTokenKind::Extern,
                            "record" => SurfTokenKind::Record,
                            "struct" => SurfTokenKind::Struct,
                            "linear" => SurfTokenKind::Linear,
                            "sync" => SurfTokenKind::Sync,
                            "tuple" => SurfTokenKind::Tuple,
                            "type" => SurfTokenKind::TypeKw,
                            "comptime" => SurfTokenKind::Comptime,
                            "let" => SurfTokenKind::Let,
                            "mut" => SurfTokenKind::Mut,
                            "rel" => SurfTokenKind::Rel,
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
                            "try" => SurfTokenKind::Try,
                            "catch" => SurfTokenKind::Catch,
                            "match" => SurfTokenKind::Match,
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
                                if let Some(rest) =
                                    s.strip_prefix('i').or_else(|| s.strip_prefix('u'))
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
                }
                _ => return Err(format!("Unexpected character '{ch}' at {line}:{col}")),
            };

            tokens.push(SurfToken { kind, line, col });
        }
        Ok(tokens)
    }
}
