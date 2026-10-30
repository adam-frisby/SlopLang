#[derive(Debug, Clone, PartialEq)]
pub enum SurfTokenKind {
    // Keywords
    Import,
    Pub,
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
    Break,
    Continue,
    AtCAbi,
    AtSizeOf,
    AtAlignOf,
    AtAddUnchecked,
    AtSubUnchecked,
    AtMulUnchecked,
    AtBswap,
    AtAtomic(crate::ast::AtomicOp),
    AtInt,
    AtDefault,
    AtClone,
    AtDrop,
    AtFormat,
    AtTrap,
    AtCompileError,
    AtSelect,
    AtInvert,
    AtDeclarations,
    AtTypeName,
    AtSatisfies,
    AtFields,
    AtLeaves,
    AtHasField,
    AtVariants,
    AtBackingType,
    AtEntries,
    AtFnInfo,
    AtField,
    AtVariant,
    AtMakeUnion,
    AtStruct,
    AtPackedStruct,
    AtTuple,
    AtEnum,
    AtUnion,
    AtError,
    AtMap,

    // Identifiers & Literals
    Ident(String),
    Int(i128),
    /// An integer literal that does not fit in `i128` (up to 512-bit `u512` values).
    WideInt(Box<crate::wide::Wide>),
    Float(u64),
    RuneLit(char),
    /// A byte literal `b'a'` (type `u8`).
    ByteLit(u8),
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

    /// Lexes the body of a rune (`'a'`) or byte (`b'a'`) literal after its opening quote, through
    /// the closing quote. Escapes: `\n \r \t \0 \\ \' \"`, `\xNN` (any byte in a byte literal,
    /// ASCII in a rune literal), and `\u{...}` (runes only).
    fn lex_char_literal(&mut self, byte: bool, line: usize, col: usize) -> Result<u32, String> {
        let kind = if byte { "byte" } else { "rune" };
        let c = self
            .advance()
            .ok_or_else(|| format!("Unterminated {kind} literal at {line}:{col}"))?;
        let v = if c == '\\' {
            let esc = self
                .advance()
                .ok_or_else(|| format!("Unterminated escape at {line}:{col}"))?;
            match esc {
                'n' => 0x0A,
                'r' => 0x0D,
                't' => 0x09,
                '0' => 0,
                '\\' => u32::from('\\'),
                '\'' => u32::from('\''),
                '"' => u32::from('"'),
                'x' => {
                    let hex: String = [self.advance(), self.advance()].iter().flatten().collect();
                    let v = u32::from_str_radix(&hex, 16).map_err(|_| {
                        format!("Invalid '\\x' escape in {kind} literal at {line}:{col}")
                    })?;
                    if !byte && v > 0x7F {
                        return Err(format!(
                            "'\\x{hex}' is not ASCII; use '\\u{{{hex}}}' in rune literals at {line}:{col}"
                        ));
                    }
                    v
                }
                'u' if !byte => {
                    if self.advance() != Some('{') {
                        return Err(format!("Expected '{{' after '\\u' at {line}:{col}"));
                    }
                    let mut hex = String::new();
                    while let Some(h) = self.peek_char() {
                        self.advance();
                        if h == '}' {
                            break;
                        }
                        hex.push(h);
                    }
                    let v = u32::from_str_radix(&hex, 16)
                        .map_err(|_| format!("Invalid '\\u{{{hex}}}' escape at {line}:{col}"))?;
                    if char::from_u32(v).is_none() {
                        return Err(format!(
                            "'\\u{{{hex}}}' is not a Unicode scalar value at {line}:{col}"
                        ));
                    }
                    v
                }
                _ => {
                    return Err(format!(
                        "Unknown {kind} escape '\\{esc}' at {line}:{col}"
                    ));
                }
            }
        } else {
            if byte && !c.is_ascii() {
                return Err(format!(
                    "Byte literal must be ASCII (use '\\x..' for other bytes) at {line}:{col}"
                ));
            }
            u32::from(c)
        };
        if self.advance() != Some('\'') {
            return Err(format!(
                "Expected closing \"'\" for {kind} literal at {line}:{col}"
            ));
        }
        Ok(v)
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
                    let v = self.lex_char_literal(false, line, col)?;
                    let ch_val = char::from_u32(v).ok_or_else(|| {
                        format!("Invalid rune literal U+{v:X} at {line}:{col}")
                    })?;
                    SurfTokenKind::RuneLit(ch_val)
                }
                'b' if self.peek_char_n(1) == Some('\'') => {
                    self.advance();
                    self.advance();
                    let v = self.lex_char_literal(true, line, col)?;
                    SurfTokenKind::ByteLit(v as u8)
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
                        "size_of" => SurfTokenKind::AtSizeOf,
                        "align_of" => SurfTokenKind::AtAlignOf,
                        "add_unchecked" => SurfTokenKind::AtAddUnchecked,
                        "sub_unchecked" => SurfTokenKind::AtSubUnchecked,
                        "mul_unchecked" => SurfTokenKind::AtMulUnchecked,
                        "bswap" => SurfTokenKind::AtBswap,
                        n if n.strip_prefix("atomic_").and_then(crate::ast::AtomicOp::from_name).is_some() => {
                            SurfTokenKind::AtAtomic(
                                crate::ast::AtomicOp::from_name(&n["atomic_".len()..]).unwrap(),
                            )
                        }
                        "Int" => SurfTokenKind::AtInt,
                        "default" => SurfTokenKind::AtDefault,
                        "clone" => SurfTokenKind::AtClone,
                        "drop" => SurfTokenKind::AtDrop,
                        "format" => SurfTokenKind::AtFormat,
                        "trap" => SurfTokenKind::AtTrap,
                        "compile_error" => SurfTokenKind::AtCompileError,
                        "select" => SurfTokenKind::AtSelect,
                        "invert" => SurfTokenKind::AtInvert,
                        "declarations" => SurfTokenKind::AtDeclarations,
                        "type_name" => SurfTokenKind::AtTypeName,
                        "satisfies" => SurfTokenKind::AtSatisfies,
                        "fields" => SurfTokenKind::AtFields,
                        "leaves" => SurfTokenKind::AtLeaves,
                        "has_field" => SurfTokenKind::AtHasField,
                        "variants" => SurfTokenKind::AtVariants,
                        "backing_type" => SurfTokenKind::AtBackingType,
                        "entries" => SurfTokenKind::AtEntries,
                        "fn_info" => SurfTokenKind::AtFnInfo,
                        "field" => SurfTokenKind::AtField,
                        "variant" => SurfTokenKind::AtVariant,
                        "make_union" => SurfTokenKind::AtMakeUnion,
                        "Struct" => SurfTokenKind::AtStruct,
                        "PackedStruct" => SurfTokenKind::AtPackedStruct,
                        "Tuple" => SurfTokenKind::AtTuple,
                        "Enum" => SurfTokenKind::AtEnum,
                        "Union" => SurfTokenKind::AtUnion,
                        "Error" => SurfTokenKind::AtError,
                        "Map" => SurfTokenKind::AtMap,
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
                        int_literal_token(&hex, 16, "0x", line, col)?
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
                        int_literal_token(&bin, 2, "0b", line, col)?
                    } else {
                        let mut num = String::new();
                        let mut is_float = false;
                        // After `.`, digits are a tuple index: `t.1.0` is `t . 1 . 0`.
                        let tuple_index = tokens
                            .last()
                            .is_some_and(|t: &SurfToken| t.kind == SurfTokenKind::Dot);
                        while let Some(nc) = self.peek_char() {
                            if nc.is_ascii_digit() || nc == '_' {
                                if nc != '_' {
                                    num.push(nc);
                                }
                                self.advance();
                            } else if nc == '.'
                                && !tuple_index
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
                            int_literal_token(&num, 10, "", line, col)?
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
                            "break" => SurfTokenKind::Break,
                            "continue" => SurfTokenKind::Continue,
                            "unsafe" => SurfTokenKind::Unsafe,
                            "move" => SurfTokenKind::Move,
                            "as" => SurfTokenKind::As,
                            "in" => SurfTokenKind::In,
                            "orelse" => SurfTokenKind::OrElse,
                            "try" => SurfTokenKind::Try,
                            "catch" => SurfTokenKind::Catch,
                            "match" => SurfTokenKind::Match,
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

/// An integer literal token: `Int` when the value fits in `i128`, otherwise `WideInt` (literals of
/// up to 512 bits are representable; larger ones are rejected).
fn int_literal_token(
    digits: &str,
    radix: u32,
    prefix: &str,
    line: usize,
    col: usize,
) -> Result<SurfTokenKind, String> {
    let Some(v) = crate::wide::Wide::from_str_radix(digits, radix)
        .filter(|v| v.fits(512, false))
    else {
        return Err(format!(
            "Invalid integer literal '{prefix}{digits}' at {line}:{col}: wider than 512 bits"
        ));
    };
    Ok(match v.to_i128() {
        Some(n) => SurfTokenKind::Int(n),
        None => SurfTokenKind::WideInt(Box::new(v)),
    })
}
