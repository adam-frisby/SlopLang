use super::*;

impl SurfaceParser {
    /// Parses the head expression of `if` / `while` / `for` / `match`, where `x {}` is `x`
    /// followed by an empty block (an empty struct literal there needs parentheses).
    pub(super) fn parse_cond_expr(&mut self) -> Result<Expr, String> {
        let saved = self.cond_start.replace(self.pos);
        let res = self.parse_expr();
        self.cond_start = saved;
        res
    }

    /// Whether `name {}` may be an empty struct literal here: anywhere except the top level of
    /// a condition (see `cond_start`).
    fn empty_struct_lit_allowed(&self) -> bool {
        let Some(start) = self.cond_start else {
            return true;
        };
        let mut depth = 0i32;
        for tok in &self.tokens[start..self.pos] {
            match tok.kind {
                SurfTokenKind::LParen | SurfTokenKind::LBracket => depth += 1,
                SurfTokenKind::RParen | SurfTokenKind::RBracket => depth -= 1,
                _ => {}
            }
        }
        depth > 0
    }

    /// Whether `defer` starts a deferred statement here, rather than naming a variable: it is
    /// followed by what starts a statement (`defer g.unlock();`, `defer { ... }`).
    fn defer_ahead(&self) -> bool {
        matches!(&self.peek().kind, SurfTokenKind::Ident(s) if s == "defer" || s == "errdefer")
            && matches!(
                self.peek_n(1).kind,
                SurfTokenKind::Ident(_)
                    | SurfTokenKind::LBrace
                    | SurfTokenKind::Pipe
                    | SurfTokenKind::Unsafe
                    | SurfTokenKind::Star
                    | SurfTokenKind::If
                    | SurfTokenKind::While
                    | SurfTokenKind::Match
                    | SurfTokenKind::Return
                    | SurfTokenKind::Break
                    | SurfTokenKind::Continue
            )
    }

    pub(super) fn parse_block(&mut self) -> Result<Block, String> {
        let saved = self.cond_start.take();
        let res = self.parse_block_inner();
        self.cond_start = saved;
        res
    }

    fn parse_block_inner(&mut self) -> Result<Block, String> {
        self.expect(&SurfTokenKind::LBrace)?;
        let (mut stmts, mut lines) = (Vec::new(), Vec::new());
        while self.peek().kind != SurfTokenKind::RBrace && self.peek().kind != SurfTokenKind::Eof {
            lines.push(self.src_pos());
            stmts.push(self.parse_stmt()?);
        }
        lines.push(self.src_pos());
        self.expect(&SurfTokenKind::RBrace)?;
        Ok(Block { stmts, lines })
    }

    pub(super) fn parse_expr_block(&mut self) -> Result<Block, String> {
        self.expect(&SurfTokenKind::LBrace)?;
        let (mut stmts, mut lines) = (Vec::new(), Vec::new());
        let mut line = Pos::default();
        while self.peek().kind != SurfTokenKind::RBrace && self.peek().kind != SurfTokenKind::Eof {
            lines.resize(stmts.len(), line);
            line = self.src_pos();
            let is_for = matches!(&self.peek().kind, SurfTokenKind::Ident(s) if s == "for");
            let is_labeled = matches!(&self.peek().kind, SurfTokenKind::Ident(_))
                && self.peek_n(1).kind == SurfTokenKind::Colon
                && (self.peek_n(2).kind == SurfTokenKind::While
                    || self.peek_n(2).kind == SurfTokenKind::LBrace
                    || matches!(&self.peek_n(2).kind, SurfTokenKind::Ident(s) if s == "for"));
            if is_for || is_labeled || self.defer_ahead() || matches!(
                self.peek().kind,
                SurfTokenKind::Let
                    | SurfTokenKind::Comptime
                    | SurfTokenKind::Const
                    | SurfTokenKind::If
                    | SurfTokenKind::While
                    | SurfTokenKind::Match
                    | SurfTokenKind::AtSelect
                    | SurfTokenKind::Return
                    | SurfTokenKind::Unsafe
            ) {
                stmts.push(self.parse_stmt()?);
            } else if self.peek().kind == SurfTokenKind::LBrace {
                let saved = self.pos;
                if let Ok(expr) = self.parse_expr()
                    && self.peek().kind == SurfTokenKind::RBrace
                {
                    stmts.push(Stmt::Expr(expr));
                } else {
                    self.pos = saved;
                    stmts.push(self.parse_stmt()?);
                }
            } else {
                let expr = self.parse_expr()?;
                match &self.peek().kind {
                    SurfTokenKind::Eq => {
                        self.advance();
                        let value = self.parse_expr()?;
                        self.expect(&SurfTokenKind::Semi)?;
                        stmts.push(Stmt::Assign {
                            target: expr,
                            op: None,
                            value,
                        });
                    }
                    kind if compound_assign_op(kind).is_some() => {
                        let op = compound_assign_op(kind).unwrap();
                        self.advance();
                        let value = self.parse_expr()?;
                        self.expect(&SurfTokenKind::Semi)?;
                        stmts.push(Stmt::Assign {
                            target: expr,
                            op: Some(op),
                            value,
                        });
                    }
                    SurfTokenKind::RBrace => {
                        stmts.push(Stmt::Expr(expr));
                    }
                    _ => {
                        if !matches!(expr, Expr::Uncancelled(_) | Expr::UnsafeBlock(_))
                            || self.peek().kind == SurfTokenKind::Semi
                        {
                            self.expect(&SurfTokenKind::Semi)?;
                        }
                        stmts.push(Stmt::Expr(expr));
                    }
                }
            }
        }
        let close = self.src_pos();
        self.expect(&SurfTokenKind::RBrace)?;
        lines.resize(stmts.len(), line);
        lines.push(close);
        Ok(Block { stmts, lines })
    }

    pub(super) fn parse_match_arms(&mut self) -> Result<Vec<(MatchPat, Expr)>, String> {
        self.expect(&SurfTokenKind::LBrace)?;
        let mut arms = Vec::new();
        while self.peek().kind != SurfTokenKind::RBrace && self.peek().kind != SurfTokenKind::Eof {
            let pat = self.parse_match_pat()?;
            self.expect(&SurfTokenKind::FatArrow)?;
            let is_block_arm = self.peek().kind == SurfTokenKind::LBrace;
            let body = if is_block_arm {
                Expr::Block(self.parse_expr_block()?)
            } else {
                self.parse_expr()?
            };
            arms.push((pat, body));
            if self.peek().kind == SurfTokenKind::Comma {
                self.advance();
            } else if !is_block_arm && self.peek().kind != SurfTokenKind::RBrace {
                return Err(format!(
                    "Expected ',' or '}}' after match arm (line {}, column {})",
                    self.peek().line,
                    self.peek().col
                ));
            }
        }
        self.expect(&SurfTokenKind::RBrace)?;
        Ok(arms)
    }

    pub(super) fn parse_select_arms(&mut self) -> Result<Vec<SelectArm>, String> {
        self.expect(&SurfTokenKind::LBrace)?;
        let mut arms = Vec::new();
        while self.peek().kind != SurfTokenKind::RBrace && self.peek().kind != SurfTokenKind::Eof {
            let op = if matches!(&self.peek().kind, SurfTokenKind::Ident(s) if s == "default")
                || (matches!(&self.peek().kind, SurfTokenKind::Ident(s) if s == "_")
                    && self.peek_n(1).kind == SurfTokenKind::FatArrow)
            {
                self.advance();
                SelectOp::Default
            } else {
                let mut bind: Option<String> = None;
                if self.peek().kind == SurfTokenKind::Let {
                    self.advance();
                    if self.peek().kind == SurfTokenKind::Mut {
                        self.advance();
                    }
                    let name = self.expect_ident()?;
                    self.expect(&SurfTokenKind::Eq)?;
                    if name != "_" {
                        bind = Some(name);
                    }
                } else if let SurfTokenKind::Ident(name) = self.peek().kind.clone()
                    && self.peek_n(1).kind == SurfTokenKind::Eq
                {
                    self.advance();
                    self.advance();
                    if name != "_" {
                        bind = Some(name);
                    }
                }
                let op_expr = self.parse_expr()?;
                match op_expr {
                    Expr::MethodCall {
                        receiver,
                        method,
                        args,
                        ..
                    } if (method == "recv" || method == "wait" || method == "await")
                        && args.is_empty() =>
                    {
                        let is_await = method == "await";
                        let loser = if is_await && self.peek().kind == SurfTokenKind::Else {
                            self.advance();
                            self.expect(&SurfTokenKind::Pipe)?;
                            let name = self.expect_ident()?;
                            self.expect(&SurfTokenKind::Pipe)?;
                            let handler = if self.peek().kind == SurfTokenKind::LBrace {
                                Expr::Block(self.parse_expr_block()?)
                            } else {
                                self.parse_expr()?
                            };
                            Some((name, Box::new(handler)))
                        } else {
                            None
                        };
                        SelectOp::Recv {
                            bind,
                            source: *receiver,
                            is_await,
                            loser,
                        }
                    }
                    Expr::MethodCall {
                        receiver,
                        method,
                        mut args,
                        ..
                    } if method == "send" && args.len() == 1 => {
                        if bind.is_some() {
                            return Err(format!(
                                "Cannot bind a variable to a '.send(...)' branch in '@select' (line {}, column {})",
                                self.peek().line,
                                self.peek().col
                            ));
                        }
                        let unsent = if self.peek().kind == SurfTokenKind::Else {
                            self.advance();
                            self.expect(&SurfTokenKind::Pipe)?;
                            let name = self.expect_ident()?;
                            self.expect(&SurfTokenKind::Pipe)?;
                            let handler = if self.peek().kind == SurfTokenKind::LBrace {
                                Expr::Block(self.parse_expr_block()?)
                            } else {
                                self.parse_expr()?
                            };
                            Some((name, Box::new(handler)))
                        } else {
                            None
                        };
                        SelectOp::Send {
                            channel: *receiver,
                            value: args.remove(0),
                            unsent,
                        }
                    }
                    Expr::Call {
                        callee,
                        args,
                        ..
                    } if args.is_empty()
                        && matches!(
                            callee.as_ref(),
                            Expr::Path(p) if p.last().is_some_and(|s| s == "check_cancelled")
                        ) =>
                    {
                        SelectOp::Cancelled { bind }
                    }
                    _ => {
                        return Err(format!(
                            "Expected '.recv()', '.send(val)', '.wait()', '.await()', 'check_cancelled()', or 'default' in '@select' arm (line {}, column {})",
                            self.peek().line,
                            self.peek().col
                        ));
                    }
                }
            };
            self.expect(&SurfTokenKind::FatArrow)?;
            let is_block_arm = self.peek().kind == SurfTokenKind::LBrace;
            let body = if is_block_arm {
                Expr::Block(self.parse_expr_block()?)
            } else {
                self.parse_expr()?
            };
            arms.push(SelectArm { op, body });
            if self.peek().kind == SurfTokenKind::Comma {
                self.advance();
            } else if !is_block_arm && self.peek().kind != SurfTokenKind::RBrace {
                return Err(format!(
                    "Expected ',' or '}}' after '@select' arm (line {}, column {})",
                    self.peek().line,
                    self.peek().col
                ));
            }
        }
        self.expect(&SurfTokenKind::RBrace)?;
        Ok(arms)
    }

    pub(super) fn parse_match_pat(&mut self) -> Result<MatchPat, String> {
        let first = self.parse_match_pat_single()?;
        if self.peek().kind != SurfTokenKind::Pipe {
            return Ok(first);
        }
        let mut pats = vec![first];
        while self.peek().kind == SurfTokenKind::Pipe {
            self.advance();
            pats.push(self.parse_match_pat_single()?);
        }
        Ok(MatchPat::Or(pats))
    }

    fn parse_match_pat_single(&mut self) -> Result<MatchPat, String> {
        let lo = self.parse_match_pat_atom()?;
        if self.peek().kind == SurfTokenKind::DotDotEq {
            self.advance();
            let hi = self.parse_match_pat_atom()?;
            return Ok(MatchPat::Range {
                lo: Box::new(lo),
                hi: Box::new(hi),
            });
        }
        if self.peek().kind == SurfTokenKind::DotDot {
            let tok = self.peek();
            return Err(format!(
                "Exclusive range '..' is not supported in match patterns; use an inclusive range '..=' (line {}, column {})",
                tok.line, tok.col
            ));
        }
        Ok(lo)
    }

    fn parse_match_pat_atom(&mut self) -> Result<MatchPat, String> {
        match &self.peek().kind {
            SurfTokenKind::Ident(s)
                if s == "_" && self.peek_n(1).kind != SurfTokenKind::ColonColon =>
            {
                self.advance();
                Ok(MatchPat::Wildcard)
            }
            SurfTokenKind::Null => {
                self.advance();
                Ok(MatchPat::Null)
            }
            SurfTokenKind::True => {
                self.advance();
                Ok(MatchPat::Bool(true))
            }
            SurfTokenKind::False => {
                self.advance();
                Ok(MatchPat::Bool(false))
            }
            SurfTokenKind::RuneLit(ch) => {
                let ch = *ch;
                self.advance();
                Ok(MatchPat::Rune(ch))
            }
            SurfTokenKind::ByteLit(b) => {
                let val = i128::from(*b);
                self.advance();
                Ok(MatchPat::Int(val))
            }
            // `b"GET"` matches what `[71, 69, 84]` does: an array or slice of exactly those bytes.
            SurfTokenKind::ByteStr(bytes) => {
                let elems = bytes.iter().map(|b| MatchPat::Int(i128::from(*b))).collect();
                self.advance();
                Ok(MatchPat::Seq { elems, rest: None, bracketed: true })
            }
            SurfTokenKind::Str(s) => {
                let s = s.clone();
                self.advance();
                Ok(MatchPat::Str(s))
            }
            SurfTokenKind::Int(n) => {
                let val = *n;
                self.advance();
                if matches!(self.peek().kind, SurfTokenKind::IntSuffix(_)) {
                    self.advance();
                }
                Ok(MatchPat::Int(val))
            }
            SurfTokenKind::WideInt(w) => {
                let val = w.clone();
                self.advance();
                if matches!(self.peek().kind, SurfTokenKind::IntSuffix(_)) {
                    self.advance();
                }
                Ok(MatchPat::WideInt(val))
            }
            SurfTokenKind::Float(bits) => {
                let val = *bits;
                self.advance();
                if matches!(self.peek().kind, SurfTokenKind::IntSuffix(_)) {
                    self.advance();
                }
                Ok(MatchPat::Float(val))
            }
            SurfTokenKind::Minus => {
                self.advance();
                match self.advance().kind {
                    SurfTokenKind::Int(n) => {
                        if matches!(self.peek().kind, SurfTokenKind::IntSuffix(_)) {
                            self.advance();
                        }
                        Ok(MatchPat::Int(-n))
                    }
                    SurfTokenKind::WideInt(w) => {
                        if matches!(self.peek().kind, SurfTokenKind::IntSuffix(_)) {
                            self.advance();
                        }
                        Ok(MatchPat::WideInt(Box::new(w.neg())))
                    }
                    SurfTokenKind::Float(bits) => {
                        if matches!(self.peek().kind, SurfTokenKind::IntSuffix(_)) {
                            self.advance();
                        }
                        Ok(MatchPat::Float((-f64::from_bits(bits)).to_bits()))
                    }
                    other => Err(format!(
                        "Expected integer or float literal after '-' in match pattern, found {:?}",
                        other
                    )),
                }
            }
            SurfTokenKind::Move => {
                self.advance();
                let name = self.expect_ident()?;
                Ok(MatchPat::CatchAllBind {
                    mode: BindMode::Move,
                    name,
                })
            }
            SurfTokenKind::Ident(s)
                if s == "ref"
                    && matches!(
                        self.peek_n(1).kind,
                        SurfTokenKind::Ident(_) | SurfTokenKind::Mut
                    ) =>
            {
                self.advance();
                let mutable = if self.peek().kind == SurfTokenKind::Mut {
                    self.advance();
                    true
                } else {
                    false
                };
                let name = self.expect_ident()?;
                Ok(MatchPat::CatchAllBind {
                    mode: BindMode::Ref { mutable },
                    name,
                })
            }
            SurfTokenKind::Dot => {
                self.advance();
                let name = self.expect_ident()?;
                let payload = if self.peek().kind == SurfTokenKind::LParen {
                    Some(Box::new(self.parse_variant_payload_pat()?))
                } else if self.peek().kind == SurfTokenKind::LBrace {
                    Some(Box::new(self.parse_brace_match_pat(None)?))
                } else {
                    None
                };
                Ok(MatchPat::DotVariant { name, payload })
            }
            SurfTokenKind::LParen => {
                self.parse_seq_match_pat(SurfTokenKind::LParen, SurfTokenKind::RParen, false)
            }
            SurfTokenKind::LBracket => {
                self.parse_seq_match_pat(SurfTokenKind::LBracket, SurfTokenKind::RBracket, true)
            }
            SurfTokenKind::LBrace => self.parse_brace_match_pat(None),
            SurfTokenKind::Ident(_)
            | SurfTokenKind::SelfType
            | SurfTokenKind::Isize
            | SurfTokenKind::Usize
            | SurfTokenKind::IntType { .. } => {
                let first_seg = match &self.peek().kind {
                    SurfTokenKind::Ident(_) => self.expect_ident()?,
                    SurfTokenKind::SelfType => {
                        self.advance();
                        "Self".to_string()
                    }
                    SurfTokenKind::Isize => {
                        self.advance();
                        "isize".to_string()
                    }
                    SurfTokenKind::Usize => {
                        self.advance();
                        "usize".to_string()
                    }
                    SurfTokenKind::IntType { signed, bits } => {
                        let s = format!("{}{}", if *signed { "i" } else { "u" }, bits);
                        self.advance();
                        s
                    }
                    _ => unreachable!(),
                };
                let mut path = vec![first_seg];
                while self.peek().kind == SurfTokenKind::ColonColon {
                    self.advance();
                    path.push(self.expect_ident()?);
                }
                // `Maybe[i32]::Some(v)`, `Pair[i32] { .. }`: no pattern follows a name with `[`.
                if self.peek().kind == SurfTokenKind::LBracket {
                    let args = self.parse_comptime_args()?;
                    let ty = TypeExpr::TypeCall { path, args };
                    let pat = if self.peek().kind == SurfTokenKind::ColonColon {
                        self.advance();
                        let variant = self.expect_ident()?;
                        let payload = if self.peek().kind == SurfTokenKind::LParen {
                            Some(Box::new(self.parse_variant_payload_pat()?))
                        } else {
                            None
                        };
                        MatchPat::Variant {
                            path: vec![variant],
                            payload,
                        }
                    } else {
                        self.parse_brace_match_pat(Some(Vec::new()))?
                    };
                    return Ok(MatchPat::TypeQualified {
                        ty,
                        pat: Box::new(pat),
                    });
                }
                if self.peek().kind == SurfTokenKind::LBrace {
                    self.parse_brace_match_pat(Some(path))
                } else if self.peek().kind == SurfTokenKind::LParen {
                    Ok(MatchPat::Variant {
                        path,
                        payload: Some(Box::new(self.parse_variant_payload_pat()?)),
                    })
                } else if path.len() >= 2 {
                    Ok(MatchPat::Variant {
                        path,
                        payload: None,
                    })
                } else {
                    Ok(MatchPat::CatchAllBind {
                        mode: BindMode::Default,
                        name: path.into_iter().next().unwrap(),
                    })
                }
            }
            _ => {
                let tok = self.peek();
                Err(format!(
                    "Expected match pattern, found {:?} (line {}, column {})",
                    tok.kind, tok.line, tok.col
                ))
            }
        }
    }

    /// Parses the `(pat)` or `(p1, p2, ...)` payload of a variant pattern.
    fn parse_variant_payload_pat(&mut self) -> Result<MatchPat, String> {
        self.parse_seq_match_pat(SurfTokenKind::LParen, SurfTokenKind::RParen, false)
    }

    /// Parses `( ... )`, `[ ... ]`, or `{ ... }` sequence patterns with optional `..`.
    fn parse_seq_match_pat(
        &mut self,
        open: SurfTokenKind,
        close: SurfTokenKind,
        bracketed: bool,
    ) -> Result<MatchPat, String> {
        self.expect(&open)?;
        let mut elems = Vec::new();
        let mut rest = None;
        let mut has_comma = false;
        while self.peek().kind != close && self.peek().kind != SurfTokenKind::Eof {
            if self.peek().kind == SurfTokenKind::DotDot {
                if rest.is_some() {
                    let tok = self.peek();
                    return Err(format!(
                        "Pattern may contain at most one '..' rest pattern (line {}, column {})",
                        tok.line, tok.col
                    ));
                }
                rest = Some(elems.len());
                self.advance();
            } else {
                elems.push(self.parse_match_pat()?);
            }
            if self.peek().kind == SurfTokenKind::Comma {
                has_comma = true;
                self.advance();
            } else {
                break;
            }
        }
        self.expect(&close)?;
        if open == SurfTokenKind::LParen && elems.len() == 1 && !has_comma && rest.is_none() {
            return Ok(elems.into_iter().next().unwrap());
        }
        Ok(MatchPat::Seq {
            elems,
            rest,
            bracketed,
        })
    }

    /// Parses `Path { ... }` (always a struct pattern) or `{ ... }` (a struct pattern if it has
    /// `field: pat`, otherwise a sequence/shorthand pattern).
    fn parse_brace_match_pat(&mut self, path: Option<Vec<String>>) -> Result<MatchPat, String> {
        let is_struct = path.is_some() || self.brace_has_colon_field();
        if !is_struct {
            return self.parse_seq_match_pat(SurfTokenKind::LBrace, SurfTokenKind::RBrace, false);
        }
        self.expect(&SurfTokenKind::LBrace)?;
        let mut fields = Vec::new();
        let mut rest = false;
        while self.peek().kind != SurfTokenKind::RBrace && self.peek().kind != SurfTokenKind::Eof {
            if self.peek().kind == SurfTokenKind::DotDot {
                self.advance();
                rest = true;
                if self.peek().kind == SurfTokenKind::Comma {
                    self.advance();
                }
                break;
            }
            let mode = if self.peek().kind == SurfTokenKind::Move {
                self.advance();
                Some(BindMode::Move)
            } else if matches!(&self.peek().kind, SurfTokenKind::Ident(s) if s == "ref")
                && matches!(
                    self.peek_n(1).kind,
                    SurfTokenKind::Ident(_) | SurfTokenKind::Mut
                )
            {
                self.advance();
                let mutable = if self.peek().kind == SurfTokenKind::Mut {
                    self.advance();
                    true
                } else {
                    false
                };
                Some(BindMode::Ref { mutable })
            } else {
                None
            };
            let fname = self.expect_ident()?;
            let fpat = if mode.is_none() && self.peek().kind == SurfTokenKind::Colon {
                self.advance();
                self.parse_match_pat()?
            } else {
                MatchPat::CatchAllBind {
                    mode: mode.unwrap_or(BindMode::Default),
                    name: fname.clone(),
                }
            };
            fields.push((fname, fpat));
            if self.peek().kind == SurfTokenKind::Comma {
                self.advance();
            } else {
                break;
            }
        }
        self.expect(&SurfTokenKind::RBrace)?;
        Ok(MatchPat::Struct { path, fields, rest })
    }

    /// Whether the current `{ ... }` pattern contains a top-level `field: pat` entry.
    fn brace_has_colon_field(&self) -> bool {
        let mut k = 1;
        let mut depth = 0usize;
        loop {
            match &self.peek_n(k).kind {
                SurfTokenKind::Eof => return false,
                SurfTokenKind::LBrace | SurfTokenKind::LParen | SurfTokenKind::LBracket => {
                    depth += 1;
                }
                SurfTokenKind::RBrace => {
                    if depth == 0 {
                        return false;
                    }
                    depth -= 1;
                }
                SurfTokenKind::RParen | SurfTokenKind::RBracket => {
                    depth = depth.saturating_sub(1);
                }
                SurfTokenKind::Colon if depth == 0 => return true,
                _ => {}
            }
            k += 1;
        }
    }

    /// Whether a `let` pattern follows: `{ ... }` (tuple) or `Path { ... }` (struct).
    fn destructure_ahead(&self) -> bool {
        if self.peek().kind == SurfTokenKind::LBrace {
            return true;
        }
        let mut k = 0;
        while matches!(self.peek_n(k).kind, SurfTokenKind::Ident(_)) {
            match self.peek_n(k + 1).kind {
                SurfTokenKind::ColonColon => k += 2,
                SurfTokenKind::LBrace => return true,
                SurfTokenKind::LBracket => {
                    // `Pair[i32] {`: past the arguments, a brace.
                    let mut depth = 0usize;
                    let mut at = k + 1;
                    loop {
                        match self.peek_n(at).kind {
                            SurfTokenKind::LBracket => depth += 1,
                            SurfTokenKind::RBracket => {
                                depth -= 1;
                                if depth == 0 {
                                    break;
                                }
                            }
                            SurfTokenKind::Eof | SurfTokenKind::Semi => return false,
                            _ => {}
                        }
                        at += 1;
                    }
                    return self.peek_n(at + 1).kind == SurfTokenKind::LBrace;
                }
                _ => return false,
            }
        }
        false
    }

    /// `let { a, b, .. } = e;` or `let P { x, y: py, .. } = e;`.
    fn parse_let_destructure(&mut self, mutable: bool) -> Result<Stmt, String> {
        let ty = if self.peek().kind == SurfTokenKind::LBrace {
            None
        } else {
            let mut path = vec![self.expect_ident()?];
            while self.peek().kind == SurfTokenKind::ColonColon {
                self.advance();
                path.push(self.expect_ident()?);
            }
            Some(path)
        };
        let ty_args = if ty.is_some() && self.peek().kind == SurfTokenKind::LBracket {
            self.parse_comptime_args()?
        } else {
            Vec::new()
        };
        self.expect(&SurfTokenKind::LBrace)?;
        let mut fields = Vec::new();
        let mut rest = false;
        while self.peek().kind != SurfTokenKind::RBrace {
            if self.peek().kind == SurfTokenKind::DotDot {
                self.advance();
                rest = true;
                break;
            }
            let name = self.expect_ident()?;
            let (field, binding) = if ty.is_some() {
                if self.peek().kind == SurfTokenKind::Colon {
                    self.advance();
                    (name, self.expect_ident()?)
                } else {
                    (name.clone(), name)
                }
            } else {
                (fields.len().to_string(), name)
            };
            fields.push((field, binding));
            if self.peek().kind == SurfTokenKind::Comma {
                self.advance();
            } else {
                break;
            }
        }
        self.expect(&SurfTokenKind::RBrace)?;
        self.expect(&SurfTokenKind::Eq)?;
        let init = self.parse_expr()?;
        self.expect(&SurfTokenKind::Semi)?;
        Ok(Stmt::LetDestructure {
            mutable,
            ty,
            ty_args,
            fields,
            rest,
            init,
        })
    }

    /// `for [ref [mut]] x in iter { ... }` or `for (x, i) in iter { ... }`, where `iter` is
    /// `start..end`, `start..=end`, or an expression.
    fn parse_for(&mut self) -> Result<Stmt, String> {
        self.advance();
        let parse_binding = |p: &mut Self| -> Result<(BindMode, String), String> {
            let mode = if matches!(&p.peek().kind, SurfTokenKind::Ident(s) if s == "ref")
                && matches!(p.peek_n(1).kind, SurfTokenKind::Ident(_) | SurfTokenKind::Mut)
            {
                p.advance();
                let mutable = p.peek().kind == SurfTokenKind::Mut;
                if mutable {
                    p.advance();
                }
                BindMode::Ref { mutable }
            } else {
                BindMode::Default
            };
            Ok((mode, p.expect_ident()?))
        };
        let (mode, var_name, idx_name) = if self.peek().kind == SurfTokenKind::LParen {
            self.advance();
            let (mode, v) = parse_binding(self)?;
            self.expect(&SurfTokenKind::Comma)?;
            let idx = self.expect_ident()?;
            self.expect(&SurfTokenKind::RParen)?;
            (mode, v, Some(idx))
        } else {
            let (mode, v) = parse_binding(self)?;
            (mode, v, None)
        };
        self.expect(&SurfTokenKind::In)?;
        let first = self.parse_cond_expr()?;
        let iter = match self.peek().kind {
            SurfTokenKind::DotDot | SurfTokenKind::DotDotEq => {
                let inclusive = self.peek().kind == SurfTokenKind::DotDotEq;
                self.advance();
                ForIter::Range {
                    start: Box::new(first),
                    end: Box::new(self.parse_cond_expr()?),
                    inclusive,
                }
            }
            _ => ForIter::Expr(Box::new(first)),
        };
        let body = self.parse_block()?;
        Ok(Stmt::For {
            var_name,
            mode,
            idx_name,
            iter,
            body,
        })
    }

    pub(super) fn parse_stmt(&mut self) -> Result<Stmt, String> {
        // `label: while ...` / `label: for ...` / `label: { ... }`
        if let SurfTokenKind::Ident(label) = &self.peek().kind
            && self.peek_n(1).kind == SurfTokenKind::Colon
            && (self.peek_n(2).kind == SurfTokenKind::While
                || self.peek_n(2).kind == SurfTokenKind::LBrace
                || matches!(&self.peek_n(2).kind, SurfTokenKind::Ident(s) if s == "for"))
        {
            let label = label.clone();
            self.advance();
            self.advance();
            let stmt = self.parse_stmt()?;
            return Ok(Stmt::Labeled {
                label,
                stmt: Box::new(stmt),
            });
        }
        if matches!(&self.peek().kind, SurfTokenKind::Ident(s) if s == "for")
            && matches!(
                self.peek_n(1).kind,
                SurfTokenKind::Ident(_) | SurfTokenKind::LParen
            )
        {
            return self.parse_for();
        }
        // `yield e;`
        if matches!(&self.peek().kind, SurfTokenKind::Ident(s) if s == "yield")
            && !matches!(self.peek_n(1).kind, SurfTokenKind::Eq | SurfTokenKind::Semi | SurfTokenKind::Dot)
        {
            self.advance();
            let val = self.parse_expr()?;
            self.expect(&SurfTokenKind::Semi)?;
            return Ok(Stmt::Yield(Some(val)));
        }
        match &self.peek().kind {
            SurfTokenKind::Let | SurfTokenKind::Comptime | SurfTokenKind::Const => {
                let is_comptime_kw = self.peek().kind == SurfTokenKind::Comptime;
                self.advance();
                if is_comptime_kw {
                    if matches!(&self.peek().kind, SurfTokenKind::Ident(s) if s == "for") {
                        self.advance();
                        let (var_name, idx_name) = if self.peek().kind == SurfTokenKind::LParen {
                            self.advance();
                            let v = self.expect_ident()?;
                            self.expect(&SurfTokenKind::Comma)?;
                            let idx = self.expect_ident()?;
                            self.expect(&SurfTokenKind::RParen)?;
                            (v, Some(idx))
                        } else {
                            (self.expect_ident()?, None)
                        };
                        self.expect(&SurfTokenKind::In)?;
                        let iterable = self.parse_expr_or_type()?;
                        let body = self.parse_block()?;
                        return Ok(Stmt::ComptimeFor {
                            var_name,
                            idx_name,
                            iterable,
                            body,
                        });
                    }
                    if self.peek().kind == SurfTokenKind::Let {
                        self.advance();
                    }
                }
                let mutable = if self.peek().kind == SurfTokenKind::Mut {
                    self.advance();
                    true
                } else {
                    false
                };
                if !is_comptime_kw && self.destructure_ahead() {
                    return self.parse_let_destructure(mutable);
                }
                let name = self.expect_ident()?;
                let ty = if self.peek().kind == SurfTokenKind::Colon {
                    self.advance();
                    Some(self.parse_type_expr()?)
                } else {
                    None
                };
                if self.peek().kind == SurfTokenKind::Semi {
                    let tok = self.peek().clone();
                    let Some(ty) = ty.filter(|_| mutable && !is_comptime_kw) else {
                        return Err(format!(
                            "A variable without an initializer must be declared 'let mut {name}: T;' (line {}, column {})",
                            tok.line, tok.col
                        ));
                    };
                    self.advance();
                    return Ok(Stmt::LetDeferred { name, ty });
                }
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
            SurfTokenKind::Match => {
                self.advance();
                let scrutinee = self.parse_cond_expr()?;
                let arms = self.parse_match_arms()?;
                if self.peek().kind == SurfTokenKind::Semi {
                    self.advance();
                }
                Ok(Stmt::Match { scrutinee, arms })
            }
            SurfTokenKind::AtSelect => {
                self.advance();
                let arms = self.parse_select_arms()?;
                if self.peek().kind == SurfTokenKind::Semi {
                    self.advance();
                }
                Ok(Stmt::Expr(Expr::Select { arms }))
            }
            SurfTokenKind::While => {
                self.advance();
                if self.let_variant_pattern_ahead() {
                    // `while let P = e { body }` is `while true { match e { P => { body }, _ => break } }`.
                    self.advance();
                    let pat = Self::let_pattern(self.parse_match_pat()?);
                    self.expect(&SurfTokenKind::Eq)?;
                    let scrutinee = self.parse_cond_expr()?;
                    let body = self.parse_block()?;
                    return Ok(Stmt::While {
                        cond: Expr::Bool(true),
                        body: Block {
                            stmts: vec![Stmt::Match {
                                scrutinee,
                                arms: vec![
                                    (pat, Expr::Block(body)),
                                    (MatchPat::Wildcard, Expr::Break(None)),
                                ],
                            }],
                            lines: Vec::new(),
                        },
                    });
                }
                if self.peek().kind == SurfTokenKind::Let {
                    self.advance();
                    let var_name = self.expect_ident()?;
                    self.expect(&SurfTokenKind::Eq)?;
                    let opt_expr = self.parse_cond_expr()?;
                    let body = self.parse_block()?;
                    return Ok(Stmt::WhileLet {
                        var_name,
                        opt_expr,
                        body,
                    });
                }
                let cond = self.parse_cond_expr()?;
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
            SurfTokenKind::LBrace => {
                let blk = self.parse_block()?;
                if self.peek().kind == SurfTokenKind::Semi {
                    self.advance();
                }
                Ok(Stmt::Block(blk))
            }
            SurfTokenKind::Unsafe => {
                self.advance();
                let blk = self.parse_block()?;
                Ok(Stmt::Unsafe(blk))
            }
            SurfTokenKind::Ident(s)
                if s == "nosuspend" && self.peek_n(1).kind == SurfTokenKind::LBrace =>
            {
                self.advance();
                let blk = self.parse_block()?;
                Ok(Stmt::NoSuspend(blk))
            }
            SurfTokenKind::Ident(s)
                if s == "uncancelled" && self.peek_n(1).kind == SurfTokenKind::LBrace =>
            {
                self.advance();
                let blk = self.parse_block()?;
                if self.peek().kind == SurfTokenKind::Semi {
                    self.advance();
                }
                Ok(Stmt::Uncancelled(blk))
            }
            _ if self.defer_ahead() => {
                let on_error = matches!(&self.advance().kind, SurfTokenKind::Ident(s) if s == "errdefer");
                // `errdefer |e| ...`: the error being returned, by name.
                let mut err = None;
                if !on_error && self.peek().kind == SurfTokenKind::Pipe {
                    let tok = self.peek();
                    return Err(format!(
                        "'defer |e|' names an error, which only 'errdefer' has: write 'errdefer |e| ...' (line {}, column {})",
                        tok.line, tok.col
                    ));
                }
                if on_error && self.peek().kind == SurfTokenKind::Pipe {
                    self.advance();
                    err = Some(self.expect_ident()?);
                    self.expect(&SurfTokenKind::Pipe)?;
                }
                let block = if self.peek().kind == SurfTokenKind::LBrace {
                    self.parse_block()?
                } else {
                    let line = self.src_pos();
                    let inner = self.parse_stmt()?;
                    Block { stmts: vec![inner], lines: vec![line] }
                };
                Ok(if on_error { Stmt::ErrDefer { block, err } } else { Stmt::Defer(block) })
            }
            _ => {
                let expr = self.parse_expr()?;
                match &self.peek().kind {
                    SurfTokenKind::Eq => {
                        self.advance();
                        // A type literal may be assigned to a `type` local:
                        // `t = tuple { t, u8 };`.
                        let value = self.parse_expr_or_type()?;
                        self.expect(&SurfTokenKind::Semi)?;
                        Ok(Stmt::Assign {
                            target: expr,
                            op: None,
                            value,
                        })
                    }
                    kind if compound_assign_op(kind).is_some() => {
                        let op = compound_assign_op(kind).unwrap();
                        self.advance();
                        let value = self.parse_expr()?;
                        self.expect(&SurfTokenKind::Semi)?;
                        Ok(Stmt::Assign {
                            target: expr,
                            op: Some(op),
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

    /// The pattern of `if let` / `while let`. `ref v` unwraps a `?T` as `v` does, by reference.
    fn let_pattern(pat: MatchPat) -> MatchPat {
        match pat {
            MatchPat::CatchAllBind { mode: BindMode::Ref { .. }, .. } => MatchPat::DotVariant {
                name: "Some".to_string(),
                payload: Some(Box::new(pat)),
            },
            other => other,
        }
    }

    /// Whether the tokens after the current `let` form a general match pattern (`Msg::Ping(x)`,
    /// `.Ping(x)`, `Point { x, y }`, `{ a, b }`, `[first, ..]`, etc.) rather than the `?T`
    /// single-identifier binding form (`let v = ...`).
    fn let_variant_pattern_ahead(&self) -> bool {
        self.peek().kind == SurfTokenKind::Let
            && !(matches!(&self.peek_n(1).kind, SurfTokenKind::Ident(s) if s != "_")
                && self.peek_n(2).kind == SurfTokenKind::Eq)
    }

    pub(super) fn parse_if_stmt(&mut self) -> Result<Stmt, String> {
        self.expect(&SurfTokenKind::If)?;
        if self.let_variant_pattern_ahead() {
            // `if let Msg::Ping(seq) = msg { A } else { B }` is `match msg { Msg::Ping(seq) => { A }, _ => { B } }`.
            self.advance();
            let pat = Self::let_pattern(self.parse_match_pat()?);
            self.expect(&SurfTokenKind::Eq)?;
            let scrutinee = self.parse_cond_expr()?;
            let then_block = self.parse_block()?;
            let else_block = if self.peek().kind == SurfTokenKind::Else {
                self.advance();
                if self.peek().kind == SurfTokenKind::If {
                    Block {
                        stmts: vec![self.parse_if_stmt()?],
                        lines: Vec::new(),
                    }
                } else {
                    self.parse_block()?
                }
            } else {
                Block { stmts: Vec::new(), lines: Vec::new() }
            };
            return Ok(Stmt::Match {
                scrutinee,
                arms: vec![
                    (pat, Expr::Block(then_block)),
                    (MatchPat::Wildcard, Expr::Block(else_block)),
                ],
            });
        }
        if self.peek().kind == SurfTokenKind::Let {
            self.advance();
            let var_name = self.expect_ident()?;
            self.expect(&SurfTokenKind::Eq)?;
            let opt_expr = self.parse_cond_expr()?;
            let then_block = self.parse_block()?;
            let else_block = if self.peek().kind == SurfTokenKind::Else {
                self.advance();
                if self.peek().kind == SurfTokenKind::If {
                    Some(Block {
                        stmts: vec![self.parse_if_stmt()?],
                        lines: Vec::new(),
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
            let cond = self.parse_cond_expr()?;
            let then_block = self.parse_block()?;
            let else_block = if self.peek().kind == SurfTokenKind::Else {
                self.advance();
                if self.peek().kind == SurfTokenKind::If {
                    Some(Block {
                        stmts: vec![self.parse_if_stmt()?],
                        lines: Vec::new(),
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
        self.parse_binop_expr(1)
    }

    pub(super) fn parse_additive_expr(&mut self) -> Result<Expr, String> {
        self.parse_binop_expr(8)
    }

    fn peek_binop(&self) -> Option<(u8, Option<BinOp>)> {
        match self.peek().kind {
            SurfTokenKind::PipePipe => Some((1, None)),
            SurfTokenKind::AmpAmp => Some((2, None)),
            SurfTokenKind::EqEq => Some((3, Some(BinOp::Eq))),
            SurfTokenKind::Ne => Some((3, Some(BinOp::Ne))),
            SurfTokenKind::Lt => Some((3, Some(BinOp::Lt))),
            SurfTokenKind::Le => Some((3, Some(BinOp::Le))),
            SurfTokenKind::Gt => Some((3, Some(BinOp::Gt))),
            SurfTokenKind::Ge => Some((3, Some(BinOp::Ge))),
            SurfTokenKind::Pipe => Some((4, Some(BinOp::BitOr))),
            SurfTokenKind::Caret => Some((5, Some(BinOp::BitXor))),
            SurfTokenKind::Amp => Some((6, Some(BinOp::BitAnd))),
            SurfTokenKind::Shl => Some((7, Some(BinOp::Shl))),
            SurfTokenKind::Shr => Some((7, Some(BinOp::Shr))),
            SurfTokenKind::Plus => Some((8, Some(BinOp::Add))),
            SurfTokenKind::PlusPercent => Some((8, Some(BinOp::AddWrap))),
            SurfTokenKind::PlusPipe => Some((8, Some(BinOp::AddSat))),
            SurfTokenKind::PlusQuestion => Some((8, Some(BinOp::AddChecked))),
            SurfTokenKind::Minus => Some((8, Some(BinOp::Sub))),
            SurfTokenKind::MinusPercent => Some((8, Some(BinOp::SubWrap))),
            SurfTokenKind::MinusPipe => Some((8, Some(BinOp::SubSat))),
            SurfTokenKind::MinusQuestion => Some((8, Some(BinOp::SubChecked))),
            SurfTokenKind::Star => Some((9, Some(BinOp::Mul))),
            SurfTokenKind::StarPercent => Some((9, Some(BinOp::MulWrap))),
            SurfTokenKind::StarPipe => Some((9, Some(BinOp::MulSat))),
            SurfTokenKind::StarQuestion => Some((9, Some(BinOp::MulChecked))),
            SurfTokenKind::Slash => Some((9, Some(BinOp::Div))),
            SurfTokenKind::Percent => Some((9, Some(BinOp::Rem))),
            _ => None,
        }
    }

    fn parse_binop_expr(&mut self, min_prec: u8) -> Result<Expr, String> {
        let mut lhs = self.parse_cast_or_orelse()?;
        while let Some((prec, op_opt)) = self.peek_binop() {
            if prec < min_prec {
                break;
            }
            let is_logical_or = self.peek().kind == SurfTokenKind::PipePipe;
            self.advance();
            let rhs = self.parse_binop_expr(prec + 1)?;
            lhs = match op_opt {
                Some(op) => Expr::Binary {
                    op,
                    lhs: Box::new(lhs),
                    rhs: Box::new(rhs),
                },
                None if is_logical_or => Expr::LogicalOr(Box::new(lhs), Box::new(rhs)),
                None => Expr::LogicalAnd(Box::new(lhs), Box::new(rhs)),
            };
        }
        Ok(lhs)
    }

    pub(super) fn parse_cast_or_orelse(&mut self) -> Result<Expr, String> {
        let mut expr = self.parse_unary()?;
        loop {
            if self.peek().kind == SurfTokenKind::As {
                self.advance();
                let ty = self.parse_base_type_expr()?;
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
            } else if self.peek().kind == SurfTokenKind::Catch {
                self.advance();
                let err_binding = if self.peek().kind == SurfTokenKind::Pipe {
                    self.advance();
                    let name = self.expect_ident()?;
                    self.expect(&SurfTokenKind::Pipe)?;
                    Some(name)
                } else {
                    None
                };
                let fallback = if self.peek().kind == SurfTokenKind::LBrace {
                    Expr::Block(self.parse_expr_block()?)
                } else {
                    self.parse_unary()?
                };
                expr = Expr::Catch {
                    expr: Box::new(expr),
                    err_binding,
                    fallback: Box::new(fallback),
                };
            } else {
                break;
            }
        }
        Ok(expr)
    }

    pub(super) fn parse_unary(&mut self) -> Result<Expr, String> {
        match &self.peek().kind {
            SurfTokenKind::Try => {
                self.advance();
                let expr = self.parse_unary()?;
                Ok(Expr::Try(Box::new(expr)))
            }
            SurfTokenKind::Async => {
                let (line, col) = (self.peek().line, self.peek().col);
                self.advance();
                let mut executor = None;
                if self.peek().kind == SurfTokenKind::LParen {
                    self.advance();
                    executor = Some(Box::new(self.parse_expr()?));
                    self.expect(&SurfTokenKind::RParen)?;
                }
                let call = self.parse_unary()?;
                if !matches!(call, Expr::Call { .. } | Expr::MethodCall { .. }) {
                    return Err(format!("'async' takes a call at {line}:{col}"));
                }
                Ok(Expr::Async { call: Box::new(call), bound: false, executor })
            }
            SurfTokenKind::Minus => {
                let minus = self.advance();
                if let (
                    SurfTokenKind::Int(n),
                    Some(SurfToken {
                        kind:
                            SurfTokenKind::IntSuffix(
                                ty @ (TypeExpr::Int { signed: true, .. } | TypeExpr::Isize),
                            ),
                        ..
                    }),
                ) = (
                    self.peek().kind.clone(),
                    self.tokens.get(self.pos + 1).cloned(),
                ) {
                    self.advance();
                    self.advance();
                    let neg = crate::wide::Wide::from_i128(n).neg();
                    Self::check_int_suffix(&neg, &ty, minus.line, minus.col)?;
                    let inner = match neg.to_i128() {
                        Some(v) => Expr::Int(v),
                        None => Expr::WideInt(Box::new(neg)),
                    };
                    return Ok(Expr::Cast {
                        expr: Box::new(inner),
                        ty,
                    });
                }
                if let (
                    SurfTokenKind::WideInt(w),
                    Some(SurfToken {
                        kind:
                            SurfTokenKind::IntSuffix(
                                ty @ (TypeExpr::Int { signed: true, .. } | TypeExpr::Isize),
                            ),
                        ..
                    }),
                ) = (
                    self.peek().kind.clone(),
                    self.tokens.get(self.pos + 1).cloned(),
                ) {
                    self.advance();
                    self.advance();
                    let neg = w.neg();
                    Self::check_int_suffix(&neg, &ty, minus.line, minus.col)?;
                    let inner = match neg.to_i128() {
                        Some(v) => Expr::Int(v),
                        None => Expr::WideInt(Box::new(neg)),
                    };
                    return Ok(Expr::Cast {
                        expr: Box::new(inner),
                        ty,
                    });
                }
                if let (
                    SurfTokenKind::Float(bits),
                    Some(SurfToken {
                        kind: SurfTokenKind::IntSuffix(ty),
                        ..
                    }),
                ) = (
                    self.peek().kind.clone(),
                    self.tokens.get(self.pos + 1).cloned(),
                ) {
                    self.advance();
                    self.advance();
                    let neg_bits = (-f64::from_bits(bits)).to_bits();
                    return Ok(Expr::Cast {
                        expr: Box::new(Expr::Float(neg_bits)),
                        ty,
                    });
                }
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
            SurfTokenKind::Amp | SurfTokenKind::AmpAmp => {
                if self.peek().kind == SurfTokenKind::AmpAmp {
                    self.tokens[self.pos].kind = SurfTokenKind::Amp;
                } else {
                    self.advance();
                }
                if self.peek().kind == SurfTokenKind::Rel {
                    self.advance();
                    let expr = self.parse_unary()?;
                    return Ok(Expr::RelRef(Box::new(expr)));
                }
                if matches!(&self.peek().kind, SurfTokenKind::Ident(s) if s == "raw")
                    && matches!(
                        self.peek_n(1).kind,
                        SurfTokenKind::Const | SurfTokenKind::Mut
                    )
                {
                    self.advance(); // consume 'raw'
                    let mutable = if self.peek().kind == SurfTokenKind::Mut {
                        self.advance();
                        true
                    } else {
                        self.advance(); // consume 'const'
                        false
                    };
                    let expr = self.parse_unary()?;
                    return Ok(Expr::RawPtr {
                        mutable,
                        expr: Box::new(expr),
                    });
                }
                let mutable = if self.peek().kind == SurfTokenKind::Mut {
                    self.advance();
                    true
                } else {
                    false
                };
                if self.peek().kind == SurfTokenKind::LBracket && !self.is_slice_type_ahead(0) {
                    self.advance();
                    let mut elems = Vec::new();
                    while self.peek().kind != SurfTokenKind::RBracket {
                        elems.push(self.parse_expr_or_type()?);
                        if self.peek().kind == SurfTokenKind::Comma {
                            self.advance();
                        } else {
                            break;
                        }
                    }
                    self.expect(&SurfTokenKind::RBracket)?;
                    return Ok(Expr::SliceLit { mutable, elems });
                }
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

    pub(super) fn parse_postfix(&mut self) -> Result<Expr, String> {
        let start = At(Some(self.src_pos()));
        let mut expr = self.parse_primary()?;
        loop {
            match &self.peek().kind {
                SurfTokenKind::ColonColon => {
                    self.advance();
                    let at = At(Some(self.src_pos()));
                    let name = self.expect_ident()?;
                    if self.peek().kind == SurfTokenKind::LParen
                        || (self.peek().kind == SurfTokenKind::LBracket
                            && self.bracket_then_call_ahead())
                    {
                        let ct_args = if self.peek().kind == SurfTokenKind::LBracket {
                            Some(self.parse_comptime_args()?)
                        } else {
                            None
                        };
                        let args = self.parse_call_args()?;
                        expr = Expr::MethodCall {
                            receiver: Box::new(expr),
                            method: name,
                            ct_args,
                            args,
                            at,
                        };
                    } else {
                        expr = Expr::Field {
                            base: Box::new(expr),
                            field: name,
                        };
                    }
                }
                SurfTokenKind::Dot => {
                    if self.peek_n(1).kind == SurfTokenKind::LBrace {
                        let tok = self.peek_n(1);
                        return Err(format!(
                            "Write a struct literal as 'Type {{ field: value }}', or '{{ field: value }}' where the type is known (line {}, column {})",
                            tok.line, tok.col
                        ));
                    }
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
                            let at = At(Some(self.src_pos()));
                            let name = self.expect_ident()?;
                            if self.peek().kind == SurfTokenKind::LParen {
                                let args = self.parse_call_args()?;
                                expr = Expr::MethodCall {
                                    receiver: Box::new(expr),
                                    method: name,
                                    ct_args: None,
                                    args,
                                    at,
                                };
                            } else if self.peek().kind == SurfTokenKind::LBracket
                                && self.bracket_then_call_ahead()
                            {
                                // `recv.m[T](x)`; lowering turns it back into `recv.f[i](x)`
                                // when `f` is a field holding callables.
                                let ct_args = self.parse_comptime_args()?;
                                let args = self.parse_call_args()?;
                                expr = Expr::MethodCall {
                                    receiver: Box::new(expr),
                                    method: name,
                                    ct_args: Some(ct_args),
                                    args,
                                    at,
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
                                "Expected field name or tuple index after '.', found {:?} (line {}, column {})",
                                tok.kind, tok.line, tok.col
                            ));
                        }
                    }
                }
                SurfTokenKind::LBracket => {
                    self.advance();
                    let first = if self.peek().kind == SurfTokenKind::DotDot {
                        Expr::Int(0)
                    } else {
                        self.parse_expr_or_type()?
                    };
                    if self.peek().kind == SurfTokenKind::DotDot {
                        self.advance();
                        let end = if self.peek().kind == SurfTokenKind::RBracket {
                            // `base[start..]`: to `base.len`, so `base` must be safe to repeat.
                            if !is_plain_place(&expr) {
                                let tok = self.peek();
                                return Err(format!(
                                    "An open-ended range needs a variable or field to slice; write the end explicitly (line {}, column {})",
                                    tok.line, tok.col
                                ));
                            }
                            Expr::Field {
                                base: Box::new(expr.clone()),
                                field: "len".to_string(),
                            }
                        } else {
                            self.parse_expr()?
                        };
                        self.expect(&SurfTokenKind::RBracket)?;
                        expr = Expr::Slice {
                            base: Box::new(expr),
                            start: Box::new(first),
                            end: Box::new(end),
                        };
                        continue;
                    }
                    let mut items = vec![first];
                    while self.peek().kind == SurfTokenKind::Comma {
                        self.advance();
                        if self.peek().kind == SurfTokenKind::RBracket {
                            break;
                        }
                        items.push(self.parse_expr_or_type()?);
                    }
                    self.expect(&SurfTokenKind::RBracket)?;
                    if self.peek().kind == SurfTokenKind::LParen {
                        // `f[ct_args](args)`: a call with explicit comptime arguments.
                        let args = self.parse_call_args()?;
                        expr = Expr::Call {
                            callee: Box::new(expr),
                            ct_args: Some(items),
                            args,
                            at: start,
                        };
                        continue;
                    }
                    if let Expr::Path(path) = &expr
                        && (items.len() > 1 || self.type_call_suffix_ahead())
                    {
                        // `F[args]`, `F[args] { field: val }`, `F[args]::method(...)`.
                        let ty = TypeExpr::TypeCall {
                            path: path.clone(),
                            args: items,
                        };
                        if self.peek().kind == SurfTokenKind::LBrace {
                            // A literal can be the start of more: `Pair[i32] { .. }.sum()`.
                            expr = self.parse_struct_lit_fields(ty)?;
                            continue;
                        }
                        if self.peek().kind == SurfTokenKind::ColonColon {
                            self.advance();
                            let at = At(Some(self.src_pos()));
                            let method = self.expect_ident()?;
                            if !matches!(
                                self.peek().kind,
                                SurfTokenKind::LParen | SurfTokenKind::LBracket
                            ) {
                                expr = Expr::TypeMember { ty, name: method };
                                continue;
                            }
                            let ct_args = if self.peek().kind == SurfTokenKind::LBracket {
                                Some(self.parse_comptime_args()?)
                            } else {
                                None
                            };
                            let call_args = self.parse_call_args()?;
                            expr = Expr::MethodCall {
                                receiver: Box::new(Expr::TypeVal(ty)),
                                method,
                                ct_args,
                                args: call_args,
                                at,
                            };
                            continue;
                        }
                        expr = Expr::TypeVal(ty);
                        continue;
                    }
                    if items.len() > 1 {
                        return Err(format!(
                            "Only a type function can take several bracketed arguments (line {}, column {})",
                            self.peek().line,
                            self.peek().col
                        ));
                    }
                    // `a[i]`, or `F[T]` resolved to a type function call during lowering.
                    expr = Expr::Index {
                        base: Box::new(expr),
                        index: Box::new(items.pop().unwrap()),
                    };
                }
                SurfTokenKind::LParen => {
                    if let Expr::Path(path) = &expr {
                        // `F(args)` where `F` takes comptime arguments is caught during lowering;
                        // `F(args) { ... }` / `F(args)::m()` are type-call forms that need brackets.
                        let mut k = 1;
                        let mut depth = 1;
                        while depth > 0 && self.peek_n(k).kind != SurfTokenKind::Eof {
                            match self.peek_n(k).kind {
                                SurfTokenKind::LParen => depth += 1,
                                SurfTokenKind::RParen => depth -= 1,
                                _ => {}
                            }
                            k += 1;
                        }
                        if self.peek_n(k).kind == SurfTokenKind::ColonColon {
                            return Err(format!(
                                "Type function arguments go in brackets: write '{}[...]::...' (line {}, column {})",
                                path.join("::"),
                                self.peek().line,
                                self.peek().col
                            ));
                        }
                    }
                    let args = self.parse_call_args()?;
                    expr = Expr::Call {
                        callee: Box::new(expr),
                        ct_args: None,
                        args,
                        at: start,
                    };
                }
                _ => break,
            }
        }
        Ok(expr)
    }

    /// Parses a parenthesized argument list `(a, b)`.
    pub(super) fn parse_call_args(&mut self) -> Result<Vec<Expr>, String> {
        self.expect(&SurfTokenKind::LParen)?;
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
        Ok(args)
    }

    /// Whether the `[` at the cursor closes on a `]` directly followed by `(`.
    fn bracket_then_call_ahead(&self) -> bool {
        let mut k = 0;
        let mut depth = 0;
        loop {
            match self.peek_n(k).kind {
                SurfTokenKind::LBracket => depth += 1,
                SurfTokenKind::RBracket => {
                    depth -= 1;
                    if depth == 0 {
                        return self.peek_n(k + 1).kind == SurfTokenKind::LParen;
                    }
                }
                SurfTokenKind::Eof => return false,
                _ => {}
            }
            k += 1;
        }
    }

    /// Whether the tokens after `F[args]` make it a type: a struct literal `{ field: ... }` (or
    /// `{}` where allowed) or a static member `::name`.
    fn type_call_suffix_ahead(&self) -> bool {
        match self.peek().kind {
            SurfTokenKind::ColonColon => true,
            SurfTokenKind::LBrace => {
                (self.peek_n(1).kind == SurfTokenKind::RBrace && self.empty_struct_lit_allowed())
                    || (matches!(self.peek_n(1).kind, SurfTokenKind::Ident(_))
                        && self.peek_n(2).kind == SurfTokenKind::Colon)
            }
            _ => false,
        }
    }

    pub(super) fn parse_struct_lit_fields(&mut self, ty: TypeExpr) -> Result<Expr, String> {
        self.expect(&SurfTokenKind::LBrace)?;
        let mut fields = Vec::new();
        while self.peek().kind != SurfTokenKind::RBrace {
            let fname = self.expect_ident()?;
            self.expect(&SurfTokenKind::Colon)?;
            let fval = self.parse_expr_or_type()?;
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

    pub(super) fn parse_lambda_expr(&mut self, is_move: bool) -> Result<Expr, String> {
        self.expect(&SurfTokenKind::Fn)?;
        self.expect(&SurfTokenKind::LParen)?;
        let mut params = Vec::new();
        while self.peek().kind != SurfTokenKind::RParen {
            let mut is_mut = if self.peek().kind == SurfTokenKind::Mut {
                self.advance();
                true
            } else {
                false
            };
            let pname = self.expect_ident()?;
            self.expect(&SurfTokenKind::Colon)?;
            if self.peek().kind == SurfTokenKind::Mut {
                self.advance();
                is_mut = true;
            }
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

    pub(super) fn parse_primary(&mut self) -> Result<Expr, String> {
        let tok = self.peek().clone();
        match tok.kind {
            // `.Name` / `.Name(payload)`: a variant of the expected type.
            SurfTokenKind::Dot if matches!(self.peek_n(1).kind, SurfTokenKind::Ident(_)) => {
                self.advance();
                let name = self.expect_ident()?;
                let payload = if self.peek().kind == SurfTokenKind::LParen {
                    self.advance();
                    let p = self.parse_expr()?;
                    self.expect(&SurfTokenKind::RParen)?;
                    Some(Box::new(p))
                } else {
                    None
                };
                Ok(Expr::DotVariant { name, payload })
            }
            SurfTokenKind::Int(n) => {
                let tok = self.advance();
                if let SurfTokenKind::IntSuffix(ty) = self.peek().kind.clone() {
                    self.advance();
                    Self::check_int_suffix(
                        &crate::wide::Wide::from_i128(n),
                        &ty,
                        tok.line,
                        tok.col,
                    )?;
                    return Ok(Expr::Cast {
                        expr: Box::new(Expr::Int(n)),
                        ty,
                    });
                }
                Ok(Expr::Int(n))
            }
            SurfTokenKind::WideInt(w) => {
                let tok = self.advance();
                if let SurfTokenKind::IntSuffix(ty) = self.peek().kind.clone() {
                    self.advance();
                    Self::check_int_suffix(&w, &ty, tok.line, tok.col)?;
                    return Ok(Expr::Cast {
                        expr: Box::new(Expr::WideInt(w)),
                        ty,
                    });
                }
                Ok(Expr::WideInt(w))
            }
            // `b"blah"` is the array `[u8; 4] { 98, 108, 97, 104 }`.
            SurfTokenKind::ByteStr(bytes) => {
                self.advance();
                let len = bytes.len() as i128;
                Ok(Expr::SimdLit {
                    ty: TypeExpr::Array {
                        elem: Box::new(TypeExpr::Int { signed: false, bits: 8 }),
                        len: Box::new(Expr::Int(len)),
                    },
                    elems: bytes.into_iter().map(|b| Expr::Int(i128::from(b))).collect(),
                })
            }
            SurfTokenKind::ByteLit(b) => {
                self.advance();
                Ok(Expr::Cast {
                    expr: Box::new(Expr::Int(i128::from(b))),
                    ty: TypeExpr::Int {
                        signed: false,
                        bits: 8,
                    },
                })
            }
            SurfTokenKind::Float(bits) => {
                self.advance();
                if let SurfTokenKind::IntSuffix(ty) = self.peek().kind.clone() {
                    self.advance();
                    return Ok(Expr::Cast {
                        expr: Box::new(Expr::Float(bits)),
                        ty,
                    });
                }
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
            SurfTokenKind::FStr(parts) => {
                self.advance();
                let mut segments = Vec::with_capacity(parts.len());
                for (lit, interp_opt) in parts {
                    if let Some((expr_src, spec)) = interp_opt {
                        let sub_tokens = SurfaceLexer::new(&expr_src).tokenize()?;
                        let mut sub_parser = SurfaceParser {
                            tokens: sub_tokens,
                            pos: 0,
                            current_type_name: None,
                            extra_items: Vec::new(),
                            cond_start: None,
                            pending_where: Vec::new(),
                            lines: Vec::new(),
                        };
                        let expr = sub_parser.parse_expr()?;
                        segments.push(FmtSegment::Interp { expr, spec });
                    } else {
                        segments.push(FmtSegment::Lit(lit));
                    }
                }
                Ok(Expr::FormatStr(segments))
            }
            SurfTokenKind::Null => {
                self.advance();
                Ok(Expr::Null)
            }
            SurfTokenKind::AtAlloc
            | SurfTokenKind::AtRealloc
            | SurfTokenKind::AtDealloc
            | SurfTokenKind::AtRawAlloc
            | SurfTokenKind::AtRawAllocZeroed
            | SurfTokenKind::AtMemcpy
            | SurfTokenKind::AtMemmove
            | SurfTokenKind::AtTransmute
            | SurfTokenKind::AtForget
            | SurfTokenKind::AtCAbi
            | SurfTokenKind::AtBswap
            | SurfTokenKind::AtAtomic(_)
            | SurfTokenKind::AtAddUnchecked
            | SurfTokenKind::AtSubUnchecked
            | SurfTokenKind::AtMulUnchecked
            | SurfTokenKind::IntType { .. }
            | SurfTokenKind::Isize
            | SurfTokenKind::Usize
            | SurfTokenKind::Bool
            | SurfTokenKind::RuneKw
            | SurfTokenKind::F32
            | SurfTokenKind::F64
            | SurfTokenKind::AtInt
            | SurfTokenKind::AtBackingType
            | SurfTokenKind::AtTypeOf
            | SurfTokenKind::TypeKw
            | SurfTokenKind::AtStruct
            | SurfTokenKind::AtPackedStruct
            | SurfTokenKind::AtTuple
            | SurfTokenKind::AtEnum
            | SurfTokenKind::AtUnion
            | SurfTokenKind::AtError
            | SurfTokenKind::AtSizeOf
            | SurfTokenKind::AtAlignOf
            | SurfTokenKind::AtDefault
            | SurfTokenKind::AtClone
            | SurfTokenKind::AtDrop
            | SurfTokenKind::AtFormat
            | SurfTokenKind::AtTrap
            | SurfTokenKind::AtCompileError
            | SurfTokenKind::AtInvert
            | SurfTokenKind::AtDeclarations
            | SurfTokenKind::AtTypeName
            | SurfTokenKind::AtSatisfies
            | SurfTokenKind::AtFields
            | SurfTokenKind::AtLeaves
            | SurfTokenKind::AtHasField
            | SurfTokenKind::AtHasMethod
            | SurfTokenKind::AtAssert
            | SurfTokenKind::AtVariants
            | SurfTokenKind::AtEntries
            | SurfTokenKind::AtFnInfo
            | SurfTokenKind::AtField
            | SurfTokenKind::AtVariant
            | SurfTokenKind::AtMakeUnion
            | SurfTokenKind::AtMap => self.parse_intrinsic_primary(),
            SurfTokenKind::If => {
                self.advance();
                let cond = self.parse_cond_expr()?;
                let then_block = self.parse_expr_block()?;
                let else_block = if self.peek().kind == SurfTokenKind::Else {
                    self.advance();
                    if self.peek().kind == SurfTokenKind::If {
                        let nested = self.parse_primary()?;
                        Some(Block {
                            stmts: vec![Stmt::Expr(nested)],
                            lines: Vec::new(),
                        })
                    } else {
                        Some(self.parse_expr_block()?)
                    }
                } else {
                    None
                };
                Ok(Expr::If {
                    cond: Box::new(cond),
                    then_block,
                    else_block,
                })
            }
            SurfTokenKind::Break | SurfTokenKind::Continue => {
                let is_break = self.peek().kind == SurfTokenKind::Break;
                self.advance();
                let label = match &self.peek().kind {
                    SurfTokenKind::Ident(l) => {
                        let l = l.clone();
                        self.advance();
                        Some(l)
                    }
                    _ => None,
                };
                Ok(if is_break {
                    Expr::Break(label)
                } else {
                    Expr::Continue(label)
                })
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
            SurfTokenKind::Match => {
                self.advance();
                let scrutinee = self.parse_cond_expr()?;
                let arms = self.parse_match_arms()?;
                Ok(Expr::Match {
                    scrutinee: Box::new(scrutinee),
                    arms,
                })
            }
            SurfTokenKind::AtSelect => {
                self.advance();
                let arms = self.parse_select_arms()?;
                Ok(Expr::Select { arms })
            }
            SurfTokenKind::LParen => {
                self.advance();
                let inner = self.parse_expr()?;
                self.expect(&SurfTokenKind::RParen)?;
                Ok(inner)
            }
            SurfTokenKind::LBrace => {
                self.advance();
                if self.peek().kind == SurfTokenKind::RBrace {
                    self.advance();
                    return Ok(Expr::TupleLit(Vec::new()));
                }
                if matches!(self.peek().kind, SurfTokenKind::Ident(_))
                    && self.peek_n(1).kind == SurfTokenKind::Colon
                {
                    let mut fields = Vec::new();
                    while self.peek().kind != SurfTokenKind::RBrace {
                        let name = self.expect_ident()?;
                        self.expect(&SurfTokenKind::Colon)?;
                        fields.push((name, self.parse_expr()?));
                        if self.peek().kind == SurfTokenKind::Comma {
                            self.advance();
                        } else {
                            break;
                        }
                    }
                    self.expect(&SurfTokenKind::RBrace)?;
                    return Ok(Expr::RecordLit(fields));
                }
                let first = self.parse_expr_or_type()?;
                if self.peek().kind == SurfTokenKind::FatArrow {
                    self.advance();
                    let first_val = self.parse_expr_or_type()?;
                    let mut pairs = vec![(first, first_val)];
                    if self.peek().kind == SurfTokenKind::Comma {
                        self.advance();
                        while self.peek().kind != SurfTokenKind::RBrace {
                            let k = self.parse_expr_or_type()?;
                            self.expect(&SurfTokenKind::FatArrow)?;
                            let v = self.parse_expr_or_type()?;
                            pairs.push((k, v));
                            if self.peek().kind == SurfTokenKind::Comma {
                                self.advance();
                            } else {
                                break;
                            }
                        }
                    }
                    self.expect(&SurfTokenKind::RBrace)?;
                    Ok(Expr::MapLit(pairs))
                } else {
                    let mut elems = vec![first];
                    if self.peek().kind == SurfTokenKind::Comma {
                        self.advance();
                        while self.peek().kind != SurfTokenKind::RBrace {
                            elems.push(self.parse_expr_or_type()?);
                            if self.peek().kind == SurfTokenKind::Comma {
                                self.advance();
                            } else {
                                break;
                            }
                        }
                    }
                    self.expect(&SurfTokenKind::RBrace)?;
                    Ok(Expr::TupleLit(elems))
                }
            }
            // `void` is the type and its one value; which it is depends on what is expected.
            SurfTokenKind::Void => {
                self.advance();
                Ok(Expr::TypeVal(TypeExpr::Void))
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
                if matches!(
                    self.peek_n(1).kind,
                    SurfTokenKind::Sync | SurfTokenKind::Linear | SurfTokenKind::Fn | SurfTokenKind::Extern
                ) {
                    return Ok(Expr::TypeVal(self.parse_type_expr()?));
                }
                self.advance();
                let blk = self.parse_expr_block()?;
                Ok(Expr::UnsafeBlock(blk))
            }
            SurfTokenKind::Ident(s)
                if s == "uncancelled" && self.peek_n(1).kind == SurfTokenKind::LBrace =>
            {
                self.advance();
                let blk = self.parse_expr_block()?;
                Ok(Expr::Uncancelled(blk))
            }
            SurfTokenKind::Fn => self.parse_lambda_expr(false),
            SurfTokenKind::Ident(s)
                if s == "unreachable"
                    && self.peek_n(1).kind != SurfTokenKind::ColonColon
                    && self.peek_n(1).kind != SurfTokenKind::LParen =>
            {
                self.advance();
                Ok(Expr::IntrinsicTrap)
            }
            SurfTokenKind::Struct => {
                let ty = self.parse_type_expr()?;
                if self.peek().kind == SurfTokenKind::LBrace {
                    self.parse_struct_lit_fields(ty)
                } else {
                    Ok(Expr::TypeVal(ty))
                }
            }
            SurfTokenKind::Ident(s)
                if s == "packed"
                    && (self.peek_n(1).kind == SurfTokenKind::Struct
                        || matches!(&self.peek_n(1).kind, SurfTokenKind::Ident(s2) if s2 == "opaque")) =>
            {
                let ty = self.parse_type_expr()?;
                if self.peek().kind == SurfTokenKind::LBrace {
                    self.parse_struct_lit_fields(ty)
                } else {
                    Ok(Expr::TypeVal(ty))
                }
            }
            SurfTokenKind::Ident(s)
                if s == "overlay" && self.peek_n(1).kind == SurfTokenKind::LBrace =>
            {
                let ty = self.parse_type_expr()?;
                if self.peek().kind == SurfTokenKind::LBrace {
                    self.parse_struct_lit_fields(ty)
                } else {
                    Ok(Expr::TypeVal(ty))
                }
            }
            SurfTokenKind::Ident(s)
                if s == "zeroinit" && self.peek_n(1).kind != SurfTokenKind::ColonColon =>
            {
                self.advance();
                Ok(Expr::ZeroInit)
            }
            SurfTokenKind::Ident(s)
                if s == "uninit" && self.peek_n(1).kind != SurfTokenKind::ColonColon =>
            {
                self.advance();
                if self.peek().kind == SurfTokenKind::LParen {
                    self.advance();
                    let val = self.parse_expr()?;
                    self.expect(&SurfTokenKind::RParen)?;
                    Ok(Expr::Uninit(Some(Box::new(val))))
                } else {
                    Ok(Expr::Uninit(None))
                }
            }
            SurfTokenKind::Ident(_) | SurfTokenKind::Sync => {
                let mut path = vec![self.expect_ident()?];
                while self.peek().kind == SurfTokenKind::ColonColon {
                    self.advance();
                    path.push(self.expect_ident()?);
                }
                // Check for `Type { field: val, ... }` struct/record literal
                if self.peek().kind == SurfTokenKind::LBrace
                    && ((self.peek_n(1).kind == SurfTokenKind::RBrace
                        && self.empty_struct_lit_allowed())
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
                "Expected expression, found {:?} (line {}, column {})",
                tok.kind, tok.line, tok.col
            )),
        }
    }

    #[inline(never)]
    fn parse_intrinsic_primary(&mut self) -> Result<Expr, String> {
        let tok = self.peek().clone();
        match tok.kind {
            SurfTokenKind::AtAlloc => {
                self.advance();
                self.expect(&SurfTokenKind::LParen)?;
                let ty = self.parse_type_expr()?;
                self.expect(&SurfTokenKind::Comma)?;
                let len = self.parse_expr()?;
                self.expect(&SurfTokenKind::RParen)?;
                Ok(Expr::IntrinsicAlloc {
                    ty,
                    len: Box::new(len),
                })
            }
            SurfTokenKind::AtRealloc => {
                self.advance();
                self.expect(&SurfTokenKind::LParen)?;
                let ty = self.parse_type_expr()?;
                self.expect(&SurfTokenKind::Comma)?;
                let ptr = self.parse_expr()?;
                self.expect(&SurfTokenKind::Comma)?;
                let len = self.parse_expr()?;
                self.expect(&SurfTokenKind::RParen)?;
                Ok(Expr::IntrinsicRealloc {
                    ty,
                    ptr: Box::new(ptr),
                    len: Box::new(len),
                })
            }
            SurfTokenKind::AtDealloc => {
                self.advance();
                self.expect(&SurfTokenKind::LParen)?;
                let ptr = self.parse_expr()?;
                self.expect(&SurfTokenKind::RParen)?;
                Ok(Expr::IntrinsicDealloc(Box::new(ptr)))
            }
            SurfTokenKind::AtRawAlloc | SurfTokenKind::AtRawAllocZeroed => {
                let zeroed = self.peek().kind == SurfTokenKind::AtRawAllocZeroed;
                self.advance();
                self.expect(&SurfTokenKind::LParen)?;
                let bytes = Box::new(self.parse_expr()?);
                self.expect(&SurfTokenKind::RParen)?;
                Ok(if zeroed { Expr::IntrinsicRawAllocZeroed(bytes) } else { Expr::IntrinsicRawAlloc(bytes) })
            }
            SurfTokenKind::AtMemcpy => {
                self.advance();
                self.expect(&SurfTokenKind::LParen)?;
                let dest = self.parse_expr()?;
                self.expect(&SurfTokenKind::Comma)?;
                let src = self.parse_expr()?;
                self.expect(&SurfTokenKind::Comma)?;
                let len = self.parse_expr()?;
                self.expect(&SurfTokenKind::RParen)?;
                Ok(Expr::IntrinsicMemcpy {
                    dest: Box::new(dest),
                    src: Box::new(src),
                    len: Box::new(len),
                })
            }
            SurfTokenKind::AtMemmove => {
                self.advance();
                self.expect(&SurfTokenKind::LParen)?;
                let dest = self.parse_expr()?;
                self.expect(&SurfTokenKind::Comma)?;
                let src = self.parse_expr()?;
                self.expect(&SurfTokenKind::Comma)?;
                let len = self.parse_expr()?;
                self.expect(&SurfTokenKind::RParen)?;
                Ok(Expr::IntrinsicMemmove {
                    dest: Box::new(dest),
                    src: Box::new(src),
                    len: Box::new(len),
                })
            }
            SurfTokenKind::AtTransmute => {
                self.advance();
                self.expect(&SurfTokenKind::LParen)?;
                let dst_ty = self.parse_type_expr()?;
                self.expect(&SurfTokenKind::Comma)?;
                let src = self.parse_expr()?;
                self.expect(&SurfTokenKind::RParen)?;
                Ok(Expr::IntrinsicTransmute {
                    dst_ty,
                    src: Box::new(src),
                })
            }
            SurfTokenKind::AtForget => {
                self.advance();
                self.expect(&SurfTokenKind::LParen)?;
                let val = self.parse_expr()?;
                self.expect(&SurfTokenKind::RParen)?;
                Ok(Expr::IntrinsicForget(Box::new(val)))
            }
            SurfTokenKind::AtCAbi => {
                self.advance();
                self.expect(&SurfTokenKind::LParen)?;
                let target = self.parse_expr()?;
                self.expect(&SurfTokenKind::RParen)?;
                Ok(Expr::IntrinsicCAbi(Box::new(target)))
            }
            SurfTokenKind::AtBswap => {
                self.advance();
                self.expect(&SurfTokenKind::LParen)?;
                let val = self.parse_expr()?;
                self.expect(&SurfTokenKind::RParen)?;
                Ok(Expr::IntrinsicBswap(Box::new(val)))
            }
            SurfTokenKind::AtAtomic(op) => {
                self.advance();
                self.expect(&SurfTokenKind::LParen)?;
                let mut args = Vec::new();
                while self.peek().kind != SurfTokenKind::RParen {
                    args.push(self.parse_expr()?);
                    if self.peek().kind == SurfTokenKind::Comma {
                        self.advance();
                    } else {
                        break;
                    }
                }
                self.expect(&SurfTokenKind::RParen)?;
                Ok(Expr::IntrinsicAtomic { op, args })
            }
            SurfTokenKind::AtAddUnchecked
            | SurfTokenKind::AtSubUnchecked
            | SurfTokenKind::AtMulUnchecked => {
                let op = match tok.kind {
                    SurfTokenKind::AtAddUnchecked => BinOp::AddUnchecked,
                    SurfTokenKind::AtSubUnchecked => BinOp::SubUnchecked,
                    SurfTokenKind::AtMulUnchecked => BinOp::MulUnchecked,
                    _ => unreachable!(),
                };
                self.advance();
                self.expect(&SurfTokenKind::LParen)?;
                let lhs = self.parse_expr()?;
                self.expect(&SurfTokenKind::Comma)?;
                let rhs = self.parse_expr()?;
                self.expect(&SurfTokenKind::RParen)?;
                Ok(Expr::IntrinsicArithUnchecked {
                    op,
                    lhs: Box::new(lhs),
                    rhs: Box::new(rhs),
                })
            }
            SurfTokenKind::IntType { .. }
            | SurfTokenKind::Isize
            | SurfTokenKind::Usize
            | SurfTokenKind::Bool
            | SurfTokenKind::RuneKw
            | SurfTokenKind::F32
            | SurfTokenKind::F64
            | SurfTokenKind::AtInt
            | SurfTokenKind::AtBackingType
            | SurfTokenKind::AtTypeOf
            | SurfTokenKind::TypeKw
            | SurfTokenKind::AtStruct
            | SurfTokenKind::AtPackedStruct
            | SurfTokenKind::AtTuple
            | SurfTokenKind::AtEnum
            | SurfTokenKind::AtUnion
            | SurfTokenKind::AtError => {
                let ty = self.parse_base_type_expr()?;
                if self.peek().kind == SurfTokenKind::LBrace
                    && matches!(ty, TypeExpr::SynthesizedStruct { .. })
                {
                    self.parse_struct_lit_fields(ty)
                } else {
                    Ok(Expr::TypeVal(ty))
                }
            }
            SurfTokenKind::AtSizeOf | SurfTokenKind::AtAlignOf => {
                let align = self.peek().kind == SurfTokenKind::AtAlignOf;
                let intr = if align { "@align_of" } else { "@size_of" };
                self.advance();
                self.expect(&SurfTokenKind::LParen)?;
                let ty = self.parse_intrinsic_type_arg(intr, false)?;
                Ok(Expr::IntrinsicLayout { ty, align })
            }
            SurfTokenKind::AtDefault => {
                self.advance();
                self.expect(&SurfTokenKind::LParen)?;
                // `@default()`: of the type the context expects.
                let ty = if self.peek().kind == SurfTokenKind::RParen {
                    None
                } else {
                    Some(self.parse_type_expr()?)
                };
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
            SurfTokenKind::AtFormat => {
                self.advance();
                self.expect(&SurfTokenKind::LParen)?;
                let formatter = self.parse_expr()?;
                self.expect(&SurfTokenKind::Comma)?;
                let value = self.parse_expr()?;
                let spec = if self.peek().kind == SurfTokenKind::Comma {
                    self.advance();
                    if let SurfTokenKind::Str(s) = self.peek().kind.clone() {
                        self.advance();
                        Some(s)
                    } else {
                        None
                    }
                } else {
                    None
                };
                self.expect(&SurfTokenKind::RParen)?;
                Ok(Expr::IntrinsicFormat {
                    formatter: Box::new(formatter),
                    value: Box::new(value),
                    spec,
                })
            }
            SurfTokenKind::AtTrap => {
                self.advance();
                self.expect(&SurfTokenKind::LParen)?;
                self.expect(&SurfTokenKind::RParen)?;
                Ok(Expr::IntrinsicTrap)
            }
            SurfTokenKind::AtCompileError => {
                self.advance();
                Ok(Expr::IntrinsicCompileError(self.parse_call_args()?))
            }
            SurfTokenKind::AtInvert => {
                self.advance();
                self.expect(&SurfTokenKind::LParen)?;
                let inner = self.parse_expr()?;
                self.expect(&SurfTokenKind::RParen)?;
                Ok(Expr::IntrinsicInvert(Box::new(inner)))
            }
            SurfTokenKind::AtDeclarations => {
                self.advance();
                self.expect(&SurfTokenKind::LParen)?;
                let inner = self.parse_expr_or_type()?;
                self.expect(&SurfTokenKind::RParen)?;
                Ok(Expr::IntrinsicDeclarations(Box::new(inner)))
            }
            SurfTokenKind::AtTypeName => {
                self.advance();
                self.expect(&SurfTokenKind::LParen)?;
                let ty = self.parse_intrinsic_type_arg("@type_name", true)?;
                Ok(Expr::IntrinsicTypeName(Box::new(ty)))
            }
            SurfTokenKind::AtSatisfies => {
                self.advance();
                self.expect(&SurfTokenKind::LParen)?;
                let ty = self.parse_type_expr()?;
                self.expect(&SurfTokenKind::Comma)?;
                let bound = self.parse_type_expr()?;
                self.expect(&SurfTokenKind::RParen)?;
                Ok(Expr::IntrinsicSatisfies {
                    ty: Box::new(ty),
                    bound: Box::new(bound),
                })
            }
            SurfTokenKind::AtFields => {
                self.advance();
                self.expect(&SurfTokenKind::LParen)?;
                let ty = self.parse_type_expr()?;
                self.expect(&SurfTokenKind::RParen)?;
                Ok(Expr::IntrinsicFields(Box::new(ty)))
            }
            SurfTokenKind::AtLeaves => {
                self.advance();
                self.expect(&SurfTokenKind::LParen)?;
                let ty = self.parse_type_expr()?;
                self.expect(&SurfTokenKind::RParen)?;
                Ok(Expr::IntrinsicLeaves(Box::new(ty)))
            }
            SurfTokenKind::AtAssert => {
                let pos = self.src_pos();
                self.advance();
                self.expect(&SurfTokenKind::LParen)?;
                let cond_from = self.src_pos();
                let cond = Box::new(self.parse_expr()?);
                // Without a message, the condition as written says what failed.
                let quoted = self.source_between(cond_from, self.src_pos());
                let message = if self.peek().kind == SurfTokenKind::Comma {
                    self.advance();
                    let Expr::Str(m) = self.parse_expr()? else {
                        return Err("'@assert(cond, message)': the message is a string literal".to_string());
                    };
                    Some(m)
                } else if quoted.is_empty() {
                    None
                } else {
                    Some(quoted)
                };
                self.expect(&SurfTokenKind::RParen)?;
                Ok(Expr::IntrinsicAssert { cond, message, pos })
            }
            SurfTokenKind::AtHasField | SurfTokenKind::AtHasMethod => {
                let method = self.peek().kind == SurfTokenKind::AtHasMethod;
                self.advance();
                self.expect(&SurfTokenKind::LParen)?;
                let ty = Box::new(self.parse_type_expr()?);
                self.expect(&SurfTokenKind::Comma)?;
                let name = Box::new(self.parse_expr()?);
                self.expect(&SurfTokenKind::RParen)?;
                Ok(if method {
                    Expr::IntrinsicHasMethod { ty, name }
                } else {
                    Expr::IntrinsicHasField { ty, name }
                })
            }
            SurfTokenKind::AtVariants => {
                self.advance();
                self.expect(&SurfTokenKind::LParen)?;
                let ty = self.parse_type_expr()?;
                self.expect(&SurfTokenKind::RParen)?;
                Ok(Expr::IntrinsicVariants(Box::new(ty)))
            }
            SurfTokenKind::AtEntries => {
                self.advance();
                self.expect(&SurfTokenKind::LParen)?;
                let map_expr = self.parse_expr()?;
                self.expect(&SurfTokenKind::RParen)?;
                Ok(Expr::IntrinsicEntries(Box::new(map_expr)))
            }
            SurfTokenKind::AtFnInfo => {
                self.advance();
                self.expect(&SurfTokenKind::LParen)?;
                let ty = self.parse_type_expr()?;
                self.expect(&SurfTokenKind::RParen)?;
                Ok(Expr::IntrinsicFnInfo(Box::new(ty)))
            }
            SurfTokenKind::AtField => {
                self.advance();
                self.expect(&SurfTokenKind::LParen)?;
                let base = self.parse_expr()?;
                self.expect(&SurfTokenKind::Comma)?;
                let field = self.parse_expr()?;
                self.expect(&SurfTokenKind::RParen)?;
                Ok(Expr::IntrinsicField {
                    base: Box::new(base),
                    field: Box::new(field),
                })
            }
            SurfTokenKind::AtVariant => {
                self.advance();
                self.expect(&SurfTokenKind::LParen)?;
                let base = self.parse_expr()?;
                self.expect(&SurfTokenKind::Comma)?;
                let variant = self.parse_expr()?;
                self.expect(&SurfTokenKind::RParen)?;
                Ok(Expr::IntrinsicVariant {
                    base: Box::new(base),
                    variant: Box::new(variant),
                })
            }
            SurfTokenKind::AtMakeUnion => {
                self.advance();
                self.expect(&SurfTokenKind::LParen)?;
                let ty = self.parse_type_expr()?;
                self.expect(&SurfTokenKind::Comma)?;
                let variant = self.parse_expr()?;
                let payload = if self.peek().kind == SurfTokenKind::Comma {
                    self.advance();
                    if self.peek().kind == SurfTokenKind::RParen {
                        None
                    } else {
                        Some(Box::new(self.parse_expr_or_type()?))
                    }
                } else {
                    None
                };
                self.expect(&SurfTokenKind::RParen)?;
                Ok(Expr::IntrinsicMakeUnion {
                    ty: Box::new(ty),
                    variant: Box::new(variant),
                    payload,
                })
            }
            SurfTokenKind::AtMap => {
                self.advance();
                self.expect(&SurfTokenKind::LParen)?;
                let key_ty = self.parse_type_expr()?;
                self.expect(&SurfTokenKind::Comma)?;
                let val_ty = self.parse_type_expr()?;
                self.expect(&SurfTokenKind::Comma)?;
                let entries = self.parse_expr()?;
                self.expect(&SurfTokenKind::RParen)?;
                Ok(Expr::IntrinsicMap {
                    key_ty: Box::new(key_ty),
                    val_ty: Box::new(val_ty),
                    entries: Box::new(entries),
                })
            }
            _ => unreachable!(),
        }
    }

    fn check_int_suffix(
        v: &crate::wide::Wide,
        ty: &TypeExpr,
        line: usize,
        col: usize,
    ) -> Result<(), String> {
        let (signed, bits, name) = match ty {
            TypeExpr::Isize => (true, 64, "isize".to_string()),
            TypeExpr::Usize => (false, 64, "usize".to_string()),
            TypeExpr::Int { signed, bits } => (
                *signed,
                *bits,
                format!("{}{bits}", if *signed { 'i' } else { 'u' }),
            ),
            _ => return Ok(()),
        };
        if !v.fits(bits, signed) {
            return Err(format!(
                "Integer literal {v} does not fit in '{name}' (line {line}, column {col})"
            ));
        }
        Ok(())
    }

    fn parse_intrinsic_type_arg(&mut self, intr: &str, allow_bounds: bool) -> Result<TypeExpr, String> {
        let saved_pos = self.pos;
        let tok = self.peek().clone();
        match self.parse_type_expr() {
            Ok(ty)
                if self.peek().kind == SurfTokenKind::RParen
                    && (allow_bounds || !matches!(ty, TypeExpr::TraitBounds(_))) =>
            {
                self.advance();
                Ok(ty)
            }
            res => {
                self.pos = saved_pos;
                if self.parse_expr().is_ok() && self.peek().kind == SurfTokenKind::RParen {
                    return Err(format!(
                        "'{intr}' expects a type, found value expression; use '{intr}(@type_of(...))' (line {}, column {})",
                        tok.line, tok.col
                    ));
                }
                self.pos = saved_pos;
                let ty = res?;
                self.expect(&SurfTokenKind::RParen)?;
                Ok(ty)
            }
        }
    }
}

/// Whether evaluating `expr` twice is the same as once: a variable or a field path of one.
fn is_plain_place(expr: &Expr) -> bool {
    match expr {
        Expr::Path(_) => true,
        Expr::Field { base, .. } | Expr::TupleIndex { base, .. } | Expr::Deref(base) => is_plain_place(base),
        _ => false,
    }
}

/// The operator of a compound assignment token (`+=`, `&=`, `<<=`, ...).
fn compound_assign_op(kind: &SurfTokenKind) -> Option<BinOp> {
    Some(match kind {
        SurfTokenKind::PlusEq => BinOp::Add,
        SurfTokenKind::MinusEq => BinOp::Sub,
        SurfTokenKind::StarEq => BinOp::Mul,
        SurfTokenKind::SlashEq => BinOp::Div,
        SurfTokenKind::PercentEq => BinOp::Rem,
        SurfTokenKind::AmpEq => BinOp::BitAnd,
        SurfTokenKind::PipeEq => BinOp::BitOr,
        SurfTokenKind::CaretEq => BinOp::BitXor,
        SurfTokenKind::ShlEq => BinOp::Shl,
        SurfTokenKind::ShrEq => BinOp::Shr,
        SurfTokenKind::PlusPercentEq => BinOp::AddWrap,
        SurfTokenKind::MinusPercentEq => BinOp::SubWrap,
        SurfTokenKind::StarPercentEq => BinOp::MulWrap,
        SurfTokenKind::PlusPipeEq => BinOp::AddSat,
        SurfTokenKind::MinusPipeEq => BinOp::SubSat,
        SurfTokenKind::StarPipeEq => BinOp::MulSat,
        _ => return None,
    })
}
