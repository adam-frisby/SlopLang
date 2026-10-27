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

    pub(super) fn parse_block(&mut self) -> Result<Block, String> {
        let saved = self.cond_start.take();
        let res = self.parse_block_inner();
        self.cond_start = saved;
        res
    }

    fn parse_block_inner(&mut self) -> Result<Block, String> {
        self.expect(&SurfTokenKind::LBrace)?;
        let mut stmts = Vec::new();
        while self.peek().kind != SurfTokenKind::RBrace && self.peek().kind != SurfTokenKind::Eof {
            stmts.push(self.parse_stmt()?);
        }
        self.expect(&SurfTokenKind::RBrace)?;
        Ok(Block { stmts })
    }

    pub(super) fn parse_expr_block(&mut self) -> Result<Block, String> {
        self.expect(&SurfTokenKind::LBrace)?;
        let mut stmts = Vec::new();
        while self.peek().kind != SurfTokenKind::RBrace && self.peek().kind != SurfTokenKind::Eof {
            if matches!(
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
                    SurfTokenKind::PlusEq => {
                        self.advance();
                        let value = self.parse_expr()?;
                        self.expect(&SurfTokenKind::Semi)?;
                        stmts.push(Stmt::Assign {
                            target: expr,
                            op: Some(BinOp::Add),
                            value,
                        });
                    }
                    SurfTokenKind::MinusEq => {
                        self.advance();
                        let value = self.parse_expr()?;
                        self.expect(&SurfTokenKind::Semi)?;
                        stmts.push(Stmt::Assign {
                            target: expr,
                            op: Some(BinOp::Sub),
                            value,
                        });
                    }
                    SurfTokenKind::StarEq => {
                        self.advance();
                        let value = self.parse_expr()?;
                        self.expect(&SurfTokenKind::Semi)?;
                        stmts.push(Stmt::Assign {
                            target: expr,
                            op: Some(BinOp::Mul),
                            value,
                        });
                    }
                    SurfTokenKind::RBrace => {
                        stmts.push(Stmt::Expr(expr));
                    }
                    _ => {
                        self.expect(&SurfTokenKind::Semi)?;
                        stmts.push(Stmt::Expr(expr));
                    }
                }
            }
        }
        self.expect(&SurfTokenKind::RBrace)?;
        Ok(Block { stmts })
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
                    "Expected ',' or '}}' after match arm at {}:{}",
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
            let op = if self.peek().kind == SurfTokenKind::DefaultKw
                || matches!(&self.peek().kind, SurfTokenKind::Ident(s) if s == "default")
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
                    } if (method == "recv" || method == "wait") && args.is_empty() => {
                        SelectOp::Recv {
                            bind,
                            source: *receiver,
                        }
                    }
                    Expr::MethodCall {
                        receiver,
                        method,
                        mut args,
                    } if method == "send" && args.len() == 1 => {
                        if bind.is_some() {
                            return Err(format!(
                                "Cannot bind a variable to a '.send(...)' branch in '@select' at {}:{}",
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
                    _ => {
                        return Err(format!(
                            "Expected '.recv()', '.send(val)', '.wait()', or 'default' in '@select' arm at {}:{}",
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
                    "Expected ',' or '}}' after '@select' arm at {}:{}",
                    self.peek().line,
                    self.peek().col
                ));
            }
        }
        self.expect(&SurfTokenKind::RBrace)?;
        Ok(arms)
    }

    pub(super) fn parse_match_pat(&mut self) -> Result<MatchPat, String> {
        match &self.peek().kind {
            SurfTokenKind::Ident(s)
                if s == "_" && self.peek_n(1).kind != SurfTokenKind::ColonColon =>
            {
                self.advance();
                Ok(MatchPat::Wildcard)
            }
            SurfTokenKind::Int(n) => {
                let val = *n;
                self.advance();
                Ok(MatchPat::Int(val))
            }
            SurfTokenKind::Minus => {
                self.advance();
                match self.advance().kind {
                    SurfTokenKind::Int(n) => Ok(MatchPat::Int(-n)),
                    other => Err(format!(
                        "Expected integer after '-' in match pattern, found {:?}",
                        other
                    )),
                }
            }
            SurfTokenKind::Move => {
                self.advance();
                let name = self.expect_ident()?;
                Ok(MatchPat::CatchAllBind {
                    is_move: true,
                    name,
                })
            }
            SurfTokenKind::Dot => {
                self.advance();
                let name = self.expect_ident()?;
                let binding = if self.peek().kind == SurfTokenKind::LParen {
                    Some(self.parse_pattern_binding()?)
                } else {
                    None
                };
                Ok(MatchPat::DotVariant { name, binding })
            }
            SurfTokenKind::Ident(_) => {
                let mut path = vec![self.expect_ident()?];
                while self.peek().kind == SurfTokenKind::ColonColon {
                    self.advance();
                    path.push(self.expect_ident()?);
                }
                if self.peek().kind == SurfTokenKind::LParen {
                    Ok(MatchPat::Variant {
                        path,
                        binding: Some(self.parse_pattern_binding()?),
                    })
                } else if path.len() >= 2 {
                    Ok(MatchPat::Variant {
                        path,
                        binding: None,
                    })
                } else {
                    Ok(MatchPat::CatchAllBind {
                        is_move: false,
                        name: path.into_iter().next().unwrap(),
                    })
                }
            }
            _ => {
                let tok = self.peek();
                Err(format!(
                    "Expected match pattern, found {:?} at {}:{}",
                    tok.kind, tok.line, tok.col
                ))
            }
        }
    }

    /// The `(x)` / `(move x)` / `(ref mut x)` payload binding of a variant pattern.
    fn parse_pattern_binding(&mut self) -> Result<(BindMode, String), String> {
        self.advance();
        let mode = if self.peek().kind == SurfTokenKind::Move {
            self.advance();
            BindMode::Move
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
            BindMode::Ref { mutable }
        } else {
            BindMode::Default
        };
        let bind_name = self.expect_ident()?;
        self.expect(&SurfTokenKind::RParen)?;
        Ok((mode, bind_name))
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
        // `label: while ...` / `label: for ...`
        if let SurfTokenKind::Ident(label) = &self.peek().kind
            && self.peek_n(1).kind == SurfTokenKind::Colon
            && (self.peek_n(2).kind == SurfTokenKind::While
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
                    let pat = self.parse_match_pat()?;
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

    /// Whether the tokens after the current `let` form a variant pattern (`Msg::Ping(x)`,
    /// `Msg::Quit`) rather than the `?T` binding form (`let v = ...`).
    fn let_variant_pattern_ahead(&self) -> bool {
        self.peek().kind == SurfTokenKind::Let
            && ((matches!(self.peek_n(1).kind, SurfTokenKind::Ident(_))
                && matches!(
                    self.peek_n(2).kind,
                    SurfTokenKind::ColonColon | SurfTokenKind::LParen
                ))
                || (self.peek_n(1).kind == SurfTokenKind::Dot
                    && matches!(self.peek_n(2).kind, SurfTokenKind::Ident(_))))
    }

    pub(super) fn parse_if_stmt(&mut self) -> Result<Stmt, String> {
        self.expect(&SurfTokenKind::If)?;
        if self.let_variant_pattern_ahead() {
            // `if let Msg::Ping(seq) = msg { A } else { B }` is `match msg { Msg::Ping(seq) => { A }, _ => { B } }`.
            self.advance();
            let pat = self.parse_match_pat()?;
            self.expect(&SurfTokenKind::Eq)?;
            let scrutinee = self.parse_cond_expr()?;
            let then_block = self.parse_block()?;
            let else_block = if self.peek().kind == SurfTokenKind::Else {
                self.advance();
                if self.peek().kind == SurfTokenKind::If {
                    Block {
                        stmts: vec![self.parse_if_stmt()?],
                    }
                } else {
                    self.parse_block()?
                }
            } else {
                Block { stmts: Vec::new() }
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
        let mut expr = self.parse_primary()?;
        loop {
            match &self.peek().kind {
                SurfTokenKind::ColonColon => {
                    self.advance();
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
                SurfTokenKind::Dot => {
                    if self.peek_n(1).kind == SurfTokenKind::LBrace {
                        let tok = self.peek_n(1);
                        return Err(format!(
                            "Write a struct literal as 'Type {{ field: value }}', or '{{ field: value }}' where the type is known, at {}:{}",
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
                    let first = self.parse_expr_or_type()?;
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
                        && ((self.peek_n(1).kind == SurfTokenKind::RBrace
                            && self.empty_struct_lit_allowed())
                            || (matches!(self.peek_n(1).kind, SurfTokenKind::Ident(_))
                                && self.peek_n(2).kind == SurfTokenKind::Colon))
                        && let Expr::Path(path) = expr
                    {
                        let ty = TypeExpr::TypeCall { path, args };
                        return self.parse_struct_lit_fields(ty);
                    }
                    // Check if `TypeCall(args)::method(...)` static method call!
                    if self.peek().kind == SurfTokenKind::ColonColon
                        && let Expr::Path(path) = expr
                    {
                        self.advance();
                        let method = self.expect_ident()?;
                        self.expect(&SurfTokenKind::LParen)?;
                        let mut call_args = Vec::new();
                        while self.peek().kind != SurfTokenKind::RParen {
                            call_args.push(self.parse_expr_or_type()?);
                            if self.peek().kind == SurfTokenKind::Comma {
                                self.advance();
                            } else {
                                break;
                            }
                        }
                        self.expect(&SurfTokenKind::RParen)?;
                        let ty = TypeExpr::TypeCall { path, args };
                        expr = Expr::MethodCall {
                            receiver: Box::new(Expr::TypeVal(ty)),
                            method,
                            args: call_args,
                        };
                        continue;
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
                self.advance();
                Ok(Expr::Int(n))
            }
            SurfTokenKind::WideInt(w) => {
                self.advance();
                Ok(Expr::WideInt(w))
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
            | SurfTokenKind::AtMemcpy
            | SurfTokenKind::AtMemmove
            | SurfTokenKind::AtTransmute
            | SurfTokenKind::AtForget
            | SurfTokenKind::AtCAbi
            | SurfTokenKind::AtBswap
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
            | SurfTokenKind::AtInvert
            | SurfTokenKind::AtDeclarations
            | SurfTokenKind::AtTypeName
            | SurfTokenKind::AtSatisfies
            | SurfTokenKind::AtFields
            | SurfTokenKind::AtHasField
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
                    SurfTokenKind::Sync | SurfTokenKind::Linear
                ) {
                    return Ok(Expr::TypeVal(self.parse_type_expr()?));
                }
                self.advance();
                let blk = self.parse_expr_block()?;
                Ok(Expr::UnsafeBlock(blk))
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
                "Expected expression, found {:?} at {}:{}",
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
                self.advance();
                self.expect(&SurfTokenKind::LParen)?;
                let ty = self.parse_type_expr()?;
                self.expect(&SurfTokenKind::RParen)?;
                Ok(Expr::IntrinsicLayout { ty, align })
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
                let ty = self.parse_type_expr()?;
                self.expect(&SurfTokenKind::RParen)?;
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
            SurfTokenKind::AtHasField => {
                self.advance();
                self.expect(&SurfTokenKind::LParen)?;
                let ty = self.parse_type_expr()?;
                self.expect(&SurfTokenKind::Comma)?;
                let name = self.parse_expr()?;
                self.expect(&SurfTokenKind::RParen)?;
                Ok(Expr::IntrinsicHasField {
                    ty: Box::new(ty),
                    name: Box::new(name),
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
}
