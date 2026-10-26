use super::*;

impl SurfaceParser {
    pub(super) fn parse_block(&mut self) -> Result<Block, String> {
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
            SurfTokenKind::Ident(_) => {
                let mut path = vec![self.expect_ident()?];
                while self.peek().kind == SurfTokenKind::ColonColon {
                    self.advance();
                    path.push(self.expect_ident()?);
                }
                if self.peek().kind == SurfTokenKind::LParen {
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
                    Ok(MatchPat::Variant {
                        path,
                        binding: Some((mode, bind_name)),
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

    pub(super) fn parse_stmt(&mut self) -> Result<Stmt, String> {
        match &self.peek().kind {
            SurfTokenKind::Let | SurfTokenKind::Comptime | SurfTokenKind::Const => {
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
            SurfTokenKind::Match => {
                self.advance();
                let scrutinee = self.parse_expr()?;
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
                    let scrutinee = self.parse_expr()?;
                    let body = self.parse_block()?;
                    return Ok(Stmt::While {
                        cond: Expr::Bool(true),
                        body: Block {
                            stmts: vec![Stmt::Match {
                                scrutinee,
                                arms: vec![(pat, Expr::Block(body)), (MatchPat::Wildcard, Expr::Break)],
                            }],
                        },
                    });
                }
                if self.peek().kind == SurfTokenKind::Let {
                    self.advance();
                    let var_name = self.expect_ident()?;
                    self.expect(&SurfTokenKind::Eq)?;
                    let opt_expr = self.parse_expr()?;
                    let body = self.parse_block()?;
                    return Ok(Stmt::WhileLet {
                        var_name,
                        opt_expr,
                        body,
                    });
                }
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

    /// Whether the tokens after the current `let` form a variant pattern (`Msg::Ping(x)`,
    /// `Msg::Quit`) rather than the `?T` binding form (`let v = ...`).
    fn let_variant_pattern_ahead(&self) -> bool {
        self.peek().kind == SurfTokenKind::Let
            && matches!(self.peek_n(1).kind, SurfTokenKind::Ident(_))
            && matches!(
                self.peek_n(2).kind,
                SurfTokenKind::ColonColon | SurfTokenKind::LParen
            )
    }

    pub(super) fn parse_if_stmt(&mut self) -> Result<Stmt, String> {
        self.expect(&SurfTokenKind::If)?;
        if self.let_variant_pattern_ahead() {
            // `if let Msg::Ping(seq) = msg { A } else { B }` is `match msg { Msg::Ping(seq) => { A }, _ => { B } }`.
            self.advance();
            let pat = self.parse_match_pat()?;
            self.expect(&SurfTokenKind::Eq)?;
            let scrutinee = self.parse_expr()?;
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

    pub(super) fn parse_logical_or(&mut self) -> Result<Expr, String> {
        let mut lhs = self.parse_logical_and()?;
        while self.peek().kind == SurfTokenKind::PipePipe {
            self.advance();
            let rhs = self.parse_logical_and()?;
            lhs = Expr::LogicalOr(Box::new(lhs), Box::new(rhs));
        }
        Ok(lhs)
    }

    pub(super) fn parse_logical_and(&mut self) -> Result<Expr, String> {
        let mut lhs = self.parse_comparison()?;
        while self.peek().kind == SurfTokenKind::AmpAmp {
            self.advance();
            let rhs = self.parse_comparison()?;
            lhs = Expr::LogicalAnd(Box::new(lhs), Box::new(rhs));
        }
        Ok(lhs)
    }

    pub(super) fn parse_comparison(&mut self) -> Result<Expr, String> {
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

    pub(super) fn parse_bitwise_or(&mut self) -> Result<Expr, String> {
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

    pub(super) fn parse_bitwise_xor(&mut self) -> Result<Expr, String> {
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

    pub(super) fn parse_bitwise_and(&mut self) -> Result<Expr, String> {
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

    pub(super) fn parse_shift(&mut self) -> Result<Expr, String> {
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

    pub(super) fn parse_additive_expr(&mut self) -> Result<Expr, String> {
        let mut lhs = self.parse_multiplicative_expr()?;
        loop {
            let op = match self.peek().kind {
                SurfTokenKind::Plus => BinOp::Add,
                SurfTokenKind::PlusPercent => BinOp::AddWrap,
                SurfTokenKind::PlusPipe => BinOp::AddSat,
                SurfTokenKind::PlusQuestion => BinOp::AddChecked,
                SurfTokenKind::Minus => BinOp::Sub,
                SurfTokenKind::MinusPercent => BinOp::SubWrap,
                SurfTokenKind::MinusPipe => BinOp::SubSat,
                SurfTokenKind::MinusQuestion => BinOp::SubChecked,
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

    pub(super) fn parse_multiplicative_expr(&mut self) -> Result<Expr, String> {
        let mut lhs = self.parse_cast_or_orelse()?;
        loop {
            let op = match self.peek().kind {
                SurfTokenKind::Star => BinOp::Mul,
                SurfTokenKind::StarPercent => BinOp::MulWrap,
                SurfTokenKind::StarPipe => BinOp::MulSat,
                SurfTokenKind::StarQuestion => BinOp::MulChecked,
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
                        elems.push(self.parse_expr()?);
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
                        && matches!(self.peek_n(1).kind, SurfTokenKind::Ident(_))
                        && self.peek_n(2).kind == SurfTokenKind::Colon
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
            | SurfTokenKind::AtInt => {
                let ty = self.parse_base_type_expr()?;
                Ok(Expr::TypeVal(ty))
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
                let inner = self.parse_expr()?;
                self.expect(&SurfTokenKind::RParen)?;
                Ok(Expr::IntrinsicDeclarations(Box::new(inner)))
            }
            SurfTokenKind::If => {
                self.advance();
                let cond = self.parse_expr()?;
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
            SurfTokenKind::Break => {
                self.advance();
                Ok(Expr::Break)
            }
            SurfTokenKind::Continue => {
                self.advance();
                Ok(Expr::Continue)
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
                let scrutinee = self.parse_expr()?;
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
                            elems.push(self.parse_expr()?);
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
