use crate::ir::{
    BasicBlock, BlockId, ConstValue, ExternFunc, FuncId, Function, Global, GlobalId, LocalId,
    Operand, Place, Program, Projection, Rvalue, Statement, Terminator, Type, TypeId,
};
use crate::lexer::{Lexer, Token, TokenKind};

pub struct Parser {
    tokens: Vec<Token>,
    pos: usize,
}

impl Parser {
    pub fn parse_program(source: &str) -> Result<Program, String> {
        let tokens = Lexer::new(source).tokenize()?;
        let mut parser = Self { tokens, pos: 0 };
        let mut types = Vec::new();
        let mut destructors = Vec::new();
        let mut globals = Vec::new();
        let mut externs = Vec::new();
        let mut functions = Vec::new();

        while let TokenKind::Type(_) = parser.peek().kind {
            let ty_id = parser.expect_type_id()?;
            if ty_id.0 as usize != types.len() {
                return Err(format!("Expected ty{}, found {ty_id}", types.len()));
            }
            parser.expect(&TokenKind::Eq)?;
            let ty = parser.parse_type_def()?;
            parser.expect(&TokenKind::Semi)?;
            types.push(ty);
        }

        while parser.peek().kind == TokenKind::Drop {
            parser.advance();
            let ty_id = parser.expect_type_id()?;
            parser.expect(&TokenKind::Eq)?;
            let fn_id = parser.expect_func_id()?;
            parser.expect(&TokenKind::Semi)?;
            destructors.push((ty_id, fn_id));
        }

        while parser.peek().kind == TokenKind::GlobalKw {
            globals.push(parser.parse_global()?);
        }

        while parser.peek().kind == TokenKind::Extern {
            externs.push(parser.parse_extern_func()?);
        }

        while parser.peek().kind != TokenKind::Eof {
            functions.push(parser.parse_function()?);
        }

        Ok(Program {
            types,
            destructors,
            linear_types: Vec::new(),
            raw_ptr_types: Vec::new(),
            own_ptr_types: Vec::new(),
            view_ptr_types: Vec::new(),
            loan_types: Vec::new(),
            dangle_types: Vec::new(),
            thread_local_globals: Vec::new(),
            c_fn_ptr_types: Vec::new(),
            fn_ptr_contracts: Vec::new(),
            tagged_unions: Vec::new(),
            union_tag_values: Vec::new(),
            type_names: Vec::new(),
            field_names: Vec::new(),
            globals,
            externs,
            functions,
        })
    }

    pub fn parse(source: &str) -> Result<Vec<Function>, String> {
        Ok(Self::parse_program(source)?.functions)
    }

    fn peek(&self) -> &Token {
        &self.tokens[self.pos]
    }

    fn advance(&mut self) -> &Token {
        let tok = &self.tokens[self.pos];
        if self.pos + 1 < self.tokens.len() {
            self.pos += 1;
        }
        tok
    }

    fn expect(&mut self, expected: &TokenKind) -> Result<(), String> {
        let tok = self.peek();
        if &tok.kind == expected {
            self.advance();
            Ok(())
        } else {
            Err(format!(
                "Expected {:?}, found {:?} at {}:{}",
                expected, tok.kind, tok.line, tok.col
            ))
        }
    }

    fn expect_type_id(&mut self) -> Result<TypeId, String> {
        let tok = self.peek().clone();
        if let TokenKind::Type(id) = tok.kind {
            self.advance();
            Ok(id)
        } else {
            Err(format!(
                "Expected TypeId (ty<N>), found {:?} at {}:{}",
                tok.kind, tok.line, tok.col
            ))
        }
    }

    fn expect_local_id(&mut self) -> Result<LocalId, String> {
        let tok = self.peek().clone();
        if let TokenKind::Local(id) = tok.kind {
            self.advance();
            Ok(id)
        } else {
            Err(format!(
                "Expected LocalId (_<N>), found {:?} at {}:{}",
                tok.kind, tok.line, tok.col
            ))
        }
    }

    fn expect_block_id(&mut self) -> Result<BlockId, String> {
        let tok = self.peek().clone();
        if let TokenKind::Block(id) = tok.kind {
            self.advance();
            Ok(id)
        } else {
            Err(format!(
                "Expected BlockId (bb<N>), found {:?} at {}:{}",
                tok.kind, tok.line, tok.col
            ))
        }
    }

    fn expect_func_id(&mut self) -> Result<FuncId, String> {
        let tok = self.peek().clone();
        if let TokenKind::Func(id) = tok.kind {
            self.advance();
            Ok(id)
        } else {
            Err(format!(
                "Expected FuncId (fn<N>), found {:?} at {}:{}",
                tok.kind, tok.line, tok.col
            ))
        }
    }

    fn expect_global_id(&mut self) -> Result<GlobalId, String> {
        let tok = self.peek().clone();
        if let TokenKind::Global(id) = tok.kind {
            self.advance();
            Ok(id)
        } else {
            Err(format!(
                "Expected GlobalId (gl<N>), found {:?} at {}:{}",
                tok.kind, tok.line, tok.col
            ))
        }
    }

    fn expect_variant_idx(&mut self) -> Result<u32, String> {
        let tok = self.peek().clone();
        if let TokenKind::Variant(idx) = tok.kind {
            self.advance();
            Ok(idx)
        } else {
            Err(format!(
                "Expected Variant index (v<N>), found {:?} at {}:{}",
                tok.kind, tok.line, tok.col
            ))
        }
    }

    fn parse_global(&mut self) -> Result<Global, String> {
        self.expect(&TokenKind::GlobalKw)?;
        let mutable = if self.peek().kind == TokenKind::Mut {
            self.advance();
            true
        } else {
            false
        };
        let id = self.expect_global_id()?;
        self.expect(&TokenKind::Colon)?;
        let ty = self.expect_type_id()?;
        self.expect(&TokenKind::Eq)?;
        let Operand::Const(init) = self.parse_operand()? else {
            let tok = self.peek();
            return Err(format!(
                "Global initializer must be 'const <val>' at {}:{}",
                tok.line, tok.col
            ));
        };
        self.expect(&TokenKind::Semi)?;
        Ok(Global {
            id,
            mutable,
            ty,
            init,
        })
    }

    fn parse_extern_func(&mut self) -> Result<ExternFunc, String> {
        self.expect(&TokenKind::Extern)?;
        let id = self.expect_func_id()?;
        self.expect(&TokenKind::LParen)?;
        let mut args = Vec::new();
        while self.peek().kind != TokenKind::RParen {
            args.push(self.expect_type_id()?);
            if self.peek().kind == TokenKind::Comma {
                self.advance();
            } else {
                break;
            }
        }
        self.expect(&TokenKind::RParen)?;
        self.expect(&TokenKind::Arrow)?;
        let ret = self.expect_type_id()?;
        self.expect(&TokenKind::Eq)?;
        let tok = self.peek().clone();
        let TokenKind::Str(symbol) = tok.kind else {
            return Err(format!(
                "Expected string symbol name in extern declaration, found {:?} at {}:{}",
                tok.kind, tok.line, tok.col
            ));
        };
        self.advance();
        self.expect(&TokenKind::Semi)?;
        Ok(ExternFunc {
            id,
            args,
            ret,
            symbol,
        })
    }

    fn parse_type_def(&mut self) -> Result<Type, String> {
        match &self.peek().kind {
            TokenKind::Void => {
                self.advance();
                Ok(Type::Void)
            }
            TokenKind::Never => {
                self.advance();
                Ok(Type::Never)
            }
            TokenKind::Bool => {
                self.advance();
                Ok(Type::Bool)
            }
            TokenKind::Rune => {
                self.advance();
                Ok(Type::Rune)
            }
            TokenKind::IntType { signed, bits } => {
                let (signed, bits) = (*signed, *bits);
                self.advance();
                Ok(Type::Int { signed, bits })
            }
            TokenKind::F32 => {
                self.advance();
                Ok(Type::F32)
            }
            TokenKind::F64 => {
                self.advance();
                Ok(Type::F64)
            }
            TokenKind::MetaType => {
                self.advance();
                Ok(Type::MetaType)
            }
            TokenKind::Type(base) => {
                let base = *base;
                self.advance();
                self.expect(&TokenKind::In)?;
                let mut ranges = Vec::new();
                loop {
                    let tok = self.peek().clone();
                    let lo = match tok.kind {
                        TokenKind::Int(n) => crate::wide::Wide::from_i128(n),
                        TokenKind::WideInt(w) => *w,
                        other => {
                            return Err(format!(
                                "Expected integer range lower bound, found {other:?} at {}:{}",
                                tok.line, tok.col
                            ));
                        }
                    };
                    self.advance();
                    self.expect(&TokenKind::DotDotEq)?;
                    let tok = self.peek().clone();
                    let hi = match tok.kind {
                        TokenKind::Int(n) => crate::wide::Wide::from_i128(n),
                        TokenKind::WideInt(w) => *w,
                        other => {
                            return Err(format!(
                                "Expected integer range upper bound, found {other:?} at {}:{}",
                                tok.line, tok.col
                            ));
                        }
                    };
                    self.advance();
                    ranges.push((lo, hi));
                    if self.peek().kind == TokenKind::Pipe {
                        self.advance();
                    } else {
                        break;
                    }
                }
                Ok(Type::Pattern { base, ranges })
            }
            TokenKind::Amp => {
                self.advance();
                let mutable = if self.peek().kind == TokenKind::Mut {
                    self.advance();
                    true
                } else {
                    false
                };
                let pointee = self.expect_type_id()?;
                Ok(Type::Ptr { mutable, pointee })
            }
            TokenKind::LBracket => {
                self.advance();
                let elem = self.expect_type_id()?;
                self.expect(&TokenKind::Semi)?;
                let tok = self.peek().clone();
                let TokenKind::Int(len) = tok.kind else {
                    return Err(format!(
                        "Expected array length integer, found {:?} at {}:{}",
                        tok.kind, tok.line, tok.col
                    ));
                };
                if len < 0 {
                    return Err(format!(
                        "Array length cannot be negative at {}:{}",
                        tok.line, tok.col
                    ));
                }
                self.advance();
                self.expect(&TokenKind::RBracket)?;
                Ok(Type::Array {
                    elem,
                    len: len as u64,
                })
            }
            TokenKind::Simd => {
                self.advance();
                self.expect(&TokenKind::LBracket)?;
                let elem = self.expect_type_id()?;
                self.expect(&TokenKind::Semi)?;
                let tok = self.peek().clone();
                let TokenKind::Int(len) = tok.kind else {
                    return Err(format!(
                        "Expected SIMD lane count integer, found {:?} at {}:{}",
                        tok.kind, tok.line, tok.col
                    ));
                };
                if len <= 0 {
                    return Err(format!(
                        "SIMD lane count must be positive at {}:{}",
                        tok.line, tok.col
                    ));
                }
                self.advance();
                self.expect(&TokenKind::RBracket)?;
                Ok(Type::Simd {
                    elem,
                    len: len as u64,
                })
            }
            TokenKind::LBrace => {
                self.advance();
                let mut fields = Vec::new();
                while self.peek().kind != TokenKind::RBrace {
                    fields.push(self.expect_type_id()?);
                    if self.peek().kind == TokenKind::Comma {
                        self.advance();
                    } else {
                        break;
                    }
                }
                self.expect(&TokenKind::RBrace)?;
                Ok(Type::Struct(fields))
            }
            TokenKind::Overlay => {
                self.advance();
                self.expect(&TokenKind::LBrace)?;
                let mut fields = Vec::new();
                while self.peek().kind != TokenKind::RBrace {
                    fields.push(self.expect_type_id()?);
                    if self.peek().kind == TokenKind::Comma {
                        self.advance();
                    } else {
                        break;
                    }
                }
                self.expect(&TokenKind::RBrace)?;
                Ok(Type::Overlay(fields))
            }
            TokenKind::Union => {
                self.advance();
                let tag = self.expect_type_id()?;
                self.expect(&TokenKind::LBrace)?;
                let mut variants = Vec::new();
                while self.peek().kind != TokenKind::RBrace {
                    variants.push(self.expect_type_id()?);
                    if self.peek().kind == TokenKind::Comma {
                        self.advance();
                    } else {
                        break;
                    }
                }
                self.expect(&TokenKind::RBrace)?;
                Ok(Type::Union { tag, variants })
            }
            TokenKind::Fn => {
                self.advance();
                self.expect(&TokenKind::LParen)?;
                let mut args = Vec::new();
                while self.peek().kind != TokenKind::RParen {
                    args.push(self.expect_type_id()?);
                    if self.peek().kind == TokenKind::Comma {
                        self.advance();
                    } else {
                        break;
                    }
                }
                self.expect(&TokenKind::RParen)?;
                self.expect(&TokenKind::Arrow)?;
                let ret = self.expect_type_id()?;
                Ok(Type::FnPtr { args, ret })
            }
            _ => {
                let tok = self.peek();
                Err(format!(
                    "Expected type definition, found {:?} at {}:{}",
                    tok.kind, tok.line, tok.col
                ))
            }
        }
    }

    fn parse_function(&mut self) -> Result<Function, String> {
        let id = self.expect_func_id()?;
        let arg_count = if self.peek().kind == TokenKind::LParen {
            self.advance();
            let tok = self.peek().clone();
            let TokenKind::Int(n) = tok.kind else {
                return Err(format!(
                    "Expected parameter count integer in {id}(...), found {:?} at {}:{}",
                    tok.kind, tok.line, tok.col
                ));
            };
            self.advance();
            self.expect(&TokenKind::RParen)?;
            n as usize
        } else {
            0
        };

        let ret_borrows = if self.peek().kind == TokenKind::Borrows {
            self.advance();
            self.expect(&TokenKind::LParen)?;
            let mut params = Vec::new();
            while self.peek().kind != TokenKind::RParen {
                params.push(self.expect_local_id()?);
                if self.peek().kind == TokenKind::Comma {
                    self.advance();
                } else {
                    break;
                }
            }
            self.expect(&TokenKind::RParen)?;
            Some(params)
        } else {
            None
        };

        let export = if self.peek().kind == TokenKind::Eq {
            self.advance();
            let tok = self.peek().clone();
            let TokenKind::Str(sym) = tok.kind else {
                return Err(format!(
                    "Expected string export symbol after '=' in {id}, found {:?} at {}:{}",
                    tok.kind, tok.line, tok.col
                ));
            };
            self.advance();
            Some(sym)
        } else {
            None
        };

        self.expect(&TokenKind::LBrace)?;

        // Parse local declarations: `let _0: ty0;`
        let mut locals = Vec::new();
        while self.peek().kind == TokenKind::Let {
            self.advance();
            let local_id = self.expect_local_id()?;
            if local_id.0 as usize != locals.len() {
                return Err(format!(
                    "Expected local _{} declaration, found {local_id} in {id}",
                    locals.len()
                ));
            }
            self.expect(&TokenKind::Colon)?;
            let ty_id = self.expect_type_id()?;
            self.expect(&TokenKind::Semi)?;
            locals.push(ty_id);
        }

        // Parse basic blocks: `bb0: { ... }`
        let mut blocks = Vec::new();
        while self.peek().kind != TokenKind::RBrace {
            let block_id = self.expect_block_id()?;
            if block_id.0 as usize != blocks.len() {
                return Err(format!(
                    "Expected bb{}, found {block_id} in {id}",
                    blocks.len()
                ));
            }
            self.expect(&TokenKind::Colon)?;
            self.expect(&TokenKind::LBrace)?;

            let mut statements = Vec::new();
            let mut terminator = None;

            while self.peek().kind != TokenKind::RBrace {
                if self.is_terminator_keyword() {
                    terminator = Some(self.parse_terminator()?);
                    break;
                }

                // Distinguish `<Place> = call ...` (Terminator::Call) from `<Place> = <Rvalue>;` (Statement::Assign)
                if matches!(
                    self.peek().kind,
                    TokenKind::Local(_) | TokenKind::LParen | TokenKind::Star
                ) {
                    let saved_pos = self.pos;
                    let place = self.parse_place()?;
                    self.expect(&TokenKind::Eq)?;
                    if self.peek().kind == TokenKind::Call {
                        terminator = Some(self.parse_call_terminator(place)?);
                        break;
                    } else {
                        self.pos = saved_pos;
                        statements.push(self.parse_statement()?);
                    }
                } else {
                    statements.push(self.parse_statement()?);
                }
            }

            let terminator = terminator
                .ok_or_else(|| format!("Basic block {block_id} in {id} is missing a terminator"))?;
            self.expect(&TokenKind::RBrace)?;
            blocks.push(BasicBlock {
                statements,
                terminator,
            });
        }

        self.expect(&TokenKind::RBrace)?;
        Ok(Function {
            id,
            export,
            arg_count,
            ret_borrows,
            param_borrows: None,
            linear_self: None,
            linear_owner: false,
            debug_name: None,
            param_names: Vec::new(),
            local_names: Vec::new(),
            locals,
            blocks,
        })
    }

    fn is_terminator_keyword(&self) -> bool {
        matches!(
            self.peek().kind,
            TokenKind::Goto
                | TokenKind::SwitchInt
                | TokenKind::Drop
                | TokenKind::Return
                | TokenKind::Unreachable
        )
    }

    fn parse_statement(&mut self) -> Result<Statement, String> {
        match &self.peek().kind {
            TokenKind::StorageLive => {
                self.advance();
                self.expect(&TokenKind::LParen)?;
                let local = self.expect_local_id()?;
                self.expect(&TokenKind::RParen)?;
                self.expect(&TokenKind::Semi)?;
                Ok(Statement::StorageLive(local))
            }
            TokenKind::StorageDead => {
                self.advance();
                self.expect(&TokenKind::LParen)?;
                let local = self.expect_local_id()?;
                self.expect(&TokenKind::RParen)?;
                self.expect(&TokenKind::Semi)?;
                Ok(Statement::StorageDead(local))
            }
            TokenKind::Discriminant => {
                self.advance();
                self.expect(&TokenKind::LParen)?;
                let place = self.parse_place()?;
                self.expect(&TokenKind::RParen)?;
                self.expect(&TokenKind::Eq)?;
                let variant = self.expect_variant_idx()?;
                self.expect(&TokenKind::Semi)?;
                Ok(Statement::SetDiscriminant(place, variant))
            }
            _ => {
                let place = self.parse_place()?;
                self.expect(&TokenKind::Eq)?;
                let rvalue = self.parse_rvalue()?;
                self.expect(&TokenKind::Semi)?;
                Ok(Statement::Assign(place, rvalue))
            }
        }
    }

    fn parse_place(&mut self) -> Result<Place, String> {
        let mut place = if self.peek().kind == TokenKind::LParen {
            self.advance();
            self.expect(&TokenKind::Star)?;
            let mut inner = self.parse_place()?;
            self.expect(&TokenKind::RParen)?;
            inner.projections.push(Projection::Deref);
            inner
        } else if self.peek().kind == TokenKind::Star {
            self.advance();
            let mut inner = self.parse_place()?;
            inner.projections.push(Projection::Deref);
            inner
        } else {
            let local = self.expect_local_id()?;
            Place::new(local)
        };

        loop {
            match &self.peek().kind {
                TokenKind::Dot => {
                    self.advance();
                    let tok = self.peek().clone();
                    match tok.kind {
                        TokenKind::Int(field_idx) => {
                            if field_idx < 0 {
                                return Err(format!(
                                    "Field index cannot be negative at {}:{}",
                                    tok.line, tok.col
                                ));
                            }
                            self.advance();
                            place.projections.push(Projection::Field(field_idx as u32));
                        }
                        TokenKind::Variant(v_idx) => {
                            self.advance();
                            place.projections.push(Projection::Variant(v_idx));
                        }
                        _ => {
                            return Err(format!(
                                "Expected non-negative field index or variant (v<N>) after '.', found {:?} at {}:{}",
                                tok.kind, tok.line, tok.col
                            ));
                        }
                    }
                }
                TokenKind::LBracket => {
                    self.advance();
                    let idx_local = self.expect_local_id()?;
                    self.expect(&TokenKind::RBracket)?;
                    place.projections.push(Projection::Index(idx_local));
                }
                _ => break,
            }
        }

        Ok(place)
    }

    fn parse_operand(&mut self) -> Result<Operand, String> {
        match &self.peek().kind {
            TokenKind::Copy => {
                self.advance();
                Ok(Operand::Copy(self.parse_place()?))
            }
            TokenKind::Move => {
                self.advance();
                Ok(Operand::Move(self.parse_place()?))
            }
            TokenKind::Const => {
                self.advance();
                let cv = self.parse_const_value()?;
                Ok(Operand::Const(cv))
            }
            _ => {
                let tok = self.peek();
                Err(format!(
                    "Expected operand ('copy', 'move', or 'const'), found {:?} at {}:{}",
                    tok.kind, tok.line, tok.col
                ))
            }
        }
    }

    fn parse_const_value(&mut self) -> Result<ConstValue, String> {
        let cv = match &self.peek().kind {
            TokenKind::Int(n) => {
                let n = *n;
                self.advance();
                ConstValue::I64(n)
            }
            TokenKind::WideInt(w) => {
                let w = w.clone();
                self.advance();
                ConstValue::Wide(w)
            }
            TokenKind::Float(bits) => {
                let bits = *bits;
                self.advance();
                ConstValue::F64(bits)
            }
            TokenKind::True => {
                self.advance();
                ConstValue::Bool(true)
            }
            TokenKind::False => {
                self.advance();
                ConstValue::Bool(false)
            }
            TokenKind::Type(ty_id) => {
                let ty_id = *ty_id;
                self.advance();
                ConstValue::Type(ty_id)
            }
            TokenKind::Func(fn_id) => {
                let fn_id = *fn_id;
                self.advance();
                ConstValue::Func(fn_id)
            }
            TokenKind::Global(gl_id) => {
                let gl_id = *gl_id;
                self.advance();
                ConstValue::Global(gl_id)
            }
            TokenKind::Str(s) => {
                let s = s.clone();
                self.advance();
                ConstValue::Str(s)
            }
            TokenKind::Void => {
                self.advance();
                ConstValue::Void
            }
            TokenKind::Zeroed => {
                self.advance();
                ConstValue::Zeroed
            }
            TokenKind::LBrace => {
                self.advance();
                let mut items = Vec::new();
                while self.peek().kind != TokenKind::RBrace {
                    items.push(self.parse_const_value()?);
                    if self.peek().kind == TokenKind::Comma {
                        self.advance();
                    } else {
                        break;
                    }
                }
                self.expect(&TokenKind::RBrace)?;
                ConstValue::Aggregate(items)
            }
            _ => {
                let tok = self.peek();
                return Err(format!(
                    "Expected constant value after 'const', found {:?} at {}:{}",
                    tok.kind, tok.line, tok.col
                ));
            }
        };
        Ok(cv)
    }

    fn parse_rvalue(&mut self) -> Result<Rvalue, String> {
        match &self.peek().kind {
            TokenKind::Copy | TokenKind::Move | TokenKind::Const => {
                let op = self.parse_operand()?;
                if self.peek().kind == TokenKind::In {
                    self.advance();
                    let mut ranges = Vec::new();
                    loop {
                        let lo = self.parse_operand()?;
                        self.expect(&TokenKind::DotDotEq)?;
                        let hi = self.parse_operand()?;
                        ranges.push((lo, hi));
                        if self.peek().kind == TokenKind::Pipe {
                            self.advance();
                        } else {
                            break;
                        }
                    }
                    Ok(Rvalue::PatternType { base: op, ranges })
                } else {
                    Ok(Rvalue::Use(op))
                }
            }
            TokenKind::UnOp(op) => {
                let op = *op;
                self.advance();
                self.expect(&TokenKind::LParen)?;
                let val = self.parse_operand()?;
                self.expect(&TokenKind::RParen)?;
                Ok(Rvalue::UnaryOp(op, val))
            }
            TokenKind::BinOp(op) => {
                let op = *op;
                self.advance();
                self.expect(&TokenKind::LParen)?;
                let lhs = self.parse_operand()?;
                self.expect(&TokenKind::Comma)?;
                let rhs = self.parse_operand()?;
                self.expect(&TokenKind::RParen)?;
                Ok(Rvalue::BinaryOp(op, lhs, rhs))
            }
            TokenKind::Cast => {
                self.advance();
                self.expect(&TokenKind::LParen)?;
                let op = self.parse_operand()?;
                self.expect(&TokenKind::Comma)?;
                let ty = self.expect_type_id()?;
                self.expect(&TokenKind::RParen)?;
                Ok(Rvalue::Cast(op, ty))
            }
            TokenKind::Amp => {
                self.advance();
                let mutable = if self.peek().kind == TokenKind::Mut {
                    self.advance();
                    true
                } else {
                    false
                };
                let place = self.parse_place()?;
                Ok(Rvalue::Ref { mutable, place })
            }
            TokenKind::Aggregate => {
                self.advance();
                let ty = self.expect_type_id()?;
                self.expect(&TokenKind::LParen)?;
                let mut fields = Vec::new();
                while self.peek().kind != TokenKind::RParen {
                    fields.push(self.parse_operand()?);
                    if self.peek().kind == TokenKind::Comma {
                        self.advance();
                    } else {
                        break;
                    }
                }
                self.expect(&TokenKind::RParen)?;
                Ok(Rvalue::Aggregate(ty, fields))
            }
            TokenKind::LBracket => {
                self.advance();
                let elem = self.parse_operand()?;
                self.expect(&TokenKind::Semi)?;
                let len = self.parse_operand()?;
                self.expect(&TokenKind::RBracket)?;
                Ok(Rvalue::ArrayType { elem, len })
            }
            TokenKind::Simd => {
                self.advance();
                self.expect(&TokenKind::LBracket)?;
                let elem = self.parse_operand()?;
                self.expect(&TokenKind::Semi)?;
                let len = self.parse_operand()?;
                self.expect(&TokenKind::RBracket)?;
                Ok(Rvalue::SimdType { elem, len })
            }
            TokenKind::Overlay => {
                self.advance();
                self.expect(&TokenKind::LParen)?;
                let mut fields = Vec::new();
                while self.peek().kind != TokenKind::RParen {
                    fields.push(self.parse_operand()?);
                    if self.peek().kind == TokenKind::Comma {
                        self.advance();
                    } else {
                        break;
                    }
                }
                self.expect(&TokenKind::RParen)?;
                Ok(Rvalue::OverlayType(fields))
            }
            TokenKind::Union => {
                self.advance();
                if self.peek().kind == TokenKind::LParen {
                    self.advance();
                    let tag = self.parse_operand()?;
                    let mut variants = Vec::new();
                    while self.peek().kind == TokenKind::Comma {
                        self.advance();
                        if self.peek().kind == TokenKind::RParen {
                            break;
                        }
                        variants.push(self.parse_operand()?);
                    }
                    self.expect(&TokenKind::RParen)?;
                    Ok(Rvalue::UnionType { tag, variants })
                } else {
                    let ty = self.expect_type_id()?;
                    self.expect(&TokenKind::LParen)?;
                    let variant = self.expect_variant_idx()?;
                    self.expect(&TokenKind::Comma)?;
                    let payload = self.parse_operand()?;
                    self.expect(&TokenKind::RParen)?;
                    Ok(Rvalue::Union {
                        ty,
                        variant,
                        payload,
                    })
                }
            }
            TokenKind::Discriminant => {
                self.advance();
                self.expect(&TokenKind::LParen)?;
                let place = self.parse_place()?;
                self.expect(&TokenKind::RParen)?;
                Ok(Rvalue::Discriminant(place))
            }
            _ => {
                let tok = self.peek();
                Err(format!(
                    "Expected Rvalue, found {:?} at {}:{}",
                    tok.kind, tok.line, tok.col
                ))
            }
        }
    }

    fn parse_call_terminator(&mut self, destination: Place) -> Result<Terminator, String> {
        self.expect(&TokenKind::Call)?;
        let func = self.parse_operand()?;
        self.expect(&TokenKind::LParen)?;
        let mut args = Vec::new();
        while self.peek().kind != TokenKind::RParen {
            args.push(self.parse_operand()?);
            if self.peek().kind == TokenKind::Comma {
                self.advance();
            } else {
                break;
            }
        }
        self.expect(&TokenKind::RParen)?;
        self.expect(&TokenKind::Arrow)?;
        let target = self.expect_block_id()?;
        self.expect(&TokenKind::Semi)?;

        Ok(Terminator::Call {
            func,
            args,
            destination,
            target,
        })
    }

    fn parse_terminator(&mut self) -> Result<Terminator, String> {
        match &self.peek().kind {
            TokenKind::Goto => {
                self.advance();
                self.expect(&TokenKind::Arrow)?;
                let target = self.expect_block_id()?;
                self.expect(&TokenKind::Semi)?;
                Ok(Terminator::Goto { target })
            }
            TokenKind::SwitchInt => {
                self.advance();
                self.expect(&TokenKind::LParen)?;
                let discr = self.parse_operand()?;
                self.expect(&TokenKind::RParen)?;
                self.expect(&TokenKind::Arrow)?;
                self.expect(&TokenKind::LBracket)?;

                let mut targets = Vec::new();
                let mut otherwise = None;

                while self.peek().kind != TokenKind::RBracket {
                    if self.peek().kind == TokenKind::Otherwise {
                        self.advance();
                        self.expect(&TokenKind::Colon)?;
                        otherwise = Some(self.expect_block_id()?);
                    } else if let TokenKind::Int(val) = self.peek().kind {
                        self.advance();
                        self.expect(&TokenKind::Colon)?;
                        let target = self.expect_block_id()?;
                        targets.push((val, target));
                    } else {
                        let tok = self.peek();
                        return Err(format!(
                            "Expected integer case or 'otherwise' in switchInt, found {:?} at {}:{}",
                            tok.kind, tok.line, tok.col
                        ));
                    }

                    if self.peek().kind == TokenKind::Comma {
                        self.advance();
                    } else {
                        break;
                    }
                }
                self.expect(&TokenKind::RBracket)?;
                self.expect(&TokenKind::Semi)?;

                let otherwise = otherwise
                    .ok_or_else(|| "switchInt is missing 'otherwise: bb<N>' target".to_string())?;

                Ok(Terminator::SwitchInt {
                    discr,
                    targets,
                    otherwise,
                })
            }
            TokenKind::Drop => {
                self.advance();
                self.expect(&TokenKind::LParen)?;
                let place = self.parse_place()?;
                self.expect(&TokenKind::RParen)?;
                self.expect(&TokenKind::Arrow)?;
                let target = self.expect_block_id()?;
                self.expect(&TokenKind::Semi)?;
                Ok(Terminator::Drop { place, target })
            }
            TokenKind::Return => {
                self.advance();
                self.expect(&TokenKind::Semi)?;
                Ok(Terminator::Return)
            }
            TokenKind::Unreachable => {
                self.advance();
                self.expect(&TokenKind::Semi)?;
                Ok(Terminator::Unreachable)
            }
            _ => {
                let tok = self.peek();
                Err(format!(
                    "Expected terminator, found {:?} at {}:{}",
                    tok.kind, tok.line, tok.col
                ))
            }
        }
    }
}
