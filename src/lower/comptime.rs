use super::*;

impl Compiler {
    pub(super) fn validate_static_variable_type(
        &self,
        name: &str,
        ty_id: TypeId,
        is_mut: bool,
    ) -> Result<(), String> {
        if self.is_opaque_type(ty_id) {
            return Err(format!(
                "Static variable '{name}' cannot have unsized opaque type '{}'",
                self.type_display_name(ty_id)
            ));
        }
        if let Some(tr) = self.traits.get(&ty_id) {
            return Err(format!(
                "Static variable '{name}' cannot have unsized trait type '{}'",
                tr.name
            ));
        }
        if self.is_linear_type(ty_id) {
            return Err(format!(
                "Static variable '{name}' cannot have linear type '{}'; static variables live for the entire program duration and cannot be linearly consumed",
                self.type_display_name(ty_id)
            ));
        }
        if !is_mut && !self.is_sync_type(ty_id) {
            let t_disp = self.type_display_name(ty_id);
            return Err(format!(
                "Immutable static '{name}' of type '{t_disp}' requires '{t_disp}: sync' because immutable statics may be shared across threads without 'unsafe' (mark the type 'opaque(sync)' or declare 'static mut {name}' with 'unsafe' access)"
            ));
        }
        Ok(())
    }

    pub(super) fn eval_int_reflection_field(
        &mut self,
        mod_path: &str,
        self_ty: Option<TypeId>,
        env: &HashMap<String, ComptimeVal>,
        base: &Expr,
        field: &str,
    ) -> Result<Option<(ConstValue, TypeId, ComptimeVal)>, String> {
        if !matches!(field, "bits" | "BITS" | "signed" | "SIGNED" | "MIN" | "MAX") {
            return Ok(None);
        }
        let target_opt = match base {
            Expr::TypeVal(te) => Some(self.resolve_type_expr(mod_path, self_ty, env, te)?),
            Expr::Path(p) => {
                if p.len() == 1 {
                    if p[0] == "Self" {
                        self_ty
                    } else if let Some(ComptimeVal::Type(t_id)) = env.get(&p[0]) {
                        Some(*t_id)
                    } else if let Some(ComptimeVal::Type(t_id)) =
                        env.get(&format!("__var_ty:{}", p[0]))
                    {
                        Some(*t_id)
                    } else if let Ok(ResolvedItem::Type(tmod, tname)) =
                        self.resolve_path(mod_path, p)
                    {
                        Some(self.resolve_named_type(&tmod, &tname)?)
                    } else if let Ok((_, cty, _)) =
                        self.eval_const_expr_typed(mod_path, self_ty, env, base, None)
                    {
                        Some(cty)
                    } else {
                        None
                    }
                } else if let Ok(ResolvedItem::Type(tmod, tname)) = self.resolve_path(mod_path, p) {
                    Some(self.resolve_named_type(&tmod, &tname)?)
                } else if let Ok((_, cty, _)) =
                    self.eval_const_expr_typed(mod_path, self_ty, env, base, None)
                {
                    Some(cty)
                } else {
                    None
                }
            }
            _ => {
                if let Ok((_, cty, cv)) =
                    self.eval_const_expr_typed(mod_path, self_ty, env, base, None)
                {
                    if let ComptimeVal::Type(t_id) = cv {
                        Some(t_id)
                    } else {
                        Some(cty)
                    }
                } else {
                    None
                }
            }
        };
        let Some(target_ty) = target_opt else {
            return Ok(None);
        };
        if let Some(b) = self
            .composites
            .get(&target_ty)
            .filter(|c| c.is_packed && matches!(field, "bits" | "BITS"))
            .map(|c| c.total_bits as i128)
        {
            let u32_ty = self.intern_type(Type::Int {
                signed: false,
                bits: 32,
            });
            return Ok(Some((ConstValue::I64(b), u32_ty, ComptimeVal::Int(b))));
        }
        let Some((signed, bits, min, max)) = self.int_type_reflection(target_ty) else {
            return Ok(None);
        };
        match field {
            "bits" | "BITS" => {
                let u32_ty = self.intern_type(Type::Int {
                    signed: false,
                    bits: 32,
                });
                let b = bits as i128;
                Ok(Some((ConstValue::I64(b), u32_ty, ComptimeVal::Int(b))))
            }
            "signed" | "SIGNED" => {
                let bool_ty = self.intern_type(Type::Bool);
                Ok(Some((
                    ConstValue::Bool(signed),
                    bool_ty,
                    ComptimeVal::Bool(signed),
                )))
            }
            "MIN" => Ok(Some((
                ConstValue::I64(min),
                target_ty,
                ComptimeVal::Int(min),
            ))),
            "MAX" => Ok(Some((
                ConstValue::I64(max),
                target_ty,
                ComptimeVal::Int(max),
            ))),
            _ => Ok(None),
        }
    }

    pub(super) fn eval_const_expr_typed(
        &mut self,
        mod_path: &str,
        self_ty: Option<TypeId>,
        env: &HashMap<String, ComptimeVal>,
        expr: &Expr,
        expected_ty: Option<TypeId>,
    ) -> Result<(ConstValue, TypeId, ComptimeVal), String> {
        match expr {
            Expr::Int(n) => {
                if let Some(t) = expected_ty
                    && matches!(self.program.types[t.0 as usize], Type::F32 | Type::F64)
                {
                    let bits = (*n as f64).to_bits();
                    return Ok((
                        ConstValue::F64(bits),
                        t,
                        ComptimeVal::ConstExpr(format!("f64:{bits}"), expr.clone()),
                    ));
                }
                let ty = match expected_ty {
                    Some(t)
                        if matches!(
                            self.program.types[t.0 as usize],
                            Type::Int { .. } | Type::Pattern { .. }
                        ) =>
                    {
                        if let Type::Pattern { ranges, .. } = &self.program.types[t.0 as usize]
                            && !ranges.iter().any(|&(lo, hi)| *n >= lo && *n <= hi)
                        {
                            return Err(format!(
                                "Compile-time value {n} is outside valid pattern ranges of {}",
                                self.program.types[t.0 as usize]
                            ));
                        }
                        t
                    }
                    _ => self.intern_type(Type::Int {
                        signed: true,
                        bits: 64,
                    }),
                };
                Ok((ConstValue::I64(*n), ty, ComptimeVal::Int(*n)))
            }
            Expr::Float(bits) => {
                let ty = match expected_ty {
                    Some(t)
                        if matches!(self.program.types[t.0 as usize], Type::F32 | Type::F64) =>
                    {
                        t
                    }
                    _ => self.intern_type(Type::F64),
                };
                Ok((
                    ConstValue::F64(*bits),
                    ty,
                    ComptimeVal::ConstExpr(format!("f64:{bits}"), expr.clone()),
                ))
            }
            Expr::Bool(b) => {
                let ty = self.intern_type(Type::Bool);
                Ok((ConstValue::Bool(*b), ty, ComptimeVal::Bool(*b)))
            }
            Expr::Rune(ch) => {
                let ty = self.intern_type(Type::Rune);
                let n = u32::from(*ch) as i128;
                Ok((ConstValue::I64(n), ty, ComptimeVal::Int(n)))
            }
            Expr::Str(s) => {
                let str_ty = self.intern_str_type();
                let cval = ConstValue::Aggregate(vec![
                    ConstValue::Str(s.clone()),
                    ConstValue::I64(s.len() as i128),
                ]);
                Ok((cval, str_ty, ComptimeVal::Str(s.clone())))
            }
            Expr::TypeVal(te) => {
                let t_id = self.resolve_type_expr(mod_path, self_ty, env, te)?;
                let meta_ty = self.intern_type(Type::MetaType);
                Ok((ConstValue::Type(t_id), meta_ty, ComptimeVal::Type(t_id)))
            }
            Expr::Unary {
                op: UnOp::Neg,
                expr: inner,
            } => {
                let (cval, ty, _) =
                    self.eval_const_expr_typed(mod_path, self_ty, env, inner, expected_ty)?;
                match cval {
                    ConstValue::I64(n) => Ok((ConstValue::I64(-n), ty, ComptimeVal::Int(-n))),
                    ConstValue::F64(bits) => {
                        let neg_bits = (-f64::from_bits(bits)).to_bits();
                        Ok((
                            ConstValue::F64(neg_bits),
                            ty,
                            ComptimeVal::ConstExpr(format!("f64:{neg_bits}"), expr.clone()),
                        ))
                    }
                    _ => Err(format!("Unsupported constant unary '-' on {expr:?}")),
                }
            }
            Expr::Unary {
                op: UnOp::Not,
                expr: inner,
            } => {
                let (cval, ty, _) =
                    self.eval_const_expr_typed(mod_path, self_ty, env, inner, expected_ty)?;
                match cval {
                    ConstValue::Bool(b) => Ok((ConstValue::Bool(!b), ty, ComptimeVal::Bool(!b))),
                    ConstValue::I64(n) => Ok((ConstValue::I64(!n), ty, ComptimeVal::Int(!n))),
                    _ => Err(format!("Unsupported constant unary '!' on {expr:?}")),
                }
            }
            Expr::Binary { op, lhs, rhs } => {
                let (l_val, l_ty, l_ct) =
                    self.eval_const_expr_typed(mod_path, self_ty, env, lhs, expected_ty)?;
                let (r_val, _, r_ct) =
                    self.eval_const_expr_typed(mod_path, self_ty, env, rhs, Some(l_ty))?;
                match (l_val, r_val) {
                    (ConstValue::I64(l), ConstValue::I64(r)) => {
                        let res = match op {
                            BinOp::Add | BinOp::AddWrap | BinOp::AddUnchecked => l.wrapping_add(r),
                            BinOp::Sub | BinOp::SubWrap | BinOp::SubUnchecked => l.wrapping_sub(r),
                            BinOp::Mul | BinOp::MulWrap | BinOp::MulUnchecked => l.wrapping_mul(r),
                            BinOp::AddSat => l.saturating_add(r),
                            BinOp::SubSat => l.saturating_sub(r),
                            BinOp::MulSat => l.saturating_mul(r),
                            BinOp::Div => l / r,
                            BinOp::Rem => l % r,
                            BinOp::BitAnd => l & r,
                            BinOp::BitOr => l | r,
                            BinOp::BitXor => l ^ r,
                            BinOp::Shl => l << (r as u32),
                            BinOp::Shr => l >> (r as u32),
                            BinOp::AddChecked | BinOp::SubChecked | BinOp::MulChecked => {
                                return Err(format!(
                                    "Fallible arithmetic operator '{op}' returns an optional '?T' and cannot be used directly as a scalar constant; unwrap with 'orelse' in a runtime expression"
                                ));
                            }
                            BinOp::Eq
                            | BinOp::Ne
                            | BinOp::Lt
                            | BinOp::Le
                            | BinOp::Gt
                            | BinOp::Ge => {
                                let b = match op {
                                    BinOp::Eq => l == r,
                                    BinOp::Ne => l != r,
                                    BinOp::Lt => l < r,
                                    BinOp::Le => l <= r,
                                    BinOp::Gt => l > r,
                                    BinOp::Ge => l >= r,
                                    _ => unreachable!(),
                                };
                                let bool_ty = self.intern_type(Type::Bool);
                                return Ok((ConstValue::Bool(b), bool_ty, ComptimeVal::Bool(b)));
                            }
                        };
                        Ok((ConstValue::I64(res), l_ty, ComptimeVal::Int(res)))
                    }
                    (ConstValue::Bool(l), ConstValue::Bool(r)) => {
                        let b = match op {
                            BinOp::Eq => l == r,
                            BinOp::Ne => l != r,
                            BinOp::BitAnd => l & r,
                            BinOp::BitOr => l | r,
                            BinOp::BitXor => l ^ r,
                            _ => {
                                return Err(format!(
                                    "Unsupported boolean operator '{op}' in constant expression"
                                ));
                            }
                        };
                        let bool_ty = self.intern_type(Type::Bool);
                        Ok((ConstValue::Bool(b), bool_ty, ComptimeVal::Bool(b)))
                    }
                    (ConstValue::Type(l), ConstValue::Type(r)) => {
                        let b = match op {
                            BinOp::Eq => l == r,
                            BinOp::Ne => l != r,
                            _ => {
                                return Err(format!(
                                    "Unsupported type operator '{op}' in constant expression"
                                ));
                            }
                        };
                        let bool_ty = self.intern_type(Type::Bool);
                        Ok((ConstValue::Bool(b), bool_ty, ComptimeVal::Bool(b)))
                    }
                    _ => {
                        if let (ComptimeVal::Str(ls), ComptimeVal::Str(rs)) = (&l_ct, &r_ct) {
                            let b = match op {
                                BinOp::Eq => ls == rs,
                                BinOp::Ne => ls != rs,
                                _ => {
                                    return Err(format!(
                                        "Unsupported string operator '{op}' in constant expression"
                                    ));
                                }
                            };
                            let bool_ty = self.intern_type(Type::Bool);
                            return Ok((ConstValue::Bool(b), bool_ty, ComptimeVal::Bool(b)));
                        }
                        Err(format!(
                            "Unsupported operands in constant binary expression '{op}'"
                        ))
                    }
                }
            }
            Expr::Cast { expr: inner, ty } => {
                let target_ty = self.resolve_type_expr(mod_path, self_ty, env, ty)?;
                let (cval, _, _) =
                    self.eval_const_expr_typed(mod_path, self_ty, env, inner, None)?;
                match cval {
                    ConstValue::I64(n) => {
                        if matches!(
                            self.program.types[target_ty.0 as usize],
                            Type::F32 | Type::F64
                        ) {
                            let bits = (n as f64).to_bits();
                            Ok((
                                ConstValue::F64(bits),
                                target_ty,
                                ComptimeVal::ConstExpr(format!("f64:{bits}"), expr.clone()),
                            ))
                        } else {
                            Ok((ConstValue::I64(n), target_ty, ComptimeVal::Int(n)))
                        }
                    }
                    other => Ok((
                        other,
                        target_ty,
                        ComptimeVal::ConstExpr(format!("{expr:?}"), expr.clone()),
                    )),
                }
            }
            Expr::TupleLit(elems) => {
                if let Some(t) = expected_ty
                    && matches!(
                        self.program.types[t.0 as usize],
                        Type::Int {
                            signed: false,
                            bits: 256
                        }
                    )
                    && elems.len() == 4
                {
                    let u64_ty = self.intern_type(Type::Int {
                        signed: false,
                        bits: 64,
                    });
                    let mut vals = Vec::with_capacity(4);
                    for e in elems {
                        let (cv, _, _) =
                            self.eval_const_expr_typed(mod_path, self_ty, env, e, Some(u64_ty))?;
                        vals.push(cv);
                    }
                    return Ok((
                        ConstValue::Aggregate(vals),
                        t,
                        ComptimeVal::ConstExpr(format!("{expr:?}"), expr.clone()),
                    ));
                }
                if let Some(t) = expected_ty
                    && let Type::Array { elem, len } = self.program.types[t.0 as usize]
                    && elems.len() == len as usize
                {
                    let mut vals = Vec::with_capacity(elems.len());
                    for e in elems {
                        let (cv, _, _) =
                            self.eval_const_expr_typed(mod_path, self_ty, env, e, Some(elem))?;
                        vals.push(cv);
                    }
                    return Ok((
                        ConstValue::Aggregate(vals),
                        t,
                        ComptimeVal::ConstExpr(format!("{expr:?}"), expr.clone()),
                    ));
                }
                let expected_fields = if let Some(t) = expected_ty
                    && let Type::Struct(ftys) = &self.program.types[t.0 as usize]
                {
                    Some(ftys.clone())
                } else {
                    None
                };
                let mut vals = Vec::with_capacity(elems.len());
                let mut tys = Vec::with_capacity(elems.len());
                for (i, e) in elems.iter().enumerate() {
                    let exp = expected_fields.as_ref().and_then(|v| v.get(i).copied());
                    let (cv, ty, _) = self.eval_const_expr_typed(mod_path, self_ty, env, e, exp)?;
                    vals.push(cv);
                    tys.push(ty);
                }
                let tup_ty = expected_ty.unwrap_or_else(|| self.intern_type(Type::Struct(tys)));
                Ok((
                    ConstValue::Aggregate(vals),
                    tup_ty,
                    ComptimeVal::ConstExpr(format!("{expr:?}"), expr.clone()),
                ))
            }
            Expr::SimdLit { ty, elems } => {
                let arr_ty = self.resolve_type_expr(mod_path, self_ty, env, ty)?;
                let elem = match self.program.types[arr_ty.0 as usize] {
                    Type::Simd { elem, .. } | Type::Array { elem, .. } => elem,
                    _ => {
                        return Err(format!(
                            "Expected SIMD or Array type in constant literal, got {arr_ty}"
                        ));
                    }
                };
                let mut vals = Vec::with_capacity(elems.len());
                for e in elems {
                    let (cv, _, _) =
                        self.eval_const_expr_typed(mod_path, self_ty, env, e, Some(elem))?;
                    vals.push(cv);
                }
                Ok((
                    ConstValue::Aggregate(vals),
                    arr_ty,
                    ComptimeVal::ConstExpr(format!("{expr:?}"), expr.clone()),
                ))
            }
            Expr::StructLit { ty, fields } => {
                let comp_ty = self.resolve_type_expr(mod_path, self_ty, env, ty)?;
                let Some(comp) = self.composites.get(&comp_ty).cloned() else {
                    return Err(format!(
                        "Cannot construct non-struct/opaque type {comp_ty} in constant initializer"
                    ));
                };
                if comp.is_struct && comp.fields.is_empty() && self_ty != Some(comp_ty) {
                    return Err(format!(
                        "Cannot construct opaque type '{}' outside its 'opaque {{ ... }}' block",
                        comp.name
                    ));
                }
                for (f_name, _, f_vis, _) in &comp.fields {
                    if comp.is_struct && *f_vis == Visibility::Private && self_ty != Some(comp_ty) {
                        return Err(format!(
                            "Cannot construct opaque '{}' with private field '{}' outside its 'opaque {{ ... }}' block",
                            comp.name, f_name
                        ));
                    }
                }
                let mut vals = Vec::with_capacity(comp.fields.len());
                for (f_name, f_ty, _, f_default) in &comp.fields {
                    if let Some((_, val_expr)) = fields.iter().find(|(n, _)| n == f_name) {
                        let (cv, _, _) = self.eval_const_expr_typed(
                            mod_path,
                            self_ty,
                            env,
                            val_expr,
                            Some(*f_ty),
                        )?;
                        vals.push(cv);
                    } else if let Some(def_expr) = f_default {
                        let (cv, _, _) = self.eval_const_expr_typed(
                            &comp.def_module,
                            Some(comp_ty),
                            &comp.comptime_env,
                            def_expr,
                            Some(*f_ty),
                        )?;
                        vals.push(cv);
                    } else {
                        return Err(format!(
                            "Missing field '{}' in '{}' constant literal",
                            f_name, comp.name
                        ));
                    }
                }
                if comp.is_packed {
                    let mut packed_acc = 0u128;
                    for (idx, cv) in vals.into_iter().enumerate() {
                        let (bit_offset, bit_width) = comp.packed_offsets[idx];
                        let raw_bits = match cv {
                            ConstValue::I64(n) => n as u128,
                            ConstValue::Bool(b) => u128::from(b),
                            other => {
                                return Err(format!(
                                    "Invalid field value {other:?} in packed constant '{}'",
                                    comp.name
                                ));
                            }
                        };
                        let mask = if bit_width >= 128 {
                            u128::MAX
                        } else {
                            (1u128 << bit_width) - 1
                        };
                        packed_acc |= (raw_bits & mask) << bit_offset;
                    }
                    let packed_int = packed_acc as i128;
                    return Ok((
                        ConstValue::I64(packed_int),
                        comp_ty,
                        ComptimeVal::Int(packed_int),
                    ));
                }
                Ok((
                    ConstValue::Aggregate(vals),
                    comp_ty,
                    ComptimeVal::ConstExpr(format!("{expr:?}"), expr.clone()),
                ))
            }
            Expr::IntrinsicBswap(inner) => {
                let (cval, ty, _) =
                    self.eval_const_expr_typed(mod_path, self_ty, env, inner, expected_ty)?;
                let ConstValue::I64(n) = cval else {
                    return Err("'@bswap' requires an integer or packed type operand".to_string());
                };
                let Some((bits, signed)) = self.packed_field_bit_width(ty) else {
                    return Err(format!(
                        "'@bswap' requires a byte-multiple integer or packed type, found '{}'",
                        self.type_display_name(ty)
                    ));
                };
                if bits < 8 || bits % 8 != 0 {
                    return Err(format!(
                        "'@bswap' requires a byte-multiple bit width (multiple of 8 bits), found {} bits on type '{}'",
                        bits,
                        self.type_display_name(ty)
                    ));
                }
                let swapped = crate::vm::Vm::bswap_int(n, u32::from(bits), !signed);
                Ok((ConstValue::I64(swapped), ty, ComptimeVal::Int(swapped)))
            }
            Expr::IntrinsicArithUnchecked { .. } => Err(
                "Unchecked arithmetic intrinsics ('@add_unchecked', '@sub_unchecked', '@mul_unchecked') require an 'unsafe' block and cannot be evaluated at compile time"
                    .to_string(),
            ),
            Expr::SliceLit { mutable, elems } => {
                let elem_ty = if let Some(exp) = expected_ty
                    && let Some(&info) = self.slices.get(&exp)
                {
                    info.elem
                } else if let Some(first) = elems.first() {
                    let (_, ety, _) =
                        self.eval_const_expr_typed(mod_path, self_ty, env, first, None)?;
                    ety
                } else {
                    return Err(
                        "Empty slice literal '&[]' requires an explicit slice type context"
                            .to_string(),
                    );
                };
                let slice_ty = self.intern_slice_type(*mutable, elem_ty);
                let mut vals = Vec::with_capacity(elems.len());
                for e in elems {
                    let (cv, _, _) =
                        self.eval_const_expr_typed(mod_path, self_ty, env, e, Some(elem_ty))?;
                    vals.push(cv);
                }
                let arr_ty = self.intern_type(Type::Array {
                    elem: elem_ty,
                    len: elems.len() as u64,
                });
                let gl_id = GlobalId(self.program.globals.len() as u32);
                self.program.globals.push(Global {
                    id: gl_id,
                    ty: arr_ty,
                    mutable: *mutable,
                    init: ConstValue::Aggregate(vals),
                });
                let cval = ConstValue::Aggregate(vec![
                    ConstValue::Global(gl_id),
                    ConstValue::I64(elems.len() as i128),
                ]);
                Ok((
                    cval,
                    slice_ty,
                    ComptimeVal::ConstExpr(format!("{expr:?}"), expr.clone()),
                ))
            }
            Expr::If {
                cond,
                then_block,
                else_block,
            } => {
                let bool_ty = self.intern_type(Type::Bool);
                let (cval, _, _) =
                    self.eval_const_expr_typed(mod_path, self_ty, env, cond, Some(bool_ty))?;
                let ConstValue::Bool(b) = cval else {
                    return Err("Condition of constant 'if' expression must be a bool".to_string());
                };
                let chosen = if b {
                    then_block
                } else {
                    else_block.as_ref().ok_or_else(|| {
                        "Constant 'if' expression must have an 'else' branch".to_string()
                    })?
                };
                let Some(Stmt::Expr(tail) | Stmt::Return(Some(tail))) = chosen.stmts.last() else {
                    return Err(
                        "Constant 'if' branch must end with a value expression".to_string()
                    );
                };
                self.eval_const_expr_typed(mod_path, self_ty, env, tail, expected_ty)
            }
            Expr::MapLit(pairs) => {
                self.eval_map_lit(mod_path, self_ty, env, pairs, expected_ty)
            }
            Expr::IntrinsicInvert(inner) => self.eval_map_invert(mod_path, self_ty, env, inner),
            Expr::IntrinsicDeclarations(inner) => {
                self.eval_module_declarations(mod_path, self_ty, env, inner)
            }
            Expr::Index { base, index } => {
                if let Some(map_id) = self.resolve_map_expr(mod_path, self_ty, env, base)? {
                    let map_inst = self.map_instances[map_id as usize].clone();
                    let map_info = self.maps[&map_inst.map_ty];
                    let (mkey, _, _) =
                        self.eval_map_key(mod_path, self_ty, env, index, Some(map_info.key_ty))?;
                    let Some(entry) = map_inst.entries.iter().find(|e| e.key == mkey) else {
                        return Err(format!("Key {mkey:?} not found in comptime map"));
                    };
                    return Ok((
                        entry.val_const.clone(),
                        map_info.val_ty,
                        entry.val_comptime.clone(),
                    ));
                }
                let (base_cv, base_ty, _) =
                    self.eval_const_expr_typed(mod_path, self_ty, env, base, None)?;
                let idx_val = self.eval_comptime_int(mod_path, self_ty, env, index)?;
                if idx_val < 0 {
                    return Err(format!("Negative index {idx_val} in constant expression"));
                }
                let idx = idx_val as usize;
                if let Some(&slice_info) = self.slices.get(&base_ty)
                    && let ConstValue::Aggregate(sf) = &base_cv
                    && sf.len() == 2
                    && let ConstValue::Global(gl_id) = sf[0]
                    && let ConstValue::Aggregate(elems) =
                        &self.program.globals[gl_id.0 as usize].init
                {
                    let Some(elem_cv) = elems.get(idx).cloned() else {
                        return Err(format!(
                            "Slice index {} out of bounds (len {})",
                            idx,
                            elems.len()
                        ));
                    };
                    let ct_val = Self::const_value_to_comptime(&elem_cv, expr);
                    return Ok((elem_cv, slice_info.elem, ct_val));
                }
                if let Type::Array { elem, .. } = self.program.types[base_ty.0 as usize]
                    && let ConstValue::Aggregate(elems) = base_cv
                {
                    let Some(elem_cv) = elems.get(idx).cloned() else {
                        return Err(format!(
                            "Array index {} out of bounds (len {})",
                            idx,
                            elems.len()
                        ));
                    };
                    let ct_val = Self::const_value_to_comptime(&elem_cv, expr);
                    return Ok((elem_cv, elem, ct_val));
                }
                Err(format!("Cannot index {base:?} in constant expression"))
            }
            Expr::MethodCall {
                receiver,
                method,
                args,
            } if method == "get" && args.len() == 1 => {
                if let Some(map_id) = self.resolve_map_expr(mod_path, self_ty, env, receiver)? {
                    let map_inst = self.map_instances[map_id as usize].clone();
                    let map_info = self.maps[&map_inst.map_ty];
                    let (mkey, _, _) = self.eval_map_key(
                        mod_path,
                        self_ty,
                        env,
                        &args[0],
                        Some(map_info.key_ty),
                    )?;
                    let u8_ty = self.intern_type(Type::Int {
                        signed: false,
                        bits: 8,
                    });
                    let void_ty = self.intern_type(Type::Void);
                    let opt_ty = self.intern_type(Type::Union {
                        tag: u8_ty,
                        variants: vec![void_ty, map_info.val_ty],
                    });
                    self.ensure_union_destructor(opt_ty);
                    if let Some(entry) = map_inst.entries.iter().find(|e| e.key == mkey) {
                        return Ok((
                            entry.val_const.clone(),
                            map_info.val_ty,
                            entry.val_comptime.clone(),
                        ));
                    } else {
                        return Ok((
                            ConstValue::Void,
                            opt_ty,
                            ComptimeVal::ConstExpr("null".to_string(), Expr::Null),
                        ));
                    }
                }
                Err(format!(
                    "Cannot evaluate method call '.{method}()' as a compile-time constant"
                ))
            }
            Expr::Field { base, field } => {
                if let Some(res) =
                    self.eval_int_reflection_field(mod_path, self_ty, env, base, field)?
                {
                    return Ok(res);
                }
                if let Ok((base_cv, base_ty, _)) =
                    self.eval_const_expr_typed(mod_path, self_ty, env, base, None)
                {
                    if field == "len" {
                        let usize_ty = self.intern_type(Type::Int {
                            signed: false,
                            bits: 64,
                        });
                        if self.slices.contains_key(&base_ty)
                            && let ConstValue::Aggregate(sf) = &base_cv
                            && sf.len() == 2
                            && let ConstValue::I64(len) = sf[1]
                        {
                            return Ok((ConstValue::I64(len), usize_ty, ComptimeVal::Int(len)));
                        }
                        if let Type::Array { len, .. } = self.program.types[base_ty.0 as usize] {
                            let n = len as i128;
                            return Ok((ConstValue::I64(n), usize_ty, ComptimeVal::Int(n)));
                        }
                    }
                    if let Some(comp) = self.composites.get(&base_ty).cloned()
                        && let Some((f_idx, (_, f_ty, _, _))) = comp
                            .fields
                            .iter()
                            .enumerate()
                            .find(|(_, (n, _, _, _))| n == field)
                        && let ConstValue::Aggregate(vals) = base_cv
                        && let Some(f_cv) = vals.get(f_idx).cloned()
                    {
                        let ct_val = Self::const_value_to_comptime(&f_cv, expr);
                        return Ok((f_cv, *f_ty, ct_val));
                    }
                }
                let ct_val = self.eval_comptime_val(mod_path, self_ty, env, expr)?;
                match ct_val {
                    ComptimeVal::Int(n) => {
                        let ty = expected_ty.unwrap_or_else(|| {
                            self.intern_type(Type::Int {
                                signed: true,
                                bits: 64,
                            })
                        });
                        Ok((ConstValue::I64(n), ty, ComptimeVal::Int(n)))
                    }
                    ComptimeVal::Bool(b) => {
                        let ty = self.intern_type(Type::Bool);
                        Ok((ConstValue::Bool(b), ty, ComptimeVal::Bool(b)))
                    }
                    _ => Err(format!(
                        "Cannot evaluate field access '.{field}' as a compile-time constant"
                    )),
                }
            }
            Expr::Path(p) => {
                if p.len() == 1 {
                    if let Some(ct_val) = env.get(&p[0]).cloned() {
                        match ct_val {
                            ComptimeVal::Int(n) => {
                                let ty = expected_ty.unwrap_or_else(|| {
                                    self.intern_type(Type::Int {
                                        signed: true,
                                        bits: 64,
                                    })
                                });
                                return Ok((ConstValue::I64(n), ty, ComptimeVal::Int(n)));
                            }
                            ComptimeVal::Bool(b) => {
                                let ty = self.intern_type(Type::Bool);
                                return Ok((ConstValue::Bool(b), ty, ComptimeVal::Bool(b)));
                            }
                            ComptimeVal::Str(s) => {
                                let str_ty = self.intern_str_type();
                                let cval = ConstValue::Aggregate(vec![
                                    ConstValue::Str(s.clone()),
                                    ConstValue::I64(s.len() as i128),
                                ]);
                                return Ok((cval, str_ty, ComptimeVal::Str(s)));
                            }
                            ComptimeVal::Module(m) => {
                                let meta_ty = self.intern_type(Type::MetaType);
                                return Ok((
                                    ConstValue::I64(0),
                                    meta_ty,
                                    ComptimeVal::Module(m),
                                ));
                            }
                            ComptimeVal::Map(id) => {
                                let map_ty = self.map_instances[id as usize].map_ty;
                                return Ok((
                                    ConstValue::I64(id as i128),
                                    map_ty,
                                    ComptimeVal::Map(id),
                                ));
                            }
                            ComptimeVal::Type(t_id) => {
                                let meta_ty = self.intern_type(Type::MetaType);
                                return Ok((
                                    ConstValue::Type(t_id),
                                    meta_ty,
                                    ComptimeVal::Type(t_id),
                                ));
                            }
                            ComptimeVal::ConstExpr(_, ref ce) => {
                                return self.eval_const_expr_typed(
                                    mod_path,
                                    self_ty,
                                    env,
                                    ce,
                                    expected_ty,
                                );
                            }
                        }
                    }
                    if let Ok(ResolvedItem::Module(m)) = self.resolve_path(mod_path, p) {
                        let meta_ty = self.intern_type(Type::MetaType);
                        return Ok((ConstValue::I64(0), meta_ty, ComptimeVal::Module(m)));
                    }
                    if let Ok(ResolvedItem::Const(cmod, cname)) = self.resolve_path(mod_path, p) {
                        let (cval, cty, ct_val, has_explicit_ty) =
                            self.resolve_top_const(&cmod, &cname)?;
                        let final_ty = if !has_explicit_ty
                            && matches!(cval, ConstValue::I64(_))
                            && let Some(exp) = expected_ty
                            && matches!(
                                self.program.types[exp.0 as usize],
                                Type::Int { .. } | Type::Pattern { .. }
                            ) {
                            exp
                        } else {
                            cty
                        };
                        return Ok((cval, final_ty, ct_val));
                    }
                    if let Ok(ResolvedItem::Type(tmod, tname)) = self.resolve_path(mod_path, p) {
                        let t_id = self.resolve_named_type(&tmod, &tname)?;
                        let meta_ty = self.intern_type(Type::MetaType);
                        return Ok((ConstValue::Type(t_id), meta_ty, ComptimeVal::Type(t_id)));
                    }
                } else if p.len() >= 2 {
                    let expanded = self.expand_module_path(env, p);
                    let p = &expanded;
                    let prefix = &p[..p.len() - 1];
                    let item_name = p.last().unwrap();
                    let owner_opt = if prefix.len() == 1 && prefix[0] == "Self" {
                        self_ty
                    } else if prefix.len() == 1
                        && let Some(ComptimeVal::Type(t_id)) = env.get(&prefix[0])
                    {
                        Some(*t_id)
                    } else if let Ok(ResolvedItem::Type(tmod, tname)) =
                        self.resolve_path(mod_path, prefix)
                    {
                        Some(self.resolve_named_type(&tmod, &tname)?)
                    } else {
                        None
                    };
                    if let Some(owner_ty) = owner_opt {
                        if let Some(comp) = self.composites.get(&owner_ty)
                            && comp.consts.contains_key(item_name)
                        {
                            let (cval, cty, ct_val, cvis, has_explicit_ty) =
                                self.resolve_associated_const(owner_ty, item_name)?;
                            let comp = &self.composites[&owner_ty];
                            if comp.is_struct
                                && cvis == Visibility::Private
                                && self_ty != Some(owner_ty)
                            {
                                return Err(format!(
                                    "Cannot access private constant '{}::{}' outside its 'opaque {{ ... }}' block",
                                    comp.name, item_name
                                ));
                            }
                            if cvis == Visibility::Private && comp.def_module != mod_path {
                                return Err(format!(
                                    "Constant '{}::{}' is private to module '{}'",
                                    comp.name, item_name, comp.def_module
                                ));
                            }
                            let final_ty = if !has_explicit_ty
                                && matches!(cval, ConstValue::I64(_))
                                && let Some(exp) = expected_ty
                                && matches!(
                                    self.program.types[exp.0 as usize],
                                    Type::Int { .. } | Type::Pattern { .. }
                                ) {
                                exp
                            } else {
                                cty
                            };
                            return Ok((cval, final_ty, ct_val));
                        }
                        if let Some((_, variants)) = self.enums.get(&owner_ty)
                            && let Some((_, val)) = variants.iter().find(|(vn, _)| vn == item_name)
                        {
                            return Ok((ConstValue::I64(*val), owner_ty, ComptimeVal::Int(*val)));
                        }
                        if matches!(item_name.as_str(), "MIN" | "MAX" | "BITS" | "SIGNED")
                            && let Some(res) = self.eval_int_reflection_field(
                                mod_path,
                                self_ty,
                                env,
                                &Expr::Path(prefix.to_vec()),
                                item_name,
                            )?
                        {
                            let (cval, cty, ct_val) = res;
                            let final_ty = if matches!(item_name.as_str(), "MIN" | "MAX")
                                && let Some(exp) = expected_ty
                                && matches!(
                                    self.program.types[exp.0 as usize],
                                    Type::Int { .. } | Type::Pattern { .. }
                                ) {
                                exp
                            } else {
                                cty
                            };
                            return Ok((cval, final_ty, ct_val));
                        }
                    }
                    if let Ok(ResolvedItem::Module(m)) = self.resolve_path(mod_path, p) {
                        let meta_ty = self.intern_type(Type::MetaType);
                        return Ok((ConstValue::I64(0), meta_ty, ComptimeVal::Module(m)));
                    }
                    if let Ok(ResolvedItem::Type(tmod, tname)) = self.resolve_path(mod_path, p) {
                        let t_id = self.resolve_named_type(&tmod, &tname)?;
                        let meta_ty = self.intern_type(Type::MetaType);
                        return Ok((ConstValue::Type(t_id), meta_ty, ComptimeVal::Type(t_id)));
                    }
                    if let Ok(ResolvedItem::Const(cmod, cname)) = self.resolve_path(mod_path, p) {
                        let (cval, cty, ct_val, has_explicit_ty) =
                            self.resolve_top_const(&cmod, &cname)?;
                        let final_ty = if !has_explicit_ty
                            && matches!(cval, ConstValue::I64(_))
                            && let Some(exp) = expected_ty
                            && matches!(
                                self.program.types[exp.0 as usize],
                                Type::Int { .. } | Type::Pattern { .. }
                            ) {
                            exp
                        } else {
                            cty
                        };
                        return Ok((cval, final_ty, ct_val));
                    }
                }
                Err(format!(
                    "Cannot evaluate path '{}' as a compile-time constant",
                    p.join("::")
                ))
            }
            _ => {
                let ct_val = self.eval_comptime_val(mod_path, self_ty, env, expr)?;
                match ct_val {
                    ComptimeVal::Int(n) => {
                        let ty = expected_ty.unwrap_or_else(|| {
                            self.intern_type(Type::Int {
                                signed: true,
                                bits: 64,
                            })
                        });
                        Ok((ConstValue::I64(n), ty, ComptimeVal::Int(n)))
                    }
                    ComptimeVal::Bool(b) => {
                        let ty = self.intern_type(Type::Bool);
                        Ok((ConstValue::Bool(b), ty, ComptimeVal::Bool(b)))
                    }
                    ComptimeVal::Str(s) => {
                        let str_ty = self.intern_str_type();
                        let cval = ConstValue::Aggregate(vec![
                            ConstValue::Str(s.clone()),
                            ConstValue::I64(s.len() as i128),
                        ]);
                        Ok((cval, str_ty, ComptimeVal::Str(s)))
                    }
                    ComptimeVal::Module(m) => {
                        let meta_ty = self.intern_type(Type::MetaType);
                        Ok((ConstValue::I64(0), meta_ty, ComptimeVal::Module(m)))
                    }
                    ComptimeVal::Map(id) => {
                        let map_ty = self.map_instances[id as usize].map_ty;
                        Ok((ConstValue::I64(id as i128), map_ty, ComptimeVal::Map(id)))
                    }
                    ComptimeVal::Type(t_id) => {
                        let meta_ty = self.intern_type(Type::MetaType);
                        Ok((ConstValue::Type(t_id), meta_ty, ComptimeVal::Type(t_id)))
                    }
                    ComptimeVal::ConstExpr(_, ref ce) if ce != expr => {
                        self.eval_const_expr_typed(mod_path, self_ty, env, ce, expected_ty)
                    }
                    _ => Err(format!(
                        "Expression cannot be evaluated as a compile-time constant initializer: {expr:?}"
                    )),
                }
            }
        }
    }

    pub(super) fn resolve_top_const(
        &mut self,
        mod_path: &str,
        name: &str,
    ) -> Result<(ConstValue, TypeId, ComptimeVal, bool), String> {
        let key = (mod_path.to_string(), name.to_string());
        if let Some(res) = self.resolved_consts.get(&key).cloned() {
            return Ok(res);
        }
        let Some((def_mod, _, Item::Const(cdecl), _)) =
            self.find_item_in_module(mod_path, mod_path, name)?
        else {
            return Err(format!("Constant '{name}' not found in '{mod_path}'"));
        };
        let env = HashMap::new();
        let has_explicit_ty = cdecl.ty.is_some();
        let expected_ty = if let Some(ref te) = cdecl.ty {
            Some(self.resolve_type_expr(&def_mod, None, &env, te)?)
        } else {
            None
        };
        let (cval, ty_id, ct_val) =
            self.eval_const_expr_typed(&def_mod, None, &env, &cdecl.init, expected_ty)?;
        let final_ty = expected_ty.unwrap_or(ty_id);
        let res = (cval, final_ty, ct_val, has_explicit_ty);
        self.resolved_consts.insert(key, res.clone());
        Ok(res)
    }

    pub(super) fn resolve_top_static(
        &mut self,
        mod_path: &str,
        name: &str,
    ) -> Result<(GlobalId, TypeId, bool), String> {
        let key = (mod_path.to_string(), name.to_string());
        if let Some(&res) = self.resolved_statics.get(&key) {
            return Ok(res);
        }
        let Some((def_mod, _, Item::Static(sdecl), _)) =
            self.find_item_in_module(mod_path, mod_path, name)?
        else {
            return Err(format!(
                "Static variable '{name}' not found in '{mod_path}'"
            ));
        };
        let env = HashMap::new();
        let ty_id = self.resolve_type_expr(&def_mod, None, &env, &sdecl.ty)?;
        self.validate_static_variable_type(&sdecl.name, ty_id, sdecl.mutable)?;
        let (init_val, _, _) =
            self.eval_const_expr_typed(&def_mod, None, &env, &sdecl.init, Some(ty_id))?;
        let gl_id = GlobalId(self.program.globals.len() as u32);
        self.program.globals.push(Global {
            id: gl_id,
            ty: ty_id,
            mutable: sdecl.mutable,
            init: init_val,
        });
        let res = (gl_id, ty_id, sdecl.mutable);
        self.resolved_statics.insert(key, res);
        Ok(res)
    }

    pub(super) fn resolve_associated_const(
        &mut self,
        owner_ty: TypeId,
        name: &str,
    ) -> Result<(ConstValue, TypeId, ComptimeVal, Visibility, bool), String> {
        let key = (owner_ty, name.to_string());
        if let Some(res) = self.associated_consts.get(&key).cloned() {
            return Ok(res);
        }
        let Some(comp) = self.composites.get(&owner_ty).cloned() else {
            return Err(format!("Type {owner_ty} has no associated constants"));
        };
        let Some((vis, cdecl)) = comp.consts.get(name).cloned() else {
            return Err(format!(
                "Type '{}' has no associated constant '{}'",
                comp.name, name
            ));
        };
        let has_explicit_ty = cdecl.ty.is_some();
        let expected_ty = if let Some(ref te) = cdecl.ty {
            Some(self.resolve_type_expr(
                &comp.def_module,
                Some(owner_ty),
                &comp.comptime_env,
                te,
            )?)
        } else {
            None
        };
        let (cval, ty_id, ct_val) = self.eval_const_expr_typed(
            &comp.def_module,
            Some(owner_ty),
            &comp.comptime_env,
            &cdecl.init,
            expected_ty,
        )?;
        let final_ty = expected_ty.unwrap_or(ty_id);
        let res = (cval, final_ty, ct_val, vis, has_explicit_ty);
        self.associated_consts.insert(key, res.clone());
        Ok(res)
    }

    pub(super) fn resolve_associated_static(
        &mut self,
        owner_ty: TypeId,
        name: &str,
    ) -> Result<(GlobalId, TypeId, bool, Visibility), String> {
        let key = (owner_ty, name.to_string());
        if let Some(&res) = self.associated_statics.get(&key) {
            return Ok(res);
        }
        let Some(comp) = self.composites.get(&owner_ty).cloned() else {
            return Err(format!("Type {owner_ty} has no associated statics"));
        };
        let Some((vis, sdecl)) = comp.statics.get(name).cloned() else {
            return Err(format!(
                "Type '{}' has no associated static '{}'",
                comp.name, name
            ));
        };
        let ty_id = self.resolve_type_expr(
            &comp.def_module,
            Some(owner_ty),
            &comp.comptime_env,
            &sdecl.ty,
        )?;
        let qual_name = format!("{}::{}", comp.name, sdecl.name);
        self.validate_static_variable_type(&qual_name, ty_id, sdecl.mutable)?;
        let (init_val, _, _) = self.eval_const_expr_typed(
            &comp.def_module,
            Some(owner_ty),
            &comp.comptime_env,
            &sdecl.init,
            Some(ty_id),
        )?;
        let gl_id = GlobalId(self.program.globals.len() as u32);
        self.program.globals.push(Global {
            id: gl_id,
            ty: ty_id,
            mutable: sdecl.mutable,
            init: init_val,
        });
        let res = (gl_id, ty_id, sdecl.mutable, vis);
        self.associated_statics.insert(key, res);
        Ok(res)
    }

    /// Collects all visible `FuncDecl`s (including disjoint meta-type overloads) named `name` in `target_mod`.
    pub(super) fn find_funcs_in_module(
        &self,
        from_mod: &str,
        target_mod: &str,
        name: &str,
    ) -> Result<Vec<(String, String, FuncDecl)>, String> {
        let Some(ast) = self.modules.get(target_mod) else {
            return Err(format!("Undefined module '{target_mod}'"));
        };
        let mut out = Vec::new();
        for item in &ast.items {
            if let Item::Func(f) = item
                && f.name == name
            {
                self.check_item_visibility(from_mod, target_mod, name, f.vis)?;
                out.push((target_mod.to_string(), f.name.clone(), f.clone()));
            }
        }
        for imp in &ast.imports {
            if imp.vis == Visibility::Private {
                continue;
            }
            let imp_mod = imp.path.join("::");
            match &imp.targets {
                ImportTargets::Items(items) => {
                    for (orig, alias) in items {
                        let bound = alias.as_deref().unwrap_or(orig);
                        if bound == name {
                            out.extend(self.find_funcs_in_module(target_mod, &imp_mod, orig)?);
                        }
                    }
                }
                ImportTargets::Glob => {
                    if let Ok(found) = self.find_funcs_in_module(target_mod, &imp_mod, name) {
                        out.extend(found);
                    }
                }
                ImportTargets::Module(alias) => {
                    if !self.modules.contains_key(&imp_mod) && imp.path.len() >= 2 {
                        let parent_mod = imp.path[..imp.path.len() - 1].join("::");
                        let orig = imp.path.last().unwrap();
                        let bound = alias.as_deref().unwrap_or(orig);
                        if bound == name {
                            out.extend(self.find_funcs_in_module(target_mod, &parent_mod, orig)?);
                        }
                    }
                }
            }
        }
        Ok(out)
    }

    /// Collects all top-level functions visible in `cur_mod` under `name`
    /// (defined locally, imported by item/alias, or imported by glob `*`).
    /// Compiler-injected prelude imports (`imp.is_prelude`) have the lowest lexical priority
    /// and are only consulted when no local or explicitly imported function named `name` exists.
    pub(super) fn find_in_scope_functions(
        &self,
        cur_mod: &str,
        name: &str,
    ) -> Result<Vec<(String, String, FuncDecl)>, String> {
        let mut results: Vec<(String, String, FuncDecl)> = Vec::new();
        let push_unique = |results: &mut Vec<(String, String, FuncDecl)>,
                           m: String,
                           orig: String,
                           decl: FuncDecl| {
            if !results
                .iter()
                .any(|(em, eo, ed)| em == &m && eo == &orig && ed.params == decl.params)
            {
                results.push((m, orig, decl));
            }
        };

        let Some(ast) = self.modules.get(cur_mod) else {
            return Ok(results);
        };

        // 1. Local functions in `cur_mod`
        for item in &ast.items {
            if let Item::Func(f) = item
                && f.name == name
            {
                push_unique(&mut results, cur_mod.to_string(), f.name.clone(), f.clone());
            }
        }

        // 2. Explicitly imported functions (`!imp.is_prelude`), then fallback to prelude (`imp.is_prelude`)
        for check_prelude in [false, true] {
            if check_prelude && !results.is_empty() {
                break;
            }
            for imp in &ast.imports {
                if imp.is_prelude != check_prelude {
                    continue;
                }
                let target_mod = imp.path.join("::");
                match &imp.targets {
                    ImportTargets::Items(list) => {
                        for (orig, alias) in list {
                            let bound = alias.as_deref().unwrap_or(orig);
                            if bound == name {
                                for (fm, fo, fd) in
                                    self.find_funcs_in_module(cur_mod, &target_mod, orig)?
                                {
                                    push_unique(&mut results, fm, fo, fd);
                                }
                            }
                        }
                    }
                    ImportTargets::Glob => {
                        if let Ok(found) = self.find_funcs_in_module(cur_mod, &target_mod, name) {
                            for (fm, fo, fd) in found {
                                push_unique(&mut results, fm, fo, fd);
                            }
                        }
                    }
                    ImportTargets::Module(alias) => {
                        if !self.modules.contains_key(&target_mod) && imp.path.len() >= 2 {
                            let parent_mod = imp.path[..imp.path.len() - 1].join("::");
                            let orig = imp.path.last().unwrap();
                            let bound = alias.as_deref().unwrap_or(orig);
                            if bound == name {
                                for (fm, fo, fd) in
                                    self.find_funcs_in_module(cur_mod, &parent_mod, orig)?
                                {
                                    push_unique(&mut results, fm, fo, fd);
                                }
                            }
                        }
                    }
                }
            }
        }

        Ok(results)
    }

    pub(super) fn eval_comptime_type_bound(
        &mut self,
        bound_mod: &str,
        self_ty: Option<TypeId>,
        env: &HashMap<String, ComptimeVal>,
        bound_expr: &TypeExpr,
        actual_ty: TypeId,
    ) -> Result<Option<Result<u8, String>>, String> {
        match bound_expr {
            TypeExpr::MetaType => Ok(Some(Ok(1))),
            TypeExpr::Opaque => {
                let c = TypeConstraint::Struct;
                if self.type_satisfies_constraint(actual_ty, c) {
                    Ok(Some(Ok(c.specificity())))
                } else {
                    Ok(Some(Err(format!(
                        "Type '{}' does not satisfy comptime constraint '{}'",
                        self.type_display_name(actual_ty),
                        c.name()
                    ))))
                }
            }
            TypeExpr::Constraint(c) => {
                if self.type_satisfies_constraint(actual_ty, *c) {
                    Ok(Some(Ok(c.specificity())))
                } else {
                    Ok(Some(Err(format!(
                        "Type '{}' does not satisfy comptime constraint '{}'",
                        self.type_display_name(actual_ty),
                        c.name()
                    ))))
                }
            }
            TypeExpr::TraitBounds(bounds) => {
                let mut max_spec = 1u8;
                for b in bounds {
                    match self.eval_comptime_type_bound(bound_mod, self_ty, env, b, actual_ty)? {
                        Some(Ok(s)) => max_spec = max_spec.max(s),
                        Some(Err(e)) => return Ok(Some(Err(e))),
                        None => {
                            return Err(format!(
                                "Invalid non-trait/non-constraint bound '{b:?}' in '+' bound list"
                            ));
                        }
                    }
                }
                Ok(Some(Ok(max_spec)))
            }
            TypeExpr::Trait(_) | TypeExpr::Named(_) | TypeExpr::TypeCall { .. } => {
                let Ok(bound_ty_id) = self.resolve_type_expr(bound_mod, self_ty, env, bound_expr)
                else {
                    return Ok(None);
                };
                if self.traits.contains_key(&bound_ty_id) {
                    let method_count = self.traits[&bound_ty_id].methods.len();
                    for m_idx in 0..method_count {
                        if let Err(e) = self.resolve_trait_impl_method(
                            bound_mod,
                            actual_ty,
                            bound_ty_id,
                            m_idx,
                            true,
                        ) {
                            return Ok(Some(Err(e)));
                        }
                    }
                    Ok(Some(Ok(6)))
                } else if matches!(self.program.types[bound_ty_id.0 as usize], Type::MetaType) {
                    Ok(Some(Ok(1)))
                } else {
                    Ok(None)
                }
            }
            _ => Ok(None),
        }
    }

    /// Unifies a `TypeExpr` pattern from a function in `fn_mod` against a concrete `actual_ty`,
    /// binding any `comptime_params` into `inferred` and returning a specificity score:
    /// - `20`: Concrete type match (`Point`, `i32`, `Pair(i32)`)
    /// - `11..=16`: Parameterized structural or type-constructor match (`simd[T; N]`, `[T; N]`, `?T`, `Pair(T)`),
    ///   sub-ranked by `T`'s meta-type or trait constraint
    /// - `1..=6`: Blanket generic type parameter (`T: type` = 1, `T: number` = 3, `T: signed` = 5, `T: MyTrait` = 6)
    pub(super) fn unify_type_pattern(
        &mut self,
        fn_mod: &str,
        comptime_params: &[(String, TypeExpr)],
        pat: &TypeExpr,
        actual_ty: TypeId,
        inferred: &mut HashMap<String, ComptimeVal>,
    ) -> Result<Option<u8>, String> {
        match pat {
            TypeExpr::Named(path)
                if path.len() == 1 && comptime_params.iter().any(|(n, _)| n == &path[0]) =>
            {
                let (_, bound_expr) = comptime_params
                    .iter()
                    .find(|(n, _)| n == &path[0])
                    .unwrap()
                    .clone();
                let spec = match self.eval_comptime_type_bound(
                    fn_mod,
                    None,
                    inferred,
                    &bound_expr,
                    actual_ty,
                )? {
                    Some(Ok(s)) => s,
                    Some(Err(_)) => return Ok(None),
                    None => 1,
                };
                if let Some(existing) = inferred.get(&path[0]) {
                    Ok((existing == &ComptimeVal::Type(actual_ty)).then_some(spec))
                } else {
                    inferred.insert(path[0].clone(), ComptimeVal::Type(actual_ty));
                    Ok(Some(spec))
                }
            }
            TypeExpr::Ref { inner, .. } | TypeExpr::Ptr { inner, .. } => {
                if let Type::Ptr { pointee, .. } = self.program.types[actual_ty.0 as usize] {
                    self.unify_type_pattern(fn_mod, comptime_params, inner, pointee, inferred)
                } else {
                    Ok(None)
                }
            }
            TypeExpr::Simd { elem, len } => {
                let Type::Simd {
                    elem: act_elem,
                    len: act_len,
                } = self.program.types[actual_ty.0 as usize]
                else {
                    return Ok(None);
                };
                let Some(s1) =
                    self.unify_type_pattern(fn_mod, comptime_params, elem, act_elem, inferred)?
                else {
                    return Ok(None);
                };
                let Some(s2) = self.unify_comptime_expr(
                    fn_mod,
                    comptime_params,
                    len,
                    &ComptimeVal::Int(act_len as i128),
                    inferred,
                )?
                else {
                    return Ok(None);
                };
                Ok(Some(if s1 == 20 && s2 == 20 {
                    20
                } else {
                    10 + s1.min(9)
                }))
            }
            TypeExpr::Array { elem, len } => {
                let Type::Array {
                    elem: act_elem,
                    len: act_len,
                } = self.program.types[actual_ty.0 as usize]
                else {
                    return Ok(None);
                };
                let Some(s1) =
                    self.unify_type_pattern(fn_mod, comptime_params, elem, act_elem, inferred)?
                else {
                    return Ok(None);
                };
                let Some(s2) = self.unify_comptime_expr(
                    fn_mod,
                    comptime_params,
                    len,
                    &ComptimeVal::Int(act_len as i128),
                    inferred,
                )?
                else {
                    return Ok(None);
                };
                Ok(Some(if s1 == 20 && s2 == 20 {
                    20
                } else {
                    10 + s1.min(9)
                }))
            }
            TypeExpr::Slice { mutable, elem } => {
                let act_elem = if let Some(&info) = self.slices.get(&actual_ty) {
                    if *mutable && !info.mutable {
                        return Ok(None);
                    }
                    info.elem
                } else if let Type::Ptr {
                    mutable: act_mut,
                    pointee,
                } = self.program.types[actual_ty.0 as usize]
                    && let Type::Array { elem: arr_elem, .. } =
                        self.program.types[pointee.0 as usize]
                {
                    if *mutable && !act_mut {
                        return Ok(None);
                    }
                    arr_elem
                } else {
                    return Ok(None);
                };
                let Some(s) =
                    self.unify_type_pattern(fn_mod, comptime_params, elem, act_elem, inferred)?
                else {
                    return Ok(None);
                };
                Ok(Some(if s == 20 { 20 } else { 10 + s.min(9) }))
            }
            TypeExpr::Optional(inner) => {
                if self.results.contains_key(&actual_ty)
                    || self.errors.contains_key(&actual_ty)
                    || self.unions.contains_key(&actual_ty)
                {
                    return Ok(None);
                }
                let Type::Union { variants, .. } = self.program.types[actual_ty.0 as usize].clone()
                else {
                    return Ok(None);
                };
                if variants.len() != 2
                    || !matches!(self.program.types[variants[0].0 as usize], Type::Void)
                {
                    return Ok(None);
                }
                let Some(s) =
                    self.unify_type_pattern(fn_mod, comptime_params, inner, variants[1], inferred)?
                else {
                    return Ok(None);
                };
                Ok(Some(if s == 20 { 20 } else { 10 + s.min(9) }))
            }
            TypeExpr::Uninit(inner) => {
                let Some(&inner_ty) = self.uninit_types.get(&actual_ty) else {
                    return Ok(None);
                };
                let Some(s) =
                    self.unify_type_pattern(fn_mod, comptime_params, inner, inner_ty, inferred)?
                else {
                    return Ok(None);
                };
                Ok(Some(if s == 20 { 20 } else { 10 + s.min(9) }))
            }
            TypeExpr::Result { err, ok } => {
                let Some(&res_info) = self.results.get(&actual_ty) else {
                    return Ok(None);
                };
                let Some(s_err) = self.unify_type_pattern(
                    fn_mod,
                    comptime_params,
                    err,
                    res_info.err_ty,
                    inferred,
                )?
                else {
                    return Ok(None);
                };
                let Some(s_ok) =
                    self.unify_type_pattern(fn_mod, comptime_params, ok, res_info.ok_ty, inferred)?
                else {
                    return Ok(None);
                };
                let min_s = s_err.min(s_ok);
                Ok(Some(if min_s == 20 { 20 } else { 10 + min_s.min(9) }))
            }
            TypeExpr::Tuple(elems) => {
                if self.composites.contains_key(&actual_ty)
                    || self.trait_objs.contains_key(&actual_ty)
                    || self.closures.contains_key(&actual_ty)
                    || self.slices.contains_key(&actual_ty)
                {
                    return Ok(None);
                }
                let Type::Struct(act_fields) = self.program.types[actual_ty.0 as usize].clone()
                else {
                    return Ok(None);
                };
                if act_fields.len() != elems.len() {
                    return Ok(None);
                }
                let mut all_concrete = true;
                let mut min_sub = 9u8;
                for (e_pat, act_f) in elems.iter().zip(act_fields.iter()) {
                    let Some(s) =
                        self.unify_type_pattern(fn_mod, comptime_params, e_pat, *act_f, inferred)?
                    else {
                        return Ok(None);
                    };
                    if s < 20 {
                        all_concrete = false;
                        min_sub = min_sub.min(s);
                    }
                }
                Ok(Some(if all_concrete { 20 } else { 10 + min_sub }))
            }
            TypeExpr::FnPtr { params, ret } => {
                let Type::FnPtr {
                    args: act_args,
                    ret: act_ret,
                } = self.program.types[actual_ty.0 as usize].clone()
                else {
                    return Ok(None);
                };
                if act_args.len() != params.len() {
                    return Ok(None);
                }
                let mut all_concrete = true;
                let mut min_sub = 9u8;
                for (p_pat, act_a) in params.iter().zip(act_args.iter()) {
                    let Some(s) =
                        self.unify_type_pattern(fn_mod, comptime_params, p_pat, *act_a, inferred)?
                    else {
                        return Ok(None);
                    };
                    if s < 20 {
                        all_concrete = false;
                        min_sub = min_sub.min(s);
                    }
                }
                let Some(rs) =
                    self.unify_type_pattern(fn_mod, comptime_params, ret, act_ret, inferred)?
                else {
                    return Ok(None);
                };
                if rs < 20 {
                    all_concrete = false;
                    min_sub = min_sub.min(rs);
                }
                Ok(Some(if all_concrete { 20 } else { 10 + min_sub }))
            }
            TypeExpr::TypeCall { path, args } => {
                let Ok(ResolvedItem::Func(target_mod, target_fn)) = self.resolve_path(fn_mod, path)
                else {
                    return Ok(None);
                };
                let memo_match = self
                    .memoized_type_calls
                    .iter()
                    .find(|((m_mod, m_fn, m_args), m_ty_id)| {
                        **m_ty_id == actual_ty
                            && m_mod == &target_mod
                            && m_fn == &target_fn
                            && m_args.len() == args.len()
                    })
                    .map(|((_, _, m_args), _)| m_args.clone());
                let Some(m_args) = memo_match else {
                    return Ok(None);
                };
                let mut all_concrete = true;
                let mut min_sub = 9u8;
                for (arg_expr, actual_val) in args.iter().zip(m_args.iter()) {
                    let Some(s) = self.unify_comptime_expr(
                        fn_mod,
                        comptime_params,
                        arg_expr,
                        actual_val,
                        inferred,
                    )?
                    else {
                        return Ok(None);
                    };
                    if s < 20 {
                        all_concrete = false;
                        min_sub = min_sub.min(s);
                    }
                }
                Ok(Some(if all_concrete { 20 } else { 10 + min_sub }))
            }
            _ => {
                if let Ok(resolved_ty) = self.resolve_type_expr(fn_mod, None, inferred, pat)
                    && resolved_ty == actual_ty
                {
                    Ok(Some(20))
                } else {
                    Ok(None)
                }
            }
        }
    }

    pub(super) fn unify_comptime_expr(
        &mut self,
        fn_mod: &str,
        comptime_params: &[(String, TypeExpr)],
        expr: &Expr,
        actual: &ComptimeVal,
        inferred: &mut HashMap<String, ComptimeVal>,
    ) -> Result<Option<u8>, String> {
        match expr {
            Expr::Path(p) if p.len() == 1 && comptime_params.iter().any(|(n, _)| n == &p[0]) => {
                let (_, bound_expr) = comptime_params
                    .iter()
                    .find(|(n, _)| n == &p[0])
                    .unwrap()
                    .clone();
                let spec = if let ComptimeVal::Type(act_ty) = actual {
                    match self.eval_comptime_type_bound(
                        fn_mod,
                        None,
                        inferred,
                        &bound_expr,
                        *act_ty,
                    )? {
                        Some(Ok(s)) => s,
                        Some(Err(_)) => return Ok(None),
                        None => 1,
                    }
                } else {
                    1
                };
                if let Some(existing) = inferred.get(&p[0]) {
                    Ok((existing == actual).then_some(spec))
                } else {
                    inferred.insert(p[0].clone(), actual.clone());
                    Ok(Some(spec))
                }
            }
            Expr::TypeVal(te) => {
                if let ComptimeVal::Type(act_ty) = actual {
                    self.unify_type_pattern(fn_mod, comptime_params, te, *act_ty, inferred)
                } else {
                    Ok(None)
                }
            }
            _ => {
                if let Ok(val) = self.eval_comptime_val(fn_mod, None, inferred, expr)
                    && &val == actual
                {
                    Ok(Some(20))
                } else {
                    Ok(None)
                }
            }
        }
    }

    /// Resolves a `self`-receiver extension function in `cur_mod` for receiver base type `comp_ty`.
    pub(super) fn resolve_extension_method(
        &mut self,
        cur_mod: &str,
        comp_ty: TypeId,
        method_name: &str,
    ) -> Result<(String, String, FuncDecl, HashMap<String, ComptimeVal>), String> {
        let mut candidates = self.find_in_scope_functions(cur_mod, method_name)?;
        // Also check the composite's/newtype's defining module if `comp_ty` is a user-defined type
        // and no candidates were found in `cur_mod` (e.g. inside a generic function).
        if candidates.is_empty() {
            let def_mod_opt = self
                .composites
                .get(&comp_ty)
                .map(|c| c.def_module.clone())
                .or_else(|| {
                    self.opaque_newtypes
                        .get(&comp_ty)
                        .map(|nt| nt.def_module.clone())
                });
            if let Some(def_mod) = def_mod_opt
                && def_mod != cur_mod
                && let Ok(found) = self.find_funcs_in_module(cur_mod, &def_mod, method_name)
            {
                candidates.extend(found);
            }
        }
        // Also check defining modules of traits that declare `method_name`
        if candidates.is_empty() {
            let trait_mods: Vec<String> = self
                .traits
                .values()
                .filter(|tr| {
                    tr.def_module != cur_mod && tr.methods.iter().any(|m| m.name == method_name)
                })
                .map(|tr| tr.def_module.clone())
                .collect();
            for tmod in trait_mods {
                if let Ok(found) = self.find_funcs_in_module(&tmod, &tmod, method_name) {
                    for item in found {
                        if !candidates.iter().any(|(em, eo, ed)| {
                            em == &item.0 && eo == &item.1 && ed.params == item.2.params
                        }) {
                            candidates.push(item);
                        }
                    }
                }
            }
        }

        let mut matched: Vec<(String, String, FuncDecl, HashMap<String, ComptimeVal>, u8)> =
            Vec::new();

        for (fn_mod, orig_name, decl) in candidates {
            let Some(self_param) = decl.params.iter().find(|p| !p.is_comptime) else {
                continue;
            };
            if self_param.name != "self" {
                continue;
            }
            let comptime_params: Vec<(String, TypeExpr)> = decl
                .params
                .iter()
                .filter(|p| p.is_comptime)
                .map(|p| (p.name.clone(), p.ty.clone()))
                .collect();
            let self_target_pat = match &self_param.ty {
                TypeExpr::Ref { inner, .. } | TypeExpr::Ptr { inner, .. } => inner.as_ref(),
                other => other,
            };
            let mut inferred = HashMap::new();
            if let Some(specificity) = self.unify_type_pattern(
                &fn_mod,
                &comptime_params,
                self_target_pat,
                comp_ty,
                &mut inferred,
            )? {
                matched.push((fn_mod, orig_name, decl, inferred, specificity));
            }
        }

        let type_display = self.type_display_name(comp_ty);

        if matched.is_empty() {
            return Err(format!(
                "Type '{}' has no method '{}'",
                type_display, method_name
            ));
        }

        let max_spec = matched.iter().map(|m| m.4).max().unwrap();
        let best: Vec<_> = matched.into_iter().filter(|m| m.4 == max_spec).collect();
        if best.len() > 1 {
            return Err(format!(
                "Ambiguous extension method '{}' for type '{}': conflicting definitions in module '{}' and module '{}'",
                method_name, type_display, best[0].0, best[1].0
            ));
        }

        let (fn_mod, orig_name, decl, inferred, _) = best.into_iter().next().unwrap();
        Ok((fn_mod, orig_name, decl, inferred))
    }

    fn const_value_to_comptime(cv: &ConstValue, fallback_expr: &Expr) -> ComptimeVal {
        match cv {
            ConstValue::I64(n) => ComptimeVal::Int(*n),
            ConstValue::Bool(b) => ComptimeVal::Bool(*b),
            ConstValue::Type(t) => ComptimeVal::Type(*t),
            ConstValue::Str(s) => ComptimeVal::Str(s.clone()),
            ConstValue::Aggregate(items) => {
                if items.len() == 2
                    && let ConstValue::Str(s) = &items[0]
                {
                    return ComptimeVal::Str(s.clone());
                }
                ComptimeVal::ConstExpr(format!("{cv:?}"), fallback_expr.clone())
            }
            _ => ComptimeVal::ConstExpr(format!("{cv:?}"), fallback_expr.clone()),
        }
    }

    pub(super) fn eval_map_key(
        &mut self,
        mod_path: &str,
        self_ty: Option<TypeId>,
        env: &HashMap<String, ComptimeVal>,
        expr: &Expr,
        expected_ty: Option<TypeId>,
    ) -> Result<(MapKey, ConstValue, ComptimeVal), String> {
        let (cval, _ty, ct_val) =
            self.eval_const_expr_typed(mod_path, self_ty, env, expr, expected_ty)?;
        let mkey = match &ct_val {
            ComptimeVal::Type(t) => MapKey::Type(*t),
            ComptimeVal::Int(n) => MapKey::Int(*n),
            ComptimeVal::Bool(b) => MapKey::Bool(*b),
            ComptimeVal::Str(s) => MapKey::Str(s.clone()),
            ComptimeVal::Module(m) => MapKey::Module(m.clone()),
            _ => {
                return Err(format!(
                    "Map key '{expr:?}' must evaluate to a compile-time type, integer/enum, bool, &str, or module"
                ));
            }
        };
        Ok((mkey, cval, ct_val))
    }

    pub(super) fn eval_map_lit(
        &mut self,
        mod_path: &str,
        self_ty: Option<TypeId>,
        env: &HashMap<String, ComptimeVal>,
        pairs: &[(Expr, Expr)],
        expected_ty: Option<TypeId>,
    ) -> Result<(ConstValue, TypeId, ComptimeVal), String> {
        let (key_ty, val_ty, map_ty) = if let Some(exp) = expected_ty
            && let Some(&info) = self.maps.get(&exp)
        {
            (info.key_ty, info.val_ty, exp)
        } else if let Some((first_k, first_v)) = pairs.first() {
            let (_, k_ty, _) = self.eval_const_expr_typed(mod_path, self_ty, env, first_k, None)?;
            let (_, v_ty, _) = self.eval_const_expr_typed(mod_path, self_ty, env, first_v, None)?;
            let m_ty = self.intern_map_type(k_ty, v_ty);
            (k_ty, v_ty, m_ty)
        } else {
            return Err("Empty map literal requires an explicit 'map[K, V]' type".to_string());
        };
        let mut entries = Vec::with_capacity(pairs.len());
        for (k_expr, v_expr) in pairs {
            let (mkey, k_const, k_ct) =
                self.eval_map_key(mod_path, self_ty, env, k_expr, Some(key_ty))?;
            if entries.iter().any(|e: &MapEntry| e.key == mkey) {
                return Err(format!(
                    "Duplicate key {mkey:?} in comptime associative map literal"
                ));
            }
            let (v_const, _, v_ct) =
                self.eval_const_expr_typed(mod_path, self_ty, env, v_expr, Some(val_ty))?;
            entries.push(MapEntry {
                key: mkey,
                key_const: k_const,
                key_comptime: k_ct,
                val_const: v_const,
                val_comptime: v_ct,
            });
        }
        let map_id = self.map_instances.len() as u32;
        self.map_instances.push(MapInstance { map_ty, entries });
        Ok((
            ConstValue::I64(map_id as i128),
            map_ty,
            ComptimeVal::Map(map_id),
        ))
    }

    pub(super) fn eval_map_invert(
        &mut self,
        mod_path: &str,
        self_ty: Option<TypeId>,
        env: &HashMap<String, ComptimeVal>,
        inner: &Expr,
    ) -> Result<(ConstValue, TypeId, ComptimeVal), String> {
        let Some(src_id) = self.resolve_map_expr(mod_path, self_ty, env, inner)? else {
            return Err("'@invert' requires a comptime associative map argument".to_string());
        };
        let src_inst = self.map_instances[src_id as usize].clone();
        let src_info = self.maps[&src_inst.map_ty];
        let inv_map_ty = self.intern_map_type(src_info.val_ty, src_info.key_ty);
        let mut inv_entries = Vec::with_capacity(src_inst.entries.len());
        for entry in src_inst.entries {
            let inv_key = match &entry.val_comptime {
                ComptimeVal::Type(t) => MapKey::Type(*t),
                ComptimeVal::Int(n) => MapKey::Int(*n),
                ComptimeVal::Bool(b) => MapKey::Bool(*b),
                ComptimeVal::Str(s) => MapKey::Str(s.clone()),
                ComptimeVal::Module(m) => MapKey::Module(m.clone()),
                _ => {
                    return Err(
                        "Cannot '@invert' map whose values are not valid map keys".to_string(),
                    );
                }
            };
            if inv_entries.iter().any(|e: &MapEntry| e.key == inv_key) {
                return Err(format!(
                    "Cannot '@invert' map: duplicate value {inv_key:?} violates 1-to-1 bijection"
                ));
            }
            inv_entries.push(MapEntry {
                key: inv_key,
                key_const: entry.val_const,
                key_comptime: entry.val_comptime,
                val_const: entry.key_const,
                val_comptime: entry.key_comptime,
            });
        }
        let inv_id = self.map_instances.len() as u32;
        self.map_instances.push(MapInstance {
            map_ty: inv_map_ty,
            entries: inv_entries,
        });
        Ok((
            ConstValue::I64(inv_id as i128),
            inv_map_ty,
            ComptimeVal::Map(inv_id),
        ))
    }

    pub(super) fn resolve_map_expr(
        &mut self,
        mod_path: &str,
        self_ty: Option<TypeId>,
        env: &HashMap<String, ComptimeVal>,
        expr: &Expr,
    ) -> Result<Option<u32>, String> {
        match expr {
            Expr::Path(p) => {
                if p.len() == 1
                    && let Some(ComptimeVal::Map(id)) = env.get(&p[0])
                {
                    return Ok(Some(*id));
                }
                let expanded = self.expand_module_path(env, p);
                if expanded.len() >= 2 {
                    let prefix = &expanded[..expanded.len() - 1];
                    let cname = expanded.last().unwrap();
                    let owner_opt = if prefix.len() == 1 && prefix[0] == "Self" {
                        self_ty
                    } else if prefix.len() == 1
                        && let Some(ComptimeVal::Type(t_id)) = env.get(&prefix[0])
                    {
                        Some(*t_id)
                    } else if let Ok(ResolvedItem::Type(tmod, tname)) =
                        self.resolve_path(mod_path, prefix)
                    {
                        self.resolve_named_type(&tmod, &tname).ok()
                    } else {
                        None
                    };
                    if let Some(owner_ty) = owner_opt
                        && let Some(comp) = self.composites.get(&owner_ty)
                        && comp.consts.contains_key(cname)
                    {
                        let (_, _, ct_val, _, _) = self.resolve_associated_const(owner_ty, cname)?;
                        if let ComptimeVal::Map(id) = ct_val {
                            return Ok(Some(id));
                        }
                    }
                }
                if let Ok(ResolvedItem::Const(cmod, cname)) =
                    self.resolve_path(mod_path, &expanded)
                {
                    let (_, _, ct_val, _) = self.resolve_top_const(&cmod, &cname)?;
                    if let ComptimeVal::Map(id) = ct_val {
                        return Ok(Some(id));
                    }
                }
                Ok(None)
            }
            Expr::MapLit(_) | Expr::IntrinsicInvert(_) => {
                let (_, _, ct_val) =
                    self.eval_const_expr_typed(mod_path, self_ty, env, expr, None)?;
                if let ComptimeVal::Map(id) = ct_val {
                    Ok(Some(id))
                } else {
                    Ok(None)
                }
            }
            _ => Ok(None),
        }
    }

    pub(super) fn eval_module_declarations(
        &mut self,
        mod_path: &str,
        self_ty: Option<TypeId>,
        env: &HashMap<String, ComptimeVal>,
        inner: &Expr,
    ) -> Result<(ConstValue, TypeId, ComptimeVal), String> {
        let target_mod = match inner {
            Expr::Path(p) => {
                if p.len() == 1
                    && let Some(ComptimeVal::Module(m)) = env.get(&p[0])
                {
                    m.clone()
                } else {
                    let expanded = self.expand_module_path(env, p);
                    match self.resolve_path(mod_path, &expanded)? {
                        ResolvedItem::Module(m) => m,
                        ResolvedItem::Const(cmod, cname) => {
                            let (_, _, cv, _) = self.resolve_top_const(&cmod, &cname)?;
                            if let ComptimeVal::Module(m) = cv {
                                m
                            } else {
                                return Err(format!(
                                    "'@declarations' argument '{}' is not a module",
                                    expanded.join("::")
                                ));
                            }
                        }
                        _ => {
                            return Err(format!(
                                "'@declarations' argument '{}' is not a module",
                                expanded.join("::")
                            ));
                        }
                    }
                }
            }
            other => match self.eval_comptime_val(mod_path, self_ty, env, other)? {
                ComptimeVal::Module(m) => m,
                _ => {
                    return Err("'@declarations' requires a comptime module argument".to_string());
                }
            },
        };
        let Some(ast) = self.modules.get(&target_mod) else {
            return Err(format!("Undefined module '{target_mod}' in '@declarations'"));
        };
        let mut decl_names = Vec::new();
        for item in &ast.items {
            let (vis, name) = match item {
                Item::Func(f) => (f.vis, &f.name),
                Item::ExternFunc(e) => (e.vis, &e.name),
                Item::TypeDecl { vis, name, .. } => (*vis, name),
                Item::Static(s) => (s.vis, &s.name),
                Item::Const(c) => (c.vis, &c.name),
            };
            if vis != Visibility::Private && !name.contains("::") && !name.starts_with("__lrrr_") {
                decl_names.push(name.clone());
            }
        }
        let str_ty = self.intern_str_type();
        let slice_ty = self.intern_slice_type(false, str_ty);
        let arr_ty = self.intern_type(Type::Array {
            elem: str_ty,
            len: decl_names.len() as u64,
        });
        let elem_consts: Vec<ConstValue> = decl_names
            .iter()
            .map(|s| {
                ConstValue::Aggregate(vec![
                    ConstValue::Str(s.clone()),
                    ConstValue::I64(s.len() as i128),
                ])
            })
            .collect();
        let gl_id = GlobalId(self.program.globals.len() as u32);
        self.program.globals.push(Global {
            id: gl_id,
            ty: arr_ty,
            mutable: false,
            init: ConstValue::Aggregate(elem_consts),
        });
        let cval = ConstValue::Aggregate(vec![
            ConstValue::Global(gl_id),
            ConstValue::I64(decl_names.len() as i128),
        ]);
        Ok((
            cval,
            slice_ty,
            ComptimeVal::ConstExpr(format!("@declarations({target_mod})"), inner.clone()),
        ))
    }

    pub(super) fn eval_comptime_val(
        &mut self,
        mod_path: &str,
        self_ty: Option<TypeId>,
        env: &HashMap<String, ComptimeVal>,
        expr: &Expr,
    ) -> Result<ComptimeVal, String> {
        match expr {
            Expr::TypeVal(te) => Ok(ComptimeVal::Type(
                self.resolve_type_expr(mod_path, self_ty, env, te)?,
            )),
            Expr::LogicalOr(lhs, rhs) => {
                let l_val = self.eval_comptime_val(mod_path, self_ty, env, lhs)?;
                let r_val = self.eval_comptime_val(mod_path, self_ty, env, rhs)?;
                match (l_val, r_val) {
                    (ComptimeVal::Type(l_ty), ComptimeVal::Type(r_ty)) => {
                        Ok(ComptimeVal::Type(self.combine_error_types(l_ty, r_ty)?))
                    }
                    (ComptimeVal::Bool(l_b), ComptimeVal::Bool(r_b)) => {
                        Ok(ComptimeVal::Bool(l_b || r_b))
                    }
                    _ => Err("Unsupported operands for comptime '||'".to_string()),
                }
            }
            Expr::Int(n) => Ok(ComptimeVal::Int(*n)),
            Expr::Bool(b) => Ok(ComptimeVal::Bool(*b)),
            Expr::Str(s) => Ok(ComptimeVal::Str(s.clone())),
            Expr::MapLit(_)
            | Expr::IntrinsicInvert(_)
            | Expr::IntrinsicDeclarations(_)
            | Expr::If { .. }
            | Expr::Index { .. } => {
                let (_, _, ct_val) =
                    self.eval_const_expr_typed(mod_path, self_ty, env, expr, None)?;
                Ok(ct_val)
            }
            Expr::Path(p) => {
                if p.len() == 1
                    && let Some(v) = env.get(&p[0])
                {
                    return Ok(v.clone());
                }
                let expanded = self.expand_module_path(env, p);
                let p = &expanded;
                if p.len() >= 2 {
                    let prefix = &p[..p.len() - 1];
                    let cname = p.last().unwrap();
                    let owner_opt = if prefix.len() == 1 && prefix[0] == "Self" {
                        self_ty
                    } else if prefix.len() == 1
                        && let Some(ComptimeVal::Type(t_id)) = env.get(&prefix[0])
                    {
                        Some(*t_id)
                    } else if let Ok(ResolvedItem::Type(tmod, tname)) =
                        self.resolve_path(mod_path, prefix)
                    {
                        Some(self.resolve_named_type(&tmod, &tname)?)
                    } else {
                        None
                    };
                    if let Some(owner_ty) = owner_opt
                        && let Some(comp) = self.composites.get(&owner_ty)
                        && comp.consts.contains_key(cname)
                    {
                        let (_, _, ct_val, cvis, _) =
                            self.resolve_associated_const(owner_ty, cname)?;
                        let comp = &self.composites[&owner_ty];
                        if comp.is_struct
                            && cvis == Visibility::Private
                            && self_ty != Some(owner_ty)
                        {
                            return Err(format!(
                                "Cannot access private constant '{}::{}' outside its 'opaque {{ ... }}' block",
                                comp.name, cname
                            ));
                        }
                        if cvis == Visibility::Private && comp.def_module != mod_path {
                            return Err(format!(
                                "Constant '{}::{}' is private to module '{}'",
                                comp.name, cname, comp.def_module
                            ));
                        }
                        return Ok(ct_val);
                    }
                    if let Some(owner_ty) = owner_opt
                        && let Some((_, variants)) = self.enums.get(&owner_ty)
                        && let Some((_, val)) = variants.iter().find(|(vn, _)| vn == cname)
                    {
                        return Ok(ComptimeVal::Int(*val));
                    }
                    if let Some(_owner_ty) = owner_opt
                        && matches!(cname.as_str(), "MIN" | "MAX" | "BITS" | "SIGNED")
                        && let Some((_, _, ct_val)) = self.eval_int_reflection_field(
                            mod_path,
                            self_ty,
                            env,
                            &Expr::Path(prefix.to_vec()),
                            cname,
                        )?
                    {
                        return Ok(ct_val);
                    }
                }
                if let Ok(ResolvedItem::Module(m)) = self.resolve_path(mod_path, p) {
                    return Ok(ComptimeVal::Module(m));
                }
                if let Ok(ResolvedItem::Type(tmod, tname)) = self.resolve_path(mod_path, p) {
                    return Ok(ComptimeVal::Type(self.resolve_named_type(&tmod, &tname)?));
                }
                if let Ok(ResolvedItem::Const(cmod, cname)) = self.resolve_path(mod_path, p) {
                    let (_, _, ct_val, _) = self.resolve_top_const(&cmod, &cname)?;
                    return Ok(ct_val);
                }
                Err(format!("Cannot evaluate '{}' at comptime", p.join("::")))
            }
            Expr::Field { base, field } => {
                if let Some((_, _, ct_val)) =
                    self.eval_int_reflection_field(mod_path, self_ty, env, base, field)?
                {
                    return Ok(ct_val);
                }
                if let Ok((_, _, ct_val)) =
                    self.eval_const_expr_typed(mod_path, self_ty, env, expr, None)
                {
                    return Ok(ct_val);
                }
                Ok(ComptimeVal::Int(
                    self.eval_comptime_int(mod_path, self_ty, env, expr)?,
                ))
            }
            Expr::Call { callee, args } => {
                if let Expr::Path(path) = callee.as_ref() {
                    let expanded = self.expand_module_path(env, path);
                    if let Ok(ResolvedItem::Func(fmod, fname)) =
                        self.resolve_path(mod_path, &expanded)
                    {
                        let mut ct_args = Vec::with_capacity(args.len());
                        for a in args {
                            ct_args.push(self.eval_comptime_val(mod_path, self_ty, env, a)?);
                        }
                        return self.eval_comptime_func(&fmod, &fname, &ct_args);
                    }
                }
                Err(format!("Unsupported comptime call {expr:?}"))
            }
            Expr::StructLit { .. } | Expr::Ref { .. } => {
                Ok(ComptimeVal::ConstExpr(format!("{expr:?}"), expr.clone()))
            }
            _ => {
                if let Ok((_, _, ct_val)) =
                    self.eval_const_expr_typed(mod_path, self_ty, env, expr, None)
                {
                    return Ok(ct_val);
                }
                Ok(ComptimeVal::Int(
                    self.eval_comptime_int(mod_path, self_ty, env, expr)?,
                ))
            }
        }
    }

    #[allow(clippy::only_used_in_recursion)]
    pub(super) fn eval_comptime_int(
        &mut self,
        mod_path: &str,
        self_ty: Option<TypeId>,
        env: &HashMap<String, ComptimeVal>,
        expr: &Expr,
    ) -> Result<i128, String> {
        match expr {
            Expr::Int(n) => Ok(*n),
            Expr::Path(p) => {
                if p.len() == 1
                    && let Some(ComptimeVal::Int(n)) = env.get(&p[0])
                {
                    return Ok(*n);
                }
                if let Ok(ComptimeVal::Int(n)) =
                    self.eval_comptime_val(mod_path, self_ty, env, expr)
                {
                    return Ok(n);
                }
                Err(format!("Expected comptime integer for '{}'", p.join("::")))
            }
            Expr::Unary {
                op: UnOp::Neg,
                expr: inner,
            } => Ok(-self.eval_comptime_int(mod_path, self_ty, env, inner)?),
            Expr::Field { base, field } => {
                if let Some((_, _, ComptimeVal::Int(n))) =
                    self.eval_int_reflection_field(mod_path, self_ty, env, base, field)?
                {
                    return Ok(n);
                }
                Err(format!(
                    "Cannot evaluate field '.{field}' as comptime integer"
                ))
            }
            Expr::Binary { op, lhs, rhs } => {
                let l = self.eval_comptime_int(mod_path, self_ty, env, lhs)?;
                let r = self.eval_comptime_int(mod_path, self_ty, env, rhs)?;
                match op {
                    BinOp::Add | BinOp::AddWrap => Ok(l + r),
                    BinOp::Sub | BinOp::SubWrap => Ok(l - r),
                    BinOp::Mul | BinOp::MulWrap => Ok(l * r),
                    BinOp::Div => Ok(l / r),
                    BinOp::Rem => Ok(l % r),
                    _ => Err(format!("Unsupported comptime binary op {op}")),
                }
            }
            _ => Err(format!(
                "Cannot evaluate expression as comptime integer: {expr:?}"
            )),
        }
    }

    pub(super) fn eval_comptime_type_func(
        &mut self,
        mod_path: &str,
        fname: &str,
        args: &[ComptimeVal],
    ) -> Result<TypeId, String> {
        let mut norm_args = args.to_vec();
        if fname == "JoinHandle"
            && norm_args.len() == 1
            && let ComptimeVal::Type(ty_id) = norm_args[0]
        {
            if let Type::FnPtr { ret, .. } = self.program.types[ty_id.0 as usize] {
                norm_args[0] = ComptimeVal::Type(ret);
            } else if let Some(cinfo) = self.closures.get(&ty_id) {
                norm_args[0] = ComptimeVal::Type(cinfo.ret_ty);
            }
        }
        let key = (mod_path.to_string(), fname.to_string(), norm_args.clone());
        if let Some(&ty_id) = self.memoized_type_calls.get(&key) {
            return Ok(ty_id);
        }
        if let Ok(Some((def_mod, orig_name, _, _))) =
            self.find_item_in_module(mod_path, mod_path, fname)
        {
            let def_key = (def_mod, orig_name, norm_args.clone());
            if let Some(&ty_id) = self.memoized_type_calls.get(&def_key) {
                self.memoized_type_calls.insert(key, ty_id);
                return Ok(ty_id);
            }
        }
        let val = self.eval_comptime_func(mod_path, fname, &norm_args)?;
        let ComptimeVal::Type(ty_id) = val else {
            return Err(format!(
                "Expected comptime function '{fname}' to return a type, got {val:?}"
            ));
        };
        self.memoized_type_calls.insert(key, ty_id);
        Ok(ty_id)
    }

    pub(super) fn eval_comptime_func(
        &mut self,
        mod_path: &str,
        fname: &str,
        args: &[ComptimeVal],
    ) -> Result<ComptimeVal, String> {
        let Some((def_mod, orig_name, Item::Func(decl), _)) =
            self.find_item_in_module(mod_path, mod_path, fname)?
        else {
            return Err(format!(
                "Comptime function '{fname}' not found in '{mod_path}'"
            ));
        };
        let mod_path = def_mod.as_str();
        let fname = orig_name.as_str();
        if decl.params.len() != args.len() {
            return Err(format!(
                "Comptime function '{fname}' expects {} args, got {}",
                decl.params.len(),
                args.len()
            ));
        }
        let mut local_env = HashMap::new();
        for (p, arg) in decl.params.iter().zip(args.iter()) {
            if let ComptimeVal::Type(arg_ty) = arg
                && let Some(Err(e)) =
                    self.eval_comptime_type_bound(mod_path, None, &local_env, &p.ty, *arg_ty)?
            {
                return Err(format!("{} (for parameter '{}' in '{}')", e, p.name, fname));
            }
            local_env.insert(p.name.clone(), arg.clone());
        }
        for stmt in &decl.body.stmts {
            match stmt {
                Stmt::Let { name, init, .. } => {
                    let v = self.eval_comptime_val(mod_path, None, &local_env, init)?;
                    local_env.insert(name.clone(), v);
                }
                Stmt::Return(Some(Expr::TypeVal(TypeExpr::Opaque))) => {
                    let ty_id = self.instantiate_named_opaque(
                        mod_path,
                        fname,
                        &local_env,
                        Some((mod_path.to_string(), fname.to_string(), args.to_vec())),
                        &[],
                    )?;
                    return Ok(ComptimeVal::Type(ty_id));
                }
                Stmt::Return(Some(Expr::TypeVal(TypeExpr::OpaqueDef { methods }))) => {
                    let ty_id = self.instantiate_named_opaque(
                        mod_path,
                        fname,
                        &local_env,
                        Some((mod_path.to_string(), fname.to_string(), args.to_vec())),
                        methods,
                    )?;
                    return Ok(ComptimeVal::Type(ty_id));
                }
                Stmt::Return(Some(Expr::TypeVal(TypeExpr::OpaqueNewtype {
                    underlying,
                    methods,
                }))) => {
                    let ty_id = self.instantiate_opaque_newtype(
                        mod_path,
                        fname,
                        &local_env,
                        Some((mod_path.to_string(), fname.to_string(), args.to_vec())),
                        underlying,
                        methods,
                    )?;
                    return Ok(ComptimeVal::Type(ty_id));
                }
                Stmt::Return(Some(Expr::TypeVal(TypeExpr::Trait(methods)))) => {
                    let ty_id = self.instantiate_trait(
                        mod_path,
                        fname,
                        &local_env,
                        Some((mod_path.to_string(), fname.to_string(), args.to_vec())),
                        methods,
                    )?;
                    return Ok(ComptimeVal::Type(ty_id));
                }
                Stmt::Return(Some(Expr::TypeVal(TypeExpr::Union(variants)))) => {
                    let ty_id = self.instantiate_union(
                        mod_path,
                        fname,
                        &local_env,
                        Some((mod_path.to_string(), fname.to_string(), args.to_vec())),
                        variants,
                    )?;
                    return Ok(ComptimeVal::Type(ty_id));
                }
                Stmt::Return(Some(Expr::TypeVal(TypeExpr::Overlay(fields)))) => {
                    let ty_id = self.instantiate_overlay(
                        mod_path,
                        fname,
                        &local_env,
                        Some((mod_path.to_string(), fname.to_string(), args.to_vec())),
                        fields,
                    )?;
                    return Ok(ComptimeVal::Type(ty_id));
                }
                Stmt::Return(Some(Expr::TypeVal(TypeExpr::Error(items)))) => {
                    let ty_id = self.instantiate_error(
                        mod_path,
                        fname,
                        &local_env,
                        Some((mod_path.to_string(), fname.to_string(), args.to_vec())),
                        items,
                    )?;
                    return Ok(ComptimeVal::Type(ty_id));
                }
                Stmt::Return(Some(Expr::TypeVal(TypeExpr::Record {
                    is_packed,
                    fields,
                    methods,
                }))) => {
                    let ty_id = self.instantiate_composite(
                        mod_path,
                        fname,
                        false,
                        *is_packed,
                        StructOwnership::Copy,
                        false,
                        &local_env,
                        Some((mod_path.to_string(), fname.to_string(), args.to_vec())),
                        fields,
                        &[],
                        &[],
                        methods,
                        None,
                        &[],
                        &[],
                        None,
                    )?;
                    return Ok(ComptimeVal::Type(ty_id));
                }
                Stmt::Return(Some(Expr::TypeVal(TypeExpr::Struct {
                    is_packed,
                    ownership,
                    is_sync,
                    fields,
                    consts,
                    statics,
                    methods,
                    default_hook,
                    clone_hooks,
                    drop_hooks,
                    format_hook,
                }))) => {
                    let ty_id = self.instantiate_composite(
                        mod_path,
                        fname,
                        true,
                        *is_packed,
                        *ownership,
                        *is_sync,
                        &local_env,
                        Some((mod_path.to_string(), fname.to_string(), args.to_vec())),
                        fields,
                        consts,
                        statics,
                        methods,
                        default_hook.clone(),
                        clone_hooks,
                        drop_hooks,
                        format_hook.clone(),
                    )?;
                    return Ok(ComptimeVal::Type(ty_id));
                }
                Stmt::Return(Some(expr)) => {
                    return self.eval_comptime_val(mod_path, None, &local_env, expr);
                }
                Stmt::If {
                    cond,
                    then_block,
                    else_block,
                } => {
                    let ComptimeVal::Bool(b) =
                        self.eval_comptime_val(mod_path, None, &local_env, cond)?
                    else {
                        return Err(format!(
                            "Expected bool condition in comptime 'if' inside '{fname}'"
                        ));
                    };
                    let branch = if b {
                        Some(then_block)
                    } else {
                        else_block.as_ref()
                    };
                    if let Some(blk) = branch {
                        for b_stmt in &blk.stmts {
                            match b_stmt {
                                Stmt::Let { name, init, .. } => {
                                    let v =
                                        self.eval_comptime_val(mod_path, None, &local_env, init)?;
                                    local_env.insert(name.clone(), v);
                                }
                                Stmt::Return(Some(expr)) => {
                                    return self.eval_comptime_val(
                                        mod_path,
                                        None,
                                        &local_env,
                                        expr,
                                    );
                                }
                                Stmt::Expr(expr) => {
                                    return self.eval_comptime_val(
                                        mod_path,
                                        None,
                                        &local_env,
                                        expr,
                                    );
                                }
                                _ => {}
                            }
                        }
                    }
                }
                Stmt::Unsafe(_) => {
                    return Err(format!(
                        "Unsafe blocks are forbidden during compile-time ('comptime') evaluation in '{fname}'"
                    ));
                }
                _ => {
                    return Err(format!(
                        "Unsupported statement in comptime function '{fname}': {stmt:?}"
                    ));
                }
            }
        }
        Err(format!(
            "Comptime function '{fname}' did not return a value"
        ))
    }
}
