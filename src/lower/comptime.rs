use super::*;

/// A method candidate: `(defining module, name, declaration, inferred comptime arguments,
/// specificity)`.
type MethodMatch = (String, String, FuncDecl, HashMap<String, ComptimeVal>, u8);

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
                "Immutable static '{name}' of type '{t_disp}' requires '{t_disp}: sync' because immutable statics may be shared across threads without 'unsafe' (wrap it in an 'opaque(unsafe sync)' type or declare 'static mut {name}' with 'unsafe' access)"
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
            "MIN" => Ok(Some(wide_const_result(min, target_ty))),
            "MAX" => Ok(Some(wide_const_result(max, target_ty))),
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
        if let Some(tc) = self.index_as_type_call(mod_path, env, expr) {
            return self.eval_const_expr_typed(mod_path, self_ty, env, &tc, expected_ty);
        }
        match expr {
            Expr::WideInt(w) => {
                let Some(t) = expected_ty else {
                    return Err(format!(
                        "Integer literal {w} does not fit in the default 'i64'; give it a wide integer type (e.g. 'u256')"
                    ));
                };
                let Some(t) = self.check_int_literal(w, t)? else {
                    return Err(format!(
                        "Integer literal {w} cannot initialize '{}'",
                        self.type_display_name(t)
                    ));
                };
                Ok(wide_const_result(**w, t))
            }
            Expr::IntrinsicLayout { ty, align } => {
                let n = self.eval_layout_intrinsic(mod_path, self_ty, env, ty, *align)?;
                let usize_ty = self.intern_type(Type::Int {
                    signed: false,
                    bits: 64,
                });
                Ok((ConstValue::I64(n), usize_ty, ComptimeVal::Int(n)))
            }
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
                let default_ty = self.intern_type(Type::Int {
                    signed: true,
                    bits: 64,
                });
                let n_wide = Wide::from_i128(*n);
                let ty = match expected_ty {
                    Some(t) => self.check_int_literal(&n_wide, t)?,
                    None => None,
                };
                let ty = match ty {
                    Some(t) => t,
                    None => self.check_int_literal(&n_wide, default_ty)?.unwrap(),
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
                // A negated literal is one literal (`-128` fits `i8` although `128` does not).
                if let Expr::Int(n) = inner.as_ref() {
                    return self.eval_const_expr_typed(
                        mod_path,
                        self_ty,
                        env,
                        &Expr::Int(-n),
                        expected_ty,
                    );
                }
                let (cval, ty, _) =
                    self.eval_const_expr_typed(mod_path, self_ty, env, inner, expected_ty)?;
                match cval {
                    v @ (ConstValue::I64(_) | ConstValue::Wide(_)) => {
                        let neg = const_to_wide(&v).neg();
                        if let Some((signed, bits, _, _)) = self.int_type_reflection(ty)
                            && !neg.fits(bits, signed)
                        {
                            return Err(format!(
                                "Compile-time integer overflow: -({}) does not fit in '{}'",
                                const_to_wide(&v),
                                self.type_display_name(ty)
                            ));
                        }
                        Ok(wide_const_result(neg, ty))
                    }
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
                    v @ (ConstValue::I64(_) | ConstValue::Wide(_)) => {
                        let mut res = const_to_wide(&v).not();
                        if let Some((signed, bits, _, _)) = self.int_type_reflection(ty) {
                            res = res.wrap(bits, signed);
                        }
                        Ok(wide_const_result(res, ty))
                    }
                    _ => Err(format!("Unsupported constant unary '!' on {expr:?}")),
                }
            }
            Expr::Binary { op, lhs, rhs } => {
                self.eval_const_binary(mod_path, self_ty, env, expected_ty, op, lhs, rhs)
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
                self.eval_const_tuple_lit(mod_path, self_ty, env, expr, expected_ty, elems)
            }
            Expr::SimdLit { ty, elems } => {
                let arr_ty = self.resolve_type_expr(mod_path, self_ty, env, ty)?;
                let elem = match self.program.types[arr_ty.0 as usize] {
                    Type::Simd { elem, .. } | Type::Array { elem, .. } => elem,
                    _ => {
                        return Err(format!(
                            "Expected SIMD or Array type in constant literal, got '{}'",
                            self.type_display_name(arr_ty)
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
                self.eval_const_struct_lit(mod_path, self_ty, env, expr, ty, fields)
            }
            Expr::RecordLit(fields) => {
                if let Some(exp) = expected_ty {
                    let mut candidates = vec![exp];
                    if let Some(inner) = self.as_optional_type(exp) {
                        candidates.push(inner);
                    }
                    if let Some(&res) = self.results.get(&exp) {
                        candidates.push(res.ok_ty);
                        if let Some(inner) = self.as_optional_type(res.ok_ty) {
                            candidates.push(inner);
                        }
                    }
                    if let Some(ty) = candidates
                        .into_iter()
                        .find(|t| self.composites.contains_key(t))
                    {
                        return self
                            .eval_const_struct_lit_of(mod_path, self_ty, env, expr, ty, fields);
                    }
                }
                let mut vals = Vec::with_capacity(fields.len());
                let mut field_tys = Vec::with_capacity(fields.len());
                for (name, value) in fields {
                    if field_tys.iter().any(|(n, _): &(String, TypeId)| n == name) {
                        return Err(format!("Duplicate field '{name}' in struct literal"));
                    }
                    let (cv, ty, _) =
                        self.eval_const_expr_typed(mod_path, self_ty, env, value, None)?;
                    vals.push(cv);
                    field_tys.push((name.clone(), ty));
                }
                let ty = self.structural_struct(mod_path, false, field_tys, "struct literal")?;
                Ok((
                    ConstValue::Aggregate(vals),
                    ty,
                    ComptimeVal::ConstExpr(format!("{expr:?}"), expr.clone()),
                ))
            }
            Expr::DotVariant { name, payload } => {
                let Some(exp) = expected_ty else {
                    return Err(format!(
                        "'.{name}' needs a known type; write 'Type::{name}' where none is expected"
                    ));
                };
                let mut candidates = vec![exp];
                if let Some(inner) = self.as_optional_type(exp) {
                    candidates.push(inner);
                }
                if let Some(&res) = self.results.get(&exp) {
                    candidates.push(res.ok_ty);
                    if let Some(inner) = self.as_optional_type(res.ok_ty) {
                        candidates.push(inner);
                    }
                    candidates.push(res.err_ty);
                }
                for ty in candidates {
                    if let Some((_, variants)) = self.enums.get(&ty)
                        && let Some(&(_, value)) = variants.iter().find(|(vn, _)| vn == name)
                    {
                        if payload.is_some() {
                            return Err(format!("Enum variant '.{name}' takes no payload"));
                        }
                        return Ok((ConstValue::I64(value), ty, ComptimeVal::Int(value)));
                    }
                }
                Err(format!(
                    "'.{name}' is not a constant enum variant of '{}'",
                    self.type_display_name(exp)
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
            Expr::Match { scrutinee, arms } => {
                self.eval_const_match(mod_path, self_ty, env, scrutinee, arms, expected_ty)
            }
            Expr::MapLit(pairs) => {
                self.eval_map_lit(mod_path, self_ty, env, pairs, expected_ty)
            }
            Expr::IntrinsicMap {
                key_ty,
                val_ty,
                entries,
            } => self.eval_synthesized_map(mod_path, self_ty, env, key_ty, val_ty, entries),
            Expr::IntrinsicInvert(inner) => self.eval_map_invert(mod_path, self_ty, env, inner),
            Expr::IntrinsicDeclarations(inner) => {
                self.eval_module_declarations(mod_path, self_ty, env, inner)
            }
            Expr::IntrinsicTypeName(ty) => {
                self.eval_type_name_intrinsic(mod_path, self_ty, env, ty)
            }
            Expr::IntrinsicSatisfies { ty, bound } => {
                let b = self.eval_satisfies_intrinsic(mod_path, self_ty, env, ty, bound)?;
                let bool_ty = self.intern_type(Type::Bool);
                Ok((ConstValue::Bool(b), bool_ty, ComptimeVal::Bool(b)))
            }
            Expr::IntrinsicHasField { ty, name } => {
                let b = self.eval_has_field_intrinsic(mod_path, self_ty, env, ty, name)?;
                let bool_ty = self.intern_type(Type::Bool);
                Ok((ConstValue::Bool(b), bool_ty, ComptimeVal::Bool(b)))
            }
            Expr::IntrinsicHasMethod { ty, name } => {
                let b = self.eval_has_method_intrinsic(mod_path, self_ty, env, ty, name)?;
                let bool_ty = self.intern_type(Type::Bool);
                Ok((ConstValue::Bool(b), bool_ty, ComptimeVal::Bool(b)))
            }
            Expr::IntrinsicVariants(ty) => {
                self.eval_variants_const(mod_path, self_ty, env, ty)
            }
            Expr::IntrinsicEntries(inner) => {
                self.eval_entries_const(mod_path, self_ty, env, inner)
            }
            Expr::IntrinsicField { base, field } => {
                let fval = self.eval_comptime_val(mod_path, self_ty, env, field)?;
                let resolved = self.field_access_expr(base, &fval)?;
                self.eval_const_expr_typed(mod_path, self_ty, env, &resolved, expected_ty)
            }
            Expr::TupleIndex { base, index } => {
                if let Ok((ConstValue::Aggregate(vals), base_ty, _)) =
                    self.eval_const_expr_typed(mod_path, self_ty, env, base, None)
                    && let Type::Struct(ftys) = &self.program.types[base_ty.0 as usize]
                    && let Some(elem_cv) = vals.get(*index as usize).cloned()
                    && let Some(&elem_ty) = ftys.get(*index as usize)
                {
                    let ct_val = Self::const_value_to_comptime(&elem_cv, expr);
                    return Ok((elem_cv, elem_ty, ct_val));
                }
                let key = expr as *const Expr as usize;
                if self.const_eval_fallback.contains(&key) {
                    return Err(format!(
                        "Expression {expr:?} cannot be evaluated at compile time"
                    ));
                }
                self.const_eval_fallback.push(key);
                let res = self.eval_comptime_val(mod_path, self_ty, env, expr);
                self.const_eval_fallback.pop();
                let ct_val = res?;
                self.comptime_val_to_const_result(&ct_val, expected_ty)
            }
            Expr::Index { base, index } => {
                self.eval_const_index(mod_path, self_ty, env, expr, expected_ty, base, index)
            }
            Expr::MethodCall {
                receiver,
                method,
                ct_args: None,
                args,
                ..
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
                self.eval_const_field(mod_path, self_ty, env, expr, expected_ty, base, field)
            }
            Expr::Path(p) => {
                self.eval_const_path(mod_path, self_ty, env, expected_ty, p)
            }
            _ => {
                // `eval_comptime_val` falls back to this function for expressions it does not
                // handle itself; refuse to re-enter for the same expression instead of recursing
                // until the stack overflows.
                let key = expr as *const Expr as usize;
                if self.const_eval_fallback.contains(&key) {
                    return Err(format!(
                        "Expression {expr:?} cannot be evaluated at compile time"
                    ));
                }
                self.const_eval_fallback.push(key);
                let res = self.eval_comptime_val(mod_path, self_ty, env, expr);
                self.const_eval_fallback.pop();
                let ct_val = res?;
                if let ComptimeVal::ConstExpr(_, ref ce) = ct_val
                    && ce != expr
                {
                    return self.eval_const_expr_typed(mod_path, self_ty, env, ce, expected_ty);
                }
                self.comptime_val_to_const_result(&ct_val, expected_ty)
            }
        }
    }

    /// Folds a binary operator in a constant expression with the runtime semantics of its type.
    #[allow(clippy::too_many_arguments)]
    fn eval_const_binary(
        &mut self,
        mod_path: &str,
        self_ty: Option<TypeId>,
        env: &HashMap<String, ComptimeVal>,
        expected_ty: Option<TypeId>,
        op: &BinOp,
        lhs: &Expr,
        rhs: &Expr,
    ) -> Result<(ConstValue, TypeId, ComptimeVal), String> {
        let (l_val, l_ty, l_ct) =
            self.eval_const_expr_typed(mod_path, self_ty, env, lhs, expected_ty)?;
        let (r_val, _, r_ct) =
            self.eval_const_expr_typed(mod_path, self_ty, env, rhs, Some(l_ty))?;
        match (l_val, r_val) {
            (
                l @ (ConstValue::I64(_) | ConstValue::Wide(_)),
                r @ (ConstValue::I64(_) | ConstValue::Wide(_)),
            ) => {
                let (l, r) = (const_to_wide(&l), const_to_wide(&r));
                if let Some(b) = match op {
                    BinOp::Eq => Some(l == r),
                    BinOp::Ne => Some(l != r),
                    BinOp::Lt => Some(l < r),
                    BinOp::Le => Some(l <= r),
                    BinOp::Gt => Some(l > r),
                    BinOp::Ge => Some(l >= r),
                    _ => None,
                } {
                    let bool_ty = self.intern_type(Type::Bool);
                    return Ok((ConstValue::Bool(b), bool_ty, ComptimeVal::Bool(b)));
                }
                let res = self.fold_int_binop(*op, &l, &r, l_ty)?;
                Ok(wide_const_result(res, l_ty))
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

    /// Evaluates a tuple or array literal in a constant expression.
    fn eval_const_tuple_lit(
        &mut self,
        mod_path: &str,
        self_ty: Option<TypeId>,
        env: &HashMap<String, ComptimeVal>,
        expr: &Expr,
        expected_ty: Option<TypeId>,
        elems: &[Expr],
    ) -> Result<(ConstValue, TypeId, ComptimeVal), String> {
        if elems.is_empty()
            && let Some(exp) = expected_ty
        {
            let mut candidates = vec![exp];
            if let Some(inner) = self.as_optional_type(exp) {
                candidates.push(inner);
            }
            if let Some(&res) = self.results.get(&exp) {
                candidates.push(res.ok_ty);
                if let Some(inner) = self.as_optional_type(res.ok_ty) {
                    candidates.push(inner);
                }
            }
            if let Some(ty) = candidates
                .into_iter()
                .find(|t| self.composites.contains_key(t))
            {
                return self.eval_const_struct_lit_of(mod_path, self_ty, env, expr, ty, &[]);
            }
        }
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

    /// Evaluates a struct literal in a constant expression (packed structs fold to their backing integer).
    fn eval_const_struct_lit(
        &mut self,
        mod_path: &str,
        self_ty: Option<TypeId>,
        env: &HashMap<String, ComptimeVal>,
        expr: &Expr,
        ty: &TypeExpr,
        fields: &[(String, Expr)],
    ) -> Result<(ConstValue, TypeId, ComptimeVal), String> {
        let comp_ty = self.resolve_type_expr(mod_path, self_ty, env, ty)?;
        self.eval_const_struct_lit_of(mod_path, self_ty, env, expr, comp_ty, fields)
    }

    /// A constant struct literal of type `comp_ty`.
    fn eval_const_struct_lit_of(
        &mut self,
        mod_path: &str,
        self_ty: Option<TypeId>,
        env: &HashMap<String, ComptimeVal>,
        expr: &Expr,
        comp_ty: TypeId,
        fields: &[(String, Expr)],
    ) -> Result<(ConstValue, TypeId, ComptimeVal), String> {
        let Some(comp) = self.composites.get(&comp_ty).cloned() else {
            return Err(format!(
                "Cannot construct non-struct/opaque type '{}' in constant initializer",
                self.type_display_name(comp_ty)
            ));
        };
        super::expr::check_literal_fields(&comp.name, &comp.fields, fields)?;
        if comp.is_opaque && comp.fields.is_empty() && self_ty != Some(comp_ty) {
            return Err(format!(
                "Cannot construct opaque type '{}' outside its 'opaque {{ ... }}' block",
                comp.name
            ));
        }
        for (f_name, _, f_vis, _) in &comp.fields {
            if comp.is_opaque && *f_vis == Visibility::Private && self_ty != Some(comp_ty) {
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

    /// Evaluates `base[index]` in a constant expression.
    #[allow(clippy::too_many_arguments)]
    fn eval_const_index(
        &mut self,
        mod_path: &str,
        self_ty: Option<TypeId>,
        env: &HashMap<String, ComptimeVal>,
        expr: &Expr,
        expected_ty: Option<TypeId>,
        base: &Expr,
        index: &Expr,
    ) -> Result<(ConstValue, TypeId, ComptimeVal), String> {
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
        if let Ok(ComptimeVal::List(items, elem_ty_opt)) =
            self.eval_comptime_val(mod_path, self_ty, env, base)
        {
            let idx_val = self.eval_comptime_int(mod_path, self_ty, env, index)?;
            if idx_val < 0 || (idx_val as usize) >= items.len() {
                return Err(format!(
                    "Comptime index {} out of bounds (len {})",
                    idx_val,
                    items.len()
                ));
            }
            let elem = &items[idx_val as usize];
            return self.comptime_val_to_const_result(elem, elem_ty_opt.or(expected_ty));
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

    /// Evaluates `base.field` in a constant expression: type reflection, `.len`, and fields of constant aggregates.
    #[allow(clippy::too_many_arguments)]
    fn eval_const_field(
        &mut self,
        mod_path: &str,
        self_ty: Option<TypeId>,
        env: &HashMap<String, ComptimeVal>,
        expr: &Expr,
        expected_ty: Option<TypeId>,
        base: &Expr,
        field: &str,
    ) -> Result<(ConstValue, TypeId, ComptimeVal), String> {
        if let Some(res) =
            self.eval_int_reflection_field(mod_path, self_ty, env, base, field)?
        {
            return Ok(res);
        }
        if let Ok(Some(map_id)) = self.resolve_map_expr(mod_path, self_ty, env, base) {
            match field {
                "len" => {
                    let usize_ty = self.intern_type(Type::Int {
                        signed: false,
                        bits: 64,
                    });
                    let len = self.map_instances[map_id as usize].entries.len() as i128;
                    return Ok((ConstValue::I64(len), usize_ty, ComptimeVal::Int(len)));
                }
                "keys" => return self.eval_map_keys_const(map_id),
                "values" => return self.eval_map_values_const(map_id),
                _ => {}
            }
        }
        if let Ok(ComptimeVal::Record(entries)) =
            self.eval_comptime_val(mod_path, self_ty, env, base)
            && let Some((_, fval)) = entries.iter().find(|(k, _)| k == field)
        {
            let fval = fval.clone();
            let ty_hint = entries
                .iter()
                .find_map(|(k, v)| {
                    if k == &format!("__ty:{field}")
                        && let ComptimeVal::Type(t) = v
                    {
                        Some(*t)
                    } else {
                        None
                    }
                })
                .or(expected_ty);
            return self.comptime_val_to_const_result(&fval, ty_hint);
        }
        if field == "len"
            && let Ok(ComptimeVal::List(items, _)) =
                self.eval_comptime_val(mod_path, self_ty, env, base)
        {
            let usize_ty = self.intern_type(Type::Int {
                signed: false,
                bits: 64,
            });
            let len = items.len() as i128;
            return Ok((ConstValue::I64(len), usize_ty, ComptimeVal::Int(len)));
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
        let key = expr as *const Expr as usize;
        if self.const_eval_fallback.contains(&key) {
            return Err(format!(
                "Expression {expr:?} cannot be evaluated at compile time"
            ));
        }
        self.const_eval_fallback.push(key);
        let res = self.eval_comptime_val(mod_path, self_ty, env, expr);
        self.const_eval_fallback.pop();
        let ct_val = res?;
        self.comptime_val_to_const_result(&ct_val, expected_ty)
    }

    fn eval_const_match(
        &mut self,
        mod_path: &str,
        self_ty: Option<TypeId>,
        env: &HashMap<String, ComptimeVal>,
        scrutinee: &Expr,
        arms: &[(MatchPat, Expr)],
        expected_ty: Option<TypeId>,
    ) -> Result<(ConstValue, TypeId, ComptimeVal), String> {
        let (scrut_cv, scrut_ty, scrut_ct) =
            self.eval_const_expr_typed(mod_path, self_ty, env, scrutinee, None)?;
        for (pat, body) in arms {
            let mut arm_env = env.clone();
            if self.match_const_pat(
                mod_path,
                self_ty,
                env,
                &scrut_cv,
                scrut_ty,
                &scrut_ct,
                pat,
                &mut arm_env,
            )? {
                let arm_expr = match body {
                    Expr::Block(blk) => match blk.stmts.last() {
                        Some(Stmt::Expr(tail) | Stmt::Return(Some(tail))) => tail,
                        _ => {
                            return Err(
                                "Constant 'match' arm block must end with a value expression"
                                    .to_string(),
                            );
                        }
                    },
                    other => other,
                };
                return self.eval_const_expr_typed(
                    mod_path,
                    self_ty,
                    &arm_env,
                    arm_expr,
                    expected_ty,
                );
            }
        }
        Err("Non-exhaustive or unmatched constant 'match' expression".to_string())
    }

    #[allow(clippy::too_many_arguments)]
    fn match_const_pat(
        &mut self,
        mod_path: &str,
        self_ty: Option<TypeId>,
        env: &HashMap<String, ComptimeVal>,
        cval: &ConstValue,
        ty: TypeId,
        ct_val: &ComptimeVal,
        pat: &MatchPat,
        arm_env: &mut HashMap<String, ComptimeVal>,
    ) -> Result<bool, String> {
        match pat {
            MatchPat::Wildcard => Ok(true),
            MatchPat::CatchAllBind {
                mode: BindMode::Default,
                name,
            } if matches!(
                self.resolve_path(mod_path, std::slice::from_ref(name)),
                Ok(ResolvedItem::Const(..))
            ) =>
            {
                let (p_cv, _, _) = self.eval_const_path(
                    mod_path,
                    self_ty,
                    env,
                    Some(ty),
                    std::slice::from_ref(name),
                )?;
                Ok(&p_cv == cval)
            }
            MatchPat::CatchAllBind { name, .. } => {
                if name != "_" {
                    arm_env.insert(name.clone(), ct_val.clone());
                    arm_env.insert(format!("__var_ty:{name}"), ComptimeVal::Type(ty));
                }
                Ok(true)
            }
            MatchPat::Or(alts) => {
                for a in alts {
                    let mut sub_env = arm_env.clone();
                    if self.match_const_pat(
                        mod_path,
                        self_ty,
                        env,
                        cval,
                        ty,
                        ct_val,
                        a,
                        &mut sub_env,
                    )? {
                        *arm_env = sub_env;
                        return Ok(true);
                    }
                }
                Ok(false)
            }
            MatchPat::Null => Ok(matches!(cval, ConstValue::Void)),
            MatchPat::Bool(b) => Ok(matches!(cval, ConstValue::Bool(v) if v == b)),
            MatchPat::Rune(ch) => {
                Ok(matches!(cval, ConstValue::I64(n) if *n == i128::from(u32::from(*ch))))
            }
            MatchPat::Int(n) => match cval {
                ConstValue::I64(v) => Ok(*v == *n),
                ConstValue::Wide(w) => Ok(**w == crate::wide::Wide::from_i128(*n)),
                ConstValue::F64(bits) => Ok(f64::from_bits(*bits) == (*n as f64)),
                _ => Ok(false),
            },
            MatchPat::WideInt(w) => Ok(const_to_wide(cval) == **w),
            MatchPat::Float(bits) => {
                Ok(matches!(cval, ConstValue::F64(v) if f64::from_bits(*v) == f64::from_bits(*bits)))
            }
            MatchPat::Str(s) => match (cval, ct_val) {
                (_, ComptimeVal::Str(v)) => Ok(v == s),
                (ConstValue::Aggregate(items), _) => {
                    Ok(matches!(items.first(), Some(ConstValue::Str(v)) if v == s))
                }
                _ => Ok(false),
            },
            MatchPat::Range { lo, hi } => {
                let eval_b = |s: &mut Self, p: &MatchPat| -> Result<crate::wide::Wide, String> {
                    match p {
                        MatchPat::Int(n) => Ok(crate::wide::Wide::from_i128(*n)),
                        MatchPat::WideInt(w) => Ok(**w),
                        MatchPat::Rune(ch) => Ok(crate::wide::Wide::from_i128(i128::from(u32::from(*ch)))),
                        MatchPat::CatchAllBind { name, .. } => {
                            let (cv, _, _) = s.eval_const_path(
                                mod_path,
                                self_ty,
                                env,
                                Some(ty),
                                std::slice::from_ref(name),
                            )?;
                            Ok(const_to_wide(&cv))
                        }
                        MatchPat::Variant { path, payload: None } => {
                            let (cv, _, _) = s.eval_const_path(mod_path, self_ty, env, Some(ty), path)?;
                            Ok(const_to_wide(&cv))
                        }
                        _ => Err("Invalid range bound in constant match".to_string()),
                    }
                };
                let lo_w = eval_b(self, lo)?;
                let hi_w = eval_b(self, hi)?;
                let v_w = const_to_wide(cval);
                Ok(v_w >= lo_w && v_w <= hi_w)
            }
            MatchPat::DotVariant { name, payload: None } => {
                if let Some((_, vs)) = self.enums.get(&ty)
                    && let Some((_, val)) = vs.iter().find(|(vn, _)| vn == name)
                {
                    return Ok(matches!(cval, ConstValue::I64(n) if *n == *val));
                }
                if name == "None" {
                    return Ok(matches!(cval, ConstValue::Void));
                }
                Ok(false)
            }
            MatchPat::Variant { path, payload: None } => {
                if let Some((_, vs)) = self.enums.get(&ty) {
                    let vn = path.last().unwrap();
                    if let Some((_, val)) = vs.iter().find(|(n, _)| n == vn) {
                        return Ok(matches!(cval, ConstValue::I64(n) if *n == *val));
                    }
                }
                let (p_cv, _, _) = self.eval_const_path(mod_path, self_ty, env, Some(ty), path)?;
                Ok(&p_cv == cval)
            }
            MatchPat::Struct { fields, .. } => {
                let Some(comp) = self.composites.get(&ty).cloned() else {
                    return Ok(false);
                };
                let ConstValue::Aggregate(vals) = cval else {
                    return Ok(false);
                };
                for (fname, fpat) in fields {
                    let Some((f_idx, (_, f_ty, _, _))) = comp
                        .fields
                        .iter()
                        .enumerate()
                        .find(|(_, (n, _, _, _))| n == fname)
                    else {
                        return Err(format!("Struct '{}' has no field '{fname}'", comp.name));
                    };
                    let f_cv = &vals[f_idx];
                    let f_ct = Self::const_value_to_comptime(f_cv, &Expr::Null);
                    if !self.match_const_pat(
                        mod_path, self_ty, env, f_cv, *f_ty, &f_ct, fpat, arm_env,
                    )? {
                        return Ok(false);
                    }
                }
                Ok(true)
            }
            MatchPat::Seq {
                bracketed: false, ..
            } if self.composites.contains_key(&ty) => {
                if let Some((fields, rest_b)) =
                    super::FuncLowerer::seq_to_shorthand_struct_pat(pat)
                {
                    let s_pat = MatchPat::Struct {
                        path: None,
                        fields,
                        rest: rest_b,
                    };
                    return self.match_const_pat(
                        mod_path, self_ty, env, cval, ty, ct_val, &s_pat, arm_env,
                    );
                }
                Ok(false)
            }
            MatchPat::Seq { elems, rest, .. } => {
                let ConstValue::Aggregate(vals) = cval else {
                    return Ok(false);
                };
                let elem_tys: Vec<TypeId> = match &self.program.types[ty.0 as usize] {
                    Type::Struct(ts) => ts.clone(),
                    Type::Array { elem, len } => vec![*elem; *len as usize],
                    _ => return Ok(false),
                };
                let n = vals.len();
                let split = match rest {
                    None => {
                        if elems.len() != n {
                            return Ok(false);
                        }
                        elems.len()
                    }
                    Some(s) => {
                        if elems.len() > n {
                            return Ok(false);
                        }
                        *s
                    }
                };
                let suffix_count = elems.len() - split;
                for (i, ep) in elems[..split].iter().enumerate() {
                    let e_cv = &vals[i];
                    let e_ty = elem_tys[i];
                    let e_ct = Self::const_value_to_comptime(e_cv, &Expr::Null);
                    if !self.match_const_pat(
                        mod_path, self_ty, env, e_cv, e_ty, &e_ct, ep, arm_env,
                    )? {
                        return Ok(false);
                    }
                }
                for (k, ep) in elems[split..].iter().enumerate() {
                    let idx = n - suffix_count + k;
                    let e_cv = &vals[idx];
                    let e_ty = elem_tys[idx];
                    let e_ct = Self::const_value_to_comptime(e_cv, &Expr::Null);
                    if !self.match_const_pat(
                        mod_path, self_ty, env, e_cv, e_ty, &e_ct, ep, arm_env,
                    )? {
                        return Ok(false);
                    }
                }
                Ok(true)
            }
            _ => Ok(false),
        }
    }

    /// Evaluates a path in a constant expression: a `comptime` binding, a constant or static, an enum or error variant, or an associated constant.
    pub(super) fn eval_const_path(
        &mut self,
        mod_path: &str,
        self_ty: Option<TypeId>,
        env: &HashMap<String, ComptimeVal>,
        expected_ty: Option<TypeId>,
        p: &[String],
    ) -> Result<(ConstValue, TypeId, ComptimeVal), String> {
        if p.len() == 1 {
            if let Some(ct_val) = env.get(&p[0]).cloned() {
                let ty_hint = env
                    .get(&format!("__var_ty:{}", p[0]))
                    .and_then(|v| match v {
                        ComptimeVal::Type(t) => Some(*t),
                        _ => None,
                    })
                    .or(expected_ty);
                if let ComptimeVal::ConstExpr(_, ref ce) = ct_val {
                    return self.eval_const_expr_typed(
                        mod_path, self_ty, env, ce, ty_hint,
                    );
                }
                return self.comptime_val_to_const_result(&ct_val, ty_hint);
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
                self.resolve_type_path(mod_path, self_ty, env, prefix).ok()
            };
            if let Some(owner_ty) = owner_opt {
                if let Some(comp) = self.composites.get(&owner_ty)
                    && comp.consts.contains_key(item_name)
                {
                    let (cval, cty, ct_val, cvis, has_explicit_ty) =
                        self.resolve_associated_const(owner_ty, item_name)?;
                    let comp = &self.composites[&owner_ty];
                    if comp.is_opaque
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
                if let Some(res) = self.impl_assoc_const(owner_ty, item_name)? {
                    return Ok(res);
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
        if sdecl.thread_local {
            self.program.thread_local_globals.push(gl_id);
        }
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
            return Err(format!(
                "Type '{}' has no associated constants",
                self.type_display_name(owner_ty)
            ));
        };
        let Some((vis, cdecl)) = comp.consts.get(name).cloned() else {
            return Err(format!(
                "Type '{}' has no associated constant '{}'",
                comp.name, name
            ));
        };
        let has_explicit_ty = cdecl.ty.is_some();
        let what = format!("'{}'", comp.name);
        let (cval, final_ty, ct_val) =
            self.eval_field(&comp.def_module, Some(owner_ty), &comp.comptime_env, &cdecl, &what)?;
        let res = (cval, final_ty, ct_val, vis, has_explicit_ty);
        self.associated_consts.insert(key, res.clone());
        Ok(res)
    }

    /// Whether a compile-time field's declared type is a bound on a type rather than its type
    /// (`copy`, `Hash + Eq`, a trait), so that its value is a type to check against it.
    pub(super) fn is_bound_expr(
        &mut self,
        mod_path: &str,
        env: &HashMap<String, ComptimeVal>,
        te: &TypeExpr,
    ) -> bool {
        match te {
            TypeExpr::Constraint(_) | TypeExpr::TraitBounds(_) => true,
            TypeExpr::Named(_) | TypeExpr::TypeCall { .. } => self
                .resolve_type_expr(mod_path, None, env, te)
                .is_ok_and(|t| self.traits.contains_key(&t)),
            _ => false,
        }
    }

    /// The value of compile-time field `c` (of `what`, for errors), checked against its bound when
    /// its declared type is one: `const Handle: copy = String;` is refused where it is written.
    pub(super) fn eval_field(
        &mut self,
        mod_path: &str,
        self_ty: Option<TypeId>,
        env: &HashMap<String, ComptimeVal>,
        c: &ConstDecl,
        what: &str,
    ) -> Result<(ConstValue, TypeId, ComptimeVal), String> {
        if let Some(te) = &c.ty
            && self.is_bound_expr(mod_path, env, te)
        {
            let ComptimeVal::Type(t) = self.eval_comptime_val(mod_path, self_ty, env, &c.init)? else {
                return Err(format!(
                    "'const {}' in {what} is bounded as a type, but its value is not a type",
                    c.name
                ));
            };
            if let Some(Err(e)) = self.eval_comptime_type_bound(mod_path, self_ty, env, te, t)? {
                return Err(format!(
                    "'const {}: ... = {}' in {what} does not meet its bound: {e}",
                    c.name,
                    self.type_display_name(t)
                ));
            }
            let meta = self.intern_type(Type::MetaType);
            return Ok((ConstValue::Type(t), meta, ComptimeVal::Type(t)));
        }
        let expected = match &c.ty {
            Some(te) => Some(self.resolve_type_expr(mod_path, self_ty, env, te)?),
            None => None,
        };
        let (cval, ty, ct) = self.eval_const_expr_typed(mod_path, self_ty, env, &c.init, expected)?;
        Ok((cval, expected.unwrap_or(ty), ct))
    }

    /// An associated item `owner_ty` gets from an impl (`const Handle: copy = *own u8;` in `impl[A:
    /// Allocator + copy] Storage for A`), evaluated where the impl is, or none.
    pub(super) fn impl_assoc_const(
        &mut self,
        owner_ty: TypeId,
        name: &str,
    ) -> Result<Option<(ConstValue, TypeId, ComptimeVal)>, String> {
        // Cached apart from the type's own constants, which may share the name.
        let key = (owner_ty, format!("impl {name}"));
        if let Some((cval, ty, ct, ..)) = self.associated_consts.get(&key).cloned() {
            return Ok(Some((cval, ty, ct)));
        }
        for (_, imp) in self.collect_trait_impls(owner_ty, None)? {
            let Some(c) = imp.consts.iter().find(|c| c.name == name).cloned() else {
                continue;
            };
            let (cval, ty, ct) = self.eval_field(&imp.def_module, Some(owner_ty), &imp.env, &c, &imp.origin)?;
            self.associated_consts
                .insert(key, (cval.clone(), ty, ct.clone(), Visibility::Pub, true));
            return Ok(Some((cval, ty, ct)));
        }
        Ok(None)
    }

    /// That `ty` gives each associated item `trait_ty` asks for, meeting its bound.
    pub(super) fn check_assoc_items(&mut self, ty: TypeId, trait_ty: TypeId) -> Result<(), String> {
        let info = self.traits[&trait_ty].clone();
        let shown = self.type_display_name(ty);
        for item in &info.assoc {
            let own = self.composites.get(&ty).and_then(|c| c.consts.get(&item.name)).map(|(v, _)| *v);
            let val = if matches!(own, Some(Visibility::Pub)) {
                self.resolve_associated_const(ty, &item.name)?.2
            } else if let Some((_, _, v)) = self.impl_assoc_const(ty, &item.name)? {
                v
            } else if own.is_some() {
                // Generic code elsewhere reads it through the trait, so it must be public.
                return Err(format!(
                    "Type '{shown}' gives 'const {}' for trait '{}', but privately; write 'pub const {}'",
                    item.name, info.name, item.name
                ));
            } else {
                return Err(format!(
                    "Type '{shown}' gives no 'const {}', which trait '{}' asks of each implementation",
                    item.name, info.name
                ));
            };
            if let ComptimeVal::Type(t) = val
                && let Some(Err(e)) =
                    self.eval_comptime_type_bound(&info.def_module, None, &info.comptime_env, &item.bound, t)?
            {
                return Err(format!(
                    "'{shown}::{}' does not meet its bound in trait '{}': {e}",
                    item.name, info.name
                ));
            }
        }
        Ok(())
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
            return Err(format!(
                "Type '{}' has no associated statics",
                self.type_display_name(owner_ty)
            ));
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

    /// `eval_comptime_type_bound` for a comptime parameter's bound, which a linear type meets
    /// only when it says so: `?linear` (or `linear`, or `unchecked`). A generic that does not say
    /// so may drop what it is given. An unsized type, likewise, needs `?sized` (or `unchecked`):
    /// one that does not say so may hold a `T` by value or take its size.
    pub(super) fn eval_param_bound(
        &mut self,
        bound_mod: &str,
        self_ty: Option<TypeId>,
        env: &HashMap<String, ComptimeVal>,
        bound_expr: &TypeExpr,
        actual_ty: TypeId,
    ) -> Result<Option<Result<u8, String>>, String> {
        if self.is_linear_type(actual_ty) && !admits_linear(bound_expr) && !self.traits.contains_key(&actual_ty) {
            return Ok(Some(Err(format!(
                "Type '{}' is linear, and a type parameter takes linear types only when its bound says '?linear' ('[T: ?linear]'), as it may otherwise drop them",
                self.type_display_name(actual_ty)
            ))));
        }
        if self.is_opaque_type(actual_ty) && !admits_unsized(bound_expr) {
            return Ok(Some(Err(format!(
                "Type '{}' is unsized, and a type parameter takes unsized types only when its bound says '?sized' ('[T: ?sized]'), as it may otherwise hold one by value or take its size",
                self.type_display_name(actual_ty)
            ))));
        }
        self.eval_comptime_type_bound(bound_mod, self_ty, env, bound_expr, actual_ty)
    }

    pub(super) fn eval_comptime_type_bound(
        &mut self,
        bound_mod: &str,
        self_ty: Option<TypeId>,
        env: &HashMap<String, ComptimeVal>,
        bound_expr: &TypeExpr,
        actual_ty: TypeId,
    ) -> Result<Option<Result<u8, String>>, String> {
        if let Some(tr) = self.traits.get(&actual_ty) {
            // Traits are a distinct comptime kind: they may only appear as bounds and in
            // `&Trait` / `-> opaque Trait`, never where a `type` is expected.
            return Ok(Some(Err(format!(
                "Trait '{}' is not a type and cannot be passed where a 'type' is expected",
                tr.name
            ))));
        }
        match bound_expr {
            TypeExpr::MetaType => Ok(Some(Ok(1))),
            TypeExpr::BareOpaque => {
                let c = TypeConstraint::Opaque;
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
            TypeExpr::CallableSig { params, ret } => {
                let sig = self.callable_sig_type(bound_mod, self_ty, env, params, ret)?;
                if self.callable_as(actual_ty, sig) {
                    Ok(Some(Ok(3)))
                } else {
                    Ok(Some(Err(format!(
                        "Type '{}' cannot be called as '{}'",
                        self.type_display_name(actual_ty),
                        self.type_display_name(sig)
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
            TypeExpr::Trait(..) | TypeExpr::Named(_) | TypeExpr::TypeCall { .. } => {
                let Ok(bound_ty_id) = self.resolve_type_expr(bound_mod, self_ty, env, bound_expr)
                else {
                    return Ok(None);
                };
                if self.traits.contains_key(&bound_ty_id) {
                    let method_count = self.traits[&bound_ty_id].methods.len();
                    // A nominal trait with no methods (a marker) is still met only by an impl.
                    if method_count == 0
                        && self.traits[&bound_ty_id].kind != TraitKind::Structural
                        && let Err(e) = self.find_trait_impl(actual_ty, bound_ty_id)
                    {
                        return Ok(Some(Err(e)));
                    }
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
                    if let Err(e) = self.check_assoc_items(actual_ty, bound_ty_id) {
                        return Ok(Some(Err(e)));
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
    /// - `20`: Concrete type match (`Point`, `i32`, `Pair[i32]`)
    /// - `11..=16`: Parameterized structural or type-constructor match (`simd[T; N]`, `[T; N]`, `?T`, `Pair[T]`),
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
                let spec = match self.eval_param_bound(
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
                // A value that is not optional is given to `?T` as a `T` (`&t` for `?&T`).
                if self.as_optional_type(actual_ty).is_none() {
                    return self.unify_type_pattern(fn_mod, comptime_params, inner, actual_ty, inferred);
                }
                let Type::Union { variants, .. } = self.program.types[actual_ty.0 as usize].clone()
                else {
                    return Ok(None);
                };
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
            TypeExpr::FnPtr { params, ret, .. } => {
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
                            && m_args.len() >= args.len()
                    })
                    .map(|((_, _, m_args), _)| m_args.clone());
                let Some(m_args) = memo_match else {
                    return Ok(None);
                };
                // `Vec[T]` means `Vec[T, Global]`: what the pattern leaves out takes its default.
                if m_args.len() > args.len() {
                    let given: Vec<Option<ComptimeVal>> = m_args[..args.len()]
                        .iter()
                        .cloned()
                        .map(Some)
                        .chain(std::iter::repeat_n(None, m_args.len() - args.len()))
                        .collect();
                    if self.complete_comptime_args_of(&target_mod, &target_fn, &given)? != m_args {
                        return Ok(None);
                    }
                }
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
                    match self.eval_param_bound(
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
                // A one-argument type call inside another's arguments (the `N[T]` of
                // `Box[N[T]]`) parses as an index expression.
                if let (Expr::Index { base, index }, ComptimeVal::Type(act_ty)) = (expr, actual)
                    && let Expr::Path(path) = base.as_ref()
                {
                    let call = TypeExpr::TypeCall { path: path.clone(), args: vec![(**index).clone()] };
                    if let Some(s) =
                        self.unify_type_pattern(fn_mod, comptime_params, &call, *act_ty, inferred)?
                    {
                        return Ok(Some(s));
                    }
                }
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
        // Also check the defining module of a user-defined `comp_ty` (composite or distinct type)
        // and no candidates were found in `cur_mod` (e.g. inside a generic function).
        if candidates.is_empty() {
            let def_mod_opt = self
                .composites
                .get(&comp_ty)
                .map(|c| c.def_module.clone())
                .or_else(|| {
                    self.distinct_types
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

        let mut matched: Vec<MethodMatch> = Vec::new();

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

        let cands: Vec<(String, FuncDecl, HashMap<String, ComptimeVal>, u32)> = matched
            .iter()
            .map(|(m, _, d, e, s)| (m.clone(), d.clone(), e.clone(), u32::from(*s)))
            .collect();
        let idx = self.most_specific_overload(method_name, &cands).map_err(|e| {
            format!(
                "Ambiguous extension method '{method_name}' for type '{type_display}': {}",
                e.trim_start_matches(&format!("Ambiguous call to overloaded '{method_name}': "))
            )
        })?;
        let (fn_mod, orig_name, decl, inferred, _) = matched.into_iter().nth(idx).unwrap();
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

    pub(super) fn comptime_val_to_const_result(
        &mut self,
        ct_val: &ComptimeVal,
        expected_ty: Option<TypeId>,
    ) -> Result<(ConstValue, TypeId, ComptimeVal), String> {
        match ct_val {
            ComptimeVal::Null => {
                let Some(exp) = expected_ty else {
                    return Err("'null' requires an explicit optional type context".to_string());
                };
                Ok((ConstValue::Void, exp, ComptimeVal::Null))
            }
            ComptimeVal::Int(n) => {
                let ty = expected_ty.unwrap_or_else(|| {
                    self.intern_type(Type::Int {
                        signed: true,
                        bits: 64,
                    })
                });
                Ok((ConstValue::I64(*n), ty, ComptimeVal::Int(*n)))
            }
            ComptimeVal::Bool(b) => {
                let ty = self.intern_type(Type::Bool);
                Ok((ConstValue::Bool(*b), ty, ComptimeVal::Bool(*b)))
            }
            ComptimeVal::Str(s) => {
                let str_ty = self.intern_str_type();
                let cval = ConstValue::Aggregate(vec![
                    ConstValue::Str(s.clone()),
                    ConstValue::I64(s.len() as i128),
                ]);
                Ok((cval, str_ty, ComptimeVal::Str(s.clone())))
            }
            ComptimeVal::Module(m) => {
                let meta_ty = self.intern_type(Type::MetaType);
                Ok((ConstValue::I64(0), meta_ty, ComptimeVal::Module(m.clone())))
            }
            ComptimeVal::Map(id) => {
                let map_ty = self.map_instances[*id as usize].map_ty;
                Ok((
                    ConstValue::I64(*id as i128),
                    map_ty,
                    ComptimeVal::Map(*id),
                ))
            }
            ComptimeVal::Type(t_id) => {
                let meta_ty = self.intern_type(Type::MetaType);
                Ok((ConstValue::Type(*t_id), meta_ty, ComptimeVal::Type(*t_id)))
            }
            ComptimeVal::List(items, elem_ty_opt) => {
                let elem_ty = if let Some(exp) = expected_ty
                    && let Some(&info) = self.slices.get(&exp)
                {
                    info.elem
                } else if let Some(et) = elem_ty_opt {
                    *et
                } else if let Some(first) = items.first() {
                    let (_, et, _) = self.comptime_val_to_const_result(first, None)?;
                    et
                } else {
                    return Err("Empty comptime list requires an explicit slice type".to_string());
                };
                if matches!(self.program.types[elem_ty.0 as usize], Type::MetaType) {
                    return Err(
                        "Comptime list of types cannot be materialized as a runtime slice"
                            .to_string(),
                    );
                }
                let mut elem_consts = Vec::with_capacity(items.len());
                for item in items {
                    let (cv, _, _) = self.comptime_val_to_const_result(item, Some(elem_ty))?;
                    elem_consts.push(cv);
                }
                let slice_ty = self.intern_slice_type(false, elem_ty);
                let arr_ty = self.intern_type(Type::Array {
                    elem: elem_ty,
                    len: elem_consts.len() as u64,
                });
                let gl_id = GlobalId(self.program.globals.len() as u32);
                self.program.globals.push(Global {
                    id: gl_id,
                    ty: arr_ty,
                    mutable: false,
                    init: ConstValue::Aggregate(elem_consts),
                });
                let cval = ConstValue::Aggregate(vec![
                    ConstValue::Global(gl_id),
                    ConstValue::I64(items.len() as i128),
                ]);
                Ok((
                    cval,
                    slice_ty,
                    ComptimeVal::List(items.clone(), Some(elem_ty)),
                ))
            }
            ComptimeVal::Record(entries) => {
                let Some(comp_ty) = expected_ty else {
                    return Err(format!(
                        "Comptime record {ct_val:?} cannot be materialized without an explicit struct type"
                    ));
                };
                let Some(comp) = self.composites.get(&comp_ty).cloned() else {
                    return Err(format!(
                        "Expected struct type for comptime record initializer, found '{}'",
                        self.type_display_name(comp_ty)
                    ));
                };
                let mut vals = Vec::with_capacity(comp.fields.len());
                for (fname, fty, _, _) in &comp.fields {
                    let Some((_, fval)) = entries.iter().find(|(k, _)| k == fname) else {
                        return Err(format!(
                            "Missing field '{}' in comptime record for '{}'",
                            fname, comp.name
                        ));
                    };
                    let (cv, _, _) = self.comptime_val_to_const_result(fval, Some(*fty))?;
                    vals.push(cv);
                }
                Ok((ConstValue::Aggregate(vals), comp_ty, ct_val.clone()))
            }
            ComptimeVal::Tuple(items) => {
                let expected_fields = if let Some(t) = expected_ty
                    && let Type::Struct(ftys) = &self.program.types[t.0 as usize]
                {
                    Some(ftys.clone())
                } else {
                    None
                };
                let mut vals = Vec::with_capacity(items.len());
                let mut tys = Vec::with_capacity(items.len());
                for (i, item) in items.iter().enumerate() {
                    let exp = expected_fields.as_ref().and_then(|v| v.get(i).copied());
                    let (cv, ty, _) = self.comptime_val_to_const_result(item, exp)?;
                    vals.push(cv);
                    tys.push(ty);
                }
                let tup_ty = expected_ty.unwrap_or_else(|| self.intern_type(Type::Struct(tys)));
                Ok((ConstValue::Aggregate(vals), tup_ty, ct_val.clone()))
            }
            ComptimeVal::ConstExpr(_, ce) => {
                Err(format!(
                    "Expression cannot be evaluated as a compile-time constant initializer: {ce:?}"
                ))
            }
        }
    }

    pub(super) fn eval_type_name_intrinsic(
        &mut self,
        mod_path: &str,
        self_ty: Option<TypeId>,
        env: &HashMap<String, ComptimeVal>,
        ty: &TypeExpr,
    ) -> Result<(ConstValue, TypeId, ComptimeVal), String> {
        let t_id = self.resolve_type_expr(mod_path, self_ty, env, ty)?;
        let name = self.type_display_name(t_id);
        let str_ty = self.intern_str_type();
        let cval = ConstValue::Aggregate(vec![
            ConstValue::Str(name.clone()),
            ConstValue::I64(name.len() as i128),
        ]);
        Ok((cval, str_ty, ComptimeVal::Str(name)))
    }

    pub(super) fn eval_satisfies_intrinsic(
        &mut self,
        mod_path: &str,
        self_ty: Option<TypeId>,
        env: &HashMap<String, ComptimeVal>,
        ty: &TypeExpr,
        bound: &TypeExpr,
    ) -> Result<bool, String> {
        if let TypeExpr::Named(p) = ty
            && p.len() == 1
            && matches!(env.get(&p[0]), Some(ComptimeVal::Module(_)))
        {
            return Ok(matches!(bound, TypeExpr::Constraint(TypeConstraint::Module)));
        }
        let t_id = self.resolve_type_expr(mod_path, self_ty, env, ty)?;
        match self.eval_comptime_type_bound(mod_path, self_ty, env, bound, t_id)? {
            Some(Ok(_)) => Ok(true),
            Some(Err(_)) => Ok(false),
            None => {
                let b_id = self.resolve_type_expr(mod_path, self_ty, env, bound)?;
                Ok(t_id == b_id)
            }
        }
    }

    pub(super) fn eval_has_field_intrinsic(
        &mut self,
        mod_path: &str,
        self_ty: Option<TypeId>,
        env: &HashMap<String, ComptimeVal>,
        ty: &TypeExpr,
        name_expr: &Expr,
    ) -> Result<bool, String> {
        let mut t_id = self.resolve_type_expr(mod_path, self_ty, env, ty)?;
        if let Type::Ptr { pointee, .. } = self.program.types[t_id.0 as usize]
            && !self.slices.contains_key(&t_id)
            && !self.raw_ptrs.contains_key(&t_id)
        {
            t_id = pointee;
        }
        let name_val = self.eval_comptime_val(mod_path, self_ty, env, name_expr)?;
        if let Some(comp) = self.composites.get(&t_id) {
            if comp.is_opaque && self_ty != Some(t_id) {
                return Err(format!(
                    "Cannot reflect over private fields of opaque type '{}'; 'opaque' types encapsulate their representation",
                    self.type_display_name(t_id)
                ));
            }
            let ComptimeVal::Str(fname) = name_val else {
                return Err("'@has_field' second argument must be a comptime string".to_string());
            };
            return Ok(comp.fields.iter().any(|(n, _, _, _)| n == &fname));
        }
        if self.named_opaques.contains(&t_id)
            || self.distinct_types.contains_key(&t_id)
            || self.is_opaque_type(t_id)
        {
            if self_ty != Some(t_id) {
                return Err(format!(
                    "Cannot reflect over private fields of opaque type '{}'; 'opaque' types encapsulate their representation",
                    self.type_display_name(t_id)
                ));
            }
            return Ok(false);
        }
        if let Some(ov) = self.overlays.get(&t_id) {
            let ComptimeVal::Str(fname) = name_val else {
                return Err("'@has_field' second argument must be a comptime string".to_string());
            };
            return Ok(ov.fields.iter().any(|(n, _)| n == &fname));
        }
        if self.type_satisfies_constraint(t_id, TypeConstraint::Tuple) {
            let Type::Struct(elems) = &self.program.types[t_id.0 as usize] else {
                return Ok(false);
            };
            return match name_val {
                ComptimeVal::Int(idx) => Ok(idx >= 0 && (idx as usize) < elems.len()),
                ComptimeVal::Str(s) => Ok(s.parse::<usize>().is_ok_and(|i| i < elems.len())),
                _ => Err(
                    "'@has_field' second argument must be a comptime string or integer index"
                        .to_string(),
                ),
            };
        }
        Ok(false)
    }

    /// `@has_method(T, "name")`: a method `T` declares (`pub`, or any of them inside `T`), or one
    /// a trait it implements gives it. A reference reflects over what it refers to.
    pub(super) fn eval_has_method_intrinsic(
        &mut self,
        mod_path: &str,
        self_ty: Option<TypeId>,
        env: &HashMap<String, ComptimeVal>,
        ty: &TypeExpr,
        name_expr: &Expr,
    ) -> Result<bool, String> {
        let mut t_id = self.resolve_type_expr(mod_path, self_ty, env, ty)?;
        if let Type::Ptr { pointee, .. } = self.program.types[t_id.0 as usize]
            && !self.slices.contains_key(&t_id)
            && !self.raw_ptrs.contains_key(&t_id)
        {
            t_id = pointee;
        }
        let ComptimeVal::Str(name) = self.eval_comptime_val(mod_path, self_ty, env, name_expr)? else {
            return Err("'@has_method' second argument must be a comptime string".to_string());
        };
        let own = match (self.composites.get(&t_id), self.distinct_types.get(&t_id)) {
            (Some(c), _) => c.methods.get(&name).map(|(v, _)| *v),
            (None, Some(d)) => d.methods.get(&name).map(|(v, _)| *v),
            _ => None,
        };
        if let Some(vis) = own
            && (self_ty == Some(t_id) || matches!(vis, Visibility::Pub | Visibility::Export))
        {
            return Ok(true);
        }
        for t in self.traits_implemented_by(t_id)? {
            if self.traits[&t].methods.iter().any(|m| m.name == name) {
                return Ok(true);
            }
        }
        Ok(false)
    }

    /// The place the comptime second argument of `@field` reaches from `base`: a field name, a
    /// tuple index (as an integer or a string of digits), or a path, which is a list of those.
    pub(super) fn field_access_expr(&self, base: &Expr, field: &ComptimeVal) -> Result<Expr, String> {
        match field {
            ComptimeVal::Str(name) => Ok(match name.parse::<u32>() {
                Ok(index) => Expr::TupleIndex {
                    base: Box::new(base.clone()),
                    index,
                },
                Err(_) => Expr::Field {
                    base: Box::new(base.clone()),
                    field: name.clone(),
                },
            }),
            ComptimeVal::Int(idx) if *idx >= 0 => Ok(Expr::TupleIndex {
                base: Box::new(base.clone()),
                index: *idx as u32,
            }),
            ComptimeVal::Int(idx) => {
                Err(format!("'@field' tuple index must be non-negative, found {idx}"))
            }
            ComptimeVal::List(steps, _) => {
                let mut place = base.clone();
                for step in steps {
                    place = self.field_access_expr(&place, step)?;
                }
                Ok(place)
            }
            other => Err(format!(
                "'@field' second argument must evaluate at comptime to a field name ('&str'), a tuple index, or a path ('&[&str]'), found {}",
                self.comptime_val_label(other)
            )),
        }
    }

    /// `@leaves(T)`: the path of every field of `T` that is not itself a `struct` or `tuple`,
    /// depth-first. Encapsulated types are leaves.
    pub(super) fn eval_leaves_intrinsic(
        &mut self,
        mod_path: &str,
        self_ty: Option<TypeId>,
        env: &HashMap<String, ComptimeVal>,
        ty: &TypeExpr,
    ) -> Result<ComptimeVal, String> {
        let t_id = self.resolve_type_expr(mod_path, self_ty, env, ty)?;
        let mut out = Vec::new();
        self.collect_leaves(t_id, &mut Vec::new(), &mut out);
        Ok(ComptimeVal::List(out, None))
    }

    fn collect_leaves(&mut self, ty: TypeId, path: &mut Vec<String>, out: &mut Vec<ComptimeVal>) {
        let children: Vec<(String, TypeId)> = match self.composites.get(&ty) {
            Some(comp) if !comp.is_opaque => {
                comp.fields.iter().map(|(name, fty, ..)| (name.clone(), *fty)).collect()
            }
            Some(_) => Vec::new(),
            None if self.type_satisfies_constraint(ty, TypeConstraint::Tuple) => {
                let Type::Struct(elems) = self.program.types[ty.0 as usize].clone() else {
                    unreachable!()
                };
                elems.into_iter().enumerate().map(|(i, t)| (i.to_string(), t)).collect()
            }
            None => Vec::new(),
        };
        if children.is_empty() {
            let steps = path.iter().cloned().map(ComptimeVal::Str).collect();
            out.push(ComptimeVal::List(steps, None));
        }
        for (name, child) in children {
            path.push(name);
            self.collect_leaves(child, path, out);
            path.pop();
        }
    }

    pub(super) fn eval_fields_intrinsic(
        &mut self,
        mod_path: &str,
        self_ty: Option<TypeId>,
        env: &HashMap<String, ComptimeVal>,
        ty: &TypeExpr,
    ) -> Result<ComptimeVal, String> {
        let mut t_id = self.resolve_type_expr(mod_path, self_ty, env, ty)?;
        if let Type::Ptr { pointee, .. } = self.program.types[t_id.0 as usize]
            && !self.slices.contains_key(&t_id)
            && !self.raw_ptrs.contains_key(&t_id)
        {
            t_id = pointee;
        }
        let usize_ty = self.intern_type(Type::Int {
            signed: false,
            bits: 64,
        });
        if let Some(comp) = self.composites.get(&t_id).cloned() {
            if comp.is_opaque && self_ty != Some(t_id) {
                return Err(format!(
                    "Cannot reflect over private fields of opaque type '{}'; 'opaque' types encapsulate their representation",
                    self.type_display_name(t_id)
                ));
            }
            let mut items = Vec::with_capacity(comp.fields.len());
            let mut cur_offset = 0u64;
            for (idx, (fname, fty, _vis, fdef)) in comp.fields.iter().enumerate() {
                let offset_val = if comp.is_packed {
                    comp.packed_offsets[idx].0 as i128
                } else {
                    let (fs, fa) = self.program.type_size_align(*fty)?;
                    cur_offset = (cur_offset + fa - 1) & !(fa - 1);
                    let field_off = cur_offset as i128;
                    cur_offset += fs;
                    field_off
                };
                items.push(ComptimeVal::Record(vec![
                    ("name".to_string(), ComptimeVal::Str(fname.clone())),
                    ("ty".to_string(), ComptimeVal::Type(*fty)),
                    ("offset".to_string(), ComptimeVal::Int(offset_val)),
                    ("__ty:offset".to_string(), ComptimeVal::Type(usize_ty)),
                    ("has_default".to_string(), ComptimeVal::Bool(fdef.is_some())),
                ]));
            }
            return Ok(ComptimeVal::List(items, None));
        }
        if self.named_opaques.contains(&t_id)
            || self.distinct_types.contains_key(&t_id)
            || self.is_opaque_type(t_id)
        {
            if self_ty != Some(t_id) {
                return Err(format!(
                    "Cannot reflect over private fields of opaque type '{}'; 'opaque' types encapsulate their representation",
                    self.type_display_name(t_id)
                ));
            }
            return Ok(ComptimeVal::List(Vec::new(), None));
        }
        if let Some(ov) = self.overlays.get(&t_id).cloned() {
            let mut items = Vec::with_capacity(ov.fields.len());
            for (fname, fty) in &ov.fields {
                items.push(ComptimeVal::Record(vec![
                    ("name".to_string(), ComptimeVal::Str(fname.clone())),
                    ("ty".to_string(), ComptimeVal::Type(*fty)),
                ]));
            }
            return Ok(ComptimeVal::List(items, None));
        }
        if self.type_satisfies_constraint(t_id, TypeConstraint::Tuple) {
            let Type::Struct(field_tys) = self.program.types[t_id.0 as usize].clone() else {
                unreachable!()
            };
            let mut items = Vec::with_capacity(field_tys.len());
            let mut cur_offset = 0u64;
            for (idx, fty) in field_tys.iter().enumerate() {
                let (fs, fa) = self.program.type_size_align(*fty)?;
                cur_offset = (cur_offset + fa - 1) & !(fa - 1);
                let field_off = cur_offset as i128;
                cur_offset += fs;
                items.push(ComptimeVal::Record(vec![
                    ("name".to_string(), ComptimeVal::Str(idx.to_string())),
                    ("index".to_string(), ComptimeVal::Int(idx as i128)),
                    ("__ty:index".to_string(), ComptimeVal::Type(usize_ty)),
                    ("ty".to_string(), ComptimeVal::Type(*fty)),
                    ("offset".to_string(), ComptimeVal::Int(field_off)),
                    ("__ty:offset".to_string(), ComptimeVal::Type(usize_ty)),
                ]));
            }
            return Ok(ComptimeVal::List(items, None));
        }
        Err(format!(
            "'@fields' expects a 'struct', 'tuple', or 'overlay' type, found '{}'",
            self.type_display_name(t_id)
        ))
    }

    pub(super) fn eval_variants_intrinsic(
        &mut self,
        mod_path: &str,
        self_ty: Option<TypeId>,
        env: &HashMap<String, ComptimeVal>,
        ty: &TypeExpr,
    ) -> Result<ComptimeVal, String> {
        let t_id = self.resolve_type_expr(mod_path, self_ty, env, ty)?;
        if let Some((_, variants)) = self.enums.get(&t_id).cloned() {
            let Type::Int { signed, bits } = self.program.types[t_id.0 as usize] else {
                unreachable!()
            };
            let backing_ty = self.intern_type(Type::Int { signed, bits });
            let elem_ty = self
                .eval_comptime_type_func("core::meta", "EnumVariant", &[ComptimeVal::Type(t_id)])
                .ok();
            let mut items = Vec::with_capacity(variants.len());
            for (vname, val) in variants {
                items.push(ComptimeVal::Record(vec![
                    ("name".to_string(), ComptimeVal::Str(vname)),
                    ("value".to_string(), ComptimeVal::Int(val)),
                    ("__ty:value".to_string(), ComptimeVal::Type(backing_ty)),
                    ("val".to_string(), ComptimeVal::Int(val)),
                    ("__ty:val".to_string(), ComptimeVal::Type(t_id)),
                ]));
            }
            return Ok(ComptimeVal::List(items, elem_ty));
        }
        if let Some(uinfo) = self.unions.get(&t_id).cloned() {
            let tag_enum_ty = self.union_tag_enum(t_id);
            let tag_variants = self.enums[&tag_enum_ty].1.clone();
            let mut items = Vec::with_capacity(uinfo.variants.len());
            for (idx, (vname, payload_ty)) in uinfo.variants.iter().enumerate() {
                let tag_val = tag_variants.get(idx).map(|(_, v)| *v).unwrap_or(idx as i128);
                items.push(ComptimeVal::Record(vec![
                    ("name".to_string(), ComptimeVal::Str(vname.clone())),
                    ("payload".to_string(), ComptimeVal::Type(*payload_ty)),
                    ("tag".to_string(), ComptimeVal::Int(tag_val)),
                    ("__ty:tag".to_string(), ComptimeVal::Type(tag_enum_ty)),
                ]));
            }
            return Ok(ComptimeVal::List(items, None));
        }
        if let Some(einfo) = self.errors.get(&t_id).cloned() {
            let mut items = Vec::with_capacity(einfo.decl_order.len());
            for key in &einfo.decl_order {
                let leaf = einfo.leaves.iter().find(|l| &l.key == key).unwrap();
                items.push(ComptimeVal::Record(vec![
                    (
                        "error_name".to_string(),
                        ComptimeVal::Str(leaf.key.error_name.clone()),
                    ),
                    (
                        "name".to_string(),
                        ComptimeVal::Str(leaf.key.variant_name.clone()),
                    ),
                    ("payload".to_string(), ComptimeVal::Type(leaf.payload_ty)),
                ]));
            }
            return Ok(ComptimeVal::List(items, None));
        }
        Err(format!(
            "'@variants' expects an 'enum', 'union', or 'error' type, found '{}'",
            self.type_display_name(t_id)
        ))
    }

    pub(super) fn eval_variants_const(
        &mut self,
        mod_path: &str,
        self_ty: Option<TypeId>,
        env: &HashMap<String, ComptimeVal>,
        ty: &TypeExpr,
    ) -> Result<(ConstValue, TypeId, ComptimeVal), String> {
        let t_id = self.resolve_type_expr(mod_path, self_ty, env, ty)?;
        let ct_list = self.eval_variants_intrinsic(mod_path, self_ty, env, ty)?;
        let Some((_, variants)) = self.enums.get(&t_id).cloned() else {
            return Err(format!(
                "'@variants({})' carries comptime-only 'type' payloads and can only be iterated in 'comptime for' (not at runtime)",
                self.type_display_name(t_id)
            ));
        };
        let elem_ty =
            self.eval_comptime_type_func("core::meta", "EnumVariant", &[ComptimeVal::Type(t_id)])?;
        let slice_ty = self.intern_slice_type(false, elem_ty);
        let arr_ty = self.intern_type(Type::Array {
            elem: elem_ty,
            len: variants.len() as u64,
        });
        let elem_consts: Vec<ConstValue> = variants
            .iter()
            .map(|(vname, val)| {
                ConstValue::Aggregate(vec![
                    ConstValue::Aggregate(vec![
                        ConstValue::Str(vname.clone()),
                        ConstValue::I64(vname.len() as i128),
                    ]),
                    ConstValue::I64(*val),
                    ConstValue::I64(*val),
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
            ConstValue::I64(variants.len() as i128),
        ]);
        Ok((cval, slice_ty, ct_list))
    }

    pub(super) fn eval_entries_intrinsic(
        &mut self,
        mod_path: &str,
        self_ty: Option<TypeId>,
        env: &HashMap<String, ComptimeVal>,
        inner: &Expr,
    ) -> Result<ComptimeVal, String> {
        let Some(map_id) = self.resolve_map_expr(mod_path, self_ty, env, inner)? else {
            return Err("'@entries' requires a comptime associative map argument".to_string());
        };
        let map_inst = self.map_instances[map_id as usize].clone();
        let map_info = self.maps[&map_inst.map_ty];
        let mut items = Vec::with_capacity(map_inst.entries.len());
        for entry in &map_inst.entries {
            items.push(ComptimeVal::Record(vec![
                ("key".to_string(), entry.key_comptime.clone()),
                ("__ty:key".to_string(), ComptimeVal::Type(map_info.key_ty)),
                ("val".to_string(), entry.val_comptime.clone()),
                ("__ty:val".to_string(), ComptimeVal::Type(map_info.val_ty)),
            ]));
        }
        Ok(ComptimeVal::List(items, None))
    }

    /// The record type of an `@entries` item: `struct { key: K, val: V }`.
    fn map_entry_struct_type(&mut self, key_ty: TypeId, val_ty: TypeId) -> TypeId {
        let fields = vec![("key".to_string(), key_ty), ("val".to_string(), val_ty)];
        self.structural_struct("core::meta", false, fields, "@entries")
            .expect("an unpacked struct of two sized fields is always valid")
    }

    pub(super) fn eval_entries_const(
        &mut self,
        mod_path: &str,
        self_ty: Option<TypeId>,
        env: &HashMap<String, ComptimeVal>,
        inner: &Expr,
    ) -> Result<(ConstValue, TypeId, ComptimeVal), String> {
        let Some(map_id) = self.resolve_map_expr(mod_path, self_ty, env, inner)? else {
            return Err("'@entries' requires a comptime associative map argument".to_string());
        };
        let map_inst = self.map_instances[map_id as usize].clone();
        let map_info = self.maps[&map_inst.map_ty];
        if matches!(
            self.program.types[map_info.key_ty.0 as usize],
            Type::MetaType
        ) || matches!(
            self.program.types[map_info.val_ty.0 as usize],
            Type::MetaType
        ) {
            return Err(
                "'@entries' on a map with 'type' or 'module' keys/values can only be iterated in 'comptime for' (not at runtime)"
                    .to_string(),
            );
        }
        let elem_ty = self.map_entry_struct_type(map_info.key_ty, map_info.val_ty);
        let slice_ty = self.intern_slice_type(false, elem_ty);
        let arr_ty = self.intern_type(Type::Array {
            elem: elem_ty,
            len: map_inst.entries.len() as u64,
        });
        let mut elem_consts = Vec::with_capacity(map_inst.entries.len());
        let mut items = Vec::with_capacity(map_inst.entries.len());
        for entry in &map_inst.entries {
            elem_consts.push(ConstValue::Aggregate(vec![
                entry.key_const.clone(),
                entry.val_const.clone(),
            ]));
            items.push(ComptimeVal::Record(vec![
                ("key".to_string(), entry.key_comptime.clone()),
                ("__ty:key".to_string(), ComptimeVal::Type(map_info.key_ty)),
                ("val".to_string(), entry.val_comptime.clone()),
                ("__ty:val".to_string(), ComptimeVal::Type(map_info.val_ty)),
            ]));
        }
        let gl_id = GlobalId(self.program.globals.len() as u32);
        self.program.globals.push(Global {
            id: gl_id,
            ty: arr_ty,
            mutable: false,
            init: ConstValue::Aggregate(elem_consts),
        });
        let cval = ConstValue::Aggregate(vec![
            ConstValue::Global(gl_id),
            ConstValue::I64(map_inst.entries.len() as i128),
        ]);
        Ok((cval, slice_ty, ComptimeVal::List(items, Some(elem_ty))))
    }

    pub(super) fn eval_map_keys_const(
        &mut self,
        map_id: u32,
    ) -> Result<(ConstValue, TypeId, ComptimeVal), String> {
        let map_inst = self.map_instances[map_id as usize].clone();
        let map_info = self.maps[&map_inst.map_ty];
        let items: Vec<ComptimeVal> = map_inst
            .entries
            .iter()
            .map(|e| e.key_comptime.clone())
            .collect();
        if matches!(
            self.program.types[map_info.key_ty.0 as usize],
            Type::MetaType
        ) {
            return Err(
                "Map '.keys' of 'type' or 'module' can only be iterated in 'comptime for' (not at runtime)"
                    .to_string(),
            );
        }
        let slice_ty = self.intern_slice_type(false, map_info.key_ty);
        let arr_ty = self.intern_type(Type::Array {
            elem: map_info.key_ty,
            len: map_inst.entries.len() as u64,
        });
        let elem_consts: Vec<ConstValue> = map_inst
            .entries
            .iter()
            .map(|e| e.key_const.clone())
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
            ConstValue::I64(map_inst.entries.len() as i128),
        ]);
        Ok((
            cval,
            slice_ty,
            ComptimeVal::List(items, Some(map_info.key_ty)),
        ))
    }

    pub(super) fn eval_map_values_const(
        &mut self,
        map_id: u32,
    ) -> Result<(ConstValue, TypeId, ComptimeVal), String> {
        let map_inst = self.map_instances[map_id as usize].clone();
        let map_info = self.maps[&map_inst.map_ty];
        let items: Vec<ComptimeVal> = map_inst
            .entries
            .iter()
            .map(|e| e.val_comptime.clone())
            .collect();
        if matches!(
            self.program.types[map_info.val_ty.0 as usize],
            Type::MetaType
        ) {
            return Err(
                "Map '.values' of 'type' or 'module' can only be iterated in 'comptime for' (not at runtime)"
                    .to_string(),
            );
        }
        let slice_ty = self.intern_slice_type(false, map_info.val_ty);
        let arr_ty = self.intern_type(Type::Array {
            elem: map_info.val_ty,
            len: map_inst.entries.len() as u64,
        });
        let elem_consts: Vec<ConstValue> = map_inst
            .entries
            .iter()
            .map(|e| e.val_const.clone())
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
            ConstValue::I64(map_inst.entries.len() as i128),
        ]);
        Ok((
            cval,
            slice_ty,
            ComptimeVal::List(items, Some(map_info.val_ty)),
        ))
    }

    pub(super) fn eval_fn_info_intrinsic(
        &mut self,
        mod_path: &str,
        self_ty: Option<TypeId>,
        env: &HashMap<String, ComptimeVal>,
        ty: &TypeExpr,
    ) -> Result<ComptimeVal, String> {
        let t_id = if let TypeExpr::Named(p) = ty {
            let expanded = self.expand_module_path(env, p);
            if p.len() == 1
                && let Some(ComptimeVal::Type(vty)) = env.get(&format!("__var_ty:{}", p[0]))
            {
                *vty
            } else if let Ok(ResolvedItem::Func(fmod, fname)) =
                self.resolve_path(mod_path, &expanded)
            {
                let fn_id = self.get_or_instantiate_func(&fmod, &fname, &[])?;
                self.named_fn_ptr_type(fn_id)
            } else {
                self.resolve_type_expr(mod_path, self_ty, env, ty)?
            }
        } else {
            self.resolve_type_expr(mod_path, self_ty, env, ty)?
        };
        let (param_tys, ret_ty) = match &self.program.types[t_id.0 as usize] {
            Type::FnPtr { args, ret } => (args.clone(), *ret),
            _ => {
                if let Some(cinfo) = self.closures.get(&t_id) {
                    (cinfo.param_tys.clone(), cinfo.ret_ty)
                } else {
                    return Err(format!(
                        "'@fn_info' expects a function pointer or closure type ('callable'), found '{}'",
                        self.type_display_name(t_id)
                    ));
                }
            }
        };
        let params: Vec<ComptimeVal> = param_tys.into_iter().map(ComptimeVal::Type).collect();
        Ok(ComptimeVal::Record(vec![
            ("params".to_string(), ComptimeVal::List(params, None)),
            ("ret".to_string(), ComptimeVal::Type(ret_ty)),
        ]))
    }

    pub(super) fn eval_synthesized_map(
        &mut self,
        mod_path: &str,
        self_ty: Option<TypeId>,
        env: &HashMap<String, ComptimeVal>,
        key_ty_expr: &TypeExpr,
        val_ty_expr: &TypeExpr,
        entries_expr: &Expr,
    ) -> Result<(ConstValue, TypeId, ComptimeVal), String> {
        let key_ty = self.resolve_type_expr(mod_path, self_ty, env, key_ty_expr)?;
        let val_ty = self.resolve_type_expr(mod_path, self_ty, env, val_ty_expr)?;
        let map_ty = self.intern_map_type(key_ty, val_ty);
        let list_val = self.eval_comptime_val(mod_path, self_ty, env, entries_expr)?;
        let ComptimeVal::List(items, _) = list_val else {
            return Err("'@Map' expects a comptime slice of '(K, V)' pairs or records".to_string());
        };
        let mut entries = Vec::with_capacity(items.len());
        for item in items {
            let (k_ct, v_ct) = match item {
                ComptimeVal::Tuple(elems) if elems.len() == 2 => {
                    (elems[0].clone(), elems[1].clone())
                }
                ComptimeVal::Record(fields) => {
                    let Some((_, k)) = fields.iter().find(|(n, _)| n == "key") else {
                        return Err("'@Map' record entry is missing 'key' field".to_string());
                    };
                    let Some((_, v)) = fields.iter().find(|(n, _)| n == "val") else {
                        return Err("'@Map' record entry is missing 'val' field".to_string());
                    };
                    (k.clone(), v.clone())
                }
                _ => {
                    return Err(
                        "'@Map' entries must be '(key, val)' tuples or records with 'key' and 'val'"
                            .to_string(),
                    );
                }
            };
            let mkey = match &k_ct {
                ComptimeVal::Type(t) => MapKey::Type(*t),
                ComptimeVal::Int(n) => MapKey::Int(*n),
                ComptimeVal::Bool(b) => MapKey::Bool(*b),
                ComptimeVal::Str(s) => MapKey::Str(s.clone()),
                ComptimeVal::Module(m) => MapKey::Module(m.clone()),
                _ => {
                    return Err(
                        "'@Map' key must be a compile-time type, integer/enum, bool, &str, or module"
                            .to_string(),
                    );
                }
            };
            if entries.iter().any(|e: &MapEntry| e.key == mkey) {
                return Err(format!("Duplicate key {mkey:?} in '@Map'"));
            }
            let (k_const, _, _) = self.comptime_val_to_const_result(&k_ct, Some(key_ty))?;
            let (v_const, _, _) = self.comptime_val_to_const_result(&v_ct, Some(val_ty))?;
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
            Expr::MapLit(_) | Expr::IntrinsicInvert(_) | Expr::IntrinsicMap { .. } => {
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
        enum DeclTarget {
            Module(String),
            Type(TypeId),
        }
        let target = match inner {
            Expr::TypeVal(te) => {
                DeclTarget::Type(self.resolve_type_expr(mod_path, self_ty, env, te)?)
            }
            Expr::Path(p) => {
                if p.len() == 1 {
                    if p[0] == "Self"
                        && let Some(st) = self_ty
                    {
                        DeclTarget::Type(st)
                    } else if let Some(ComptimeVal::Module(m)) = env.get(&p[0]) {
                        DeclTarget::Module(m.clone())
                    } else if let Some(ComptimeVal::Type(t)) = env.get(&p[0]) {
                        DeclTarget::Type(*t)
                    } else {
                        let expanded = self.expand_module_path(env, p);
                        match self.resolve_path(mod_path, &expanded)? {
                            ResolvedItem::Module(m) => DeclTarget::Module(m),
                            ResolvedItem::Type(tmod, tname) => {
                                DeclTarget::Type(self.resolve_named_type(&tmod, &tname)?)
                            }
                            ResolvedItem::Const(cmod, cname) => {
                                let (_, _, cv, _) = self.resolve_top_const(&cmod, &cname)?;
                                match cv {
                                    ComptimeVal::Module(m) => DeclTarget::Module(m),
                                    ComptimeVal::Type(t) => DeclTarget::Type(t),
                                    _ => {
                                        return Err(format!(
                                            "'@declarations' argument '{}' is not a module or type",
                                            expanded.join("::")
                                        ));
                                    }
                                }
                            }
                            _ => {
                                return Err(format!(
                                    "'@declarations' argument '{}' is not a module or type",
                                    expanded.join("::")
                                ));
                            }
                        }
                    }
                } else {
                    let expanded = self.expand_module_path(env, p);
                    match self.resolve_path(mod_path, &expanded)? {
                        ResolvedItem::Module(m) => DeclTarget::Module(m),
                        ResolvedItem::Type(tmod, tname) => {
                            DeclTarget::Type(self.resolve_named_type(&tmod, &tname)?)
                        }
                        ResolvedItem::Const(cmod, cname) => {
                            let (_, _, cv, _) = self.resolve_top_const(&cmod, &cname)?;
                            match cv {
                                ComptimeVal::Module(m) => DeclTarget::Module(m),
                                ComptimeVal::Type(t) => DeclTarget::Type(t),
                                _ => {
                                    return Err(format!(
                                        "'@declarations' argument '{}' is not a module or type",
                                        expanded.join("::")
                                    ));
                                }
                            }
                        }
                        _ => {
                            return Err(format!(
                                "'@declarations' argument '{}' is not a module or type",
                                expanded.join("::")
                            ));
                        }
                    }
                }
            }
            other => match self.eval_comptime_val(mod_path, self_ty, env, other)? {
                ComptimeVal::Module(m) => DeclTarget::Module(m),
                ComptimeVal::Type(t) => DeclTarget::Type(t),
                _ => {
                    return Err(
                        "'@declarations' requires a comptime module or type argument".to_string(),
                    );
                }
            },
        };
        let mut decl_names = Vec::new();
        match target {
            DeclTarget::Module(target_mod) => {
                let Some(ast) = self.modules.get(&target_mod) else {
                    return Err(format!("Undefined module '{target_mod}' in '@declarations'"));
                };
                for item in &ast.items {
                    let (vis, name) = match item {
                        Item::Func(f) => (f.vis, &f.name),
                        Item::ExternFunc(e) => (e.vis, &e.name),
                        Item::TypeDecl { vis, name, .. } => (*vis, name),
                        Item::Static(s) => (s.vis, &s.name),
                        Item::Const(c) => (c.vis, &c.name),
                        Item::Impl(_) | Item::Test { .. } => continue,
                    };
                    if vis != Visibility::Private
                        && !name.contains("::")
                        && !name.starts_with("__slop_")
                        && !decl_names.contains(name)
                    {
                        decl_names.push(name.clone());
                    }
                }
            }
            DeclTarget::Type(t_id) => {
                if let Some(comp) = self.composites.get(&t_id) {
                    let mut consts: Vec<String> = comp
                        .consts
                        .iter()
                        .filter(|(_, (v, _))| v.is_public_or_export())
                        .map(|(k, _)| k.clone())
                        .collect();
                    consts.sort();
                    let mut statics: Vec<String> = comp
                        .statics
                        .iter()
                        .filter(|(_, (v, _))| v.is_public_or_export())
                        .map(|(k, _)| k.clone())
                        .collect();
                    statics.sort();
                    let mut methods: Vec<String> = comp
                        .methods
                        .iter()
                        .filter(|(_, (v, _))| v.is_public_or_export())
                        .map(|(k, _)| k.clone())
                        .collect();
                    if let Some(inlines) = self.inline_impls.get(&t_id) {
                        for ii in inlines {
                            for m in &ii.methods {
                                if !methods.contains(&m.name) {
                                    methods.push(m.name.clone());
                                }
                            }
                        }
                    }
                    methods.sort();
                    decl_names.extend(consts);
                    decl_names.extend(statics);
                    decl_names.extend(methods);
                } else if let Some(nt) = self.distinct_types.get(&t_id) {
                    let mut methods: Vec<String> = nt
                        .methods
                        .iter()
                        .filter(|(_, (v, _))| v.is_public_or_export())
                        .map(|(k, _)| k.clone())
                        .collect();
                    if let Some(inlines) = self.inline_impls.get(&t_id) {
                        for ii in inlines {
                            for m in &ii.methods {
                                if !methods.contains(&m.name) {
                                    methods.push(m.name.clone());
                                }
                            }
                        }
                    }
                    methods.sort();
                    decl_names.extend(methods);
                } else if let Some(tr) = self.traits.get(&t_id) {
                    for m in &tr.methods {
                        decl_names.push(m.name.clone());
                    }
                }
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
        let ct_items: Vec<ComptimeVal> = decl_names.into_iter().map(ComptimeVal::Str).collect();
        let gl_id = GlobalId(self.program.globals.len() as u32);
        self.program.globals.push(Global {
            id: gl_id,
            ty: arr_ty,
            mutable: false,
            init: ConstValue::Aggregate(elem_consts),
        });
        let cval = ConstValue::Aggregate(vec![
            ConstValue::Global(gl_id),
            ConstValue::I64(ct_items.len() as i128),
        ]);
        Ok((cval, slice_ty, ComptimeVal::List(ct_items, Some(str_ty))))
    }

    pub(super) fn eval_comptime_val(
        &mut self,
        mod_path: &str,
        self_ty: Option<TypeId>,
        env: &HashMap<String, ComptimeVal>,
        expr: &Expr,
    ) -> Result<ComptimeVal, String> {
        if let Some(tc) = self.index_as_type_call(mod_path, env, expr) {
            return self.eval_comptime_val(mod_path, self_ty, env, &tc);
        }
        match expr {
            Expr::Null => Ok(ComptimeVal::Null),
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
            Expr::LogicalAnd(lhs, rhs) => {
                let l_val = self.eval_comptime_val(mod_path, self_ty, env, lhs)?;
                let r_val = self.eval_comptime_val(mod_path, self_ty, env, rhs)?;
                match (l_val, r_val) {
                    (ComptimeVal::Bool(l_b), ComptimeVal::Bool(r_b)) => {
                        Ok(ComptimeVal::Bool(l_b && r_b))
                    }
                    _ => Err("Unsupported operands for comptime '&&'".to_string()),
                }
            }
            Expr::Int(n) => Ok(ComptimeVal::Int(*n)),
            Expr::Bool(b) => Ok(ComptimeVal::Bool(*b)),
            Expr::Str(s) => Ok(ComptimeVal::Str(s.clone())),
            Expr::IntrinsicTypeName(ty) => {
                let (_, _, ct) = self.eval_type_name_intrinsic(mod_path, self_ty, env, ty)?;
                Ok(ct)
            }
            Expr::IntrinsicSatisfies { ty, bound } => Ok(ComptimeVal::Bool(
                self.eval_satisfies_intrinsic(mod_path, self_ty, env, ty, bound)?,
            )),
            Expr::IntrinsicHasField { ty, name } => Ok(ComptimeVal::Bool(
                self.eval_has_field_intrinsic(mod_path, self_ty, env, ty, name)?,
            )),
            Expr::IntrinsicHasMethod { ty, name } => Ok(ComptimeVal::Bool(
                self.eval_has_method_intrinsic(mod_path, self_ty, env, ty, name)?,
            )),
            Expr::IntrinsicFields(ty) => self.eval_fields_intrinsic(mod_path, self_ty, env, ty),
            Expr::IntrinsicLeaves(ty) => self.eval_leaves_intrinsic(mod_path, self_ty, env, ty),
            Expr::IntrinsicAssert { cond, message, pos } => {
                match self.eval_comptime_val(mod_path, self_ty, env, cond)? {
                    ComptimeVal::Bool(true) => Ok(ComptimeVal::Tuple(Vec::new())),
                    ComptimeVal::Bool(false) => Err(super::expr::assertion_message(message.as_deref(), *pos, mod_path)),
                    other => Err(format!(
                        "'@assert' takes a 'bool', found {}",
                        self.comptime_val_label(&other)
                    )),
                }
            }
            Expr::IntrinsicCompileError(parts) => {
                let mut message = String::new();
                for part in parts {
                    match self.eval_comptime_val(mod_path, self_ty, env, part)? {
                        ComptimeVal::Str(s) => message.push_str(&s),
                        other => message.push_str(&self.comptime_val_label(&other)),
                    }
                }
                Err(message)
            }
            Expr::IntrinsicVariants(ty) => self.eval_variants_intrinsic(mod_path, self_ty, env, ty),
            Expr::IntrinsicEntries(inner) => {
                self.eval_entries_intrinsic(mod_path, self_ty, env, inner)
            }
            Expr::IntrinsicFnInfo(ty) => self.eval_fn_info_intrinsic(mod_path, self_ty, env, ty),
            Expr::IntrinsicField { base, field } => {
                let fval = self.eval_comptime_val(mod_path, self_ty, env, field)?;
                let resolved = self.field_access_expr(base, &fval)?;
                self.eval_comptime_val(mod_path, self_ty, env, &resolved)
            }
            Expr::SliceLit { elems, .. } => {
                let mut items = Vec::with_capacity(elems.len());
                for e in elems {
                    items.push(self.eval_comptime_val(mod_path, self_ty, env, e)?);
                }
                Ok(ComptimeVal::List(items, None))
            }
            Expr::TupleLit(elems) => {
                let mut items = Vec::with_capacity(elems.len());
                for e in elems {
                    items.push(self.eval_comptime_val(mod_path, self_ty, env, e)?);
                }
                Ok(ComptimeVal::Tuple(items))
            }
            Expr::RecordLit(fields) => {
                let mut entries = Vec::with_capacity(fields.len());
                for (name, value) in fields {
                    if entries.iter().any(|(n, _): &(String, ComptimeVal)| n == name) {
                        return Err(format!("Duplicate field '{name}' in struct literal"));
                    }
                    let v = self.eval_comptime_val(mod_path, self_ty, env, value)?;
                    entries.push((name.clone(), v));
                }
                Ok(ComptimeVal::Record(entries))
            }
            Expr::StructLit { ty, fields } => {
                let comp_ty = self.resolve_type_expr(mod_path, self_ty, env, ty)?;
                if let Some(comp) = self.composites.get(&comp_ty).cloned() {
                    if comp.is_opaque && comp.fields.is_empty() && self_ty != Some(comp_ty) {
                        return Err(format!(
                            "Cannot construct opaque type '{}' outside its 'opaque {{ ... }}' block",
                            comp.name
                        ));
                    }
                    let mut entries = Vec::with_capacity(comp.fields.len() * 2);
                    for (f_name, f_ty, f_vis, f_default) in &comp.fields {
                        if comp.is_opaque
                            && *f_vis == Visibility::Private
                            && self_ty != Some(comp_ty)
                        {
                            return Err(format!(
                                "Cannot construct opaque '{}' with private field '{}' outside its 'opaque {{ ... }}' block",
                                comp.name, f_name
                            ));
                        }
                        let f_val = if let Some((_, val_expr)) =
                            fields.iter().find(|(n, _)| n == f_name)
                        {
                            self.eval_comptime_val(mod_path, self_ty, env, val_expr)?
                        } else if let Some(def_expr) = f_default {
                            self.eval_comptime_val(
                                &comp.def_module,
                                Some(comp_ty),
                                &comp.comptime_env,
                                def_expr,
                            )?
                        } else {
                            return Err(format!(
                                "Missing field '{}' in '{}' comptime literal",
                                f_name, comp.name
                            ));
                        };
                        entries.push((f_name.clone(), f_val));
                        entries.push((format!("__ty:{f_name}"), ComptimeVal::Type(*f_ty)));
                    }
                    return Ok(ComptimeVal::Record(entries));
                }
                Ok(ComptimeVal::ConstExpr(format!("{expr:?}"), expr.clone()))
            }
            Expr::TupleIndex { base, index } => {
                let base_val = self.eval_comptime_val(mod_path, self_ty, env, base)?;
                if let ComptimeVal::Tuple(items) = base_val {
                    items.get(*index as usize).cloned().ok_or_else(|| {
                        format!(
                            "Tuple index {} out of bounds (len {})",
                            index,
                            items.len()
                        )
                    })
                } else {
                    let (_, _, ct_val) =
                        self.eval_const_expr_typed(mod_path, self_ty, env, expr, None)?;
                    Ok(ct_val)
                }
            }
            Expr::Slice { base, start, end } => {
                let base_val = self.eval_comptime_val(mod_path, self_ty, env, base)?;
                if let ComptimeVal::List(items, elem_ty) = base_val {
                    let s = self.eval_comptime_int(mod_path, self_ty, env, start)?;
                    let e = self.eval_comptime_int(mod_path, self_ty, env, end)?;
                    if s < 0 || e < s || (e as usize) > items.len() {
                        return Err(format!(
                            "Comptime slice {}..{} out of bounds (len {})",
                            s,
                            e,
                            items.len()
                        ));
                    }
                    Ok(ComptimeVal::List(items[s as usize..e as usize].to_vec(), elem_ty))
                } else {
                    Err(format!("Cannot slice {base:?} at compile time"))
                }
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
                    return Ok(entry.val_comptime.clone());
                }
                if let Ok(ComptimeVal::List(items, _)) =
                    self.eval_comptime_val(mod_path, self_ty, env, base)
                {
                    let idx = self.eval_comptime_int(mod_path, self_ty, env, index)?;
                    if idx < 0 || (idx as usize) >= items.len() {
                        return Err(format!(
                            "Comptime index {} out of bounds (len {})",
                            idx,
                            items.len()
                        ));
                    }
                    return Ok(items[idx as usize].clone());
                }
                let (_, _, ct_val) =
                    self.eval_const_expr_typed(mod_path, self_ty, env, expr, None)?;
                Ok(ct_val)
            }
            Expr::MapLit(_)
            | Expr::IntrinsicMap { .. }
            | Expr::IntrinsicInvert(_)
            | Expr::IntrinsicDeclarations(_)
            | Expr::If { .. }
            | Expr::Match { .. } => {
                let (_, _, ct_val) =
                    self.eval_const_expr_typed(mod_path, self_ty, env, expr, None)?;
                Ok(ct_val)
            }
            Expr::Path(p) => {
                if p.len() == 1 && p[0] == "Self" && let Some(st) = self_ty {
                    return Ok(ComptimeVal::Type(st));
                }
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
                        self.resolve_type_path(mod_path, self_ty, env, prefix).ok()
                    };
                    if let Some(owner_ty) = owner_opt
                        && let Some(comp) = self.composites.get(&owner_ty)
                        && comp.consts.contains_key(cname)
                    {
                        let (_, _, ct_val, cvis, _) =
                            self.resolve_associated_const(owner_ty, cname)?;
                        let comp = &self.composites[&owner_ty];
                        if comp.is_opaque
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
                        && let Some((_, _, ct_val)) = self.impl_assoc_const(owner_ty, cname)?
                    {
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
                if let Ok(Some(map_id)) = self.resolve_map_expr(mod_path, self_ty, env, base) {
                    let map_inst = self.map_instances[map_id as usize].clone();
                    let map_info = self.maps[&map_inst.map_ty];
                    match field.as_str() {
                        "len" => return Ok(ComptimeVal::Int(map_inst.entries.len() as i128)),
                        "keys" => {
                            let items = map_inst
                                .entries
                                .iter()
                                .map(|e| e.key_comptime.clone())
                                .collect();
                            return Ok(ComptimeVal::List(items, Some(map_info.key_ty)));
                        }
                        "values" => {
                            let items = map_inst
                                .entries
                                .iter()
                                .map(|e| e.val_comptime.clone())
                                .collect();
                            return Ok(ComptimeVal::List(items, Some(map_info.val_ty)));
                        }
                        _ => {}
                    }
                }
                if let Ok(base_val) = self.eval_comptime_val(mod_path, self_ty, env, base) {
                    match base_val {
                        ComptimeVal::Record(entries) => {
                            if let Some((_, v)) = entries.into_iter().find(|(k, _)| k == field) {
                                return Ok(v);
                            }
                        }
                        ComptimeVal::List(items, _) if field == "len" => {
                            return Ok(ComptimeVal::Int(items.len() as i128));
                        }
                        ComptimeVal::Str(s) if field == "len" => {
                            return Ok(ComptimeVal::Int(s.len() as i128));
                        }
                        _ => {}
                    }
                }
                if let Ok((_, _, ct_val)) =
                    self.eval_const_expr_typed(mod_path, self_ty, env, expr, None)
                {
                    return Ok(ct_val);
                }
                Err(format!(
                    "Cannot evaluate field access '.{field}' at compile time"
                ))
            }
            Expr::Call {
                callee,
                ct_args: explicit_ct,
                args,
                ..
            } => {
                if let Expr::Path(path) = callee.as_ref() {
                    let expanded = self.expand_module_path(env, path);
                    if let Ok(ResolvedItem::Func(fmod, fname)) =
                        self.resolve_path(mod_path, &expanded)
                    {
                        let mut ct_args = match explicit_ct {
                            Some(ct) => {
                                let mut given = Vec::with_capacity(ct.len());
                                for a in ct {
                                    given.push(if Self::is_placeholder(a) {
                                        None
                                    } else {
                                        Some(self.eval_comptime_val(mod_path, self_ty, env, a)?)
                                    });
                                }
                                self.complete_comptime_args_of(&fmod, &fname, &given)?
                            }
                            None => Vec::new(),
                        };
                        let mut rt_vals = Vec::with_capacity(args.len());
                        for a in args {
                            rt_vals.push(self.eval_comptime_val(mod_path, self_ty, env, a)?);
                        }
                        if explicit_ct.is_none() {
                            ct_args = self.infer_comptime_call_args(mod_path, self_ty, env, &fmod, &fname, args, &rt_vals)?;
                        }
                        ct_args.extend(rt_vals);
                        return self.eval_comptime_func(&fmod, &fname, &ct_args);
                    }
                }
                Err(format!("Unsupported comptime call {expr:?}"))
            }
            Expr::Ref {
                mutable,
                expr: inner,
            } => {
                // `&T` / `&mut T` whose operand is a type is a reference *type* argument
                // (`Box[&i32]`, or `Vec[&Shape]` of a trait, a trait object); otherwise it is a
                // comptime reference value (`[c: &Counter]`).
                if let Ok(inner_val) = self.eval_comptime_val(mod_path, self_ty, env, inner) {
                    match inner_val {
                        ComptimeVal::Type(pointee) if self.traits.contains_key(&pointee) => {
                            let object = self.instantiate_trait_obj_type(pointee, *mutable)?;
                            return Ok(ComptimeVal::Type(object));
                        }
                        ComptimeVal::Type(pointee) => {
                            return Ok(ComptimeVal::Type(self.intern_type(Type::Ptr {
                                mutable: *mutable,
                                pointee,
                            })));
                        }
                        list @ ComptimeVal::List(..) => return Ok(list),
                        _ => {}
                    }
                }
                Ok(ComptimeVal::ConstExpr(format!("{expr:?}"), expr.clone()))
            }
            _ => {
                let key = expr as *const Expr as usize;
                if !self.const_eval_fallback.contains(&key)
                    && let Ok((_, _, ct_val)) =
                        self.eval_const_expr_typed(mod_path, self_ty, env, expr, None)
                {
                    return Ok(ct_val);
                }
                if matches!(
                    expr,
                    Expr::IntrinsicLayout { .. } | Expr::Unary { .. } | Expr::Binary { .. }
                ) {
                    return Ok(ComptimeVal::Int(
                        self.eval_comptime_int(mod_path, self_ty, env, expr)?,
                    ));
                }
                Err(format!(
                    "Cannot evaluate expression at compile time: {expr:?}"
                ))
            }
        }
    }

    /// Folds an integer binary operator at compile time with the semantics it has at runtime for
    /// type `ty` (see [`crate::wide::apply_binop`]); errors become compile errors.
    pub(super) fn fold_int_binop(
        &self,
        op: BinOp,
        l: &crate::wide::Wide,
        r: &crate::wide::Wide,
        ty: TypeId,
    ) -> Result<crate::wide::Wide, String> {
        if matches!(op, BinOp::AddChecked | BinOp::SubChecked | BinOp::MulChecked) {
            return Err(format!(
                "Fallible arithmetic operator '{op}' returns an optional '?T' and cannot be used directly as a scalar constant; unwrap with 'orelse' in a runtime expression"
            ));
        }
        let (signed, bits) = self
            .int_type_reflection(ty)
            .map_or((true, 128), |(s, b, _, _)| (s, b));
        match crate::wide::apply_binop(op, l, r, bits, signed) {
            Ok(crate::wide::BinResult::Int(v)) => Ok(v),
            Ok(crate::wide::BinResult::Bool(_)) => unreachable!("comparisons are folded by the caller"),
            Err(e) => Err(format!(
                "Compile-time {e} (in '{}')",
                self.type_display_name(ty)
            )),
        }
    }

    /// Evaluates `@size_of(T)` / `@align_of(T)` using the target layout of the resolved type.
    pub(super) fn eval_layout_intrinsic(
        &mut self,
        mod_path: &str,
        self_ty: Option<TypeId>,
        env: &HashMap<String, ComptimeVal>,
        ty: &TypeExpr,
        align: bool,
    ) -> Result<i128, String> {
        let t = self.resolve_type_expr(mod_path, self_ty, env, ty)?;
        let what = if align { "'@align_of'" } else { "'@size_of'" };
        if self.layout_is_pending(t) {
            return Err(format!(
                "{what} of '{}' needs a type still being defined",
                self.type_display_name(t)
            ));
        }
        let (size, alignment) = self.sized_type_layout(t, what)?;
        Ok(i128::from(if align { alignment } else { size }))
    }

    #[allow(clippy::only_used_in_recursion)]
    /// Evaluates `expr` as a compile-time integer that fits `i128` (array lengths, bit widths,
    /// and other sizes), with the same semantics as any constant expression.
    pub(super) fn eval_comptime_int(
        &mut self,
        mod_path: &str,
        self_ty: Option<TypeId>,
        env: &HashMap<String, ComptimeVal>,
        expr: &Expr,
    ) -> Result<i128, String> {
        match self.eval_const_expr_typed(mod_path, self_ty, env, expr, None)?.0 {
            ConstValue::I64(n) => Ok(n),
            ConstValue::Wide(w) => Err(format!(
                "Compile-time integer {w} is too large here (it must fit in 'i128')"
            )),
            other => Err(format!(
                "Expected a compile-time integer, found {other:?} in {expr:?}"
            )),
        }
    }

    /// The comptime arguments of a call to `decl`: each parameter takes its explicit argument
    /// (`given[i]`; `None` for `_`), else its inferred value, else its default, evaluated in
    /// `fmod` with the parameters before it in scope.
    pub(super) fn complete_comptime_args(
        &mut self,
        fmod: &str,
        fname: &str,
        decl: &FuncDecl,
        given: &[Option<ComptimeVal>],
        inferred: &HashMap<String, ComptimeVal>,
    ) -> Result<Vec<ComptimeVal>, String> {
        self.complete_comptime_args_in(fmod, fname, decl, given, inferred, &HashMap::new())
    }

    /// [`Self::complete_comptime_args`] with defaults evaluated in `outer` (a method's type
    /// parameters) as well as the earlier parameters.
    pub(super) fn complete_comptime_args_in(
        &mut self,
        fmod: &str,
        fname: &str,
        decl: &FuncDecl,
        given: &[Option<ComptimeVal>],
        inferred: &HashMap<String, ComptimeVal>,
        outer: &HashMap<String, ComptimeVal>,
    ) -> Result<Vec<ComptimeVal>, String> {
        let ct_params: Vec<&crate::ast::Param> = decl.params.iter().filter(|p| p.is_comptime).collect();
        if given.len() > ct_params.len() {
            return Err(format!(
                "Function '{fname}' takes {} comptime argument(s) in brackets, got {}",
                ct_params.len(),
                given.len()
            ));
        }
        let mut env = outer.clone();
        let mut vals = Vec::with_capacity(ct_params.len());
        for (i, p) in ct_params.iter().enumerate() {
            let val = if let Some(Some(v)) = given.get(i) {
                v.clone()
            } else if let Some(v) = inferred.get(&p.name) {
                v.clone()
            } else if let Some(d) = &p.default {
                self.eval_comptime_val(fmod, None, &env, d)?
            } else {
                return Err(format!(
                    "Comptime argument '{}' of '{fname}' is neither given nor inferable and has no default; pass it in brackets ('{fname}[...]')",
                    p.name
                ));
            };
            env.insert(p.name.clone(), val.clone());
            vals.push(val);
        }
        Ok(vals)
    }

    /// [`Self::complete_comptime_args`] for the function `fname` named in `mod_path`, with nothing
    /// inferred.
    pub(super) fn complete_comptime_args_of(
        &mut self,
        mod_path: &str,
        fname: &str,
        given: &[Option<ComptimeVal>],
    ) -> Result<Vec<ComptimeVal>, String> {
        let Ok(Some((def_mod, _, Item::Func(decl), _))) =
            self.find_item_in_module(mod_path, mod_path, fname)
        else {
            return Ok(given.iter().flatten().cloned().collect());
        };
        self.complete_comptime_args(&def_mod, fname, &decl, given, &HashMap::new())
    }

    /// `_` in a comptime argument list: infer this argument, or use its default.
    pub(super) fn is_placeholder(e: &Expr) -> bool {
        matches!(e, Expr::Path(p) if p.len() == 1 && p[0] == "_")
    }

    pub(super) fn eval_comptime_type_func(
        &mut self,
        mod_path: &str,
        fname: &str,
        args: &[ComptimeVal],
    ) -> Result<TypeId, String> {
        // Defaults are filled first, so `HashMap[K, V]` and `HashMap[K, V, Fnv]` are one type.
        let given: Vec<Option<ComptimeVal>> = args.iter().cloned().map(Some).collect();
        let mut norm_args = self.complete_comptime_args_of(mod_path, fname, &given)?;
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
            let def_key = (def_mod.clone(), orig_name, norm_args.clone());
            if let Some(&ty_id) = self.memoized_type_calls.get(&def_key) {
                if self.reused_type_calls.contains(&def_key) {
                    self.reused_type_calls.insert(key.clone());
                }
                self.memoized_type_calls.insert(key, ty_id);
                return Ok(ty_id);
            }
        }
        if let Some(id) = self.defer_type_call(mod_path, fname, &norm_args)? {
            self.memoized_type_calls.insert(key, id);
            return Ok(id);
        }
        let types_before = self.program.types.len();
        let val = self.eval_comptime_func(mod_path, fname, &norm_args)?;
        let ComptimeVal::Type(ty_id) = val else {
            return Err(format!(
                "Expected comptime function '{fname}' to return a type, got {val:?}"
            ));
        };
        if (ty_id.0 as usize) < types_before {
            self.reused_type_calls.insert(key.clone());
        }
        self.memoized_type_calls.insert(key, ty_id);
        Ok(ty_id)
    }

    /// The comptime arguments of a compile-time call `fname(args)` that gives none (`second(i64,
    /// 8)` in a `const`), inferred from what its run-time arguments are, as at run time. Empty
    /// when `fname` has no comptime parameters.
    #[allow(clippy::too_many_arguments)]
    fn infer_comptime_call_args(
        &mut self,
        mod_path: &str,
        self_ty: Option<TypeId>,
        env: &HashMap<String, ComptimeVal>,
        fmod: &str,
        fname: &str,
        args: &[Expr],
        vals: &[ComptimeVal],
    ) -> Result<Vec<ComptimeVal>, String> {
        let Some((def_mod, _, Item::Func(decl), _)) = self.find_item_in_module(fmod, fmod, fname)? else {
            return Ok(Vec::new());
        };
        let ct_params: Vec<(String, TypeExpr)> =
            decl.params.iter().filter(|p| p.is_comptime).map(|p| (p.name.clone(), p.ty.clone())).collect();
        if ct_params.is_empty() {
            return Ok(Vec::new());
        }
        let rt_params: Vec<&crate::ast::Param> = decl.params.iter().filter(|p| !p.is_comptime).collect();
        if rt_params.len() != args.len() {
            return Ok(Vec::new());
        }
        // Any type, for inference; the bounds are checked when the function is instantiated.
        let open: Vec<(String, TypeExpr)> = ct_params
            .iter()
            .map(|(n, _)| (n.clone(), TypeExpr::Constraint(TypeConstraint::Unchecked)))
            .collect();
        let mut inferred = HashMap::new();
        for ((p, arg), val) in rt_params.iter().zip(args).zip(vals) {
            let ty = match val {
                ComptimeVal::Type(_) => self.intern_type(Type::MetaType),
                ComptimeVal::Bool(_) => self.intern_type(Type::Bool),
                _ => match self.eval_const_expr_typed(mod_path, self_ty, env, arg, None) {
                    Ok((_, ty, _)) => ty,
                    Err(_) => continue,
                },
            };
            // What does not match (a literal for an `i32`) says nothing about the parameters;
            // the call checks it.
            let mut trial = inferred.clone();
            if self.unify_type_pattern(&def_mod, &open, &p.ty, ty, &mut trial)?.is_some() {
                inferred = trial;
            }
        }
        let given: Vec<Option<ComptimeVal>> = ct_params.iter().map(|(n, _)| inferred.get(n).cloned()).collect();
        self.complete_comptime_args_of(fmod, fname, &given)
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
        // Every compile-time function runs on the Stage 3 VM (full statements, recursion, step
        // limit); type functions call back into the compiler to build types (`typefn.rs`).
        if decl.ret_ty != TypeExpr::MetaType {
            return self.eval_comptime_call_on_vm(&def_mod, &orig_name, &decl, args);
        }
        if self.comptime_depth >= 256 {
            return Err(format!(
                "Compile-time evaluation of '{fname}' recursed too deeply (more than 256 nested type-function calls)"
            ));
        }
        self.comptime_depth += 1;
        let res = self.eval_type_fn_on_vm(&def_mod, &orig_name, &decl, args);
        self.comptime_depth -= 1;
        res
    }

    /// Evaluates a call to a value-returning function at compile time by instantiating it, lowering
    /// it and its callees, and running it on the sandboxed Stage 3 VM.
    fn eval_comptime_call_on_vm(
        &mut self,
        def_mod: &str,
        fname: &str,
        decl: &FuncDecl,
        args: &[ComptimeVal],
    ) -> Result<ComptimeVal, String> {
        if decl.params.len() != args.len() {
            return Err(format!(
                "Comptime function '{fname}' expects {} args, got {}",
                decl.params.len(),
                args.len()
            ));
        }
        let mut ct_args = Vec::new();
        let mut rt_args = Vec::new();
        for (p, a) in decl.params.iter().zip(args) {
            if p.is_comptime {
                ct_args.push(a.clone());
            } else {
                rt_args.push(comptime_to_vm_value(a).ok_or_else(|| {
                    format!(
                        "Argument for parameter '{}' of '{fname}' cannot be passed to a compile-time call",
                        p.name
                    )
                })?);
            }
        }
        let fn_id = self.get_or_instantiate_func(def_mod, fname, &ct_args)?;
        self.lower_for_comptime(fn_id)?;
        let pure = self.implicit_folding;
        let mut vm = crate::vm::Vm::new(&mut self.program);
        if pure {
            vm.require_purity();
        }
        let result = vm
            .eval_call(fn_id, rt_args)
            .map_err(|e| format!("Compile-time evaluation of '{fname}' failed: {e}"))?;
        vm_value_to_comptime(&result).ok_or_else(|| {
            format!("Compile-time call to '{fname}' produced a value that is not a constant: {result:?}")
        })
    }
}

/// An integer constant as a `Wide` value.
pub(super) fn const_to_wide(v: &ConstValue) -> crate::wide::Wide {
    match v {
        ConstValue::I64(n) => crate::wide::Wide::from_i128(*n),
        ConstValue::Wide(w) => **w,
        _ => crate::wide::Wide::ZERO,
    }
}

/// An integer constant in canonical form: `I64` when it fits in `i128`, otherwise `Wide`.
pub(super) fn int_const(v: crate::wide::Wide) -> ConstValue {
    match v.to_i128() {
        Some(n) => ConstValue::I64(n),
        None => ConstValue::Wide(Box::new(v)),
    }
}

/// A folded integer constant in canonical form: `I64` when it fits in `i128`, otherwise `Wide`.
fn wide_const_result(v: crate::wide::Wide, ty: TypeId) -> (ConstValue, TypeId, ComptimeVal) {
    match v.to_i128() {
        Some(n) => (ConstValue::I64(n), ty, ComptimeVal::Int(n)),
        None => (
            ConstValue::Wide(Box::new(v)),
            ty,
            ComptimeVal::ConstExpr(format!("wide:{v}"), Expr::WideInt(Box::new(v))),
        ),
    }
}

/// A compile-time value as a VM argument (`None` for values with no VM representation).
pub(super) fn comptime_to_vm_value(v: &ComptimeVal) -> Option<crate::vm::Value> {
    Some(match v {
        ComptimeVal::Int(n) => crate::vm::Value::Int(*n),
        ComptimeVal::Bool(b) => crate::vm::Value::Bool(*b),
        ComptimeVal::Type(t) => crate::vm::Value::Type(*t),
        ComptimeVal::Str(s) => crate::vm::Value::Str(s.clone()),
        ComptimeVal::ConstExpr(_, Expr::WideInt(w)) => crate::vm::Value::Wide(w.clone()),
        _ => return None,
    })
}

/// A VM result as a compile-time value (`None` for aggregates and pointers).
pub(super) fn vm_value_to_comptime(v: &crate::vm::Value) -> Option<ComptimeVal> {
    Some(match v {
        crate::vm::Value::Int(n) => ComptimeVal::Int(*n),
        crate::vm::Value::Bool(b) => ComptimeVal::Bool(*b),
        crate::vm::Value::Type(t) => ComptimeVal::Type(*t),
        crate::vm::Value::Str(s) => ComptimeVal::Str(s.clone()),
        crate::vm::Value::Wide(w) => {
            ComptimeVal::ConstExpr(format!("wide:{w}"), Expr::WideInt(w.clone()))
        }
        _ => return None,
    })
}

/// Whether a parameter bounded by `bound` takes unsized types.
pub(super) fn admits_unsized(bound: &TypeExpr) -> bool {
    match bound {
        TypeExpr::Constraint(TypeConstraint::MaybeSized | TypeConstraint::Unchecked) => true,
        TypeExpr::TraitBounds(bounds) => bounds.iter().any(admits_unsized),
        _ => false,
    }
}

/// Whether a parameter bounded by `bound` takes linear types.
pub(super) fn admits_linear(bound: &TypeExpr) -> bool {
    match bound {
        TypeExpr::Constraint(TypeConstraint::MaybeLinear | TypeConstraint::Linear | TypeConstraint::Unchecked) => true,
        TypeExpr::TraitBounds(bounds) => bounds.iter().any(admits_linear),
        _ => false,
    }
}
