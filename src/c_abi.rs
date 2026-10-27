//! How values cross the C calling convention at `export fn` / `extern fn` boundaries.
//!
//! LLVM passes first-class aggregates (`{ i64, i64, i64 }`) its own way, which is not the platform
//! C ABI: a C caller would pass that struct in memory, LLVM splits it across registers. Following
//! clang, aggregates are therefore lowered explicitly: small ones are reinterpreted as the scalar
//! registers they occupy, larger ones go through memory (`byval` arguments, `sret` returns).
//!
//! Implemented for x86-64 System V (Linux, macOS, BSD), the targets this backend emits for.

use crate::ir::{Program, Type, TypeId};

/// How one argument or return value crosses the C ABI.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CAbi {
    /// Passed as its own LLVM type, with a `zeroext` / `signext` attribute for integers narrower
    /// than 32 bits.
    Direct { ext: Option<&'static str> },
    /// An aggregate passed in registers: its bytes reinterpreted as these LLVM scalar types, one
    /// per eightbyte (`i64`, `i32`, `double`, `<2 x float>`, ...).
    Coerced(Vec<String>),
    /// An aggregate passed in memory: a `byval` pointer argument, or an `sret` pointer for a
    /// return value.
    Indirect,
    /// A zero-sized value, which C does not pass.
    Ignore,
}

/// The C ABI of a whole signature.
#[derive(Debug, Clone)]
pub struct FnAbi {
    pub ret: CAbi,
    pub args: Vec<CAbi>,
}

impl FnAbi {
    /// Whether any argument or the return value needs more than plain LLVM argument passing.
    pub fn needs_lowering(&self) -> bool {
        std::iter::once(&self.ret)
            .chain(&self.args)
            .any(|a| matches!(a, CAbi::Coerced(_) | CAbi::Indirect))
    }
}

/// Register class of an eightbyte (x86-64 System V §3.2.3).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Class {
    Integer,
    Sse,
}

/// A scalar inside an aggregate: byte offset, size, class, and whether it is an `f32`.
struct Scalar {
    offset: u64,
    size: u64,
    class: Class,
    is_f32: bool,
}

/// Classifies a full signature, falling back to memory for an aggregate that no longer fits in
/// the remaining registers (6 integer, 8 SSE), as the C compiler does.
pub fn fn_abi(program: &Program, args: &[TypeId], ret: TypeId) -> Result<FnAbi, String> {
    let ret_abi = classify(program, ret)?;
    let mut int_regs: usize = if ret_abi == CAbi::Indirect { 5 } else { 6 };
    let mut sse_regs: usize = 8;
    let mut arg_abis = Vec::with_capacity(args.len());
    for &arg in args {
        let abi = match classify(program, arg)? {
            CAbi::Coerced(pieces) => {
                let sse = pieces.iter().filter(|p| !p.starts_with('i')).count();
                let int = pieces.len() - sse;
                if int <= int_regs && sse <= sse_regs {
                    int_regs -= int;
                    sse_regs -= sse;
                    CAbi::Coerced(pieces)
                } else {
                    CAbi::Indirect
                }
            }
            CAbi::Direct { ext } => {
                match program.types[arg.0 as usize] {
                    Type::F32 | Type::F64 => sse_regs = sse_regs.saturating_sub(1),
                    _ => int_regs = int_regs.saturating_sub(1),
                }
                CAbi::Direct { ext }
            }
            other => other,
        };
        arg_abis.push(abi);
    }
    Ok(FnAbi {
        ret: ret_abi,
        args: arg_abis,
    })
}

/// Classifies one value in isolation (no register accounting).
pub fn classify(program: &Program, ty: TypeId) -> Result<CAbi, String> {
    let (size, _) = program.type_size_align(ty)?;
    let is_aggregate = matches!(
        program.types[ty.0 as usize],
        Type::Struct(_) | Type::Overlay(_) | Type::Union { .. } | Type::Array { .. }
    ) && program.union_niche(ty).is_none();
    if !is_aggregate {
        if size == 0 {
            return Ok(CAbi::Ignore);
        }
        return Ok(CAbi::Direct {
            ext: extension(&program.types[ty.0 as usize], program),
        });
    }
    if size == 0 {
        return Ok(CAbi::Ignore);
    }
    if !cfg!(target_arch = "x86_64") {
        return Err(format!(
            "Passing the aggregate '{}' by value across the C ABI is only implemented for x86-64; pass a pointer instead",
            program.type_label(ty)
        ));
    }
    if size > 16 {
        return Ok(CAbi::Indirect);
    }
    let mut scalars = Vec::new();
    collect_scalars(program, ty, 0, &mut scalars)?;
    let mut pieces = Vec::new();
    for eb in 0..size.div_ceil(8) {
        let (lo, hi) = (eb * 8, (eb * 8 + 8).min(size));
        let in_eb: Vec<&Scalar> = scalars
            .iter()
            .filter(|s| s.offset < hi && s.offset + s.size > lo)
            .collect();
        let class = if in_eb.iter().all(|s| s.class == Class::Sse) && !in_eb.is_empty() {
            Class::Sse
        } else {
            Class::Integer
        };
        pieces.push(match class {
            Class::Integer => format!("i{}", (hi - lo) * 8),
            Class::Sse => {
                let f32s: Vec<&&Scalar> = in_eb.iter().filter(|s| s.is_f32).collect();
                if f32s.is_empty() {
                    "double".to_string()
                } else if f32s.len() == 1 && f32s[0].offset == lo {
                    "float".to_string()
                } else {
                    "<2 x float>".to_string()
                }
            }
        });
    }
    Ok(CAbi::Coerced(pieces))
}

/// `zeroext` / `signext` for integers narrower than 32 bits (C promotes them in registers).
fn extension(ty: &Type, program: &Program) -> Option<&'static str> {
    match ty {
        Type::Bool => Some("zeroext"),
        Type::Int { signed, bits } if *bits < 32 => {
            Some(if *signed { "signext" } else { "zeroext" })
        }
        Type::Pattern { base, .. } => extension(&program.types[base.0 as usize], program),
        _ => None,
    }
}

/// Flattens `ty` at byte `offset` into its scalar leaves.
fn collect_scalars(
    program: &Program,
    ty: TypeId,
    offset: u64,
    out: &mut Vec<Scalar>,
) -> Result<(), String> {
    if let Some((payload, _)) = program.union_niche(ty) {
        return collect_scalars(program, payload, offset, out);
    }
    let align_up = |v: u64, a: u64| (v + a - 1) & !(a - 1);
    match &program.types[ty.0 as usize] {
        Type::Void | Type::Never => {}
        Type::F32 | Type::F64 => {
            let (size, _) = program.type_size_align(ty)?;
            out.push(Scalar {
                offset,
                size,
                class: Class::Sse,
                is_f32: size == 4,
            });
        }
        Type::Simd { elem, len } => {
            let (es, _) = program.type_size_align(*elem)?;
            let is_f32 = matches!(program.types[elem.0 as usize], Type::F32);
            for i in 0..*len {
                out.push(Scalar {
                    offset: offset + i * es,
                    size: es,
                    class: Class::Sse,
                    is_f32,
                });
            }
        }
        Type::Pattern { base, .. } => collect_scalars(program, *base, offset, out)?,
        Type::Struct(fields) => {
            let mut off = 0;
            for &f in fields {
                let (fs, fa) = program.type_size_align(f)?;
                off = align_up(off, fa);
                collect_scalars(program, f, offset + off, out)?;
                off += fs;
            }
        }
        Type::Overlay(fields) => {
            for &f in fields {
                collect_scalars(program, f, offset, out)?;
            }
        }
        Type::Union { tag, variants } => {
            let (ts, _) = program.type_size_align(*tag)?;
            collect_scalars(program, *tag, offset, out)?;
            let mut payload_align = 1;
            for &v in variants {
                payload_align = payload_align.max(program.type_size_align(v)?.1);
            }
            let payload_off = align_up(ts, payload_align);
            for &v in variants {
                collect_scalars(program, v, offset + payload_off, out)?;
            }
        }
        Type::Array { elem, len } => {
            let (es, _) = program.type_size_align(*elem)?;
            for i in 0..*len {
                collect_scalars(program, *elem, offset + i * es, out)?;
            }
        }
        Type::MetaType => return Err("A 'type' value cannot cross the C ABI".to_string()),
        _ => {
            // Integers, booleans, runes, and pointers; integers wider than 64 bits occupy
            // several integer eightbytes.
            let (size, _) = program.type_size_align(ty)?;
            out.push(Scalar {
                offset,
                size,
                class: Class::Integer,
                is_f32: false,
            });
        }
    }
    Ok(())
}
