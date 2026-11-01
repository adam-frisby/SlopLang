//! How values cross the C calling convention at `export fn` / `extern fn` boundaries.
//!
//! LLVM passes first-class aggregates (`{ i64, i64, i64 }`) its own way, which is not the platform
//! C ABI: a C caller would pass that struct in memory, LLVM splits it across registers. Following
//! clang, aggregates are therefore lowered explicitly: small ones are reinterpreted as the scalar
//! registers they occupy, larger ones go through memory (`byval` arguments, `sret` returns).
//!
//! Implemented for x86-64 System V (Linux, macOS, BSD) and AArch64 (AAPCS64, including Apple's
//! variant); other targets reject aggregates passed by value.

use crate::ir::{Program, Type, TypeId};

/// The C calling convention code is generated for.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Target {
    /// x86-64 System V.
    X86_64,
    /// AArch64 AAPCS64; `apple`: Apple's variant, where narrow integers are extended by the
    /// caller.
    Aarch64 { apple: bool },
    /// Any other target: scalars only.
    Other,
}

impl Target {
    /// The target this compiler runs on.
    pub fn host() -> Target {
        if cfg!(target_arch = "x86_64") {
            Target::X86_64
        } else if cfg!(target_arch = "aarch64") {
            Target::Aarch64 {
                apple: cfg!(target_vendor = "apple"),
            }
        } else {
            Target::Other
        }
    }

    /// The LLVM target triple, which every module names. LLVM gets the data layout from it, and
    /// without one `opt` assumes a layout of its own, where `i64` aligns to 4 bytes, so optimized
    /// code would disagree with the code generator about where fields are.
    pub fn triple(self) -> Option<&'static str> {
        match self {
            Target::X86_64 => Some("x86_64-unknown-linux-gnu"),
            Target::Aarch64 { apple: false } => Some("aarch64-unknown-linux-gnu"),
            Target::Aarch64 { apple: true } => Some("arm64-apple-macosx"),
            Target::Other => None,
        }
    }
}

/// How one argument or return value crosses the C ABI.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CAbi {
    /// Passed as its own LLVM type, with a `zeroext` / `signext` attribute for integers narrower
    /// than 32 bits.
    Direct { ext: Option<&'static str> },
    /// An aggregate passed in registers: its bytes reinterpreted as these LLVM types, one per
    /// eightbyte (`i64`, `i32`, `double`, `<2 x float>`, ...; on AArch64 a single `i64`,
    /// `[2 x i64]`, `[3 x float]`, ...).
    Coerced(Vec<String>),
    /// An aggregate passed in memory: a `byval` pointer argument, or an `sret` pointer for a
    /// return value.
    Indirect,
    /// An aggregate argument passed as a plain pointer to a copy the caller makes (AArch64,
    /// larger than 16 bytes).
    ByRef,
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
            .any(|a| matches!(a, CAbi::Coerced(_) | CAbi::Indirect | CAbi::ByRef))
    }
}

/// Register class of an eightbyte (x86-64 System V §3.2.3).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Class {
    Integer,
    Sse,
}

/// A scalar inside an aggregate: byte offset, size, class, whether it is an `f32`, and whether
/// it is a SIMD vector lane.
struct Scalar {
    offset: u64,
    size: u64,
    class: Class,
    is_f32: bool,
    vector: bool,
}

/// Classifies a full signature for `target`.
pub fn fn_abi(
    program: &Program,
    target: Target,
    args: &[TypeId],
    ret: TypeId,
) -> Result<FnAbi, String> {
    match target {
        Target::X86_64 => fn_abi_x86_64(program, args, ret),
        Target::Aarch64 { apple } => {
            // AAPCS64 has no per-argument fallback to memory: LLVM spills a whole register
            // block (`[2 x i64]`, `[3 x float]`) to the stack as the C compiler does.
            let mut arg_abis = Vec::with_capacity(args.len());
            for &arg in args {
                arg_abis.push(classify_aarch64(program, arg, apple, false)?);
            }
            Ok(FnAbi {
                ret: classify_aarch64(program, ret, apple, true)?,
                args: arg_abis,
            })
        }
        Target::Other => {
            let mut arg_abis = Vec::with_capacity(args.len());
            for &arg in args {
                arg_abis.push(classify_scalar(program, arg, target)?);
            }
            Ok(FnAbi {
                ret: classify_scalar(program, ret, target)?,
                args: arg_abis,
            })
        }
    }
}

/// Whether `ty` crosses the C ABI as an aggregate (a struct, union, or array, except a union
/// stored as its payload through a niche).
fn is_aggregate(program: &Program, ty: TypeId) -> bool {
    matches!(
        program.types[ty.0 as usize],
        Type::Struct(_) | Type::Overlay(_) | Type::Union { .. } | Type::Array { .. }
    ) && program.union_niche(ty).is_none()
}

/// The ABI of a non-aggregate (or zero-sized) value; aggregates are rejected on targets
/// without an aggregate classification.
fn classify_scalar(program: &Program, ty: TypeId, target: Target) -> Result<CAbi, String> {
    let (size, _) = program.type_size_align(ty)?;
    if size == 0 {
        return Ok(CAbi::Ignore);
    }
    if is_aggregate(program, ty) {
        return Err(format!(
            "Passing the aggregate '{}' by value across the C ABI is only implemented for x86-64 and AArch64; pass a pointer instead",
            program.type_label(ty)
        ));
    }
    let extends = !matches!(target, Target::Aarch64 { apple: false });
    Ok(CAbi::Direct {
        ext: if extends {
            extension(&program.types[ty.0 as usize], program)
        } else {
            None
        },
    })
}

/// AArch64 (AAPCS64 §6.8.2): a homogeneous floating-point aggregate (1-4 members, all `f32` or
/// all `f64`) goes in consecutive FP registers; any other aggregate of up to 16 bytes in one or
/// two integer registers; a larger one by reference (an argument) or through `x8` (a return).
fn classify_aarch64(
    program: &Program,
    ty: TypeId,
    apple: bool,
    is_ret: bool,
) -> Result<CAbi, String> {
    let (size, align) = program.type_size_align(ty)?;
    if size == 0 || !is_aggregate(program, ty) {
        return classify_scalar(program, ty, Target::Aarch64 { apple });
    }
    let mut scalars = Vec::new();
    collect_scalars(program, ty, 0, &mut scalars)?;
    if scalars.iter().any(|s| s.vector) {
        return Err(format!(
            "Passing the aggregate '{}', which holds SIMD vectors, by value across the AArch64 C ABI is not implemented; pass a pointer instead",
            program.type_label(ty)
        ));
    }
    if let Some((elem, count)) = homogeneous_float(&scalars, size) {
        return Ok(CAbi::Coerced(vec![format!("[{count} x {elem}]")]));
    }
    if size > 16 {
        return Ok(if is_ret { CAbi::Indirect } else { CAbi::ByRef });
    }
    let piece = if align == 16 {
        "i128".to_string()
    } else if size > 8 {
        "[2 x i64]".to_string()
    } else if is_ret {
        format!("i{}", size * 8)
    } else {
        "i64".to_string()
    };
    Ok(CAbi::Coerced(vec![piece]))
}

/// The element type and count when the scalar leaves of an aggregate of `size` bytes form a
/// homogeneous floating-point aggregate: every leaf the same float type, filling 1-4 slots.
fn homogeneous_float(scalars: &[Scalar], size: u64) -> Option<(&'static str, u64)> {
    let first = scalars.first()?;
    if first.class != Class::Sse {
        return None;
    }
    let es = first.size;
    if scalars
        .iter()
        .any(|s| s.class != Class::Sse || s.size != es || !s.offset.is_multiple_of(es))
    {
        return None;
    }
    let count = size / es;
    if !size.is_multiple_of(es) || !(1..=4).contains(&count) {
        return None;
    }
    // Overlapping leaves (an overlay's fields) count once; padding disqualifies.
    if (0..count).any(|k| !scalars.iter().any(|s| s.offset == k * es)) {
        return None;
    }
    Some((if es == 4 { "float" } else { "double" }, count))
}

/// x86-64 System V: classifies a full signature, falling back to memory for an aggregate that
/// no longer fits in the remaining registers (6 integer, 8 SSE), as the C compiler does.
fn fn_abi_x86_64(program: &Program, args: &[TypeId], ret: TypeId) -> Result<FnAbi, String> {
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

/// x86-64 System V: classifies one value in isolation (no register accounting).
fn classify(program: &Program, ty: TypeId) -> Result<CAbi, String> {
    let (size, _) = program.type_size_align(ty)?;
    if size == 0 || !is_aggregate(program, ty) {
        return classify_scalar(program, ty, Target::X86_64);
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
                vector: false,
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
                    vector: true,
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
                vector: false,
            });
        }
    }
    Ok(())
}
