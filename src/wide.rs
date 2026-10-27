//! Fixed-width two's-complement integers for compile-time constants wider than `i128`.
//!
//! `Wide` holds 1088 bits: enough for any `i1`..`i512` / `u1`..`u512` value and for the exact
//! (un-truncated) result of adding, subtracting, or multiplying two such values, so overflow can be
//! detected before wrapping to the declared width.

use std::cmp::Ordering;
use std::fmt;

use crate::ir::BinOp;

const LIMBS: usize = 17;
const TOTAL_BITS: u32 = (LIMBS as u32) * 64;

/// A two's-complement integer with `LIMBS` little-endian 64-bit limbs.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Wide([u64; LIMBS]);

impl Wide {
    pub const ZERO: Wide = Wide([0; LIMBS]);

    pub fn from_i128(v: i128) -> Self {
        let fill = if v < 0 { u64::MAX } else { 0 };
        let mut limbs = [fill; LIMBS];
        limbs[0] = v as u64;
        limbs[1] = (v >> 64) as u64;
        Wide(limbs)
    }

    /// The value as `i128`, if it fits.
    pub fn to_i128(&self) -> Option<i128> {
        let lo = u128::from(self.0[0]) | (u128::from(self.0[1]) << 64);
        let v = lo as i128;
        (Wide::from_i128(v) == *self).then_some(v)
    }

    /// Little-endian 64-bit words of the low `n * 64` bits.
    pub fn low_words(&self, n: usize) -> Vec<u64> {
        self.0[..n.min(LIMBS)].to_vec()
    }

    pub fn is_negative(&self) -> bool {
        self.0[LIMBS - 1] >> 63 == 1
    }

    pub fn is_zero(&self) -> bool {
        self.0.iter().all(|&l| l == 0)
    }

    /// Parses a non-negative literal in `radix` (2, 8, 10, or 16); `None` if it does not fit.
    pub fn from_str_radix(digits: &str, radix: u32) -> Option<Self> {
        let mut acc = Wide::ZERO;
        let r = Wide::from_i128(i128::from(radix));
        for c in digits.chars() {
            let d = c.to_digit(radix)?;
            acc = acc.checked_mul_small(&r)?.add(&Wide::from_i128(i128::from(d)));
            if acc.is_negative() {
                return None;
            }
        }
        Some(acc)
    }

    fn checked_mul_small(&self, rhs: &Self) -> Option<Self> {
        let p = self.mul(rhs);
        (!p.is_negative()).then_some(p)
    }

    pub fn add(&self, rhs: &Self) -> Self {
        let mut out = [0u64; LIMBS];
        let mut carry = false;
        for (i, o) in out.iter_mut().enumerate() {
            let (s1, c1) = self.0[i].overflowing_add(rhs.0[i]);
            let (s2, c2) = s1.overflowing_add(u64::from(carry));
            *o = s2;
            carry = c1 || c2;
        }
        Wide(out)
    }

    pub fn not(&self) -> Self {
        let mut out = self.0;
        for l in &mut out {
            *l = !*l;
        }
        Wide(out)
    }

    pub fn neg(&self) -> Self {
        self.not().add(&Wide::from_i128(1))
    }

    pub fn sub(&self, rhs: &Self) -> Self {
        self.add(&rhs.neg())
    }

    pub fn abs(&self) -> Self {
        if self.is_negative() { self.neg() } else { *self }
    }

    /// Product truncated to `TOTAL_BITS` (exact for operands within `i544`).
    pub fn mul(&self, rhs: &Self) -> Self {
        let neg = self.is_negative() != rhs.is_negative();
        let (a, b) = (self.abs(), rhs.abs());
        let mut out = [0u64; LIMBS];
        for i in 0..LIMBS {
            let mut carry: u128 = 0;
            for j in 0..(LIMBS - i) {
                let cur = u128::from(out[i + j]) + u128::from(a.0[i]) * u128::from(b.0[j]) + carry;
                out[i + j] = cur as u64;
                carry = cur >> 64;
            }
        }
        let p = Wide(out);
        if neg { p.neg() } else { p }
    }

    fn bit(&self, i: u32) -> bool {
        (self.0[(i / 64) as usize] >> (i % 64)) & 1 == 1
    }

    fn set_bit(&mut self, i: u32) {
        self.0[(i / 64) as usize] |= 1 << (i % 64);
    }

    fn ucmp(&self, rhs: &Self) -> Ordering {
        for i in (0..LIMBS).rev() {
            match self.0[i].cmp(&rhs.0[i]) {
                Ordering::Equal => {}
                o => return o,
            }
        }
        Ordering::Equal
    }

    /// Truncating division and remainder (the remainder takes the dividend's sign); `None` on a
    /// zero divisor.
    pub fn div_rem(&self, rhs: &Self) -> Option<(Self, Self)> {
        if rhs.is_zero() {
            return None;
        }
        let (n, d) = (self.abs(), rhs.abs());
        let mut q = Wide::ZERO;
        let mut r = Wide::ZERO;
        for i in (0..TOTAL_BITS).rev() {
            r = r.shl(1);
            if n.bit(i) {
                r.0[0] |= 1;
            }
            if r.ucmp(&d) != Ordering::Less {
                r = r.sub(&d);
                q.set_bit(i);
            }
        }
        let q = if self.is_negative() != rhs.is_negative() { q.neg() } else { q };
        let r = if self.is_negative() { r.neg() } else { r };
        Some((q, r))
    }

    pub fn shl(&self, n: u32) -> Self {
        if n >= TOTAL_BITS {
            return Wide::ZERO;
        }
        let (limb_shift, bit_shift) = ((n / 64) as usize, n % 64);
        let mut out = [0u64; LIMBS];
        for i in (limb_shift..LIMBS).rev() {
            let src = i - limb_shift;
            out[i] = self.0[src] << bit_shift;
            if bit_shift > 0 && src > 0 {
                out[i] |= self.0[src - 1] >> (64 - bit_shift);
            }
        }
        Wide(out)
    }

    /// Arithmetic (sign-propagating) right shift.
    pub fn shr(&self, n: u32) -> Self {
        let fill = if self.is_negative() { u64::MAX } else { 0 };
        if n >= TOTAL_BITS {
            return Wide([fill; LIMBS]);
        }
        let (limb_shift, bit_shift) = ((n / 64) as usize, n % 64);
        let mut out = [fill; LIMBS];
        for (i, o) in out.iter_mut().enumerate().take(LIMBS - limb_shift) {
            let src = i + limb_shift;
            let hi = if src + 1 < LIMBS { self.0[src + 1] } else { fill };
            *o = if bit_shift == 0 {
                self.0[src]
            } else {
                (self.0[src] >> bit_shift) | (hi << (64 - bit_shift))
            };
        }
        Wide(out)
    }

    pub fn bitand(&self, rhs: &Self) -> Self {
        let mut out = self.0;
        for (o, r) in out.iter_mut().zip(rhs.0) {
            *o &= r;
        }
        Wide(out)
    }

    pub fn bitor(&self, rhs: &Self) -> Self {
        let mut out = self.0;
        for (o, r) in out.iter_mut().zip(rhs.0) {
            *o |= r;
        }
        Wide(out)
    }

    pub fn bitxor(&self, rhs: &Self) -> Self {
        let mut out = self.0;
        for (o, r) in out.iter_mut().zip(rhs.0) {
            *o ^= r;
        }
        Wide(out)
    }

    /// Wraps to an `bits`-wide integer: keeps the low `bits` bits, then sign- or zero-extends.
    pub fn wrap(&self, bits: u16, signed: bool) -> Self {
        let bits = u32::from(bits).min(TOTAL_BITS);
        let up = TOTAL_BITS - bits;
        let shifted = self.shl(up);
        if signed {
            shifted.shr(up)
        } else {
            // Logical right shift: clear the sign fill introduced by `shr`.
            let s = shifted.shr(up);
            s.bitand(&Wide::mask(bits))
        }
    }

    /// `2^bits - 1`.
    fn mask(bits: u32) -> Self {
        Wide::from_i128(1).shl(bits).sub(&Wide::from_i128(1))
    }

    /// Smallest value of an `bits`-wide integer.
    pub fn min_value(bits: u16, signed: bool) -> Self {
        if signed {
            Wide::from_i128(1).shl(u32::from(bits) - 1).neg()
        } else {
            Wide::ZERO
        }
    }

    /// Largest value of an `bits`-wide integer.
    pub fn max_value(bits: u16, signed: bool) -> Self {
        if signed {
            Wide::mask(u32::from(bits) - 1)
        } else {
            Wide::mask(u32::from(bits))
        }
    }

    /// Whether the value is representable in an `bits`-wide integer.
    pub fn fits(&self, bits: u16, signed: bool) -> bool {
        *self >= Wide::min_value(bits, signed) && *self <= Wide::max_value(bits, signed)
    }
}

/// Result of an integer binary operator: an integer, or a boolean for comparisons.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinResult {
    Int(Wide),
    Bool(bool),
}

/// Source spelling of a binary operator, for diagnostics.
pub fn op_symbol(op: BinOp) -> &'static str {
    match op {
        BinOp::Add => "+",
        BinOp::Sub => "-",
        BinOp::Mul => "*",
        BinOp::AddWrap => "+%",
        BinOp::SubWrap => "-%",
        BinOp::MulWrap => "*%",
        BinOp::AddSat => "+|",
        BinOp::SubSat => "-|",
        BinOp::MulSat => "*|",
        BinOp::AddUnchecked => "@add_unchecked",
        BinOp::SubUnchecked => "@sub_unchecked",
        BinOp::MulUnchecked => "@mul_unchecked",
        BinOp::Div => "/",
        BinOp::Rem => "%",
        BinOp::BitAnd => "&",
        BinOp::BitOr => "|",
        BinOp::BitXor => "^",
        BinOp::Shl => "<<",
        BinOp::Shr => ">>",
        BinOp::Eq => "==",
        BinOp::Ne => "!=",
        BinOp::Lt => "<",
        BinOp::Le => "<=",
        BinOp::Gt => ">",
        BinOp::Ge => ">=",
        BinOp::AddChecked => "+?",
        BinOp::SubChecked => "-?",
        BinOp::MulChecked => "*?",
    }
}

/// Applies an integer binary operator with its runtime semantics for a `bits`-wide integer:
/// checked `+ - *` reject overflow, wrapping operators wrap, saturating operators clamp, division
/// and remainder reject zero divisors and `MIN / -1`, and shift amounts must lie in `0..bits`.
/// Operands are expected to be in range for the type.
pub fn apply_binop(
    op: BinOp,
    l: &Wide,
    r: &Wide,
    bits: u16,
    signed: bool,
) -> Result<BinResult, String> {
    let checked = |res: Wide| -> Result<BinResult, String> {
        if res.fits(bits, signed) {
            Ok(BinResult::Int(res))
        } else {
            Err(format!("integer overflow: {l} {} {r} = {res}", op_symbol(op)))
        }
    };
    let shift_amount = || -> Result<u32, String> {
        match r.to_i128() {
            Some(n) if n >= 0 && n < i128::from(bits) => Ok(n as u32),
            _ => Err(format!("shift amount {r} is out of range (0..{bits})")),
        }
    };
    let clamp = |res: Wide| {
        BinResult::Int(
            res.max(Wide::min_value(bits, signed))
                .min(Wide::max_value(bits, signed)),
        )
    };
    let wrapped = |res: Wide| BinResult::Int(res.wrap(bits, signed));
    Ok(match op {
        BinOp::Add | BinOp::AddUnchecked => return checked(l.add(r)),
        BinOp::Sub | BinOp::SubUnchecked => return checked(l.sub(r)),
        BinOp::Mul | BinOp::MulUnchecked => return checked(l.mul(r)),
        BinOp::AddWrap => wrapped(l.add(r)),
        BinOp::SubWrap => wrapped(l.sub(r)),
        BinOp::MulWrap => wrapped(l.mul(r)),
        BinOp::AddSat => clamp(l.add(r)),
        BinOp::SubSat => clamp(l.sub(r)),
        BinOp::MulSat => clamp(l.mul(r)),
        BinOp::Div | BinOp::Rem => {
            let Some((q, rem)) = l.div_rem(r) else {
                return Err(format!(
                    "{} by zero: {l} {} {r}",
                    if op == BinOp::Div { "division" } else { "remainder" },
                    op_symbol(op)
                ));
            };
            // `MIN / -1` overflows; `MIN % -1` is rejected with it, as at runtime.
            checked(q)?;
            BinResult::Int(if op == BinOp::Div { q } else { rem })
        }
        BinOp::BitAnd => wrapped(l.bitand(r)),
        BinOp::BitOr => wrapped(l.bitor(r)),
        BinOp::BitXor => wrapped(l.bitxor(r)),
        BinOp::Shl => wrapped(l.shl(shift_amount()?)),
        // An in-range unsigned operand is non-negative, so the arithmetic shift is logical.
        BinOp::Shr => BinResult::Int(l.wrap(bits, signed).shr(shift_amount()?)),
        BinOp::Eq => BinResult::Bool(l == r),
        BinOp::Ne => BinResult::Bool(l != r),
        BinOp::Lt => BinResult::Bool(l < r),
        BinOp::Le => BinResult::Bool(l <= r),
        BinOp::Gt => BinResult::Bool(l > r),
        BinOp::Ge => BinResult::Bool(l >= r),
        BinOp::AddChecked | BinOp::SubChecked | BinOp::MulChecked => {
            return Err(format!(
                "fallible operator '{op}' produces an optional and is evaluated separately"
            ));
        }
    })
}

impl PartialOrd for Wide {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Wide {
    /// Signed comparison.
    fn cmp(&self, other: &Self) -> Ordering {
        match (self.is_negative(), other.is_negative()) {
            (true, false) => Ordering::Less,
            (false, true) => Ordering::Greater,
            _ => self.ucmp(other),
        }
    }
}

impl fmt::Display for Wide {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if let Some(v) = self.to_i128() {
            return write!(f, "{v}");
        }
        let neg = self.is_negative();
        let mut n = self.abs();
        let ten = Wide::from_i128(10);
        let mut digits = Vec::new();
        while !n.is_zero() {
            let (q, r) = n.div_rem(&ten).expect("nonzero divisor");
            digits.push(char::from(b'0' + r.to_i128().unwrap_or(0) as u8));
            n = q;
        }
        if neg {
            write!(f, "-")?;
        }
        write!(f, "{}", digits.iter().rev().collect::<String>())
    }
}

#[cfg(test)]
mod tests {
    use super::Wide;

    fn w(v: i128) -> Wide {
        Wide::from_i128(v)
    }

    #[test]
    fn arithmetic_matches_i128_where_it_fits() {
        for &(a, b) in &[(7i128, 3i128), (-7, 3), (7, -3), (-7, -3), (i128::MAX / 3, 2)] {
            assert_eq!(w(a).add(&w(b)).to_i128(), Some(a + b));
            assert_eq!(w(a).sub(&w(b)).to_i128(), Some(a - b));
            assert_eq!(w(a).mul(&w(b)).to_i128(), Some(a * b));
            let (q, r) = w(a).div_rem(&w(b)).unwrap();
            assert_eq!((q.to_i128(), r.to_i128()), (Some(a / b), Some(a % b)));
        }
        assert_eq!(w(-1).shr(5).to_i128(), Some(-1));
        assert_eq!(w(1).shl(100).shr(99).to_i128(), Some(2));
    }

    #[test]
    fn wide_values_parse_print_and_wrap() {
        let digest = "9f86d081884c7d659a2feaa0c55ad015a3bf4f1b2b0b822cd15d6c15b0f00a08";
        let v = Wide::from_str_radix(digest, 16).unwrap();
        assert_eq!(v.to_i128(), None);
        assert_eq!(v.shr(248).to_i128(), Some(0x9f));
        assert_eq!(v.low_words(4)[0], 0xd15d6c15b0f00a08);
        assert_eq!(v.low_words(4)[3], 0x9f86d081884c7d65);
        let u128_max = Wide::from_str_radix("340282366920938463463374607431768211455", 10).unwrap();
        assert_eq!(u128_max.to_string(), "340282366920938463463374607431768211455");
        assert!(u128_max.fits(128, false) && !u128_max.fits(128, true));
        assert_eq!(u128_max.wrap(128, true).to_i128(), Some(-1));
        assert_eq!(w(-1).wrap(8, false).to_i128(), Some(255));
        assert_eq!(w(300).wrap(8, false).to_i128(), Some(44));
        let big = w(1).shl(511);
        assert!(big.fits(512, false) && !big.fits(512, true));
        assert!(!big.mul(&w(2)).fits(512, false));
        assert!(!Wide::min_value(512, true).neg().fits(512, true));
    }
}
