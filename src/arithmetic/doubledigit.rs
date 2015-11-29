use std::mem;

pub type BigDigit = u32;
pub use ::std::u32::MAX;

#[allow(non_snake_case)]
#[inline]
pub fn BITS() -> usize {
    mem::size_of::<BigDigit>() * 8
}

/// A `DoubleBigDigit` is the internal type used to do the computations.  Its
/// size is the double of the size of `BigDigit`.
type DoubleBigDigit = u64;

const BASE: DoubleBigDigit = 1 << 32;
const LO_MASK: DoubleBigDigit = MAX as DoubleBigDigit;

#[inline]
fn get_hi(n: DoubleBigDigit) -> BigDigit { (n >> BITS()) as BigDigit }
#[inline]
fn get_lo(n: DoubleBigDigit) -> BigDigit { (n & LO_MASK) as BigDigit }

/// Split one `DoubleBigDigit` into two `BigDigit`s.
#[inline]
fn from_doublebigdigit(n: DoubleBigDigit) -> (BigDigit, BigDigit) {
    (get_hi(n), get_lo(n))
}

/// Join two `BigDigit`s into one `DoubleBigDigit`
#[inline]
fn to_doublebigdigit(hi: BigDigit, lo: BigDigit) -> DoubleBigDigit {
    (lo as DoubleBigDigit) | ((hi as DoubleBigDigit) << BITS())
}

/*
 * Generic functions for add/subtract/multiply with carry/borrow:
 */

// Add with carry:
#[inline]
pub fn adc(a: BigDigit, b: BigDigit, carry: &mut BigDigit) -> BigDigit {
    let (hi, lo) = from_doublebigdigit(
        (a as DoubleBigDigit) +
        (b as DoubleBigDigit) +
        (*carry as DoubleBigDigit));

    *carry = hi;
    lo
}

// Subtract with borrow:
#[inline]
pub fn sbb(a: BigDigit, b: BigDigit, borrow: &mut BigDigit) -> BigDigit {
    let (hi, lo) = from_doublebigdigit(BASE
        + (a as DoubleBigDigit)
        - (b as DoubleBigDigit)
        - (*borrow as DoubleBigDigit));
    /*
       hi * (base) + lo == 1*(base) + ai - bi - borrow
       => ai - bi - borrow < 0 <=> hi == 0
       */
    *borrow = if hi == 0 { 1 } else { 0 };
    lo
}

#[inline]
pub fn mul_with_carry(a: BigDigit, b: BigDigit, carry: &mut BigDigit) -> BigDigit {
    let (hi, lo) = from_doublebigdigit(
        (a as DoubleBigDigit) * (b as DoubleBigDigit) + (*carry as DoubleBigDigit)
        );
    *carry = hi;
    lo
}

#[inline]
pub fn mac_with_carry(a: BigDigit, b: BigDigit, c: BigDigit, carry: &mut BigDigit) -> BigDigit {
    let (hi, lo) = from_doublebigdigit(
        (a as DoubleBigDigit) +
        (b as DoubleBigDigit) * (c as DoubleBigDigit) +
        (*carry as DoubleBigDigit));
    *carry = hi;
    lo
}

#[inline]
pub fn div_wide(hi: BigDigit, lo: BigDigit, divisor: BigDigit) -> (BigDigit, BigDigit) {
    debug_assert!(hi < divisor);

    let lhs = to_doublebigdigit(hi, lo);
    let rhs = divisor as DoubleBigDigit;
    ((lhs / rhs) as BigDigit, (lhs % rhs) as BigDigit)
}
