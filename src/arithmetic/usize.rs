use std::mem;
use std::cmp::min;

pub type BigDigit = usize;
pub use ::std::usize::MAX;

#[allow(non_snake_case)]
#[inline]
pub fn BITS() -> usize {
    mem::size_of::<BigDigit>() * 8
}

#[inline]
fn adc_no_flush(a: BigDigit, b: BigDigit, carry: &mut BigDigit) -> BigDigit {
    let ret = a.wrapping_add(b);

    if ret < a {
        *carry += 1;
    }

    ret
}

// Add with carry:
#[inline]
pub fn adc(a: BigDigit, b: BigDigit, carry: &mut BigDigit) -> BigDigit {
    debug_assert!(*carry <= 1 || b == 0);

    let ret = a.wrapping_add(*carry);

    *carry = if ret < a { 1 } else { 0 };

    adc_no_flush(ret, b, carry)
}

// Subtract with borrow:
#[inline]
pub fn sbb(a: BigDigit, b: BigDigit, borrow: &mut BigDigit) -> BigDigit {
    debug_assert!(*borrow <= 1);

    let d1 = a.wrapping_sub(*borrow);

    *borrow = if d1 > a { 1 } else { 0 };

    let d2 = d1.wrapping_sub(b);

    if d2 > d1 {
        *borrow += 1;
    }

    d2
}

#[inline]
pub fn mul_with_carry(a: BigDigit, b: BigDigit, carry: &mut BigDigit) -> BigDigit {
    let halfbits = BITS() / 2;

    let (ahi, alo) = (a >> halfbits, a & ((1 << halfbits) - 1));
    let (bhi, blo) = (b >> halfbits, b & ((1 << halfbits) - 1));

    let m1 = alo * bhi;
    let m2 = ahi * blo;

    let mut lo = adc(alo * blo, 0, carry);

    lo = adc_no_flush(lo, m1 << halfbits, carry);
    lo = adc_no_flush(lo, m2 << halfbits, carry);

    *carry += ahi * bhi
        + (m1 >> halfbits)
        + (m2 >> halfbits);
    lo
}

#[inline]
pub fn mac_with_carry(a: BigDigit, b: BigDigit, c: BigDigit, carry: &mut BigDigit) -> BigDigit {
    adc_no_flush(a, mul_with_carry(b, c, carry), carry)
}

/// Divide a two digit numerator by a one digit divisor, returns quotient and remainder:
///
/// Note: the caller must ensure that both the quotient and remainder will fit into a single digit.
/// This is _not_ true for an arbitrary numerator/denominator.
///
/// (This function also matches what the x86 divide instruction does).
#[inline]
pub fn div_wide(mut hi: BigDigit, mut lo: BigDigit, divisor: BigDigit) -> (BigDigit, BigDigit) {
    debug_assert!(hi < divisor);

    let mut bits_remaining = BITS();
    let mut quotient = 0;
    let mut borrow = 0;

    while bits_remaining != 0 {
        let mut shift = min(hi.leading_zeros() as usize,
                        min(bits_remaining, BITS() - 1));

        if shift == 0 {
            shift = 1;
            borrow = 1;
        }

        hi <<= shift;
        hi  |= lo >> (BITS() - shift);
        lo <<= shift;
        bits_remaining -= shift;

        quotient += (hi / divisor) << bits_remaining;
        hi %= divisor;

        if borrow != 0 {
            quotient += 1 << bits_remaining;
            hi = hi.wrapping_sub(divisor);
            borrow = 0;
        }
    }

    (quotient, hi)
}

#[test]
fn test_div_wide() {
    use rand::{SeedableRng, StdRng, Rng};

    let seed: &[_] = &[1, 2, 3, 4];
    let mut rng: StdRng = SeedableRng::from_seed(seed);

    for _ in 0..1000 {
        let x: BigDigit = rng.gen();
        let y: BigDigit = rng.gen();

        assert_eq!(div_wide(0, x, y), ((x / y), (x % y)));
    }
}
