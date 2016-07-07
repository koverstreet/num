use std::mem;
use std::cmp::min;

pub type BigDigit = usize;
pub use ::std::usize::MAX;
pub const ZERO_BIG_DIGIT: BigDigit = 0;

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

    // First apply borrow from previous subtract:
    let d1 = a.wrapping_sub(*borrow);
    *borrow = 0;

    // If we wrapped, borrow again:
    *borrow += (d1 > a) as BigDigit;

    // Since borrow was at most one, if we wrapped and borrowed again, a was
    // 0 and d1 is now big_digit::MAX.
    //
    // If borrow is nonzero, d1 is big_digit::MAX and subtracting b cannot borrow again - we will
    // always return with borrow at most one:

    let d2 = d1.wrapping_sub(b);
    *borrow += (d2 > d1) as BigDigit;

    d2
}

#[inline]
pub fn mul_with_carry(a: BigDigit, b: BigDigit, carry: &mut BigDigit) -> BigDigit {
    let halfbits    = BITS() / 2;
    let mask        = (1 << halfbits) - 1;

    let (a1, a0) = (a >> halfbits, a & mask);
    let (b1, b0) = (b >> halfbits, b & mask);

    let m1 = a0 * b1;
    let m2 = a1 * b0;

    let mut lo = adc(a0 * b0, 0, carry);

    lo = adc_no_flush(lo, m1 << halfbits, carry);
    lo = adc_no_flush(lo, m2 << halfbits, carry);

    *carry += a1 * b1
        + (m1 >> halfbits)
        + (m2 >> halfbits);
    lo
}

#[inline]
pub fn mac_with_carry(a: BigDigit, b: BigDigit, c: BigDigit, carry: &mut BigDigit) -> BigDigit {
    adc_no_flush(a, mul_with_carry(b, c, carry), carry)
}

#[inline]
pub fn div_wide(mut u1: BigDigit, mut u0: BigDigit, d: BigDigit) -> (BigDigit, BigDigit) {
    if u1 == 0 {
        return (u0 / d, u0 % d);
    }

    let mut offset = BITS();
    let mut q = 0;

    while offset != 0 {
        let mut shift = min(u1.leading_zeros() as usize,
                        min(offset, BITS() - 1));
        let mut borrow = 0;

        if shift == 0 {
            shift = 1;
            borrow = 1;
        }

        u1 <<= shift;
        u1 |= u0 >> (BITS() - shift);
        u0 <<= shift;
        offset -= shift;

        q += (u1 / d) << offset;
        u1 %= d;

        if borrow != 0 {
            q += 1 << offset;
            u1 = u1.wrapping_sub(d);
        }
    }

    (q, u1)
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
