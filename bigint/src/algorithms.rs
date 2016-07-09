use std::borrow::Cow;
use std::cmp;
use std::cmp::Ordering::{self, Less, Greater, Equal};
use std::iter::repeat;
use std::mem;
use traits;
use traits::{Zero, One};

use biguint::BigUint;

use bigint::Sign;
use bigint::Sign::{Minus, NoSign, Plus};

#[allow(non_snake_case)]
pub mod big_digit {
    /// A `BigDigit` is a `BigUint`'s composing element.
    pub type BigDigit = u32;

    /// A `DoubleBigDigit` is the internal type used to do the computations.  Its
    /// size is the double of the size of `BigDigit`.
    pub type DoubleBigDigit = u64;

    pub const ZERO_BIG_DIGIT: BigDigit = 0;

    // `DoubleBigDigit` size dependent
    pub const BITS: usize = 32;
    pub use ::std::u32::MAX;

    pub const BASE: DoubleBigDigit = 1 << BITS;
    const LO_MASK: DoubleBigDigit = (-1i32 as DoubleBigDigit) >> BITS;

    #[inline]
    fn get_hi(n: DoubleBigDigit) -> BigDigit {
        (n >> BITS) as BigDigit
    }
    #[inline]
    fn get_lo(n: DoubleBigDigit) -> BigDigit {
        (n & LO_MASK) as BigDigit
    }

    /// Split one `DoubleBigDigit` into two `BigDigit`s.
    #[inline]
    pub fn from_doublebigdigit(n: DoubleBigDigit) -> (BigDigit, BigDigit) {
        (get_hi(n), get_lo(n))
    }

    /// Join two `BigDigit`s into one `DoubleBigDigit`
    #[inline]
    pub fn to_doublebigdigit(hi: BigDigit, lo: BigDigit) -> DoubleBigDigit {
        (lo as DoubleBigDigit) | ((hi as DoubleBigDigit) << BITS)
    }
}

use big_digit::{BigDigit, DoubleBigDigit};

// Generic functions for add/subtract/multiply with carry/borrow:

// Add with carry:
#[inline]
fn adc(a: BigDigit, b: BigDigit, carry: &mut BigDigit) -> BigDigit {
    let (hi, lo) = big_digit::from_doublebigdigit((a as DoubleBigDigit) + (b as DoubleBigDigit) +
                                                  (*carry as DoubleBigDigit));

    *carry = hi;
    lo
}

// Subtract with borrow:
#[inline]
fn sbb(a: BigDigit, b: BigDigit, borrow: &mut BigDigit) -> BigDigit {
    let (hi, lo) = big_digit::from_doublebigdigit(big_digit::BASE + (a as DoubleBigDigit) -
                                                  (b as DoubleBigDigit) -
                                                  (*borrow as DoubleBigDigit));
    // hi * (base) + lo == 1*(base) + ai - bi - borrow
    // => ai - bi - borrow < 0 <=> hi == 0
    *borrow = (hi == 0) as BigDigit;
    lo
}

#[inline]
pub fn mac_with_carry(a: BigDigit, b: BigDigit, c: BigDigit, carry: &mut BigDigit) -> BigDigit {
    let (hi, lo) = big_digit::from_doublebigdigit((a as DoubleBigDigit) +
                                                  (b as DoubleBigDigit) * (c as DoubleBigDigit) +
                                                  (*carry as DoubleBigDigit));
    *carry = hi;
    lo
}

#[inline]
pub fn mul_with_carry(a: BigDigit, b: BigDigit, carry: &mut BigDigit) -> BigDigit {
    let (hi, lo) = big_digit::from_doublebigdigit((a as DoubleBigDigit) * (b as DoubleBigDigit) +
                                                  (*carry as DoubleBigDigit));

    *carry = hi;
    lo
}

/// Divide a two digit numerator by a one digit divisor, returns quotient and remainder:
///
/// Note: the caller must ensure that both the quotient and remainder will fit into a single digit.
/// This is _not_ true for an arbitrary numerator/denominator.
///
/// (This function also matches what the x86 divide instruction does).
#[inline]
fn div_wide(hi: BigDigit, lo: BigDigit, divisor: BigDigit) -> (BigDigit, BigDigit) {
    debug_assert!(hi < divisor);

    let lhs = big_digit::to_doublebigdigit(hi, lo);
    let rhs = divisor as DoubleBigDigit;
    ((lhs / rhs) as BigDigit, (lhs % rhs) as BigDigit)
}

pub fn div_rem_digit(mut a: BigUint, b: BigDigit) -> (BigUint, BigDigit) {
    let mut rem = 0;

    for d in a.data.iter_mut().rev() {
        let (q, r) = div_wide(rem, *d, b);
        *d = q;
        rem = r;
    }

    (a.normalize(), rem)
}

// Only for the Add impl:
#[must_use]
#[inline]
pub fn __add2(a: &mut [BigDigit], b: &[BigDigit]) -> BigDigit {
    debug_assert!(a.len() >= b.len());

    let mut carry = 0;
    let (a_lo, a_hi) = a.split_at_mut(b.len());

    for (a, b) in a_lo.iter_mut().zip(b) {
        *a = adc(*a, *b, &mut carry);
    }

    if carry != 0 {
        for a in a_hi {
            *a = adc(*a, 0, &mut carry);
            if carry == 0 { break }
        }
    }

    carry
}

/// /Two argument addition of raw slices:
/// a += b
///
/// The caller _must_ ensure that a is big enough to store the result - typically this means
/// resizing a to max(a.len(), b.len()) + 1, to fit a possible carry.
pub fn add2(a: &mut [BigDigit], b: &[BigDigit]) {
    let carry = __add2(a, b);

    debug_assert!(carry == 0);
}

pub fn sub2(a: &mut [BigDigit], b: &[BigDigit]) {
    let mut borrow = 0;

    let len = cmp::min(a.len(), b.len());
    let (a_lo, a_hi) = a.split_at_mut(len);
    let (b_lo, b_hi) = b.split_at(len);

    for (a, b) in a_lo.iter_mut().zip(b_lo) {
        *a = sbb(*a, *b, &mut borrow);
    }

    if borrow != 0 {
        for a in a_hi {
            *a = sbb(*a, 0, &mut borrow);
            if borrow == 0 { break }
        }
    }

    // note: we're _required_ to fail on underflow
    assert!(borrow == 0 && b_hi.iter().all(|x| *x == 0),
            "Cannot subtract b from a because b is larger than a.");
}

pub fn sub2rev(a: &[BigDigit], b: &mut [BigDigit]) {
    debug_assert!(b.len() >= a.len());

    let mut borrow = 0;

    let len = cmp::min(a.len(), b.len());
    let (a_lo, a_hi) = a.split_at(len);
    let (b_lo, b_hi) = b.split_at_mut(len);

    for (a, b) in a_lo.iter().zip(b_lo) {
        *b = sbb(*a, *b, &mut borrow);
    }

    assert!(a_hi.is_empty());

    // note: we're _required_ to fail on underflow
    assert!(borrow == 0 && b_hi.iter().all(|x| *x == 0),
            "Cannot subtract b from a because b is larger than a.");
}

pub fn sub_sign(a: &[BigDigit], b: &[BigDigit]) -> (Sign, BigUint) {
    // Normalize:
    let a = &a[..a.iter().rposition(|&x| x != 0).map_or(0, |i| i + 1)];
    let b = &b[..b.iter().rposition(|&x| x != 0).map_or(0, |i| i + 1)];

    match cmp_slice(a, b) {
        Greater => {
            let mut a = a.to_vec();
            sub2(&mut a, b);
            (Plus, BigUint::new(a))
        }
        Less => {
            let mut b = b.to_vec();
            sub2(&mut b, a);
            (Minus, BigUint::new(b))
        }
        _ => (NoSign, Zero::zero()),
    }
}

/// Three argument multiply accumulate:
/// acc += b * c
fn mac_digit(acc: &mut [BigDigit], b: &[BigDigit], c: BigDigit) {
    if c == 0 {
        return;
    }

    let mut b_iter = b.iter();
    let mut carry = 0;

    for ai in acc.iter_mut() {
        if let Some(bi) = b_iter.next() {
            *ai = mac_with_carry(*ai, *bi, c, &mut carry);
        } else if carry != 0 {
            *ai = mac_with_carry(*ai, 0, c, &mut carry);
        } else {
            break;
        }
    }

    assert!(carry == 0);
}

/// Three argument multiply accumulate:
/// acc += b * c
fn mac3(acc: &mut [BigDigit], b: &[BigDigit], c: &[BigDigit]) {
    let (x, y) = if b.len() < c.len() {
        (b, c)
    } else {
        (c, b)
    };

    // Karatsuba multiplication is slower than long multiplication for small x and y:
    //
    if x.len() <= 4 {
        for (i, xi) in x.iter().enumerate() {
            mac_digit(&mut acc[i..], y, *xi);
        }
    } else {
        /*
         * Karatsuba multiplication:
         *
         * The idea is that we break x and y up into two smaller numbers that each have about half
         * as many digits, like so (note that multiplying by b is just a shift):
         *
         * x = x0 + x1 * b
         * y = y0 + y1 * b
         *
         * With some algebra, we can compute x * y with three smaller products, where the inputs to
         * each of the smaller products have only about half as many digits as x and y:
         *
         * x * y = (x0 + x1 * b) * (y0 + y1 * b)
         *
         * x * y = x0 * y0
         *       + x0 * y1 * b
         *       + x1 * y0 * b
         *       + x1 * y1 * b^2
         *
         * Let p0 = x0 * y0 and p2 = x1 * y1:
         *
         * x * y = p0
         *       + (x0 * y1 + x1 * y0) * b
         *       + p2 * b^2
         *
         * The real trick is that middle term:
         *
         *         x0 * y1 + x1 * y0
         *
         *       = x0 * y1 + x1 * y0 - p0 + p0 - p2 + p2
         *
         *       = x0 * y1 + x1 * y0 - x0 * y0 - x1 * y1 + p0 + p2
         *
         * Now we complete the square:
         *
         *       = -(x0 * y0 - x0 * y1 - x1 * y0 + x1 * y1) + p0 + p2
         *
         *       = -((x1 - x0) * (y1 - y0)) + p0 + p2
         *
         * Let p1 = (x1 - x0) * (y1 - y0), and substitute back into our original formula:
         *
         * x * y = p0
         *       + (p0 + p2 - p1) * b
         *       + p2 * b^2
         *
         * Where the three intermediate products are:
         *
         * p0 = x0 * y0
         * p1 = (x1 - x0) * (y1 - y0)
         * p2 = x1 * y1
         *
         * In doing the computation, we take great care to avoid unnecessary temporary variables
         * (since creating a BigUint requires a heap allocation): thus, we rearrange the formula a
         * bit so we can use the same temporary variable for all the intermediate products:
         *
         * x * y = p2 * b^2 + p2 * b
         *       + p0 * b + p0
         *       - p1 * b
         *
         * The other trick we use is instead of doing explicit shifts, we slice acc at the
         * appropriate offset when doing the add.
         */

        /*
         * When x is smaller than y, it's significantly faster to pick b such that x is split in
         * half, not y:
         */
        let b = x.len() / 2;
        let (x0, x1) = x.split_at(b);
        let (y0, y1) = y.split_at(b);

        /*
         * We reuse the same BigUint for all the intermediate multiplies and have to size p
         * appropriately here: x1.len() >= x0.len and y1.len() >= y0.len():
         */
        let len = x1.len() + y1.len() + 1;
        let mut p = BigUint { data: vec![0; len] };

        // p2 = x1 * y1
        mac3(&mut p.data[..], x1, y1);

        // Not required, but the adds go faster if we drop any unneeded 0s from the end:
        p = p.normalize();

        add2(&mut acc[b..],        &p.data[..]);
        add2(&mut acc[b * 2..],    &p.data[..]);

        // Zero out p before the next multiply:
        p.data.truncate(0);
        p.data.extend(repeat(0).take(len));

        // p0 = x0 * y0
        mac3(&mut p.data[..], x0, y0);
        p = p.normalize();

        add2(&mut acc[..],         &p.data[..]);
        add2(&mut acc[b..],        &p.data[..]);

        // p1 = (x1 - x0) * (y1 - y0)
        // We do this one last, since it may be negative and acc can't ever be negative:
        let (j0_sign, j0) = sub_sign(x1, x0);
        let (j1_sign, j1) = sub_sign(y1, y0);

        match j0_sign * j1_sign {
            Plus    => {
                p.data.truncate(0);
                p.data.extend(repeat(0).take(len));

                mac3(&mut p.data[..], &j0.data[..], &j1.data[..]);
                p = p.normalize();

                sub2(&mut acc[b..], &p.data[..]);
            },
            Minus   => {
                mac3(&mut acc[b..], &j0.data[..], &j1.data[..]);
            },
            NoSign  => (),
        }
    }
}

pub fn mul3(x: &[BigDigit], y: &[BigDigit]) -> BigUint {
    let len = x.len() + y.len() + 1;
    let mut prod = BigUint { data: vec![0; len] };

    mac3(&mut prod.data[..], x, y);
    prod.normalize()
}

pub fn scalar_mul(a: &mut [BigDigit], b: BigDigit) -> BigDigit {
    let mut carry = 0;
    for a in a.iter_mut() {
        *a = mul_with_carry(*a, b, &mut carry);
    }
    carry
}

fn uadd(a: &[BigDigit; 2], b: &[BigDigit; 2]) -> [BigDigit; 2] {
    let mut carry = 0;
    let r0 = adc(a[0], b[0], &mut carry);
    let r1 = adc(a[1], b[1], &mut carry);
    debug_assert!(carry == 0);
    [r0, r1]
}

fn uadd_wrap(a: &[BigDigit; 2], b: &[BigDigit; 2]) -> [BigDigit; 2] {
    let mut carry = 0;
    let r0 = adc(a[0], b[0], &mut carry);
    let r1 = adc(a[1], b[1], &mut carry);
    [r0, r1]
}

fn usub(a: &[BigDigit; 2], b: &[BigDigit; 2]) -> [BigDigit; 2] {
    let mut borrow = 0;
    let r0 = sbb(a[0], b[0], &mut borrow);
    let r1 = sbb(a[1], b[1], &mut borrow);
    debug_assert!(borrow == 0);
    [r0, r1]
}

fn umul(a: BigDigit, b: BigDigit) -> [BigDigit; 2] {
    let mut r1 = 0;
    let r0 = mul_with_carry(a, b, &mut r1);
    [r0, r1]
}

/// Division by integer reciprocals, from the paper "Improved division by invariant integers", by
/// Niels Möller and Torbjörn Granlund,
///
/// Given a dividend d in base β, where d is normalized such that
///    β / 2 <= d < β
/// we can compute a "reciprocal" v such that
///    (β + v) * d = β^2 - k
///    1 <= k <= d

#[cfg(integer_inverse_by_division)]
fn integer_reciprocal(d: BigDigit) -> BigDigit {
    debug_assert!(d.leading_zeros() == 0);

    let (q, _) = div_wide(big_digit::MAX - d, big_digit::MAX, d);
    q
}

#[cfg(integer_inverse_by_newton_64)]
fn integer_reciprocal(d: BigDigit) -> BigDigit {
    debug_assert!(d.leading_zeros() == 0);

    const DIV_TABLE: [u16; 256] = [
        2045, 2037, 2029, 2021, 2013, 2005, 1998, 1990,
        1983, 1975, 1968, 1960, 1953, 1946, 1938, 1931,
        1924, 1917, 1910, 1903, 1896, 1889, 1883, 1876,
        1869, 1863, 1856, 1849, 1843, 1836, 1830, 1824,
        1817, 1811, 1805, 1799, 1792, 1786, 1780, 1774,
        1768, 1762, 1756, 1750, 1745, 1739, 1733, 1727,
        1722, 1716, 1710, 1705, 1699, 1694, 1688, 1683,
        1677, 1672, 1667, 1661, 1656, 1651, 1646, 1641,
        1636, 1630, 1625, 1620, 1615, 1610, 1605, 1600,
        1596, 1591, 1586, 1581, 1576, 1572, 1567, 1562,
        1558, 1553, 1548, 1544, 1539, 1535, 1530, 1526,
        1521, 1517, 1513, 1508, 1504, 1500, 1495, 1491,
        1487, 1483, 1478, 1474, 1470, 1466, 1462, 1458,
        1454, 1450, 1446, 1442, 1438, 1434, 1430, 1426,
        1422, 1418, 1414, 1411, 1407, 1403, 1399, 1396,
        1392, 1388, 1384, 1381, 1377, 1374, 1370, 1366,
        1363, 1359, 1356, 1352, 1349, 1345, 1342, 1338,
        1335, 1332, 1328, 1325, 1322, 1318, 1315, 1312,
        1308, 1305, 1302, 1299, 1295, 1292, 1289, 1286,
        1283, 1280, 1276, 1273, 1270, 1267, 1264, 1261,
        1258, 1255, 1252, 1249, 1246, 1243, 1240, 1237,
        1234, 1231, 1228, 1226, 1223, 1220, 1217, 1214,
        1211, 1209, 1206, 1203, 1200, 1197, 1195, 1192,
        1189, 1187, 1184, 1181, 1179, 1176, 1173, 1171,
        1168, 1165, 1163, 1160, 1158, 1155, 1153, 1150,
        1148, 1145, 1143, 1140, 1138, 1135, 1133, 1130,
        1128, 1125, 1123, 1121, 1118, 1116, 1113, 1111,
        1109, 1106, 1104, 1102, 1099, 1097, 1095, 1092,
        1090, 1088, 1086, 1083, 1081, 1079, 1077, 1074,
        1072, 1070, 1068, 1066, 1064, 1061, 1059, 1057,
        1055, 1053, 1051, 1049, 1047, 1044, 1042, 1040,
        1038, 1036, 1034, 1032, 1030, 1028, 1026, 1024,
        ];

    let d0  = d & 1;
    let d9  = d >> 55;
    let d40 = (d >> 24) + 1;
    let d63 = (d >> 1) + d0; /* d / 2 rounded up */

    //      = ((1 << 19) - (3 << 8)) / d9;
    // Note that the high bit of d9 is always set:
    let v0  = DIV_TABLE[(d9 & 255) as usize] as BigDigit;

    debug_assert_eq!(v0, ((1 << 19) - (3 << 8)) / d9);

    let v1  = (v0 << 11) - ((v0 * v0 * d40) >> 40) - 1;
    let v2  = (v1 << 13) + ((v1 * ((1 << 60) - v1 * d40)) >> 47);
    let e   = (if d0 != 0 { v2 >> 1 } else { 0 }).wrapping_sub(v2.wrapping_mul(d63));
    let v3  = (v2 << 31).wrapping_add(umul(v2, e)[1] >> 1);
    let v4  = v3.wrapping_sub(uadd_wrap(&umul(v3, d), &[d, d])[1]);
    v4
}

//#[cfg(integer_inverse_by_newton_32)]
fn integer_reciprocal(d: BigDigit) -> BigDigit {
    debug_assert!(d.leading_zeros() == 0);

    const DIV_TABLE: [u16; 512] = [
        32736, 32672, 32608, 32545, 32482, 32419, 32356, 32294,
        32232, 32170, 32108, 32047, 31986, 31925, 31864, 31804,
        31744, 31683, 31624, 31564, 31505, 31446, 31387, 31328,
        31270, 31211, 31153, 31096, 31038, 30981, 30924, 30867,
        30810, 30753, 30697, 30641, 30585, 30529, 30474, 30418,
        30363, 30308, 30254, 30199, 30145, 30091, 30037, 29983,
        29930, 29876, 29823, 29770, 29717, 29665, 29612, 29560,
        29508, 29456, 29404, 29353, 29302, 29251, 29200, 29149,
        29098, 29048, 28997, 28947, 28897, 28848, 28798, 28749,
        28700, 28650, 28602, 28553, 28504, 28456, 28408, 28360,
        28312, 28264, 28216, 28169, 28122, 28075, 28028, 27981,
        27934, 27888, 27841, 27795, 27749, 27703, 27658, 27612,
        27567, 27521, 27476, 27431, 27386, 27342, 27297, 27253,
        27209, 27165, 27121, 27077, 27033, 26990, 26946, 26903,
        26860, 26817, 26774, 26731, 26689, 26646, 26604, 26562,
        26520, 26478, 26436, 26395, 26353, 26312, 26270, 26229,
        26188, 26147, 26107, 26066, 26026, 25985, 25945, 25905,
        25865, 25825, 25785, 25746, 25706, 25667, 25628, 25589,
        25550, 25511, 25472, 25433, 25395, 25356, 25318, 25280,
        25242, 25204, 25166, 25128, 25091, 25053, 25016, 24978,
        24941, 24904, 24867, 24830, 24794, 24757, 24720, 24684,
        24648, 24612, 24576, 24540, 24504, 24468, 24432, 24397,
        24361, 24326, 24291, 24255, 24220, 24185, 24151, 24116,
        24081, 24047, 24012, 23978, 23944, 23909, 23875, 23841,
        23808, 23774, 23740, 23706, 23673, 23640, 23606, 23573,
        23540, 23507, 23474, 23441, 23408, 23376, 23343, 23311,
        23278, 23246, 23214, 23182, 23150, 23118, 23086, 23054,
        23023, 22991, 22960, 22928, 22897, 22866, 22834, 22803,
        22772, 22741, 22711, 22680, 22649, 22619, 22588, 22558,
        22528, 22497, 22467, 22437, 22407, 22377, 22347, 22318,
        22288, 22258, 22229, 22199, 22170, 22141, 22111, 22082,
        22053, 22024, 21995, 21967, 21938, 21909, 21880, 21852,
        21824, 21795, 21767, 21739, 21710, 21682, 21654, 21626,
        21599, 21571, 21543, 21515, 21488, 21460, 21433, 21405,
        21378, 21351, 21324, 21297, 21270, 21243, 21216, 21189,
        21162, 21135, 21109, 21082, 21056, 21029, 21003, 20977,
        20951, 20924, 20898, 20872, 20846, 20820, 20795, 20769,
        20743, 20717, 20692, 20666, 20641, 20616, 20590, 20565,
        20540, 20515, 20490, 20464, 20440, 20415, 20390, 20365,
        20340, 20316, 20291, 20267, 20242, 20218, 20193, 20169,
        20145, 20121, 20096, 20072, 20048, 20024, 20000, 19977,
        19953, 19929, 19905, 19882, 19858, 19835, 19811, 19788,
        19765, 19741, 19718, 19695, 19672, 19649, 19626, 19603,
        19580, 19557, 19534, 19512, 19489, 19466, 19444, 19421,
        19399, 19376, 19354, 19331, 19309, 19287, 19265, 19243,
        19221, 19199, 19177, 19155, 19133, 19111, 19089, 19068,
        19046, 19024, 19003, 18981, 18960, 18938, 18917, 18896,
        18874, 18853, 18832, 18811, 18790, 18769, 18748, 18727,
        18706, 18685, 18664, 18643, 18623, 18602, 18581, 18561,
        18540, 18520, 18499, 18479, 18459, 18438, 18418, 18398,
        18378, 18357, 18337, 18317, 18297, 18277, 18257, 18238,
        18218, 18198, 18178, 18159, 18139, 18119, 18100, 18080,
        18061, 18041, 18022, 18003, 17983, 17964, 17945, 17926,
        17906, 17887, 17868, 17849, 17830, 17811, 17792, 17773,
        17755, 17736, 17717, 17698, 17680, 17661, 17642, 17624,
        17605, 17587, 17569, 17550, 17532, 17513, 17495, 17477,
        17459, 17441, 17422, 17404, 17386, 17368, 17350, 17332,
        17314, 17297, 17279, 17261, 17243, 17225, 17208, 17190,
        17172, 17155, 17137, 17120, 17102, 17085, 17068, 17050,
        17033, 17016, 16998, 16981, 16964, 16947, 16930, 16913,
        16896, 16878, 16862, 16845, 16828, 16811, 16794, 16777,
        16760, 16744, 16727, 16710, 16694, 16677, 16660, 16644,
        16627, 16611, 16594, 16578, 16562, 16545, 16529, 16513,
        16496, 16480, 16464, 16448, 16432, 16416, 16400, 16384,
        ];

    let d0  = d & 1;
    let d10 = d >> 22;
    let d21 = (d >> 11) + 1;
    let d31 = (d >> 1) + d0; /* d / 2 rounded up */

    //      = ((1 << 24) - (1 << 14) + (1 >> 9)) / (d >> 22);
    // Note that the high bit of d10 is always set:
    let v0  = DIV_TABLE[(d10 & 511) as usize] as BigDigit;

    debug_assert_eq!(v0, ((1 << 24) - (1 << 14) + (1 >> 9)) / d10);

    let v1  = (v0 << 4) - umul(v0 * v0, d21)[1] - 1;
    let e   = (if d0 != 0 { v1 >> 1 } else { 0 }).wrapping_sub(v1.wrapping_mul(d31));
    let v2  = (v1 << 15).wrapping_add(umul(v1, e)[1] >> 1);
    let v3  = v2.wrapping_sub(uadd_wrap(&umul(v2, d), &[d, d])[1]);
    v3
}

#[inline]
fn div_wide_inverse(u1: BigDigit, u0: BigDigit, d: BigDigit, v: BigDigit) -> (BigDigit, BigDigit) {
    let u = [u0, u1];
    let mut q;
    let mut r;

    q       = umul(u[1], v);
    q       = uadd(&q, &u);
    q[1]    = q[1].wrapping_add(1);
    r       = u[0].wrapping_sub(q[1].wrapping_mul(d));

    if r > q[0] {
        q[1] = q[1].wrapping_sub(1);
        r    = r.wrapping_add(d);
    }

    if r >= d {
        q[1] = q[1].wrapping_add(1);
        r   -= d;
    }

    (q[1], r)
}

fn div_rem_digit_inv(mut u: BigUint, d: BigDigit, v: BigDigit) -> (BigUint, BigDigit) {
    let mut rem = 0;

    for ui in u.data.iter_mut().rev() {
        let (q, r) = div_wide_inverse(rem, *ui, d, v);
        *ui = q;
        rem = r;
    }

    (u.normalize(), rem)
}

pub fn div_rem(u: &BigUint, d: &BigUint) -> (BigUint, BigUint) {
    if d.is_zero() {
        panic!()
    }
    if u.is_zero() {
        return (Zero::zero(), Zero::zero());
    }
    if *d == One::one() {
        return (u.clone(), Zero::zero());
    }

    // Required or the q_len calculation below can underflow:
    match u.cmp(d) {
        Less => return (Zero::zero(), u.clone()),
        Equal => return (One::one(), Zero::zero()),
        Greater => {} // Do nothing
    }

    // This algorithm is from Knuth, TAOCP vol 2 section 4.3, algorithm D:
    //
    // First, normalize the arguments so the highest bit in the highest digit of the divisor is
    // set: the main loop uses the highest digit of the divisor for generating guesses, so we
    // want it to be the largest number we can efficiently divide by.
    //
    let shift = d.data.last().unwrap().leading_zeros() as usize;
    let mut a = u << shift;
    let b = d << shift;

    // The algorithm works by incrementally calculating "guesses", q0, for part of the
    // remainder. Once we have any number q0 such that q0 * b <= a, we can set
    //
    //     q += q0
    //     a -= q0 * b
    //
    // and then iterate until a < b. Then, (q, a) will be our desired quotient and remainder.
    //
    // q0, our guess, is calculated by dividing the last few digits of a by the last digit of b
    // - this should give us a guess that is "close" to the actual quotient, but is possibly
    // greater than the actual quotient. If q0 * b > a, we simply use iterated subtraction
    // until we have a guess such that q0 * b <= a.
    //

    let bn = *b.data.last().unwrap();
    let bn_inv = integer_reciprocal(bn);
    let q_len = a.data.len() - b.data.len() + 1;
    let mut q = BigUint { data: vec![0; q_len] };

    // We reuse the same temporary to avoid hitting the allocator in our inner loop - this is
    // sized to hold a0 (in the common case; if a particular digit of the quotient is zero a0
    // can be bigger).
    //
    let mut tmp = BigUint { data: Vec::with_capacity(2) };

    for j in (0..q_len).rev() {
        /*
         * When calculating our next guess q0, we don't need to consider the digits below j
         * + b.data.len() - 1: we're guessing digit j of the quotient (i.e. q0 << j) from
         * digit bn of the divisor (i.e. bn << (b.data.len() - 1) - so the product of those
         * two numbers will be zero in all digits up to (j + b.data.len() - 1).
         */
        let offset = j + b.data.len() - 1;
        if offset >= a.data.len() {
            continue;
        }

        /* just avoiding a heap allocation: */
        let mut a0 = tmp;
        a0.data.truncate(0);
        a0.data.extend(a.data[offset..].iter().cloned());

        /*
         * q0 << j * big_digit::BITS is our actual quotient estimate - we do the shifts
         * implicitly at the end, when adding and subtracting to a and q. Not only do we
         * save the cost of the shifts, the rest of the arithmetic gets to work with
         * smaller numbers.
         */
        let (mut q0, _) = div_rem_digit_inv(a0, bn, bn_inv);
        let mut prod = &b * &q0;

        while cmp_slice(&prod.data[..], &a.data[j..]) == Greater {
            let one: BigUint = One::one();
            q0 = q0 - one;
            prod = prod - &b;
        }

        add2(&mut q.data[j..], &q0.data[..]);
        sub2(&mut a.data[j..], &prod.data[..]);
        a = a.normalize();

        tmp = q0;
    }

    debug_assert!(a < b);

    (q.normalize(), a >> shift)
}

/// Find last set bit
/// fls(0) == 0, fls(u32::MAX) == 32
pub fn fls<T: traits::PrimInt>(v: T) -> usize {
    mem::size_of::<T>() * 8 - v.leading_zeros() as usize
}

pub fn ilog2<T: traits::PrimInt>(v: T) -> usize {
    fls(v) - 1
}

#[inline]
pub fn biguint_shl(n: Cow<BigUint>, bits: usize) -> BigUint {
    let n_unit = bits / big_digit::BITS;
    let mut data = match n_unit {
        0 => n.into_owned().data,
        _ => {
            let len = n_unit + n.data.len() + 1;
            let mut data = Vec::with_capacity(len);
            data.extend(repeat(0).take(n_unit));
            data.extend(n.data.iter().cloned());
            data
        }
    };

    let n_bits = bits % big_digit::BITS;
    if n_bits > 0 {
        let mut carry = 0;
        for elem in data[n_unit..].iter_mut() {
            let new_carry = *elem >> (big_digit::BITS - n_bits);
            *elem = (*elem << n_bits) | carry;
            carry = new_carry;
        }
        if carry != 0 {
            data.push(carry);
        }
    }

    BigUint::new(data)
}

#[inline]
pub fn biguint_shr(n: Cow<BigUint>, bits: usize) -> BigUint {
    let n_unit = bits / big_digit::BITS;
    if n_unit >= n.data.len() {
        return Zero::zero();
    }
    let mut data = match n_unit {
        0 => n.into_owned().data,
        _ => n.data[n_unit..].to_vec(),
    };

    let n_bits = bits % big_digit::BITS;
    if n_bits > 0 {
        let mut borrow = 0;
        for elem in data.iter_mut().rev() {
            let new_borrow = *elem << (big_digit::BITS - n_bits);
            *elem = (*elem >> n_bits) | borrow;
            borrow = new_borrow;
        }
    }

    BigUint::new(data)
}

pub fn cmp_slice(a: &[BigDigit], b: &[BigDigit]) -> Ordering {
    debug_assert!(a.last() != Some(&0));
    debug_assert!(b.last() != Some(&0));

    let (a_len, b_len) = (a.len(), b.len());
    if a_len < b_len {
        return Less;
    }
    if a_len > b_len {
        return Greater;
    }

    for (&ai, &bi) in a.iter().rev().zip(b.iter().rev()) {
        if ai < bi {
            return Less;
        }
        if ai > bi {
            return Greater;
        }
    }
    return Equal;
}

#[cfg(test)]
mod algorithm_tests {
    use {BigDigit, BigUint, BigInt};
    use Sign::Plus;
    use traits::Num;

    #[test]
    fn test_sub_sign() {
        use super::sub_sign;

        fn sub_sign_i(a: &[BigDigit], b: &[BigDigit]) -> BigInt {
            let (sign, val) = sub_sign(a, b);
            BigInt::from_biguint(sign, val)
        }

        let a = BigUint::from_str_radix("265252859812191058636308480000000", 10).unwrap();
        let b = BigUint::from_str_radix("26525285981219105863630848000000", 10).unwrap();
        let a_i = BigInt::from_biguint(Plus, a.clone());
        let b_i = BigInt::from_biguint(Plus, b.clone());

        assert_eq!(sub_sign_i(&a.data[..], &b.data[..]), &a_i - &b_i);
        assert_eq!(sub_sign_i(&b.data[..], &a.data[..]), &b_i - &a_i);
    }
}
