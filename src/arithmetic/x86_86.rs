use std::mem;

pub type BigDigit = usize;
pub use ::std::usize::MAX;

#[allow(non_snake_case)]
#[inline]
pub fn BITS() -> usize {
    mem::size_of::<BigDigit>() * 8
}

#[inline]
pub fn adc(mut a: BigDigit, b: BigDigit, carry: &mut BigDigit) -> BigDigit {
    unsafe {
        let carry_out: u8;

        if *carry != 0 {
            asm!("stc
                  adc $2, $0
                  setc $1"
                 : "+rm" (a), "=r" (carry_out)
                 : "r" (b)
                 : "cc");
        } else {
            asm!("clc
                  adc $2, $0
                  setc $1"
                 : "+rm" (a), "=r" (carry_out)
                 : "r" (b)
                 : "cc");
        }

        *carry = carry_out as BigDigit;
        a
    }
}

#[inline]
pub fn sbb(mut a: BigDigit, b: BigDigit, borrow: &mut BigDigit) -> BigDigit {
    unsafe {
        let borrow_out: u8;

        if *borrow != 0 {
            asm!("stc
                  sbb $2, $0
                  setc $1"
                 : "+rm" (a), "=r" (borrow_out)
                 : "r" (b)
                 : "cc");
        } else {
            asm!("clc
                  sbb $2, $0
                  setc $1"
                 : "+rm" (a), "=r" (borrow_out)
                 : "r" (b)
                 : "cc");
        }

        *borrow = borrow_out as BigDigit;
        a
    }
}

#[inline]
pub fn mul_with_carry(a: BigDigit, b: BigDigit, carry: &mut BigDigit) -> BigDigit {
    unsafe {
        let hi: BigDigit;
        let lo: BigDigit;

        asm!("mul $3
              add $4, $0
              adc $$0, $1"
             : "={eax}" (lo), "={edx}" (hi)
             : "{eax}" (a), "r" (b), "r" (*carry)
             : "cc");

        *carry = hi;
        lo
    }
}

#[inline]
/* a + b * c */
pub fn mac_with_carry(a: BigDigit, b: BigDigit, c: BigDigit, carry: &mut BigDigit) -> BigDigit {
    unsafe {
        let hi: BigDigit;
        let lo: BigDigit;

        asm!("mul $3
              add $4, $0
              adc $$0, $1
              add $5, $0
              adc $$0, $1"
             : "={eax}" (lo), "={edx}" (hi)
             : "{eax}" (b), "r" (c), "rm" (a), "r" (*carry)
             : "cc");

        *carry = hi;
        lo
    }
}

#[inline]
pub fn div_wide(hi: BigDigit, lo: BigDigit, divisor: BigDigit) -> (BigDigit, BigDigit) {
    unsafe {
        let quotient: BigDigit;
        let remainder: BigDigit;

        asm!("div $4"
             : "={eax}" (quotient), "={edx}" (remainder)
             : "{edx}" (hi), "{eax}" (lo), "r" (divisor)
             : "cc");

        (quotient, remainder)
    }
}
