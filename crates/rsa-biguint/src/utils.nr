// NOTE: this file is forked from https://github.com/shuklaayush/noir-bigint/blob/d3682670f4323f7f273043c281f365a7bfb992d4/crates/biguint/src/utils.nr

use crate::BITS_PER_LIMB as BITS;
use dep::std;

// Compute a + b + carry, returning the result and the new carry over.
// TODO: Does carry need to be a u32?
pub fn adc(a: u32, b: u32, carry: u32) -> (u32, u32) {
    let ret = a as Field + b as Field + carry as Field;
    (ret as u32, (ret as u64 >> BITS as u64) as u32)
}

// Compute a - (b + borrow), returning the result and the new borrow.
pub fn sbb(a: u32, b: u32, borrow: u32) -> (u32, u32) {
    let ret = std::wrapping_sub(a as u64, b as u64 + (borrow as u64 >> (BITS as u64 - 1)));
    (ret as u32, (ret >> 32) as u32)
}

// Compute a + (b * c) + carry, returning the result and the new carry over.
pub fn mac(a: u32, b: u32, c: u32, carry: u32) -> (u32, u32) {
    let ret = (a as Field) + ((b as Field) * (c as Field)) + (carry as Field);
    (ret as u32, (ret as u64 >> BITS as u64) as u32)
}
