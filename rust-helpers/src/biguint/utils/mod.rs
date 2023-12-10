// NOTE: this file is forked from https://github.com/shuklaayush/noir-bigint/blob/d3682670f4323f7f273043c281f365a7bfb992d4/crates/biguint/src/utils.nr

const BITS: usize = 32;

// Compute a + b + carry, returning the result and the new carry over.
// TODO: Does carry need to be a u32?
pub fn adc(a: u32, b: u32, carry: u32) -> (u32, u32) {
    let ret = a as u128 + b as u128 + carry as u128;
    (ret as u32, (ret as u64 >> BITS as u64) as u32)
}

// Compute a - (b + borrow), returning the result and the new borrow.
pub fn sbb(a: u32, b: u32, borrow: u32) -> (u32, u32) {
    let ret = u64::wrapping_sub(a as u64, b as u64 + (borrow as u64 >> (BITS as u64 - 1)));
    (ret as u32, (ret >> 32) as u32)
}

// Compute a + (b * c) + carry, returning the result and the new carry over.
pub fn mac(a: u32, b: u32, c: u32, carry: u32) -> (u32, u32) {
    let ret = (a as u128) + ((b as u128) * (c as u128)) + (carry as u128);
    (ret as u32, (ret as u64 >> BITS as u64) as u32)
}

pub fn number_to_bits(n: u32, byte_size: usize) -> Vec<u8> {
    let mut bits = Vec::with_capacity(byte_size * 8);
    for i in 0..byte_size {
        bits.push(((n >> i) & 1) as u8);
    }
    bits
}