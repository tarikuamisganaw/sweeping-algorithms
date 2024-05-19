
pub fn prefix_key(k: &u64) -> &[u8] {
    let bs = (8 - k.leading_zeros()/8) as u8;
    let kp: *const u64 = k;
    unsafe { std::slice::from_raw_parts(kp as *const _, (bs as usize).max(1)) }
}

pub fn from_prefix_key(k: Vec<u8>) -> u64 {
    let kp =  k.as_ptr() as *const u64;
    let shift = 64usize.saturating_sub(k.len()*8);
    unsafe { (*kp) & (!0u64 >> shift) }
}
