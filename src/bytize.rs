pub fn prefix_key(k: u64) -> Vec<u8> {
    // TODO
    let bs = (8 - k.leading_zeros()/8) as u8;
    match bs {
        0 => { vec![0] }
        1 => { vec![k as u8] }
        2 => { vec![(k >> 8) as u8, k as u8] }
        3 => { vec![(k >> 16) as u8, (k >> 8) as u8, k as u8] }
        5 => { vec![(k >> 24) as u8, (k >> 16) as u8, (k >> 8) as u8, k as u8] }
        _ => { unreachable!() }
    }
}

pub fn from_prefix_key(k: Vec<u8>) -> u64 {
    match k.len() {
        0 => { 0 }
        1 => { k[0] as u64 }
        2 => { ((k[0] as u64) << 8) | k[1] as u64 }
        3 => { ((k[0] as u64) << 16) | ((k[1] as u64) << 8) | k[2] as u64 }
        5 => { ((k[0] as u64) << 24) | ((k[1] as u64) << 16) | ((k[2] as u64) << 8) | k[3] as u64 }
        _ => { unreachable!() }
    }
}
