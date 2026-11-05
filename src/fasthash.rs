//! A fast hash for the compiler's and the VM's own maps, whose keys (type and function ids,
//! names, pointer targets) are not chosen by an adversary, so std's SipHash, which resists
//! collision attacks, costs time for nothing. It is FxHash: a multiply and a rotate per word.

use std::hash::{BuildHasherDefault, Hasher};

/// A `HashMap` with `FastHasher`.
pub type FastMap<K, V> = std::collections::HashMap<K, V, BuildHasherDefault<FastHasher>>;
/// A `HashSet` with `FastHasher`.
pub type FastSet<K> = std::collections::HashSet<K, BuildHasherDefault<FastHasher>>;

const SEED: u64 = 0x51_7c_c1_b7_27_22_0a_95;

#[derive(Default, Clone, Copy)]
pub struct FastHasher {
    hash: u64,
}

impl FastHasher {
    fn add(&mut self, word: u64) {
        self.hash = (self.hash.rotate_left(5) ^ word).wrapping_mul(SEED);
    }
}

impl Hasher for FastHasher {
    fn write(&mut self, bytes: &[u8]) {
        let mut chunks = bytes.chunks_exact(8);
        for c in &mut chunks {
            self.add(u64::from_le_bytes(c.try_into().expect("eight bytes")));
        }
        let mut last = [0u8; 8];
        let rest = chunks.remainder();
        last[..rest.len()].copy_from_slice(rest);
        self.add(u64::from_le_bytes(last) ^ rest.len() as u64);
    }

    fn write_u8(&mut self, n: u8) {
        self.add(u64::from(n));
    }

    fn write_u32(&mut self, n: u32) {
        self.add(u64::from(n));
    }

    fn write_u64(&mut self, n: u64) {
        self.add(n);
    }

    fn write_usize(&mut self, n: usize) {
        self.add(n as u64);
    }

    fn finish(&self) -> u64 {
        self.hash
    }
}
