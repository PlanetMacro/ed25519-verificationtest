//! Tiny smoke test for the Charon -> Aeneas -> Lean pipeline.
//! Not part of the crypto crates; just exercises the toolchain end-to-end.
#![allow(dead_code)]

pub fn add(x: u32, y: u32) -> u32 {
    x + y
}

pub fn factorial(n: u64) -> u64 {
    if n == 0 {
        1
    } else {
        n * factorial(n - 1)
    }
}

pub fn sum_slice(xs: &[u32]) -> u32 {
    let mut total: u32 = 0;
    let mut i = 0;
    while i < xs.len() {
        total += xs[i];
        i += 1;
    }
    total
}
