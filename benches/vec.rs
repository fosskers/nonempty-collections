//! Benchmarks for `NEVec` versus `Vec`.

use divan::Bencher;
use divan::black_box;
use nonempty_collections::IntoIteratorExt;
use nonempty_collections::NEVec;
use nonempty_collections::NonEmptyIterator;

fn main() {
    // Run registered benchmarks.
    divan::main();
}

const LENS: &[usize] = &[1, 8, 64, 1024];
const SAMPLE_SIZE: u32 = 10000;

#[divan::bench(args = LENS, sample_size = SAMPLE_SIZE)]
fn contains_vec(bencher: Bencher, len: usize) {
    let vec = (0..len).collect::<Vec<_>>();
    bencher.bench(|| black_box(vec.contains(&32)));
}

#[divan::bench(args = LENS, sample_size = SAMPLE_SIZE)]
fn contains_nevec(bencher: Bencher, len: usize) {
    let vec = (0..len)
        .try_into_nonempty_iter()
        .unwrap()
        .collect::<NEVec<_>>();
    bencher.bench(|| black_box(vec.contains(&32)));
}

#[divan::bench(args = LENS, sample_size = SAMPLE_SIZE)]
fn map_vec(bencher: Bencher, len: usize) {
    let vec = (0..len).collect::<Vec<_>>();
    bencher.bench(|| black_box(vec.iter().map(|i| i + 7).collect::<Vec<_>>()));
}

#[divan::bench(args = LENS, sample_size = SAMPLE_SIZE)]
fn map_nevec(bencher: Bencher, len: usize) {
    let vec = (0..len)
        .try_into_nonempty_iter()
        .unwrap()
        .collect::<NEVec<_>>();
    bencher.bench(|| black_box(vec.nonempty_iter().map(|i| i + 7).collect::<NEVec<_>>()));
}
