use divan::black_box;
use divan::Bencher;
use nonempty_collections::FromNonEmptyIterator;
use nonempty_collections::IntoIteratorExt;
use nonempty_collections::IteratorExt;
use nonempty_collections::NEVec;
use nonempty_collections::NonEmptyIterator;

fn main() {
    // Run registered benchmarks.
    divan::main();
}

const LENS: &[usize] = &[1, 8, 64, 1024];

// Register a `fibonacci` function and benchmark it over multiple cases.
// #[divan::bench(args = [1, 2, 4, 8, 16, 32])]
// fn fibonacci(n: u64) -> u64 {
//     if n <= 1 {
//         1
//     } else {
//         fibonacci(n - 2) + fibonacci(n - 1)
//     }
// }

// #[divan::bench(
//     types = [
//         Vec<i32>,
//         NEVec<i32>,
//     ],
//     args = LENS,
// )]
// fn from_iter<T: FromIterator<i32>>(bencher: Bencher, len: usize) {
//     bencher.counter(len).bench(|| collect_nums::<T>(len))
// }

#[divan::bench(args = LENS)]
fn collect_vec(bencher: Bencher, len: usize) {
    bencher.counter(len).bench(|| collect_nums::<Vec<_>>(len))
}

#[divan::bench(args = LENS)]
fn collect_nevec(bencher: Bencher, len: usize) {
    bencher
        .counter(len)
        .bench(|| ne_collect_nums::<NEVec<_>>(len))
}

pub fn collect_nums<T: FromIterator<i32>>(n: usize) -> T {
    black_box(0..(n as i32)).collect()
}

pub fn ne_collect_nums<T: FromNonEmptyIterator<i32>>(n: usize) -> T {
    black_box(0..(n as i32))
        .to_nonempty_iter()
        .unwrap()
        .collect()
}

#[divan::bench]
fn contains_vec(bencher: Bencher) {
    let vec = (0..64).collect::<Vec<_>>();
    bencher.bench(|| black_box(vec.contains(&32)))
}

#[divan::bench]
fn contains_nevec(bencher: Bencher) {
    let vec = (0..64)
        .try_into_nonempty_iter()
        .unwrap()
        .collect::<NEVec<_>>();
    bencher.bench(|| black_box(vec.contains(&32)))
}

const LOOKUPS: [usize; 7] = [7, 19, 32, 46, 64, 0, 53];

#[divan::bench]
fn get_vec(bencher: Bencher) {
    let vec = (0..64).collect::<Vec<_>>();
    bencher.bench(|| {
        for i in LOOKUPS {
            black_box(vec.get(i));
        }
    })
}

#[divan::bench]
fn get_nevec(bencher: Bencher) {
    let vec = (0..64)
        .try_into_nonempty_iter()
        .unwrap()
        .collect::<NEVec<_>>();
    bencher.bench(|| {
        for i in LOOKUPS {
            black_box(vec.get(i));
        }
    })
}

#[divan::bench]
fn map_vec(bencher: Bencher) {
    let vec = (0..64).collect::<Vec<_>>();
    bencher.bench(|| black_box(vec.iter().map(|i| i + 7).collect::<Vec<_>>()))
}

#[divan::bench]
fn map_nevec(bencher: Bencher) {
    let vec = (0..64)
        .try_into_nonempty_iter()
        .unwrap()
        .collect::<NEVec<_>>();
    bencher.bench(|| black_box(vec.iter().map(|i| i + 7).collect::<NEVec<_>>()))
}
