# Correct-by-Construction Collections

<!-- cargo-rdme start -->

Non-empty variants of the standard collections.

Non-emptiness can be a powerful guarantee. If your main use of `Vec` is as
an `Iterator`, then you may not need to distinguish on emptiness. But there
are indeed times when the `Vec` you receive as a function argument needs to
be non-empty or your function can't proceed. Similarly, there are times when
the `Vec` you return to a calling user needs to promise it actually contains
something.

With `NEVec`, you're freed from the boilerplate of constantly needing to
check `is_empty()` or pattern matching before proceeding, or erroring if you
can't. So overall, code, type signatures, and logic become cleaner.

Consider that unlike `Vec`, [`NEVec::first()`] and [`NEVec::last()`] don't
return in `Option`; they always succeed.

Alongside [`NEVec`](https://docs.rs/nonempty-collections/latest/nonempty_collections/vector/struct.NEVec.html) are its cousins
[`NESlice`](https://docs.rs/nonempty-collections/latest/nonempty_collections/slice/struct.NESlice.html), [`NEMap`](https://docs.rs/nonempty-collections/latest/nonempty_collections/map/struct.NEMap.html), and
[`NESet`](https://docs.rs/nonempty-collections/latest/nonempty_collections/set/struct.NESet.html), which are all guaranteed to contain at least
one item.

## Examples

The simplest way to construct these non-empty collections is via their
macros: [`nev!`], [`nes!`], and [`nem!`]:

```rust
use nonempty_collections::*;

let v: NEVec<u32> = nev![1, 2, 3];
let s: NESet<u32> = nes![1, 2, 2, 3]; // 1 2 3
let m: NEMap<&str, bool> = nem!["a" => true, "b" => false];
assert_eq!(&1, v.first());
assert_eq!(3, s.len().get());
assert!(m.get("a").unwrap());
```

Unlike the familiar `vec!` macro, `nev!` and friends require at least one
element:

```rust
use nonempty_collections::nev;

let v = nev![1];
```

A value must be provided:

```rust
let v = nev![]; // Doesn't compile!
```

Like `Vec`, you can also construct a [`NEVec`](https://docs.rs/nonempty-collections/latest/nonempty_collections/vector/struct.NEVec.html) the old
fashioned way with [`NEVec::new()`] or its constructor:

```rust
use nonempty_collections::NEVec;

let mut l = NEVec::from_vec(vec![42, 36, 58]).unwrap();
assert_eq!(&42, l.first());

l.push(9001);
assert_eq!(l.last(), &9001);
```

And if necessary, you're free to convert to and from `Vec`:

```rust
use nonempty_collections::nev;
use nonempty_collections::NEVec;

let l: NEVec<u32> = nev![42, 36, 58, 9001];
let v: Vec<u32> = l.into();
assert_eq!(v, vec![42, 36, 58, 9001]);

let u: Option<NEVec<u32>> = NEVec::from_vec(v);
assert_eq!(Some(nev![42, 36, 58, 9001]), u);
```

## Iterators

This library extends the notion of non-emptiness to iterators, and provides
the [`NonEmptyIterator`](https://docs.rs/nonempty-collections/latest/nonempty_collections/iter/trait.NonEmptyIterator.html) trait. This has some
interesting consequences:

- Functions like `map` preserve non-emptiness.
- Functions like `max` always have a result.
- A non-empty iterator chain can be `collect`ed back into a non-empty
  structure.
- You can chain many operations together without having to double-check for
  emptiness.

```rust
use nonempty_collections::*;

let v: NEVec<_> = nev![1, 2, 3].into_nonempty_iter().map(|n| n + 1).collect();
assert_eq!(&2, v.first());
```

Consider also [`IteratorExt::to_nonempty_iter`](https://docs.rs/nonempty-collections/latest/nonempty_collections/iter/trait.IteratorExt.html)
for converting any given [`Iterator`] into a non-empty one, if it contains
at least one item.

## Arrays

Since fixed-size arrays are by definition already not empty, they aren't
given a special wrapper type like [`NEVec`](https://docs.rs/nonempty-collections/latest/nonempty_collections/vector/struct.NEVec.html). Instead,
we enable them to be easily iterated over in a compatible way:

```rust
use nonempty_collections::*;

let a: [u32; 4] = [1, 2, 3, 4];
let v: NEVec<_> = a.into_nonempty_iter().map(|n| n + 1).collect();
assert_eq!(nev![2, 3, 4, 5], v);
```
See [`NonEmptyArrayExt`](https://docs.rs/nonempty-collections/latest/nonempty_collections/array/trait.NonEmptyArrayExt.html) for more
conversions.

## Caveats

Since `NEVec`, `NEMap`, and `NESet` must have a least one element, it is not
possible to implement the [`FromIterator`] trait for them. We can't
know, in general, if any given standard-library [`Iterator`] actually
contains something.

## Features

* `serde`: `serde` support.
* `indexmap`: adds [`NEIndexMap`](https://docs.rs/nonempty-collections/latest/nonempty_collections/index_map/struct.NEIndexMap.html) a non-empty [`IndexMap`](https://docs.rs/indexmap/latest/indexmap/).
* `itertools`: adds [`NonEmptyItertools`](https://docs.rs/nonempty-collections/latest/nonempty_collections/itertools/trait.NonEmptyItertools.html) a non-empty variant of [`itertools`](https://docs.rs/itertools/latest/itertools/).
* `either`: adds [`NEEither`](https://docs.rs/nonempty-collections/latest/nonempty_collections/either/enum.NEEither.html) a non-empty variant of `Either` from the [`either` crate](https://docs.rs/either/latest/either/).

<!-- cargo-rdme end -->
