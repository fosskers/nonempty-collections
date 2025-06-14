# `nonempty-collections`

## 0.3.1 (2025-06-14)

#### Added

- `iter_mut()` to `NEVec`, `NEMap`, and `NEIndexMap`
- `peekable()` to `NonEmptyIterator`
- `remove()`, `swap_remove()`, `retain()`, and `retain_mut()` to `NEVec`.
- `AsRef<[T]>` for `NESlice`.

## 0.3.0 (2025-02-15)

#### Changed

- **BREAKING:** Redesign of `NonEmptyIterator`:
  - `NonEmptyIterator` is now bounded by `IntoIterator` and has default
    implementations of all methods (i.e. it is a marker trait).
  - `NonEmptyIterator::first()` is renamed to `next()` and the old implementation of `next()` is removed.
  - `NonEmptyIterator::all()` now consumes self
  - `NonEmptyIterator::any()` now consumes self
  - `NonEmptyIterator::nth()` now consumes self
  - `NonEmptyIterator::take(usize)` -> `NonEmptyIterator::take(NonZeroUsize)` and doesn't panic anymore
- **BREAKING:** `NEVec::truncate(usize)` -> `NEVec::truncate(NonZeroUsize)` and doesn't panic anymore
- **BREAKING:** Capacities for all collections now use `NonZeroUsize` instead of `usize`:
  - `with_capacity(NonZeroUsize)`
  - `with_capacity_and_hasher(NonZeroUsize)`
  - `capacity() -> NonZeroUsize`
- **BREAKING:** All fields are now private for `NEVec`, `NEMap`, `NESet`, and `NESlice`
- **BREAKING:** Removed:
  - `NESlice::new(&T, &[T])`
  - `IntoIteratorProxy`
- **BREAKING:** Methods that are no longer `const`:
  - `NEVec::new()`
  - `NEVec::first()`
- **BREAKING:** non-empty maps and sets now behave similarly to their possibly
  empty counter parts: when created from an iterator with duplicates, the last
  occurence is kept.
- **BREAKING:** Consistent API, new naming to align with Rust's naming
  conventions and indicate the fallibility of the function:
  - `from_vec` to `try_from_vec`
  - `from_map` to `try_from_map`
  - `from_slice` to `try_from_slice`
  - `from_set` to `try_from_set`.
- **BREAKING:** `IteratorExt` is removed in favor of `IntoIteratorExt`. Now it's
  possible to call `try_into_nonempty_iter()` instead of `to_nonempty_iter()` on
  all regular iterators because regular iterators also implement `IntoIterator`.
- **BREAKING:** `.iter()`, `.iter_mut()`, etc, are now prefixed with `nonempty_`
- `FromNonEmptyIterator<T>` is now implemented for `HashSet<T, S>` instead of
  `HashSet<T>` (with the default hasher).

#### Fixed

- Fixes bug in `PartialEq for NEIndexMap`, previously, maps with unequal lengths
  would be considered equal if the shorter map would contain the same values as
  the longer map.
- Fixes bug in `NEMap::with_capacity()` and `NESet::with_capacity()`, it wasn't
  possible to call this method without explicitly specifying the type for `S`
  (the hasher). For this method it is assumed that it always uses the default
  hasher (just like in `std`), in case the user wants to specify the hasher
  `with_capacity_and_hasher()` can be used. The fix moved the method into the
  proper `impl` block.

#### Added

 - New feature `either`: adds `NEEither` an extension to `either::Either`.
 - New feature `itertools`: adds a new `NonEmptyItertools` trait that is an
   extension of the `NonEmptyIterator` similar to how `Itertools` extends
   `Iterator`. So far, `cartesian_product()`, `sorted_by_key()`, and
   `all_unique()` are implemented.
 - `NonEmptyIterator::find()` the equivalent of `Iterator::find()`.
 - `IntoNonEmptyIterator for &NEVec`, `&NEIndexMap`, `&NEMap`, `&NESet`,
   `&NESlice`, `&[T; $i] where $i > 0` (these previously only existed for their
   owned equivalents)
 - `NESlice::from_slice()` is now `const`
 - `Index<usize> for NESlice`
 - All public types now implement `Debug`
 - Aliases `ne_vec` for `nev`, `ne_hashset` for `nes`, and `ne_hashmap` for `nem`.
 - Strict lint configuration
 - The rust version to which the library is build is now pinned, to avoid accidental breakage.
 - A [`justfile`](https://github.com/casey/just) that allows to run
   pre-configured commands to check the codebase. E.g. `just lint` or `just
   test`.
 - Benchmarks for `Vec` versus `NEVec`.
 - Added `.iter()` methods to all collections returning a regular `Iterator`.

## 0.2.9 (2024-08-26)

#### Added

- `NonEmptyIterator::group_by`.
- `NVec::sort_by` and `NEVec::sort_by_key`.
- An impl of `Extend` for `NEVec`.

#### Fixed

- `NEVec::sort` avoids a second internal `sort`.

## 0.2.8 (2024-08-19)

#### Added

- Missing `FromNonEmptyIterator` for `HashMap`.

## 0.2.7 (2024-07-22)

#### Added

- `serde` support for `NEMap` and `NESet`.

## 0.2.6 (2024-06-27)

#### Fixed

- Ownership issues in `nem!` when using non-Copy types.

## 0.2.5 (2024-04-09)

#### Added

- Implementation of `NonEmptyIterator` for fixed-sized stdlib Arrays.

## 0.2.4 (2024-04-04)

#### Added

- Added `NEVec::partition_point` to match the function of the same name in `std`.

#### Fixed

- Render feature-gated types on `docs.rs`.

## 0.2.3 (2024-03-19)

#### Fixed

- More edge cases involving `NEChunks`.

## 0.2.2 (2024-03-18)

#### Fixed

- `IntoIterator` for `NEChunks` yielding the wrong type.
- `NonEmptyIterator` for `NEChunks` missing a cutoff condition.

## 0.2.1 (2024-03-15)

#### Added

- The missing `IntoIterator` impl for `NEChunks`.
- `IntoIteratorExt` for direct conversion from anything that implements
  `IntoIterator`. Thanks to Rinde van Lon.

#### Fixed

- A bug involving repeated keys in `NEMap` and `NEIndexedMap`. Thanks to Rinde van Lon.

## 0.2.0 (2024-03-14)

#### Added

- `NEIndexMap`, thanks to [Rinde van Lon](https://github.com/rinde/).
- `NonEmptyIterator::max_by_key` and `NonEmptyIterator::min_by_key`, also thanks to Rinde.
- `NEVec::with_capacity`
- `NEVec::nonempty_chunks` and `NESlice::nonempty_chunks`

#### Changed

- **BREAKING:** All `len` implementations and `NonEmptyIterator::count` have had
  their return type changed to `NonZeroUsize`.

## 0.1.5 (2024-01-12)

#### Added

- `NonEmptyIterator::reduce`, which yields a concrete `Self::Item` instead of an
  `Option`.
- `IteratorExt::to_nonempty_iter` for converting any given `Iterator` into a
  non-empty one (if possible).
- The `NEVec::dedup*` series for removing duplicate items in-place.

#### Fixed

- Account for potentially duplicated `head` value when converting into an
  `NESet` from other nonempty iterators.

## 0.1.4 (2023-11-02)

#### Added

- `FromNonEmptyIterator` impls for `NEMap` and `NESet`.
- `Debug`, `Clone`, `PartialEq`, and `Eq` for `NEMap`.

## 0.1.3 (2023-09-15)

#### Added

- `NESlice` for when what you have on hand is already borrowed. Thanks again to
  Greg Shuflin.

## 0.1.2 (2023-09-05)

#### Added

- A `FromNonEmptyIterator` instance for `Result`, meaning you can `collect` into
  a guaranteed `Result<NEVec<...>, Error>` (or other nonempty type). Thanks to
  Greg Shuflin.

## 0.1.1 (2023-04-08)

#### Added

- Missing `IntoNonEmptyIterator` instances.
- Missing `Intoiterator` instance for `FlatMap`.

#### Fixed

- Incorrect `IntoIterator` for `Take`.
