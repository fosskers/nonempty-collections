# `nonempty-collections`

## Unreleased

#### Added

- The missing `IntoIterator` impl for `NEChunks`.

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
