# `nonempty-collections`

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
