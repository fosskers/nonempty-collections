//! Extends non-zero length arrays with conversion methods to non-empty
//! collections.
//!
//! Since fixed-size arrays are by definition already not empty, they aren't
//! given a special wrapper type like [`crate::NEVec`]. Instead, we enable them
//! to be easily iterated over in a compatible way:
//!
//! ```
//! use nonempty_collections::*;
//!
//! let a: [u32; 4] = [1, 2, 3, 4];
//! let v: NEVec<_> = a.into_nonempty_iter().map(|n| n + 1).collect();
//! assert_eq!(nev![2, 3, 4, 5], v);
//! ```
//!
//! See [`NonEmptyArrayExt`] for more conversions.

use std::num::NonZeroUsize;

use crate::impl_nonempty_iter_for_arrays;
use crate::IntoNonEmptyIterator;
use crate::NonEmptyIterator;

/// Provides extension methods for non-empty arrays.
///
/// # Examples
///
/// Create a non-empty slice of an array:
///
/// ```
/// # use nonempty_collections::*;
/// assert_eq!(NESlice::new(&1, &[2]), [1, 2].as_nonempty_slice());
/// ```
///
/// Get the length of an array as a [`NonZeroUsize`]:
///
/// ```
/// # use nonempty_collections::NonEmptyArrayExt;
/// # use std::num::NonZeroUsize;
/// assert_eq!(NonZeroUsize::MIN, [1].nonzero_len());
/// ```
///
/// Convert array into a non-empty vec:
///
/// ```
/// # use nonempty_collections::*;
/// assert_eq!(nev![4], [4].into_nonempty_vec());
/// ```
pub trait NonEmptyArrayExt<T> {
    /// Create a `NESlice` that borrows the contents of `self`.
    fn as_nonempty_slice(&self) -> crate::NESlice<'_, T>;

    /// Returns the length of this array as a [`NonZeroUsize`].
    fn nonzero_len(&self) -> NonZeroUsize;

    /// Moves `self` into a new [`crate::NEVec`].
    fn into_nonempty_vec(self) -> crate::NEVec<T>;
}

/// Non-empty iterator for arrays with length > 0.
///
/// # Examples
///
/// Use non-zero length arrays anywhere an [`IntoNonEmptyIterator`] is expected.
///
/// ```
/// use nonempty_collections::*;
/// use std::num::NonZeroUsize;
///
/// fn is_one<T>(iter: impl IntoNonEmptyIterator<Item = T>) {
///     assert_eq!(NonZeroUsize::MIN, iter.into_nonempty_iter().count());
/// }
///
/// is_one([0]);
/// ```
///
/// Only compiles for non-empty arrays:
///
/// ```compile_fail
/// use nonempty_collections::*;
///
/// fn is_one(iter: impl IntoNonEmptyIterator<Item = usize>) {}
///
/// is_one([]); // Doesn't compile because it is empty.
/// ```
pub struct ArrayNonEmptyIterator<T, const C: usize> {
    iter: core::array::IntoIter<T, C>,
}

impl<T, const C: usize> NonEmptyIterator for ArrayNonEmptyIterator<T, C> {
    type Item = T;

    type IntoIter = core::array::IntoIter<T, C>;

    fn first(self) -> (Self::Item, Self::IntoIter) {
        let mut iter = self.iter;
        (iter.next().unwrap(), iter)
    }

    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next()
    }
}

// NOTE 2024-04-05 This must never be implemented for 0.
//
// Also, happy birthday Dad.
impl_nonempty_iter_for_arrays!(
    1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26,
    27, 28, 29, 30, 31, 32
);

#[doc(hidden)]
#[macro_export]
macro_rules! impl_nonempty_iter_for_arrays {
    ($($i:literal),+ $(,)?) => {
        $(
            impl<T> IntoNonEmptyIterator for [T; $i] {
                type Item = T;

                type IntoIter = ArrayNonEmptyIterator<T, $i>;

                fn into_nonempty_iter(self) -> Self::IntoIter {
                    ArrayNonEmptyIterator {
                        iter: self.into_iter(),
                    }
                }
            }

            impl<T> NonEmptyArrayExt<T> for [T; $i] {
                fn as_nonempty_slice(&self) -> $crate::NESlice<'_, T> {
                    // This should never panic because a slice with length > 0
                    // is non-empty by definition.
                    $crate::NESlice::from_slice(self).unwrap()
                }

                fn nonzero_len(&self) -> NonZeroUsize {
                    // This should be fine because $i is always > 0.
                    unsafe { NonZeroUsize::new_unchecked($i) }
                }

                fn into_nonempty_vec(self) -> $crate::NEVec<T> {
                    self.into_nonempty_iter().collect()
                }
            }
        )+
    };
}

#[cfg(test)]
mod test {
    use crate::IntoNonEmptyIterator;
    use crate::NonEmptyIterator;

    #[test]
    fn test_iter() {
        let iter = [1, 2, 3, 4].into_nonempty_iter();
        let (first, rest) = iter.first();
        assert_eq!(1, first);
        assert_eq!(vec![2, 3, 4], rest.into_iter().collect::<Vec<_>>());

        let iter = [1].into_nonempty_iter();
        let (first, rest) = iter.first();
        assert_eq!(1, first);
        assert_eq!(0, rest.into_iter().count());

        assert_eq!(33, [1, -2, 33, 4].into_nonempty_iter().max());
    }
}
