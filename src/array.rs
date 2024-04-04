//! Extends non-zero length arrays with conversion methods to non-empty collections.

use std::num::NonZeroUsize;

use crate::impl_nonempty_iter_for_arrays;
use crate::IntoNonEmptyIterator;
use crate::NonEmptyIterator;

/// Provides extension methods for non-empty arrays.
///
/// # Examples
///
/// Create a non-empty slice of an array:
/// ```
/// # use nonempty_collections::*;
/// assert_eq!(NESlice::new(&1, &[2]), [1, 2].as_nonempty_slice());
/// ```
/// Get the length of an array as a [`NonZeroUsize`]:
/// ```
/// # use nonempty_collections::NonEmptyArrayExt;
/// # use std::num::NonZeroUsize;
/// assert_eq!(NonZeroUsize::MIN, [1].nonzero_len());
/// ```
/// Copy into a non-empty vec:
/// ```
/// # use nonempty_collections::*;
/// assert_eq!(nev![4], [4].to_nonempty_vec());
/// ```
pub trait NonEmptyArrayExt<T> {
    /// Create a `NESlice` that borrows the contents of `self`.
    fn as_nonempty_slice(&self) -> crate::NESlice<'_, T>;

    /// Returns the length of this array as a [`NonZeroUsize`].
    fn nonzero_len(&self) -> NonZeroUsize;

    /// Copies `self` into a new [`NEVec`].
    fn to_nonempty_vec(&self) -> crate::NEVec<T>
    where
        T: Clone;
}

/// Non-empty iterator for arrays with length > 0.
///
/// # Examples
///
/// Use non-zero length arrays anywhere a [`IntoNonEmptyIterator`] is expected.
/// ```
/// # use nonempty_collections::*;
/// # use std::num::NonZeroUsize;
/// is_one([0]);
/// fn is_one<T>(iter: impl IntoNonEmptyIterator<Item = T>){
///     assert_eq!(NonZeroUsize::MIN, iter.into_nonempty_iter().count());
/// }
/// ```
/// Only compiles for non-empty arrays:
/// ```compile_fail
/// # use nonempty_collections::*;
/// is_one([]); // doesn't compile because it is empty
/// fn is_one(iter: impl IntoNonEmptyIterator<Item = usize>){}
/// ```
///
pub struct ArrayNonEmptyIterator<T, const C: usize> {
    iter: core::array::IntoIter<T, C>,
}

impl<T, const C: usize> NonEmptyIterator for ArrayNonEmptyIterator<T, C> {
    type Item = T;

    type IntoIter = core::array::IntoIter<T, C>;

    fn first(self) -> (Self::Item, Self::IntoIter) {
        let mut iter = self.iter.into_iter();
        (iter.next().unwrap(), iter)
    }

    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next()
    }
}

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
                fn as_nonempty_slice(&self) -> crate::NESlice<'_, T> {
                    // This should never panic because a slice with length > 0 is non-empty by definition
                    crate::NESlice::from_slice(self).unwrap()
                }

                fn nonzero_len(&self) -> NonZeroUsize {
                    // This should be fine because $i is always > 0
                    unsafe { NonZeroUsize::new_unchecked($i) }
                }

                fn to_nonempty_vec(&self) -> crate::NEVec<T>
                where
                    T: Clone
                {
                    // This should never panic because a slice with length > 0 is non-empty by definition
                    crate::NEVec::from_slice(self).unwrap()
                }
            }
        )+
    };
}
