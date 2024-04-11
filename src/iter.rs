//! Non-empty iterators.

use crate::nev;
use crate::NEVec;
use std::cell::RefCell;
use std::cmp::Ordering;
use std::collections::HashMap;
use std::collections::HashSet;
use std::hash::Hash;
use std::iter::Peekable;
use std::iter::{Product, Sum};
use std::num::NonZeroUsize;
use std::rc::Rc;
use std::result::Result;

// Iterator structs which _always_ have something if the source iterator is non-empty:
//
// - [x] Chain (if one, the other, or both are nonempty)
// - [x] Cloned
// - [x] Copied
// - [ ] Cycle
// - [x] Enumerate
// - [x] Map
// - [x] Once
// - [ ] Scan
// - [x] Take
// - [x] Zip (if both are nonempty)

/// Creates an iterator that yields an element exactly once.
///
/// See also [`std::iter::once`].
pub fn once<T>(value: T) -> Once<T> {
    Once::new(value)
}

/// An [`Iterator`] that is guaranteed to have at least one item.
pub trait NonEmptyIterator: IntoIterator {
    /// Advances this non-empty iterator, this consumes the iterator and returns the first item and a possibly empty iterator.
    fn next(self) -> (Self::Item, Self::IntoIter)
    where
        Self: Sized,
    {
        let mut iter = self.into_iter();
        (iter.next().unwrap(), iter)
    }

    /// Tests if every element of the iterator matches a predicate.
    ///
    /// Because this function always advances the iterator at least once, the
    /// non-empty guarantee is invalidated. Therefore, the function returns a bool
    /// and a potentially empty iterator that contains the remaining elements.
    ///
    /// See also [`Iterator::all`].
    ///
    /// ```
    /// use nonempty_collections::*;
    ///
    /// let n = nev![2,2,2];
    /// assert!(n.iter().all(|n| n % 2 == 0).0);
    /// ```
    fn all<F>(self, f: F) -> (bool, Self::IntoIter)
    where
        Self: Sized,
        F: FnMut(Self::Item) -> bool,
    {
        let mut iter = self.into_iter();
        (iter.all(f), iter)
    }

    /// Tests if any element of the iterator matches a predicate.
    ///
    /// See also [`Iterator::any`].
    ///
    /// ```
    /// use nonempty_collections::*;
    ///
    /// let n = nev![1,1,1,2,1,1];
    /// assert!(n.iter().any(|n| n % 2 == 0).0);
    /// assert!(!n.iter().any(|n| n % 3 == 0).0);
    /// ```
    fn any<F>(self, f: F) -> (bool, Self::IntoIter)
    where
        Self: Sized,
        F: FnMut(Self::Item) -> bool,
    {
        let mut iter = self.into_iter();
        (iter.any(f), iter)
    }

    /// Takes two iterators and creates a new non-empty iterator over both in sequence.
    ///
    /// Note that the second iterator need not be empty.
    ///
    /// See also [`Iterator::chain`].
    ///
    /// ```
    /// use nonempty_collections::*;
    ///
    /// let v = nev![1,2,3];
    /// let s = nes![4,5,6];
    /// let mut r: Vec<_> = v.into_nonempty_iter().chain(s).collect();
    /// r.sort();
    ///
    /// assert_eq!(vec![1,2,3,4,5,6], r);
    /// ```
    fn chain<U>(self, other: U) -> Chain<Self, U::IntoIter>
    where
        Self: Sized,
        U: IntoIterator<Item = Self::Item>,
    {
        Chain {
            a: self,
            b: other.into_iter(),
        }
    }

    /// Creates a non-empty iterator which clones all of its elements.
    ///
    /// This is useful when you have an iterator over `&T`, but you need an
    /// iterator over `T`.
    ///
    /// See also [`Iterator::cloned`].
    ///
    /// ```
    /// use nonempty_collections::*;
    /// use nonempty_collections::NEVec;
    ///
    /// #[derive(Debug, Clone, PartialEq, Eq)]
    /// enum Foo {
    ///     A,
    ///     B,
    ///     C,
    /// }
    ///
    /// let v0 = nev![Foo::A, Foo::B, Foo::C];
    /// let v1: NEVec<_> = v0.iter().collect();
    /// let v2: NEVec<_> = v0.iter().cloned().collect();
    ///
    /// assert_eq!(nev![&Foo::A, &Foo::B, &Foo::C], v1);
    /// assert_eq!(nev![Foo::A, Foo::B, Foo::C], v2);
    /// ```
    fn cloned<'a, T>(self) -> Cloned<Self>
    where
        Self: Sized + NonEmptyIterator<Item = &'a T>,
        T: Clone + 'a,
    {
        Cloned { iter: self }
    }

    /// Transforms an iterator into a collection, or some other concrete value.
    ///
    /// See also [`Iterator::collect`].
    ///
    /// ```
    /// use nonempty_collections::*;
    ///
    /// let n0 = nev![1,2,3,4];
    /// let n1 = n0.into_nonempty_iter().collect();
    /// assert_eq!(nev![1,2,3,4], n1);
    /// ```
    fn collect<B>(self) -> B
    where
        Self: Sized,
        B: FromNonEmptyIterator<Self::Item>,
    {
        FromNonEmptyIterator::from_nonempty_iter(self)
    }

    /// Creates a non-empty iterator which copies all of its elements.
    ///
    /// See also [`Iterator::copied`].
    ///
    /// ```
    /// use nonempty_collections::*;
    ///
    /// let n0 = nev![1,2,3,4];
    /// let n1 = n0.iter().copied().collect();
    /// assert_eq!(n0, n1);
    /// ```
    fn copied<'a, T>(self) -> Copied<Self>
    where
        Self: Sized + NonEmptyIterator<Item = &'a T>,
        T: Copy + 'a,
    {
        Copied { iter: self }
    }

    /// Consumes the non-empty iterator, counting the number of iterations and
    /// returning it.
    ///
    /// See also [`Iterator::count`].
    ///
    /// ```
    /// use nonempty_collections::*;
    ///
    /// let n = nev![1];
    /// assert_eq!(1, n.iter().count().get());
    ///
    /// let n = nev![1,2,3,4,5,6];
    /// assert_eq!(6, n.iter().count().get());
    /// ````
    fn count(self) -> NonZeroUsize
    where
        Self: Sized,
    {
        unsafe { NonZeroUsize::new_unchecked(self.into_iter().count()) }
    }

    /// Creates a non-empty iterator which gives the current iteration count as
    /// well as the next value.
    ///
    /// See also [`Iterator::enumerate`].
    ///
    /// ```
    /// use nonempty_collections::*;
    ///
    /// let s = nes!["Doriath", "Gondolin", "Nargothrond"];
    /// let total: usize = s.iter().enumerate().map(|(c, _)| c).sum();
    /// assert_eq!(3, total);
    /// ```
    fn enumerate(self) -> Enumerate<Self>
    where
        Self: Sized,
    {
        Enumerate { iter: self }
    }

    /// Creates an iterator which uses a closure to determine if an element
    /// should be yielded.
    ///
    /// **Note:** The iterator returned by this method is **not** a
    /// `NonEmptyIterator`, since there is never a guarantee that any element
    /// will pass the predicate.
    ///
    /// See also [`Iterator::filter`].
    ///
    /// ```
    /// use nonempty_collections::*;
    ///
    /// let n = nev![1,2,3,4,5,6];
    /// let v: Vec<_> = n.iter().map(|x| x * 2).filter(|&x| x % 3 == 0).collect();
    /// assert_eq!(vec![6, 12], v);
    /// ```
    fn filter<P>(self, predicate: P) -> std::iter::Filter<<Self as IntoIterator>::IntoIter, P>
    where
        Self: Sized,
        P: FnMut(&<Self as IntoIterator>::Item) -> bool,
    {
        self.into_iter().filter(predicate)
    }

    /// Creates an iterator that both filters and maps.
    ///
    /// **Note:** The iterator returned by this method is **not** a
    /// `NonEmptyIterator`, since there is never a guarantee that any element
    /// will yield `Some` from the given function.
    ///
    /// See also [`Iterator::filter_map`].
    ///
    /// ```
    /// use nonempty_collections::*;
    ///
    /// let v = nev!["Frodo", "Sam", "", "Peregrin", "Meriadoc"];
    /// let firsts: Vec<char> = v.into_nonempty_iter().filter_map(|s| s.chars().next()).collect();
    /// assert_eq!(vec!['F', 'S', 'P', 'M'], firsts);
    /// ```
    fn filter_map<B, F>(self, f: F) -> std::iter::FilterMap<<Self as IntoIterator>::IntoIter, F>
    where
        Self: Sized,
        F: FnMut(<Self as IntoIterator>::Item) -> Option<B>,
    {
        self.into_iter().filter_map(f)
    }

    /// Creates an iterator that works like `map`, but flattens nested,
    /// non-empty structure.
    ///
    /// See also [`Iterator::flat_map`].
    ///
    /// ```
    /// use nonempty_collections::*;
    ///
    /// let v = nev![1, 2, 3];
    /// let r = v.into_nonempty_iter().flat_map(|n| nev![n]).collect();
    /// assert_eq!(nev![1, 2, 3], r);
    /// ```
    #[inline]
    fn flat_map<U, F>(self, f: F) -> FlatMap<Self, F>
    where
        Self: Sized,
        F: FnMut(Self::Item) -> U,
        U: IntoNonEmptyIterator,
    {
        FlatMap {
            iter: self.into_nonempty_iter(),
            f,
        }
    }

    // fn flatten<F, V>(self) -> FlatMap<Self, V, F>
    // where
    //     Self: Sized,
    //     Self::Item: IntoNonEmptyIterator<IntoIter = V, Item = V::Item>,
    //     V: NonEmptyIterator,
    // {
    //     self.flat_map(|ne| ne)
    // }

    /// Folds every element into an accumulator by applying an operation,
    /// returning the final result.
    ///
    /// See also [`Iterator::fold`].
    ///
    /// ```
    /// use nonempty_collections::*;
    ///
    /// let n = nev![1,2,3,4];
    /// let r = n.into_nonempty_iter().fold(0, |acc, x| acc + x);
    /// assert_eq!(10, r);
    /// ```
    fn fold<B, F>(self, init: B, f: F) -> B
    where
        Self: Sized,
        F: FnMut(B, Self::Item) -> B,
    {
        self.into_iter().fold(init, f)
    }

    /// Group the non-empty input stream into concrete, non-empty subsections
    /// via a given function. The cutoff criterion is whether the return value
    /// of `f` changes between two consecutive elements.
    ///
    /// ```
    /// use nonempty_collections::*;
    ///
    /// let n = nev![1,1,2,3,3];
    /// let r: NEVec<_> = n.into_nonempty_iter().group_by(|n| *n).collect();
    /// assert_eq!(r, nev![nev![1,1], nev![2], nev![3,3]]);
    ///
    /// let n = nev![2,4,6,7,9,1,2,4,6,3];
    /// let r: NEVec<_> = n.into_nonempty_iter().group_by(|n| n % 2 == 0).collect();
    /// assert_eq!(r, nev![nev![2,4,6], nev![7,9,1], nev![2,4,6], nev![3]]);
    /// ```
    fn group_by<K, F>(self, f: F) -> NEGroupBy<Self, K, Self::Item, F>
    where
        Self: Sized,
        F: FnMut(&Self::Item) -> K,
        K: PartialEq,
    {
        NEGroupBy {
            iter: self,
            f,
            prev: None,
            curr: None,
        }
    }

    /// Takes a closure and creates a non-empty iterator which calls that
    /// closure on each element.
    ///
    /// If `self` is a `NonEmptyIterator`, then so is [`Map`].
    ///
    /// See also [`Iterator::map`].
    ///
    /// ```
    /// use nonempty_collections::*;
    /// use nonempty_collections::NEVec;
    ///
    /// let s = nes![1,2,3];
    /// let mut v: NEVec<_> = s.iter().map(|n| n * 2).collect();
    /// v.sort();
    /// assert_eq!(nev![2,4,6], v);
    /// ```
    #[inline]
    fn map<U, F>(self, f: F) -> Map<Self, F>
    where
        Self: Sized,
        F: FnMut(Self::Item) -> U,
    {
        Map {
            iter: self.into_iter().map(f),
        }
    }

    /// Returns the maximum element of a non-empty iterator.
    ///
    /// Unlike [`Iterator::max`], this always yields a value.
    ///
    /// ```
    /// use nonempty_collections::*;
    ///
    /// let v = nev![1, 1000, 2, 3];
    /// assert_eq!(1000, v.into_nonempty_iter().max());
    /// ```
    fn max(self) -> Self::Item
    where
        Self: Sized,
        Self::Item: Ord,
    {
        self.max_by(Ord::cmp)
    }

    /// Returns the element that gives the maximum value with respect to the
    /// given comparison function.
    ///
    /// Unlike [`Iterator::max_by`], this always yields a value.
    fn max_by<F>(self, compare: F) -> Self::Item
    where
        Self: Sized,
        F: Fn(&Self::Item, &Self::Item) -> Ordering,
    {
        let (first, iter) = self.next();

        iter.into_iter()
            .fold(first, |acc, item| match compare(&acc, &item) {
                Ordering::Less => item,
                _ => acc,
            })
    }

    /// Returns the element that gives the maximum value from the
    /// specified function.
    ///
    /// There are two differences with [`Iterator::max_by_key`]:
    /// - this function always yields a value while [`Iterator::max_by_key`]
    ///   yields an `Option`.
    /// - if several elements are equally maximum, the *first* element is
    ///   returned (unlike [`Iterator::max_by_key`] which returns the last
    ///   element).
    ///
    /// # Examples
    ///
    /// ```
    /// use nonempty_collections::*;
    /// let max = nev!["hi", "hey", "rust", "yolo"].into_nonempty_iter().max_by_key(|item| item.len());
    /// assert_eq!("rust", max);
    /// ```
    fn max_by_key<B, F>(self, mut key: F) -> Self::Item
    where
        Self: Sized,
        B: Ord,
        F: FnMut(&Self::Item) -> B,
    {
        self.map(|item| (key(&item), item))
            .max_by(|(left_key, _), (right_key, _)| left_key.cmp(right_key))
            .1
    }

    /// Returns the minimum element of a non-empty iterator.
    ///
    /// Unlike [`Iterator::min`], this always yields a value.
    ///
    /// ```
    /// use nonempty_collections::*;
    ///
    /// let v = nev![1000, 1, 2000, 3000];
    /// assert_eq!(1, v.into_nonempty_iter().min());
    /// ```
    fn min(self) -> Self::Item
    where
        Self: Sized,
        Self::Item: Ord,
    {
        self.min_by(Ord::cmp)
    }

    /// Returns the element that gives the minimum value with respect to the
    /// given comparison function.
    ///
    /// Unlike [`Iterator::min_by`], this always yields a value.
    fn min_by<F>(self, compare: F) -> Self::Item
    where
        Self: Sized,
        F: Fn(&Self::Item, &Self::Item) -> Ordering,
    {
        let (first, iter) = self.next();

        iter.into_iter()
            .fold(first, |acc, item| match compare(&acc, &item) {
                Ordering::Greater => item,
                _ => acc,
            })
    }

    /// Returns the element that gives the minimum value from the
    /// specified function.
    ///
    /// There are two differences with [`Iterator::min_by_key`]:
    /// - this function always yields a value while [`Iterator::min_by_key`]
    ///   yields an `Option`.
    /// - if several elements are equally minimum, the *first* element is
    ///   returned (unlike [`Iterator::min_by_key`] which returns the last
    ///   element).
    ///
    /// # Examples
    ///
    /// ```
    /// use nonempty_collections::*;
    /// let min = nev!["hi", "hello", "greetings", "hy"].into_nonempty_iter().min_by_key(|item| item.len());
    /// assert_eq!("hi", min);
    /// ```
    fn min_by_key<B, F>(self, mut key: F) -> Self::Item
    where
        Self: Sized,
        B: Ord,
        F: FnMut(&Self::Item) -> B,
    {
        self.map(|item| (key(&item), item))
            .min_by(|(left_key, _), (right_key, _)| left_key.cmp(right_key))
            .1
    }

    /// Returns the `n`th element of the iterator.
    ///
    /// See also [`Iterator::nth`].
    ///
    /// ```
    /// use nonempty_collections::*;
    ///
    /// let n = nev![0,1,2,3,4,5,6];
    /// assert_eq!(Some(&0), n.iter().nth(0));
    ///
    /// let n = nev![0,1,2,3,4,5,6];
    /// assert_eq!(Some(&6), n.iter().nth(6));
    ///
    /// let n = nev![0,1,2,3,4,5,6];
    /// assert_eq!(None, n.iter().nth(100));
    /// ```
    fn nth(self, n: usize) -> Option<Self::Item>
    where
        Self: Sized,
    {
        self.into_iter().nth(n)
    }

    /// Skip the first `n` elements.
    ///
    /// Note that the result will not be non-empty.
    ///
    /// See also [`Iterator::skip`].
    ///
    /// ```
    /// use nonempty_collections::*;
    ///
    /// let v = nev![1, 2, 3];
    /// assert_eq!(Some(&3), v.iter().skip(2).next());
    /// ```
    fn skip(self, n: usize) -> std::iter::Skip<<Self as IntoIterator>::IntoIter>
    where
        Self: Sized,
    {
        self.into_iter().skip(n)
    }

    /// Skips over all initial elements that pass a given predicate.
    ///
    /// **Note**: This does not yield a non-empty iterator, since there is no
    /// guarantee that anything will fail the predicate.
    ///
    /// See also [`Iterator::skip_while`].
    ///
    /// ```
    /// use nonempty_collections::*;
    ///
    /// let v = nev![2, 4, 6, 7, 8];
    /// let r: Vec<_> = v.into_nonempty_iter().skip_while(|n| n % 2 == 0).collect();
    /// assert_eq!(vec![7, 8], r);
    /// ```
    fn skip_while<P>(self, pred: P) -> std::iter::SkipWhile<<Self as IntoIterator>::IntoIter, P>
    where
        Self: Sized,
        P: FnMut(&<Self as IntoIterator>::Item) -> bool,
    {
        self.into_iter().skip_while(pred)
    }

    /// Sums the elements of a non-empty iterator.
    ///
    /// See also [`Iterator::sum`].
    ///
    /// ```
    /// use nonempty_collections::*;
    ///
    /// let sum: u32 = nev![1,2,3,4].iter().sum();
    /// assert_eq!(10, sum);
    /// ```
    fn sum<S>(self) -> S
    where
        Self: Sized + IntoIterator,
        S: Sum<<Self as IntoIterator>::Item>,
    {
        Sum::sum(self.into_iter())
    }

    /// Iterates over the first `n` elements, or fewer if the underlying iterator ends sooner.
    ///
    /// See also [`Iterator::take`].
    ///
    /// # Panics
    ///
    /// Panics if `n == 0`.
    ///
    /// # Examples
    ///
    /// ```
    /// use nonempty_collections::*;
    /// use core::num::NonZeroUsize;
    ///
    /// let n: NEVec<_> = nev![1,2,3].iter().map(|n| n * 2).take(NonZeroUsize::new(2).unwrap()).collect();
    /// assert_eq!(nev![2,4], n);
    /// ```
    fn take(self, n: NonZeroUsize) -> Take<Self>
    where
        Self: Sized,
    {
        Take {
            iter: self.into_iter().take(n.get()),
        }
    }

    /// Iterates over all initial elements that pass a given predicate.
    ///
    /// **Note**: This does not yield a non-empty iterator, since there is no
    /// guarantee that anything will pass the predicate.
    ///
    /// See also [`Iterator::take_while`].
    ///
    /// ```
    /// use nonempty_collections::*;
    ///
    /// let v = nev![2, 4, 6, 7, 8];
    /// let r: Vec<_> = v.into_nonempty_iter().take_while(|n| n % 2 == 0).collect();
    /// assert_eq!(vec![2, 4, 6], r);
    /// ```
    fn take_while<P>(self, pred: P) -> std::iter::TakeWhile<<Self as IntoIterator>::IntoIter, P>
    where
        Self: Sized,
        P: FnMut(&<Self as IntoIterator>::Item) -> bool,
    {
        self.into_iter().take_while(pred)
    }

    /// Iterates over the entire non-empty iterator, multiplying all the
    /// elements.
    ///
    /// See also [`Iterator::product`].
    ///
    /// ```
    /// use nonempty_collections::*;
    ///
    /// let prod: u32 = nev![1,2,3,4].iter().product();
    /// assert_eq!(24, prod);
    /// ```
    fn product<P>(self) -> P
    where
        Self: Sized + IntoIterator,
        P: Product<<Self as IntoIterator>::Item>,
    {
        Product::product(self.into_iter())
    }

    /// "Zips up" two non-empty iterators into a single one, while preserving
    /// non-emptiness.
    ///
    /// See also [`Iterator::zip`].
    ///
    /// ```
    /// use nonempty_collections::*;
    ///
    /// let a = nev![1, 2, 3];
    /// let b = nev![4, 5, 6, 7];
    /// let r = a.into_nonempty_iter().zip(b).map(|(av, bv)| av + bv).collect();
    /// assert_eq!(nev![5, 7, 9], r);
    /// ```
    fn zip<U>(self, other: U) -> Zip<Self, U::IntoNEIter>
    where
        Self: Sized,
        U: IntoNonEmptyIterator,
    {
        Zip {
            a: self,
            b: other.into_nonempty_iter(),
        }
    }

    /// Reduces the elements to a single one, by repeatedly applying a reducing
    /// operation.
    ///
    /// See also [`Iterator::reduce`].
    ///
    /// ```
    /// use nonempty_collections::*;
    ///
    /// let a = nev![1, 2, 3, 4];
    /// let b = a.clone();
    ///
    /// let x = a.into_nonempty_iter().reduce(|acc, v| acc + v);
    /// assert_eq!(x, 10);
    ///
    /// let y = b.into_nonempty_iter().reduce(|acc, v| acc * v);
    /// assert_eq!(y, 24);
    /// ```
    fn reduce<F>(self, f: F) -> Self::Item
    where
        Self: Sized,
        F: FnMut(Self::Item, Self::Item) -> Self::Item,
    {
        self.into_iter().reduce(f).unwrap()
    }
}

/// Conversion from a [`NonEmptyIterator`].
pub trait FromNonEmptyIterator<T>: Sized {
    /// Creates a value from a [`NonEmptyIterator`].
    fn from_nonempty_iter<I>(iter: I) -> Self
    where
        I: IntoNonEmptyIterator<Item = T>;
}

impl<T> FromNonEmptyIterator<T> for Vec<T> {
    fn from_nonempty_iter<I>(iter: I) -> Self
    where
        I: IntoNonEmptyIterator<Item = T>,
    {
        iter.into_nonempty_iter().into_iter().collect()
    }
}

impl<K, V> FromNonEmptyIterator<(K, V)> for HashMap<K, V>
where
    K: Eq + Hash,
{
    fn from_nonempty_iter<I>(iter: I) -> Self
    where
        I: IntoNonEmptyIterator<Item = (K, V)>,
    {
        let ((head_key, head_val), rest) = iter.into_nonempty_iter().first();

        let mut hm = HashMap::new();
        hm.insert(head_key, head_val);
        hm.extend(rest);
        hm
    }
}

impl<T> FromNonEmptyIterator<T> for HashSet<T>
where
    T: Eq + Hash,
{
    fn from_nonempty_iter<I>(iter: I) -> Self
    where
        I: IntoNonEmptyIterator<Item = T>,
    {
        iter.into_nonempty_iter().into_iter().collect()
    }
}

impl<A, E, V> FromNonEmptyIterator<Result<A, E>> for Result<V, E>
where
    V: FromNonEmptyIterator<A>,
{
    fn from_nonempty_iter<I>(iter: I) -> Result<V, E>
    where
        I: IntoNonEmptyIterator<Item = Result<A, E>>,
    {
        let (head, rest) = iter.into_nonempty_iter().next();
        let head: A = head?;

        let mut buf = NEVec::new(head);

        for item in rest.into_iter() {
            let item: A = item?;
            buf.push(item);
        }
        let new_iter = buf.into_nonempty_iter();
        let output: V = FromNonEmptyIterator::from_nonempty_iter(new_iter);
        Ok(output)
    }
}

impl<I: NonEmptyIterator> IntoNonEmptyIterator for I {
    type IntoNEIter = I;

    fn into_nonempty_iter(self) -> Self::IntoNEIter {
        self
    }
}

/// Conversion into a [`NonEmptyIterator`].
pub trait IntoNonEmptyIterator: IntoIterator {
    /// Which kind of [`NonEmptyIterator`] are we turning this into?
    type IntoNEIter: NonEmptyIterator<Item = Self::Item>;

    /// Creates a [`NonEmptyIterator`] from a value.
    fn into_nonempty_iter(self) -> Self::IntoNEIter;
}

/// Similar to [`std::iter::Map`], but with additional non-emptiness guarantees.
pub struct Map<I: NonEmptyIterator, F> {
    iter: std::iter::Map<I::IntoIter, F>,
}

impl<U, I, F> NonEmptyIterator for Map<I, F>
where
    I: NonEmptyIterator,
    F: FnMut(I::Item) -> U,
{
}

/// ```
/// use nonempty_collections::*;
///
/// let v: Vec<_> = nev![1,2,3].iter().map(|n| n * 2).collect();
/// ```
impl<U, I, F> IntoIterator for Map<I, F>
where
    I: NonEmptyIterator,
    F: FnMut(I::Item) -> U,
{
    type Item = U;

    type IntoIter = std::iter::Map<I::IntoIter, F>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter
    }
}

/// An iterator that clones the elements of an underlying iterator.
///
/// See also [`std::iter::Cloned`].
pub struct Cloned<I> {
    iter: I,
}

impl<'a, I, T: 'a> NonEmptyIterator for Cloned<I>
where
    I: NonEmptyIterator<Item = &'a T>,
    T: Clone,
{
}

impl<'a, I, T: 'a> IntoIterator for Cloned<I>
where
    I: IntoIterator<Item = &'a T>,
    T: Clone,
{
    type Item = T;

    type IntoIter = std::iter::Cloned<I::IntoIter>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter.into_iter().cloned()
    }
}

/// An iterator that yields the current count and the element during iteration.
///
/// See also [`std::iter::Enumerate`].
pub struct Enumerate<I> {
    iter: I,
}

impl<I> NonEmptyIterator for Enumerate<I> where I: NonEmptyIterator {}

impl<I> IntoIterator for Enumerate<I>
where
    I: IntoIterator,
{
    type Item = (usize, I::Item);

    type IntoIter = std::iter::Enumerate<I::IntoIter>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter.into_iter().enumerate()
    }
}

/// A non-empty iterator that only iterates over the first `n` iterations.
///
/// See also [`Iterator::take`].
pub struct Take<I: NonEmptyIterator> {
    iter: std::iter::Take<I::IntoIter>,
}

impl<I> NonEmptyIterator for Take<I> where I: NonEmptyIterator {}

/// ```
/// use nonempty_collections::*;
/// use core::num::NonZeroUsize;
///
/// let v = nev![1,2,3];
/// let r = v.iter().take(NonZeroUsize::new(1).unwrap()).into_iter().count();
/// assert_eq!(1, r);
/// ```
impl<I> IntoIterator for Take<I>
where
    I: NonEmptyIterator,
{
    type Item = I::Item;

    type IntoIter = std::iter::Take<I::IntoIter>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter
    }
}

/// A non-empty iterator that links two iterators together, in a chain.
pub struct Chain<A, B> {
    a: A,
    b: B,
}

impl<A, B> NonEmptyIterator for Chain<A, B>
where
    A: NonEmptyIterator,
    B: Iterator<Item = A::Item>,
{
}

impl<A, B> IntoIterator for Chain<A, B>
where
    A: IntoIterator,
    B: IntoIterator<Item = A::Item>,
{
    type Item = A::Item;

    type IntoIter = std::iter::Chain<A::IntoIter, B::IntoIter>;

    fn into_iter(self) -> Self::IntoIter {
        self.a.into_iter().chain(self.b)
    }
}

/// A non-empty iterator that yields an element exactly once.
pub struct Once<T> {
    once: std::option::IntoIter<T>,
}

impl<T> Once<T> {
    pub(crate) fn new(once: T) -> Once<T> {
        Once {
            once: Some(once).into_iter(),
        }
    }
}

impl<T> NonEmptyIterator for Once<T> {}

impl<T> IntoIterator for Once<T> {
    type Item = T;

    type IntoIter = std::option::IntoIter<T>;

    fn into_iter(self) -> Self::IntoIter {
        self.once
    }
}

/// A non-empty iterator that copies the elements of an underlying non-empty
/// iterator.
///
/// See also [`std::iter::Copied`].
pub struct Copied<I> {
    iter: I,
}

impl<'a, I, T: 'a> NonEmptyIterator for Copied<I>
where
    I: NonEmptyIterator<Item = &'a T>,
    T: Copy,
{
}

impl<'a, I, T: 'a> IntoIterator for Copied<I>
where
    I: IntoIterator<Item = &'a T>,
    T: Copy,
{
    type Item = T;

    type IntoIter = std::iter::Copied<I::IntoIter>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter.into_iter().copied()
    }
}

/// A non-empty iterator that "zips up" its sources.
///
/// See also [`std::iter::Zip`].
pub struct Zip<A, B> {
    a: A,
    b: B,
}

impl<A, B> NonEmptyIterator for Zip<A, B>
where
    A: NonEmptyIterator,
    B: NonEmptyIterator,
{
}

impl<A, B> IntoIterator for Zip<A, B>
where
    A: IntoIterator,
    B: IntoIterator,
{
    type Item = (<A as IntoIterator>::Item, <B as IntoIterator>::Item);

    type IntoIter = std::iter::Zip<<A as IntoIterator>::IntoIter, <B as IntoIterator>::IntoIter>;

    fn into_iter(self) -> Self::IntoIter {
        self.a.into_iter().zip(self.b)
    }
}

/// Wrapper struct for powering [`NonEmptyIterator::group_by`].
pub struct NEGroupBy<I, K, V, F> {
    iter: I,
    f: F,
    prev: Option<K>,
    curr: Option<NEVec<V>>,
}

impl<I, K, V, F> NonEmptyIterator for NEGroupBy<I, K, V, F>
where
    I: NonEmptyIterator<Item = V>,
    F: FnMut(&V) -> K,
    K: PartialEq,
{
    type Item = NEVec<V>;

    type IntoIter = Peekable<GroupBy<<I::IntoIter as IntoIterator>::IntoIter, K, V, F>>;

    fn first(self) -> (Self::Item, Self::IntoIter) {
        let (mut head, iter) = self.iter.first();

        let gb = GroupBy {
            iter: iter.into_iter(),
            f: Rc::new(RefCell::new(self.f)),
            prev: None,
            curr: None,
        };

        let rc = gb.f.clone();
        let mut peek = gb.peekable();

        match peek.peek() {
            Some(c) => {
                // Proactive drop of `f` to avoid a panic elsewhere.
                let must_append = {
                    let mut f = rc.borrow_mut();
                    f(&head) == f(c.first())
                };

                if must_append {
                    // NOTE: This is a safe unwrap.
                    let mut next = peek.next().unwrap();

                    // HACK: 2024-08-26 This is a way to fuse two NEVec when you
                    // don't own one of them.
                    let old_head = &mut next.head;
                    std::mem::swap(old_head, &mut head);
                    next.tail.push(head);
                    next.tail.rotate_right(1);

                    (next, peek)
                } else {
                    (nev![head], peek)
                }
            }
            None => (nev![head], peek),
        }
    }

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            match self.iter.next() {
                None => return self.curr.take(),
                Some(v) => {
                    let f = &mut self.f;
                    let k = f(&v);

                    match (self.prev.as_ref(), &mut self.curr) {
                        // Continue some run of similar values.
                        (Some(p), Some(c)) if p == &k => {
                            c.push(v);
                        }
                        // We found a break; finally yield an NEVec.
                        (Some(_), Some(_)) => {
                            let curr = self.curr.take();
                            self.curr = Some(nev![v]);
                            self.prev = Some(k);
                            return curr;
                        }
                        // Very first iteration.
                        (_, _) => {
                            self.prev = Some(k);
                            self.curr = Some(nev![v]);
                        }
                    }
                }
            }
        }
    }
}

impl<I, K, V, F> IntoIterator for NEGroupBy<I, K, V, F>
where
    I: IntoIterator,
    F: FnMut(&I::Item) -> K,
    K: PartialEq,
{
    type Item = NEVec<I::Item>;

    type IntoIter = GroupBy<<I as IntoIterator>::IntoIter, K, I::Item, F>;

    fn into_iter(self) -> Self::IntoIter {
        GroupBy {
            iter: self.iter.into_iter(),
            f: Rc::new(RefCell::new(self.f)),
            prev: None,
            curr: None,
        }
    }
}

/// A (possibly empty) definition of the group-by operation that enables
/// [`NEGroupBy`] to be written. You aren't expected to use this directly, thus
/// there is no way to construct one.
pub struct GroupBy<I, K, V, F> {
    iter: I,
    f: Rc<RefCell<F>>,
    prev: Option<K>,
    curr: Option<NEVec<V>>,
}

impl<I, K, V, F> Iterator for GroupBy<I, K, V, F>
where
    I: Iterator<Item = V>,
    F: FnMut(&I::Item) -> K,
    K: PartialEq,
{
    type Item = NEVec<I::Item>;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            match self.iter.next() {
                None => return self.curr.take(),
                Some(v) => {
                    let k = {
                        let mut f = self.f.borrow_mut();
                        f(&v)
                    };

                    match (self.prev.as_ref(), &mut self.curr) {
                        // Continue some run of similar values.
                        (Some(p), Some(c)) if p == &k => {
                            c.push(v);
                        }
                        // We found a break; finally yield an NEVec.
                        (Some(_), Some(_)) => {
                            let curr = self.curr.take();
                            self.curr = Some(nev![v]);
                            self.prev = Some(k);
                            return curr;
                        }
                        // Very first iteration.
                        (_, _) => {
                            self.prev = Some(k);
                            self.curr = Some(nev![v]);
                        }
                    }
                }
            }
        }
    }
}

/// Flatten nested, non-empty structures.
///
/// See also [`std::iter::FlatMap`].
pub struct FlatMap<I, F> {
    iter: I,
    f: F,
}

impl<I, U, F> NonEmptyIterator for FlatMap<I, F>
where
    I: NonEmptyIterator,
    F: FnMut(I::Item) -> U,
    U: IntoNonEmptyIterator,
{
}

/// ```
/// use nonempty_collections::*;
///
/// let v = nev![1, 2, 3];
/// let r: Vec<_> = v.into_nonempty_iter().flat_map(|n| nev![n]).into_iter().collect();
/// assert_eq!(vec![1, 2, 3], r);
/// ```
impl<I, U, F> IntoIterator for FlatMap<I, F>
where
    I: IntoIterator,
    F: FnMut(I::Item) -> U,
    U: IntoNonEmptyIterator,
{
    type Item = U::Item;

    type IntoIter = std::iter::FlatMap<I::IntoIter, U, F>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter.into_iter().flat_map(self.f)
    }
}

/// Convenience trait extending [`Iterator`].
pub trait IteratorExt {
    /// The type of the elements being iterated over.
    type Item;

    /// Which kind of [`NonEmptyIterator`] are we turning this into?
    type IntoIter: NonEmptyIterator<Item = Self::Item>;

    /// Tries to convert `self` into a [`NonEmptyIterator`].
    ///
    /// ```
    /// use nonempty_collections::*;
    ///
    /// let a = vec![1];
    /// let x = a.into_iter().to_nonempty_iter();
    /// assert!(x.is_some());
    ///
    /// let y = x.unwrap().collect::<NEVec<_>>();
    /// assert_eq!(y.len().get(), 1);
    /// ```
    ///
    /// ```
    /// use nonempty_collections::*;
    ///
    /// let b: Vec::<u8> = vec![];
    /// let x = b.into_iter().to_nonempty_iter();
    ///
    /// assert!(x.is_none());
    /// ```
    ///
    /// To construct non-empty collections directly, consider macros like [`crate::nev!`].
    fn to_nonempty_iter(self) -> Option<Self::IntoIter>;
}

impl<I, T> IteratorExt for I
where
    I: Iterator<Item = T>,
{
    type Item = T;
    type IntoIter = Chain<Once<Self::Item>, Self>;

    /// Tries to convert `self` into [`NonEmptyIterator`]. Calls `self.next()`
    /// once. If `self` doesn't return `Some` upon the first call to `next()`,
    /// returns `None`.
    fn to_nonempty_iter(mut self) -> Option<Self::IntoIter> {
        self.next().map(|head| once(head).chain(self))
    }
}

/// Convenience trait extending [`IntoIterator`].
pub trait IntoIteratorExt {
    /// The type of the elements being iterated over.
    type Item;
    /// Which kind of [`NonEmptyIterator`] are we turning this into?
    type IntoIter: NonEmptyIterator<Item = Self::Item>;

    /// Tries to convert `self` into a [`NonEmptyIterator`].
    ///
    /// ```
    /// use nonempty_collections::*;
    ///
    /// let a = vec![1];
    /// let x = a.try_into_nonempty_iter();
    /// assert!(x.is_some());
    ///
    /// let y = x.unwrap().collect::<NEVec<_>>();
    /// assert_eq!(y.len().get(), 1);
    /// ```
    ///
    /// ```
    /// use nonempty_collections::*;
    ///
    /// let b: Vec::<u8> = vec![];
    /// let x = b.try_into_nonempty_iter();
    ///
    /// assert!(x.is_none());
    /// ```
    ///
    /// To construct non-empty collections directly, consider macros like [`crate::nev!`].
    fn try_into_nonempty_iter(self) -> Option<Self::IntoIter>;
}

impl<T> IntoIteratorExt for T
where
    T: IntoIterator,
{
    type Item = T::Item;

    type IntoIter = Chain<Once<Self::Item>, T::IntoIter>;

    /// Tries to convert `self` into [`NonEmptyIterator`]. Calls `self.next()`
    /// once. If `self` doesn't return `Some` upon the first call to `next()`,
    /// returns `None`.
    fn try_into_nonempty_iter(self) -> Option<Self::IntoIter> {
        self.into_iter().to_nonempty_iter()
    }
}

/// A wrapper type for easy derivation of [`IntoIterator`] for anything
/// that's already [`NonEmptyIterator`].
pub struct IntoIteratorProxy<T> {
    pub(crate) iter: T,
}

impl<T> Iterator for IntoIteratorProxy<T>
where
    T: NonEmptyIterator,
{
    type Item = T::Item;

    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{nem, NEMap};

    #[test]
    fn into_hashset() {
        let m = nem!['a' => 1, 'b' => 2, 'c' => 3];
        let _: HashSet<_> = m.values().collect();
    }

    #[test]
    fn into_hashmap() {
        let m = nem!['a' => 1, 'b' => 2, 'c' => 3];
        let h: HashMap<_, _> = m.iter().map(|(k, v)| (*k, *v)).collect();
        let n = NEMap::try_from(h).unwrap();
        assert_eq!(m, n);
    }

    #[test]
    fn group_by_iterator_normal() {
        let orig: Vec<usize> = vec![1, 1, 2, 3, 3];
        let iter = orig.into_iter().map(|n| n + 1);
        let gb = GroupBy {
            iter,
            f: Rc::new(RefCell::new(|v: &usize| v.clone())),
            prev: None,
            curr: None,
        };

        let res: Vec<_> = gb.collect();
        assert_eq!(res, vec![nev![2, 2], nev![3], nev![4, 4]]);
    }

    #[test]
    fn group_by_iterator_empty() {
        let orig: Vec<usize> = vec![1, 1, 2, 3, 3];
        let iter = orig.into_iter().filter(|_| false);
        let gb = GroupBy {
            iter,
            f: Rc::new(RefCell::new(|v: &usize| v.clone())),
            prev: None,
            curr: None,
        };

        let res: Vec<_> = gb.collect();
        assert_eq!(res, Vec::new());
    }

    #[test]
    fn group_by_iterator_singleton() {
        let orig: Vec<usize> = vec![1];
        let iter = orig.into_iter();
        let gb = GroupBy {
            iter,
            f: Rc::new(RefCell::new(|v: &usize| v.clone())),
            prev: None,
            curr: None,
        };

        let res: Vec<_> = gb.collect();
        assert_eq!(res, vec![nev![1]]);
    }
}
