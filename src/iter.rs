//! Non-empty iterators.

use std::collections::HashSet;
use std::hash::Hash;
use std::iter::{Product, Sum};

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
// - [ ] Zip (if both are nonempty)

/// Creates an iterator that yields an element exactly once.
///
/// See also [`std::iter::once`].
pub fn once<T>(value: T) -> Once<T> {
    Once::new(value)
}

/// An [`Iterator`] that is guaranteed to have at least one item.
pub trait NonEmptyIterator {
    /// The value produced by this iterator.
    type Item;

    /// Each `NonEmptyIterator` knows about a possibly-empty variant of itself,
    /// likely from `std`. Critically, they share an `Item`.
    type IntoIter: IntoIterator<Item = Self::Item>;

    /// A `NonEmptyIterator` can, by consuming itself, reliably produce its
    /// first element, alongside its possibly-empty variant.
    fn first(self) -> (Self::Item, Self::IntoIter);

    /// Advances the iterator and returns the next value.
    ///
    /// See also [`Iterator::next`].
    fn next(&mut self) -> Option<Self::Item>;

    /// Tests if every element of the iterator matches a predicate.
    ///
    /// See also [`Iterator::all`].
    fn all<F>(&mut self, f: F) -> bool
    where
        Self: Sized,
        F: FnMut(Self::Item) -> bool,
    {
        let mut fun = f;

        loop {
            match self.next() {
                Some(i) => {
                    if !fun(i) {
                        return false;
                    }
                }
                None => {
                    return true;
                }
            }
        }
    }

    /// Tests if any element of the iterator matches a predicate.
    ///
    /// See also [`Iterator::any`].
    fn any<F>(&mut self, f: F) -> bool
    where
        Self: Sized,
        F: FnMut(Self::Item) -> bool,
    {
        let mut fun = f;

        loop {
            match self.next() {
                None => {
                    return false;
                }
                Some(i) => {
                    if fun(i) {
                        return true;
                    }
                }
            }
        }
    }

    /// Takes two iterators and creates a new non-empty iterator over both in sequence.
    ///
    /// Note that the second iterator need not be empty.
    ///
    /// See also [`Iterator::chain`].
    ///
    /// ```
    /// use nonempty_collections::prelude::*;
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
    /// use nonempty_collections::prelude::*;
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
    fn cloned<'a, T: 'a>(self) -> Cloned<Self>
    where
        Self: Sized + NonEmptyIterator<Item = &'a T>,
        T: Clone,
    {
        Cloned { iter: self }
    }

    /// Transforms an iterator into a collection, or some other concrete value.
    ///
    /// See also [`Iterator::collect`].
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
    /// use nonempty_collections::prelude::*;
    ///
    /// let n0 = nev![1,2,3,4];
    /// let n1 = n0.iter().copied().collect();
    /// assert_eq!(n0, n1);
    /// ```
    fn copied<'a, T: 'a>(self) -> Copied<Self>
    where
        Self: Sized + NonEmptyIterator<Item = &'a T>,
        T: Copy,
    {
        Copied { iter: self }
    }

    /// Consumes the non-empty iterator, counting the number of iterations and
    /// returning it.
    ///
    /// See also [`Iterator::count`].
    ///
    /// ```
    /// use nonempty_collections::prelude::*;
    ///
    /// let n = nev![1];
    /// assert_eq!(1, n.iter().count());
    ///
    /// let n = nev![1,2,3,4,5,6];
    /// assert_eq!(6, n.iter().count());
    /// ````
    fn count(self) -> usize
    where
        Self: Sized,
    {
        // Differs from the implementation of `Iterator::count` to absolutely
        // ensure that `count` returns at least 1.
        let (_, rest) = self.first();
        1 + rest.into_iter().count()
    }

    /// Repeats a non-empty iterator endlessly.
    ///
    /// See also [`Iterator::cycle`].
    fn cycle(self) -> Cycle<Self>
    where
        Self: Sized + Clone,
    {
        Cycle::new(self)
    }

    /// Creates a non-empty iterator which gives the current iteration count as
    /// well as the next value.
    ///
    /// See also [`Iterator::enumerate`].
    ///
    /// ```
    /// use nonempty_collections::prelude::*;
    ///
    /// let s = nes!["Doriath", "Gondolin", "Nargothrond"];
    /// let total: usize = s.iter().enumerate().map(|(c, _)| c).sum();
    /// assert_eq!(3, total);
    /// ```
    fn enumerate(self) -> Enumerate<Self>
    where
        Self: Sized,
    {
        Enumerate {
            iter: self,
            count: 0,
        }
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
    /// use nonempty_collections::prelude::*;
    ///
    /// let n = nev![1,2,3,4,5,6];
    /// let v: Vec<_> = n.iter().map(|x| x * 2).filter(|&x| x % 3 == 0).collect();
    /// assert_eq!(vec![6, 12], v);
    /// ```
    fn filter<P>(self, predicate: P) -> std::iter::Filter<<Self as IntoIterator>::IntoIter, P>
    where
        Self: Sized + IntoIterator<Item = <Self as NonEmptyIterator>::Item>,
        P: FnMut(&<Self as IntoIterator>::Item) -> bool,
    {
        self.into_iter().filter(predicate)
    }

    /// Folds every element into an accumulator by applying an operation,
    /// returning the final result.
    ///
    /// See also [`Iterator::fold`].
    fn fold<B, F>(mut self, init: B, mut f: F) -> B
    where
        Self: Sized,
        F: FnMut(B, Self::Item) -> B,
    {
        let mut accum = init;
        while let Some(x) = self.next() {
            accum = f(accum, x);
        }
        accum
    }

    /// Takes a closure and creates a non-empty iterator which calls that
    /// closure on each element.
    ///
    /// If `self` is a `NonEmptyIterator`, then so is [`Map`].
    ///
    /// See also [`Iterator::map`].
    ///
    /// ```
    /// use nonempty_collections::prelude::*;
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
        Map { iter: self, f }
    }

    /// Returns the `n`th element of the iterator.
    ///
    /// See also [`Iterator::nth`].
    ///
    /// ```
    /// use nonempty_collections::prelude::*;
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
    fn nth(&mut self, n: usize) -> Option<Self::Item> {
        for _ in 0..n {
            self.next()?;
        }
        self.next()
    }

    /// Sums the elements of a non-empty iterator.
    ///
    /// See also [`Iterator::sum`].
    ///
    /// ```
    /// use nonempty_collections::prelude::*;
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
    /// use nonempty_collections::prelude::*;
    /// use nonempty_collections::NEVec;
    ///
    /// let n: NEVec<_> = nev![1,2,3].iter().map(|n| n * 2).take(2).collect();
    /// assert_eq!(nev![2,4], n);
    /// ```
    fn take(self, n: usize) -> Take<Self>
    where
        Self: Sized,
    {
        if n == 0 {
            panic!("Cannot take 0 elements from a non-empty iterator!");
        }

        Take { iter: self, n }
    }

    /// Iterates over the entire non-empty iterator, multiplying all the
    /// elements.
    ///
    /// See also [`Iterator::product`].
    ///
    /// ```
    /// use nonempty_collections::prelude::*;
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
        let (head, rest) = iter.into_nonempty_iter().first();

        let mut v = vec![head];
        v.extend(rest);
        v
    }
}

impl<T: Eq + Hash> FromNonEmptyIterator<T> for HashSet<T> {
    fn from_nonempty_iter<I>(iter: I) -> Self
    where
        I: IntoNonEmptyIterator<Item = T>,
    {
        let (head, rest) = iter.into_nonempty_iter().first();

        let mut s = HashSet::new();
        s.insert(head);
        s.extend(rest);
        s
    }
}

impl<I: NonEmptyIterator> IntoNonEmptyIterator for I {
    type Item = I::Item;

    type IntoIter = I;

    fn into_nonempty_iter(self) -> Self::IntoIter {
        self
    }
}

/// Conversion into a [`NonEmptyIterator`].
pub trait IntoNonEmptyIterator {
    /// The type of the elements being iterated over.
    type Item;

    /// Which kind of [`NonEmptyIterator`] are we turning this into?
    type IntoIter: NonEmptyIterator<Item = Self::Item>;

    /// Creates a [`NonEmptyIterator`] from a value.
    fn into_nonempty_iter(self) -> Self::IntoIter;
}

/// Similar to [`std::iter::Map`], but with additional non-emptiness guarantees.
pub struct Map<I, F> {
    iter: I,
    f: F,
}

impl<U, I, F> NonEmptyIterator for Map<I, F>
where
    I: NonEmptyIterator,
    F: FnMut(I::Item) -> U,
{
    type Item = U;

    type IntoIter = std::iter::Map<<I::IntoIter as IntoIterator>::IntoIter, F>;

    fn first(self) -> (Self::Item, Self::IntoIter) {
        let (i, iter) = self.iter.first();
        let mut fun = self.f;

        // Reconstruct the `Map` we broke open.
        (fun(i), iter.into_iter().map(fun))
    }

    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next().map(&mut self.f)
    }
}

/// ```
/// use nonempty_collections::prelude::*;
///
/// let v: Vec<_> = nev![1,2,3].iter().map(|n| n * 2).collect();
/// ```
impl<U, I, F> IntoIterator for Map<I, F>
where
    I: IntoIterator,
    F: FnMut(I::Item) -> U,
{
    type Item = U;

    type IntoIter = std::iter::Map<I::IntoIter, F>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter.into_iter().map(self.f)
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
    type Item = T;

    type IntoIter = std::iter::Cloned<<I::IntoIter as IntoIterator>::IntoIter>;

    fn first(self) -> (Self::Item, Self::IntoIter) {
        let (i, iter) = self.iter.first();

        (i.clone(), iter.into_iter().cloned())
    }

    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next().cloned()
    }
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
    count: usize,
}

impl<I> NonEmptyIterator for Enumerate<I>
where
    I: NonEmptyIterator,
{
    type Item = (usize, I::Item);

    type IntoIter = std::iter::Enumerate<<I::IntoIter as IntoIterator>::IntoIter>;

    fn first(self) -> (Self::Item, Self::IntoIter) {
        let (head, rest) = self.iter.first();

        ((0, head), rest.into_iter().enumerate())
    }

    fn next(&mut self) -> Option<Self::Item> {
        let a = self.iter.next()?;
        let i = self.count;
        self.count += 1;
        Some((i, a))
    }
}

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
pub struct Take<I> {
    iter: I,
    n: usize,
}

impl<I> NonEmptyIterator for Take<I>
where
    I: NonEmptyIterator,
{
    type Item = I::Item;

    type IntoIter = std::iter::Take<<I::IntoIter as IntoIterator>::IntoIter>;

    fn first(self) -> (Self::Item, Self::IntoIter) {
        let (head, rest) = self.iter.first();

        if self.n < 2 {
            (head, rest.into_iter().take(0))
        } else {
            (head, rest.into_iter().take(self.n - 1))
        }
    }

    fn next(&mut self) -> Option<Self::Item> {
        if self.n != 0 {
            self.n -= 1;
            self.iter.next()
        } else {
            None
        }
    }
}

impl<I> IntoIterator for Take<I>
where
    I: IntoIterator,
{
    type Item = I::Item;

    type IntoIter = I::IntoIter;

    fn into_iter(self) -> Self::IntoIter {
        self.iter.into_iter()
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
    type Item = A::Item;

    type IntoIter = std::iter::Chain<<A::IntoIter as IntoIterator>::IntoIter, B>;

    fn first(self) -> (Self::Item, Self::IntoIter) {
        let (head, a_rest) = self.a.first();

        (head, a_rest.into_iter().chain(self.b))
    }

    fn next(&mut self) -> Option<Self::Item> {
        self.a.next().or_else(|| self.b.next())
    }
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
    once: T,
    used: bool,
}

impl<T> Once<T> {
    pub(crate) fn new(once: T) -> Once<T> {
        Once { once, used: false }
    }
}

// FIXME Get rid of this `T: Default`.
impl<T> NonEmptyIterator for Once<T>
where
    T: Default,
{
    type Item = T;

    type IntoIter = std::option::IntoIter<T>;

    fn first(self) -> (Self::Item, Self::IntoIter) {
        (self.once, None.into_iter())
    }

    fn next(&mut self) -> Option<Self::Item> {
        if self.used {
            None
        } else {
            self.used = true;
            let item = std::mem::take(&mut self.once);
            Some(item)
        }
    }
}

impl<T> IntoIterator for Once<T> {
    type Item = T;

    type IntoIter = std::option::IntoIter<T>;

    fn into_iter(self) -> Self::IntoIter {
        Some(self.once).into_iter()
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
    type Item = T;

    type IntoIter = std::iter::Copied<<I::IntoIter as IntoIterator>::IntoIter>;

    fn first(self) -> (Self::Item, Self::IntoIter) {
        let (head, rest) = self.iter.first();

        (head.clone(), rest.into_iter().copied())
    }

    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next().copied()
    }
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

/// An iterator that repeats endlessly.
///
/// See also [`std::iter::Cycle`].
pub struct Cycle<I> {
    orig: I,
    iter: I,
}

impl<I: Clone> Cycle<I> {
    fn new(iter: I) -> Self {
        Self {
            orig: iter.clone(),
            iter,
        }
    }
}

impl<I, T> NonEmptyIterator for Cycle<I>
where
    I: NonEmptyIterator<Item = T>,
    Self: IntoIterator<Item = T>,
{
    type Item = T;

    type IntoIter = Self;

    fn first(self) -> (Self::Item, Self::IntoIter) {
        todo!()
    }

    fn next(&mut self) -> Option<Self::Item> {
        todo!()
    }
}

impl<I, J, T> IntoIterator for Cycle<I>
where
    I: IntoIterator<Item = T, IntoIter = J>,
    J: Clone + Iterator<Item = T>,
{
    type Item = T;

    type IntoIter = std::iter::Cycle<I::IntoIter>;

    fn into_iter(self) -> Self::IntoIter {
        todo!()
    }
}
