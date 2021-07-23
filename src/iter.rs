//! Non-empty iterators.

// Iterator structs which _always_ have something if the source iterator is non-empty:
//
// - [ ] Chain (if one, the other, or both are nonempty)
// - [x] Cloned
// - [ ] Enumerate
// - [x] Map
// - [ ] Scan
// - [ ] Take
// - [ ] Zip (if both are nonempty)

/// An [`Iterator`] that is guaranteed to have at least one item.
pub trait NonEmptyIterator {
    /// The value produced by this iterator.
    type Item;

    /// Each `NonEmptyIterator` knows about a possibly-empty variant of itself,
    /// likely from `std`. Critically, they share an `Item`.
    type Iter: Iterator<Item = Self::Item>;

    /// A `NonEmptyIterator` can, by consuming itself, reliably produce its
    /// first element, alongside its possibly-empty variant.
    fn first(self) -> (Self::Item, Self::Iter);

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

    // TODO Fix example
    /// Takes a closure and creates an iterator which calls that closure on each
    /// element.
    ///
    /// If `self` is a `NonEmptyIterator`, then so is [`Map`].
    ///
    /// See also [`Iterator::map`].
    ///
    /// ```
    /// use nonempty_collections::nes;
    /// use nonempty_collections::iter::NonEmptyIterator;
    ///
    /// let s = nes![1,2,3];
    /// // let mut v: Vec<_> = s.iter().map(|n| n * 2).into_iter().collect();
    /// // v.sort();
    /// // assert_eq!(vec![2,4,6], v);
    /// ```
    #[inline]
    fn map<U, F>(self, f: F) -> Map<Self, F>
    where
        Self: Sized,
        F: FnMut(Self::Item) -> U,
    {
        Map { iter: self, f }
    }
}

/// Conversion from a [`NonEmptyIterator`].
pub trait FromNonEmptyIterator<A>: Sized {
    /// Creates a value from a [`NonEmptyIterator`].
    fn from_nonempty_iter<I>(iter: I) -> Self
    where
        I: IntoNonEmptyIterator<Item = A>;
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

    type Iter = std::iter::Map<I::Iter, F>;

    fn first(self) -> (Self::Item, Self::Iter) {
        let (i, iter) = self.iter.first();
        let mut fun = self.f;

        // Reconstruct the `Map` we broke open.
        (fun(i), iter.map(fun))
    }

    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next().map(&mut self.f)
    }
}

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

    type Iter = std::iter::Cloned<I::Iter>;

    fn first(self) -> (Self::Item, Self::Iter) {
        let (i, iter) = self.iter.first();

        (i.clone(), iter.cloned())
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

// pub trait NonIterator {
//     type Iter: Iterator;

//     fn first(self) -> (<<Self as NonIterator>::Iter as Iterator>::Item, Self::Iter);
// }

// pub trait NEIterator: Iterator {
//     fn first(self) -> (Self::Item, Self);
// }

// impl<U, I, F> Iterator for Map<I, F>
// where
//     I: Iterator,
//     F: FnMut(I::Item) -> U,
// {
//     type Item = U;

//     fn next(&mut self) -> Option<Self::Item> {
//         self.iter.next().map(&mut self.f)
//     }
// }

// impl<U, I, F> NonIterator for Map<I, F>
// where
//     I: Iterator + NonIterator,
//     F: FnMut(I::Item) -> U,
// {
//     type IterTo = U;
//     type Iter = std::iter::Map<I, F>;

//     fn first(self) -> (Self::IterTo, Self::Iter) {
//         let (i, iter) = self.iter.first();
//         let fun = self.f;

//         // Reconstruct the `Map` we broke open.
//         (fun(i), iter.map(fun))
//     }
// }

// impl<U, I, F> NEIterator for Map<I, F>
// where
//     I: NEIterator,
//     F: FnMut(I::Item) -> U,
// {
//     fn first(self) -> (Self::Item, Self) {
//         let (i, iter) = self.iter.first();
//         let mut fun = self.f;

//         // Reconstruct the `Map` we broke open.
//         (fun(i), Map { iter, f: fun })
//     }
// }
