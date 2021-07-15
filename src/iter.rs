//! Non-empty iterators.

// Iterator structs which _always_ have something if the source iterator is non-empty:
//
// - Chain (if one, the other, or both are nonempty)
// - Enumerate
// - Map
// - Scan
// - Take
// - Zip (if both are nonempty)

/// An [`Iterator`] that is guaranteed to have at least one item.
pub trait NonEmptyIterator {
    /// The value produced by this iterator.
    type Item;

    /// Each `NonEmptyIterator` knows about its possibly-empty variant from
    /// `std`. Critically, they share an `Item`.
    type Iter: Iterator<Item = Self::Item>;

    /// A `NonEmptyIterator` can, by consuming itself, reliably produce its
    /// first element, alongside its possibly-empty variant from `std`.
    fn first(self) -> (Self::Item, Self::Iter);

    /// Convert to the possibly-empty variant.
    fn into_std(self) -> Self::Iter;

    /// Takes a closure and creates an iterator which calls that closure on each
    /// element.
    ///
    /// If `self` is a `NonEmptyIterator`, then so is [`Map`].
    ///
    /// See also [`Iterator::map`].
    #[inline]
    fn map<U, F>(self, f: F) -> Map<Self, F>
    where
        Self: Sized,
        F: FnMut(Self::Item) -> U,
    {
        Map { iter: self, f }
    }
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

    fn into_std(self) -> Self::Iter {
        self.iter.into_std().map(self.f)
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
