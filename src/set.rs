//! Non-empty Sets.

use std::borrow::Borrow;
use std::collections::HashSet;
use std::hash::{BuildHasher, Hash};

/// Like the [`nev`] macro, but for Sets. A nice short-hand for constructing
/// [`NESet`] values.
#[macro_export]
macro_rules! nes {
    ($h:expr, $( $x:expr ),*) => {{
        let mut tail = std::collections::HashSet::new();
        tail.insert($h);
        $( tail.insert($x); )*
        tail.remove(&$h);
        $crate::NESet { head: $h, tail }
    }};
    ($h:expr) => {
        $crate::NESet { head: $h, tail: std::collections::HashSet::new() }
    }
}

/// A non-empty, growable Set.
///
/// # Examples
///
/// ```
/// use nonempty_collections::nes;
///
/// let s = nes![1,1,2,2,3,3,4,4];
/// let mut v = s.into_iter().collect::<Vec<_>>();
/// v.sort();
/// assert_eq!(vec![1,2,3,4], v);
/// ```
///
/// # API Differences with [`HashSet`]
///
/// Note that the following methods aren't implemented for `NESet`:
///
/// - `remove`
/// - `retain`
/// - `take`
#[derive(Debug, Clone)]
pub struct NESet<T, S = std::collections::hash_map::RandomState> {
    /// The element of the non-empty Vector. Always exists.
    pub head: T,

    /// The remaining elements of the non-empty Vector, perhaps empty.
    pub tail: HashSet<T, S>,
}

impl<T, S> NESet<T, S> {
    /// Returns the number of elements the set can hold without reallocating.
    pub fn capacity(&self) -> usize {
        self.tail.capacity() + 1
    }

    /// Returns a reference to the set's `BuildHasher`.
    pub fn hasher(&self) -> &S {
        self.tail.hasher()
    }

    /// An iterator visiting all elements in arbitrary order.
    pub fn iter(&self) -> Iter<'_, T> {
        Iter {
            head: Some(&self.head),
            tail: self.tail.iter(),
        }
    }

    /// Returns the number of elements in the set. Always 1 or more.
    ///
    /// ```
    /// use nonempty_collections::nes;
    ///
    /// let s = nes![1,2,3];
    /// assert_eq!(3, s.len());
    /// ```
    pub fn len(&self) -> usize {
        self.tail.len() + 1
    }
}

impl<T, S> NESet<T, S>
where
    T: Eq + Hash,
    S: BuildHasher,
{
    // TODO
    // difference
    // intersection
    // union

    /// Returns true if the set contains a value.
    ///
    /// ```
    /// use nonempty_collections::nes;
    ///
    /// let s = nes![1,2,3];
    /// assert!(s.contains(&3));
    /// assert!(!s.contains(&10));
    /// ```
    pub fn contains<Q>(&self, value: &Q) -> bool
    where
        T: Borrow<Q>,
        Q: Eq + Hash + ?Sized,
    {
        self.tail.contains(value) || value == self.head.borrow()
    }

    /// Returns a reference to the value in the set, if any, that is equal to
    /// the given value.
    ///
    /// The value may be any borrowed form of the set’s value type, but `Hash`
    /// and `Eq` on the borrowed form must match those for the value type.
    ///
    /// ```
    /// use nonempty_collections::nes;
    ///
    /// let s = nes![1,2,3];
    /// assert_eq!(Some(&3), s.get(&3));
    /// assert_eq!(None, s.get(&10));
    /// ```
    pub fn get<Q>(&self, value: &Q) -> Option<&T>
    where
        T: Borrow<Q>,
        Q: Eq + Hash,
    {
        self.tail
            .get(value)
            .or_else(|| (value == self.head.borrow()).then(|| &self.head))
    }

    /// Adds a value to the set.
    ///
    /// If the set did not have this value present, `true` is returned.
    ///
    /// If the set did have this value present, `false` is returned.
    ///
    /// ```
    /// use nonempty_collections::nes;
    ///
    /// let mut s = nes![1,2,3];
    /// assert_eq!(false, s.insert(2));
    /// assert_eq!(true, s.insert(4));
    /// ```
    pub fn insert(&mut self, value: T) -> bool {
        if self.contains(&value) {
            false
        } else {
            self.tail.insert(value)
        }
    }

    /// Creates a new `NESet` with a single element.
    pub fn new(value: T) -> NESet<T> {
        NESet {
            head: value,
            tail: HashSet::new(),
        }
    }

    /// Creates a new `NESet` with a single element and specified capacity.
    pub fn with_capacity(capacity: usize, value: T) -> NESet<T> {
        NESet {
            head: value,
            tail: HashSet::with_capacity(capacity),
        }
    }

    /// See [`HashSet::with_capacity_and_hasher`].
    pub fn with_capacity_and_hasher(capacity: usize, hasher: S, value: T) -> NESet<T, S> {
        NESet {
            head: value,
            tail: HashSet::with_capacity_and_hasher(capacity, hasher),
        }
    }

    /// See [`HashSet::with_hasher`].
    pub fn with_hasher(hasher: S, value: T) -> NESet<T, S> {
        NESet {
            head: value,
            tail: HashSet::with_hasher(hasher),
        }
    }
}

#[derive(Debug)]
pub struct Iter<'a, T: 'a> {
    head: Option<&'a T>,
    tail: std::collections::hash_set::Iter<'a, T>,
}

impl<'a, T> Iterator for Iter<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        match self.head {
            None => self.tail.next(),
            Some(_) => self.head.take(),
        }
    }
}

impl<T> IntoIterator for NESet<T> {
    type Item = T;
    type IntoIter =
        std::iter::Chain<std::iter::Once<T>, std::collections::hash_set::IntoIter<Self::Item>>;

    fn into_iter(self) -> Self::IntoIter {
        std::iter::once(self.head).chain(self.tail)
    }
}

impl<'a, T> IntoIterator for &'a NESet<T> {
    type Item = &'a T;
    type IntoIter =
        std::iter::Chain<std::iter::Once<&'a T>, std::collections::hash_set::Iter<'a, T>>;

    fn into_iter(self) -> Self::IntoIter {
        std::iter::once(&self.head).chain(self.tail.iter())
    }
}
