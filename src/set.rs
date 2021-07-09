//! Non-empty Sets.

use std::borrow::Borrow;
use std::collections::HashSet;
use std::hash::{BuildHasher, Hash};
use std::iter::Chain;

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

/// A non-empty, growable `HashSet`.
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
/// The first element can always be accessed in constant time.
///
/// ```
/// use nonempty_collections::nes;
///
/// let s = nes!["Fëanor", "Fingolfin", "Finarfin"];
/// assert_eq!("Fëanor", s.head);
/// ```
///
/// # API Differences with [`HashSet`]
///
/// Note that the following methods aren't implemented for `NESet`:
///
/// - `clear`
/// - `drain`
/// - `drain_filter`
/// - `remove`
/// - `retain`
/// - `take`
///
/// As these methods are all "mutate-in-place" style and are difficult to
/// reconcile with the non-emptiness guarantee.
#[derive(Debug, Clone)]
pub struct NESet<T, S = std::collections::hash_map::RandomState> {
    /// An element of the non-empty `HashSet`. Always exists.
    pub head: T,

    /// The remaining elements of the non-empty `HashSet`, perhaps empty.
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

    /// Visits the values representing the difference, i.e., the values that are
    /// in `self` but not in `other`.
    ///
    /// ```
    /// use nonempty_collections::nes;
    ///
    /// let s0 = nes![1,2,3];
    /// let s1 = nes![3,4,5];
    /// let mut v: Vec<_> = s0.difference(&s1).collect();
    /// v.sort();
    /// assert_eq!(vec![&1, &2], v);
    /// ```
    pub fn difference<'a>(&'a self, other: &'a NESet<T, S>) -> Difference<'a, T, S> {
        Difference {
            iter: self.iter(),
            other,
        }
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

    /// Visits the values representing the interesection, i.e., the values that
    /// are both in `self` and `other`.
    ///
    /// ```
    /// use nonempty_collections::nes;
    ///
    /// let s0 = nes![1,2,3];
    /// let s1 = nes![3,4,5];
    /// let mut v: Vec<_> = s0.intersection(&s1).collect();
    /// v.sort();
    /// assert_eq!(vec![&3], v);
    /// ```
    pub fn intersection<'a>(&'a self, other: &'a NESet<T, S>) -> Intersection<'a, T, S> {
        Intersection {
            iter: self.iter(),
            other,
        }
    }

    /// Returns `true` if the set is a subset of another, i.e., `other` contains
    /// at least all the values in `self`.
    ///
    /// ```
    /// use nonempty_collections::nes;
    ///
    /// let sub = nes![1,2,3];
    /// let sup = nes![1,2,3,4];
    ///
    /// assert!(sub.is_subset(&sup));
    /// assert!(!sup.is_subset(&sub));
    /// ```
    pub fn is_subset(&self, other: &NESet<T>) -> bool {
        self.iter().all(|t| other.contains(t))
    }

    /// Returns `true` if the set is a superset of another, i.e., `self`
    /// contains at least all the values in `other`.
    ///
    /// ```
    /// use nonempty_collections::nes;
    ///
    /// let sub = nes![1,2,3];
    /// let sup = nes![1,2,3,4];
    ///
    /// assert!(sup.is_superset(&sub));
    /// assert!(!sub.is_superset(&sup));
    /// ```
    pub fn is_superset(&self, other: &NESet<T>) -> bool {
        other.iter().all(|t| self.contains(t))
    }

    /// Creates a new `NESet` with a single element.
    pub fn new(value: T) -> NESet<T> {
        NESet {
            head: value,
            tail: HashSet::new(),
        }
    }

    /// Adds a value to the set, replacing the existing value, if any, that is
    /// equal to the given one. Returns the replaced value.
    pub fn replace(&mut self, value: T) -> Option<T> {
        if value == self.head {
            Some(std::mem::replace(&mut self.head, value))
        } else {
            self.tail.replace(value)
        }
    }

    /// Reserves capacity for at least `additional` more elements to be inserted
    /// in the `NESet`. The collection may reserve more space to avoid frequent
    /// reallocations.
    ///
    /// # Panics
    ///
    /// Panics if the new allocation size overflows `usize`.
    pub fn reserve(&mut self, additional: usize) {
        self.tail.reserve(additional)
    }

    /// Shrinks the capacity of the set as much as possible. It will drop down
    /// as much as possible while maintaining the internal rules and possibly
    /// leaving some space in accordance with the resize policy.
    pub fn shrink_to_fit(&mut self) {
        self.tail.shrink_to_fit()
    }

    /// Visits the values representing the union, i.e., all the values in `self`
    /// or `other`, without duplicates.
    ///
    /// ```
    /// use nonempty_collections::nes;
    ///
    /// let s0 = nes![1,2,3];
    /// let s1 = nes![3,4,5];
    /// let mut v: Vec<_> = s0.union(&s1).collect();
    /// v.sort();
    /// assert_eq!(vec![&1, &2, &3, &4, &5], v);
    /// ```
    pub fn union<'a>(&'a self, other: &'a NESet<T, S>) -> Union<'a, T, S> {
        if self.len() >= other.len() {
            Union {
                iter: self.iter().chain(other.difference(self)),
            }
        } else {
            Union {
                iter: other.iter().chain(self.difference(other)),
            }
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

pub struct Difference<'a, T: 'a, S: 'a> {
    iter: Iter<'a, T>,
    other: &'a NESet<T, S>,
}

impl<'a, T, S> Iterator for Difference<'a, T, S>
where
    T: Eq + Hash,
    S: BuildHasher,
{
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            let elt = self.iter.next()?;
            if !self.other.contains(elt) {
                return Some(elt);
            }
        }
    }
}

pub struct Union<'a, T: 'a, S: 'a> {
    iter: Chain<Iter<'a, T>, Difference<'a, T, S>>,
}

impl<'a, T, S> Iterator for Union<'a, T, S>
where
    T: Eq + Hash,
    S: BuildHasher,
{
    type Item = &'a T;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next()
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }
}

pub struct Intersection<'a, T: 'a, S: 'a> {
    iter: Iter<'a, T>,
    other: &'a NESet<T, S>,
}

impl<'a, T, S> Iterator for Intersection<'a, T, S>
where
    T: Eq + Hash,
    S: BuildHasher,
{
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            let elt = self.iter.next()?;
            if self.other.contains(elt) {
                return Some(elt);
            }
        }
    }
}
