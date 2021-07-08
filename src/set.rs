//! Non-empty Sets.

use std::collections::HashSet;

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
/// ```
/// use nonempty_collections::nes;
///
/// let s = nes![1,1,2,2,3,3,4,4];
/// let mut v = s.into_iter().collect::<Vec<_>>();
/// v.sort();
/// assert_eq!(vec![1,2,3,4], v);
/// ```
#[derive(Debug, Clone)]
pub struct NESet<T> {
    /// The element of the non-empty Vector. Always exists.
    pub head: T,

    /// The remaining elements of the non-empty Vector, perhaps empty.
    pub tail: HashSet<T>,
}

impl<T> NESet<T> {
    /// An iterator visiting all elements in arbitrary order.
    pub fn iter(&self) -> Iter<'_, T> {
        Iter {
            head: Some(&self.head),
            tail: self.tail.iter(),
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

impl<'a, T> IntoIterator for &'a NESet<T> {
    type Item = &'a T;
    type IntoIter = Iter<'a, T>;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

pub struct IntoIter<T> {
    head: Option<T>,
    tail: std::collections::hash_set::IntoIter<T>,
}

impl<T> Iterator for IntoIter<T> {
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        match self.head {
            None => self.tail.next(),
            Some(_) => self.head.take(),
        }
    }
}

impl<T> IntoIterator for NESet<T> {
    type Item = T;
    type IntoIter = IntoIter<T>;

    fn into_iter(self) -> Self::IntoIter {
        IntoIter {
            head: Some(self.head),
            tail: self.tail.into_iter(),
        }
    }
}
