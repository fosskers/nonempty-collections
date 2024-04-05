#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct NEVec2<T> {
    inner: Vec<T>,
}

impl<T> NEVec2<T> {
    pub fn new(head: T) -> Self {
        NEVec2 { inner: vec![head] }
    }

    pub fn try_new(vec: Vec<T>) -> Option<Self> {
        if vec.is_empty() {
            return None;
        }
        Some(NEVec2 { inner: vec })
    }

    pub fn iter(&self) -> Iter<'_, T> {
        Iter {
            inner: self.inner.iter(),
        }
    }

    pub fn contains(&self, x: &T) -> bool
    where
        T: PartialEq,
    {
        self.inner.contains(x)
    }
}

pub trait NonEmptyIterator2: IntoIterator {
    fn next(self) -> (Self::Item, Self::IntoIter);

    #[inline]
    fn map<U, F>(self, f: F) -> Map<Self, F>
    where
        Self: Sized,
        F: FnMut(Self::Item) -> U,
    {
        Map { iter: self, f }
    }

    fn collect<B>(self) -> B
    where
        Self: Sized,
        B: FromNonEmptyIterator2<Self::Item>,
    {
        FromNonEmptyIterator2::from_nonempty_iter(self)
    }
}

pub struct Iter<'a, T> {
    inner: std::slice::Iter<'a, T>,
}

impl<'a, T> IntoIterator for Iter<'a, T> {
    type Item = &'a T;

    type IntoIter = std::slice::Iter<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.inner
    }
}

impl<'a, T> NonEmptyIterator2 for Iter<'a, T> {
    fn next(mut self) -> (Self::Item, Self::IntoIter) {
        (self.inner.next().unwrap(), self.inner)
    }
}

pub struct Map<I, F> {
    iter: I,
    f: F,
}

impl<U, I, F> IntoIterator for Map<I, F>
where
    I: NonEmptyIterator2,
    F: FnMut(I::Item) -> U,
{
    type Item = U;

    type IntoIter = std::iter::Map<<I::IntoIter as IntoIterator>::IntoIter, F>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter.into_iter().map(self.f)
    }
}

impl<U, I, F> NonEmptyIterator2 for Map<I, F>
where
    I: NonEmptyIterator2,
    F: FnMut(I::Item) -> U,
{
    fn next(self) -> (Self::Item, Self::IntoIter) {
        let mut fun = self.f;

        let (first, rest) = self.iter.next();

        (fun(first), rest.into_iter().map(fun))
    }
}

pub trait FromNonEmptyIterator2<T>: Sized {
    fn from_nonempty_iter<I>(iter: I) -> Self
    where
        I: IntoNonEmptyIterator2<Item = T>;
}

impl<T> FromNonEmptyIterator2<T> for Vec<T> {
    fn from_nonempty_iter<I>(iter: I) -> Self
    where
        I: IntoNonEmptyIterator2<Item = T>,
    {
        let (head, rest) = iter.into_nonempty_iter().next();

        let mut v = vec![head];
        v.extend(rest);
        v
    }
}

pub trait IntoNonEmptyIterator2 {
    type Item;

    type IntoIter: NonEmptyIterator2<Item = Self::Item>;

    fn into_nonempty_iter(self) -> Self::IntoIter;
}

impl<I: NonEmptyIterator2> IntoNonEmptyIterator2 for I {
    type Item = I::Item;

    type IntoIter = I;

    fn into_nonempty_iter(self) -> Self::IntoIter {
        self
    }
}

impl<T> FromNonEmptyIterator2<T> for NEVec2<T> {
    fn from_nonempty_iter<I>(iter: I) -> Self
    where
        I: IntoNonEmptyIterator2<Item = T>,
    {
        NEVec2 {
            inner: iter.into_nonempty_iter().into_iter().collect(),
        }
    }
}
