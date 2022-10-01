use super::*;

/// An iterator over the entries of a `DHashMap` in arbitrary order.
/// The iterator element type is `(&'a K1, &'a K2, &'a V)`.
///
/// This `struct` is created by the [`iter`](DHashMap::iter) method
/// on [`DHashMap`]. See its documentation for more.
///
/// # Example
///
/// ```
/// use double_map::{dhashmap, DHashMap};
///
/// let map = dhashmap! {
///     1, "a" => "One",
///     2, "b" => "Two",
///     3, "c" => "Three",
/// };
///
/// let mut iter = map.iter();
/// let mut vec = vec![iter.next(), iter.next(), iter.next()];
///
/// // The `Iter` iterator produces tuples in arbitrary order, so the
/// // tuples must be sorted to test them against a sorted array.
/// vec.sort_unstable();
/// assert_eq!(
///     vec,
///     [
///         Some((&1, &"a", &"One")),
///         Some((&2, &"b", &"Two")),
///         Some((&3, &"c", &"Three"))
///     ]
/// );
///
/// // It is fused iterator
/// assert_eq!(iter.next(), None);
/// assert_eq!(iter.next(), None);
/// ```
pub struct Iter<'a, K1, K2, V> {
    pub(super) inner: RawDataIter<(K1, K2, V)>,
    pub(super) marker: PhantomData<(&'a K1, &'a K2, &'a V)>,
}

impl<K1, K2, V> Clone for Iter<'_, K1, K2, V> {
    #[cfg_attr(feature = "inline-more", inline)]
    fn clone(&self) -> Self {
        Iter {
            inner: self.inner.clone(),
            marker: PhantomData,
        }
    }
}

impl<K1: Debug, K2: Debug, V: Debug> fmt::Debug for Iter<'_, K1, K2, V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self.clone()).finish()
    }
}

impl<'a, K1, K2, V> Iterator for Iter<'a, K1, K2, V> {
    type Item = (&'a K1, &'a K2, &'a V);

    #[cfg_attr(feature = "inline-more", inline)]
    fn next(&mut self) -> Option<(&'a K1, &'a K2, &'a V)> {
        // Avoid `Option::map` because it bloats LLVM IR.
        match self.inner.next() {
            Some(x) => unsafe {
                let r = x.as_ref();
                Some((&r.0, &r.1, &r.2))
            },
            None => None,
        }
    }

    #[cfg_attr(feature = "inline-more", inline)]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

impl<K1, K2, V> ExactSizeIterator for Iter<'_, K1, K2, V> {
    #[cfg_attr(feature = "inline-more", inline)]
    fn len(&self) -> usize {
        self.inner.len()
    }
}

impl<K1, K2, V> FusedIterator for Iter<'_, K1, K2, V> {}
