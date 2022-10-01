use super::*;

/// A mutable iterator over the entries of a `DHashMap` in arbitrary order.
/// The iterator element type is `(&'a K1, &'a K2, &'a mut V)`.
///
/// This `struct` is created by the [`iter_mut`](DHashMap::iter_mut) method
/// on [`DHashMap`]. See its documentation for more.
///
/// # Example
///
/// ```
/// use double_map::{DHashMap, dhashmap};
///
/// let mut map = dhashmap!{
///     1, "a" => "One".to_owned(),
///     2, "b" => "Two".to_owned(),
///     3, "c" => "Three".to_owned(),
/// };
///
/// let mut iter = map.iter_mut();
/// iter.next().map(|(_, _, v)| v.push_str(" coin"));
/// iter.next().map(|(_, _, v)| v.push_str(" coin"));
/// iter.next().map(|(_, _, v)| v.push_str(" coin"));
///
/// // It is fused iterator
/// assert_eq!(iter.next(), None);
/// assert_eq!(iter.next(), None);
///
/// assert_eq!(map.get_key1(&1).unwrap(), &"One coin".to_owned()  );
/// assert_eq!(map.get_key1(&2).unwrap(), &"Two coin".to_owned()  );
/// assert_eq!(map.get_key1(&3).unwrap(), &"Three coin".to_owned());
/// ```
pub struct IterMut<'a, K1, K2, V> {
    pub(super) inner: RawDataIter<(K1, K2, V)>,
    // To ensure invariance with respect to V
    pub(super) marker: PhantomData<(&'a K1, &'a K2, &'a mut V)>,
}

unsafe impl<K1: Send, K2: Send, V: Send> Send for IterMut<'_, K1, K2, V> {}

impl<K1, K2, V> IterMut<'_, K1, K2, V> {
    #[cfg_attr(feature = "inline-more", inline)]
    pub(super) fn iter(&self) -> Iter<'_, K1, K2, V> {
        Iter {
            inner: self.inner.clone(),
            marker: PhantomData,
        }
    }
}

impl<'a, K1, K2, V> Iterator for IterMut<'a, K1, K2, V> {
    type Item = (&'a K1, &'a K2, &'a mut V);

    #[cfg_attr(feature = "inline-more", inline)]
    fn next(&mut self) -> Option<(&'a K1, &'a K2, &'a mut V)> {
        // Avoid `Option::map` because it bloats LLVM IR.
        match self.inner.next() {
            Some(x) => unsafe {
                let r = x.as_mut();
                Some((&r.0, &r.1, &mut r.2))
            },
            None => None,
        }
    }
    #[cfg_attr(feature = "inline-more", inline)]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

impl<K1, K2, V> ExactSizeIterator for IterMut<'_, K1, K2, V> {
    #[cfg_attr(feature = "inline-more", inline)]
    fn len(&self) -> usize {
        self.inner.len()
    }
}

impl<K1, K2, V> FusedIterator for IterMut<'_, K1, K2, V> {}

impl<K1: Debug, K2: Debug, V: Debug> fmt::Debug for IterMut<'_, K1, K2, V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self.iter()).finish()
    }
}
