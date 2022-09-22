use super::*;

/// Tre tree for
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
