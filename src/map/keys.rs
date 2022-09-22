use super::*;

pub struct Keys<'a, K1, K2, V> {
    pub(super) inner: Iter<'a, K1, K2, V>,
}

impl<K1, K2, V> Clone for Keys<'_, K1, K2, V> {
    #[cfg_attr(feature = "inline-more", inline)]
    fn clone(&self) -> Self {
        Keys {
            inner: self.inner.clone(),
        }
    }
}

impl<K1: Debug, K2: Debug, V> fmt::Debug for Keys<'_, K1, K2, V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self.clone()).finish()
    }
}

impl<'a, K1, K2, V> Iterator for Keys<'a, K1, K2, V> {
    type Item = (&'a K1, &'a K2);

    #[cfg_attr(feature = "inline-more", inline)]
    fn next(&mut self) -> Option<(&'a K1, &'a K2)> {
        // Avoid `Option::map` because it bloats LLVM IR.
        match self.inner.next() {
            Some((k1, k2, _)) => Some((k1, k2)),
            None => None,
        }
    }

    #[cfg_attr(feature = "inline-more", inline)]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

impl<K1, K2, V> ExactSizeIterator for Keys<'_, K1, K2, V> {
    #[cfg_attr(feature = "inline-more", inline)]
    fn len(&self) -> usize {
        self.inner.len()
    }
}

impl<K1, K2, V> FusedIterator for Keys<'_, K1, K2, V> {}
