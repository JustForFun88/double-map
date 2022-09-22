use super::*;

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
