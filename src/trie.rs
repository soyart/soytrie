use std::marker::PhantomData;

use crate::TrieNode;

pub struct Trie<T, K, V>
where
    K: Clone + Eq + std::hash::Hash,
    T: TrieNode<K, V>,
{
    root: T,
    key: PhantomData<K>,
    value: PhantomData<V>,
}

/// Wraps a [`TrieNode<K, V>`](TrieNode) with value [`None`](None) as its root node.
impl<T, K, V> Trie<T, K, V>
where
    K: Clone + Eq + std::hash::Hash,
    T: TrieNode<K, V>,
{
    #[inline]
    pub fn new() -> Self {
        Self {
            root: T::new(),
            key: PhantomData,
            value: PhantomData,
        }
    }
}

// Clones self's root to new trie root.
impl<T, K, V> Clone for Trie<T, K, V>
where
    K: Clone + Eq + std::hash::Hash,
    V: Clone,
    T: Clone + TrieNode<K, V>,
{
    fn clone(&self) -> Self {
        Self {
            root: self.root.clone(),
            key: PhantomData,
            value: PhantomData,
        }
    }
}

// Consumes the node as root for new trie
impl<T, K, V> From<T> for Trie<T, K, V>
where
    K: Clone + Eq + std::hash::Hash,
    T: TrieNode<K, V>,
{
    fn from(node: T) -> Self {
        Self {
            root: node,
            key: PhantomData,
            value: PhantomData,
        }
    }
}

// Returns the reference to root node
impl<T, K, V> AsRef<T> for Trie<T, K, V>
where
    K: Clone + Eq + std::hash::Hash,
    T: TrieNode<K, V>,
{
    fn as_ref(&self) -> &T {
        &self.root
    }
}

// Returns the mutable reference to root node
impl<T, K, V> AsMut<T> for Trie<T, K, V>
where
    K: Clone + Eq + std::hash::Hash,
    T: TrieNode<K, V>,
{
    fn as_mut(&mut self) -> &mut T {
        &mut self.root
    }
}

// Derefs to the root node
impl<T, K, V> std::ops::Deref for Trie<T, K, V>
where
    K: Clone + Eq + std::hash::Hash,
    T: TrieNode<K, V>,
{
    type Target = T;
    fn deref(&self) -> &Self::Target {
        &self.root
    }
}

// DerefMuts to the root node
impl<T, K, V> std::ops::DerefMut for Trie<T, K, V>
where
    K: Clone + Eq + std::hash::Hash,
    T: TrieNode<K, V>,
{
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.root
    }
}
