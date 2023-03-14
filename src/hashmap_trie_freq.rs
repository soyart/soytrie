use crate::TrieNode;

use std::collections::HashMap;

/// A [`TrieNode`](TrieNode) backed by [HashMap](HashMap) with frequency tracking built in.
/// Fields `value` and `children` are uncorrelated and can be used arbitarily.
/// If using multiple tries, consider using [`Trie`](crate::Trie), which wraps a single `TrieNode` as root.
pub struct HashMapTrieFreq<K, V>
where
    K: Clone + Eq + std::hash::Hash,
{
    pub value: Option<V>,

    freq_count: usize,
    children: HashMap<K, HashMapTrieFreq<K, V>>,
}

/// Default creates new `Self` with `self.freq_count` set to 0 and `self.value` set to `None`
impl<K, V> Default for HashMapTrieFreq<K, V>
where
    K: Clone + Eq + std::hash::Hash,
{
    fn default() -> Self {
        Self {
            freq_count: 0,
            children: HashMap::new(),
            value: None,
        }
    }
}

/// If `K` and `V` is Clone, then `TrieNode<K, V>` is also `Clone`.
impl<K, V> Clone for HashMapTrieFreq<K, V>
where
    K: Clone + Eq + std::hash::Hash,
    V: Clone,
{
    fn clone(&self) -> Self {
        Self {
            freq_count: self.freq_count.clone(),
            value: self.value.clone(),
            children: self.children.clone(),
        }
    }
}

/// PartialEq for [`HashMapFreq`](Self) compares the [value field](Self::value)
/// for equality. As of now, the node's children is not taken into consideration.
/// ```
/// # use soytrie::{HashMapTrieFreq, TrieNode};
/// let mut node1: HashMapTrieFreq<u8, _> = "node".to_string().into();
/// node1.insert_value(b"e", "e".to_string());
///
/// let mut node2: HashMapTrieFreq<u8, _> = "node".to_string().into();
/// node2.insert_value(b"f", "f".to_string());
///
/// assert!(node1 == node2) // ok, because we only compare values
/// ```
impl<K, V> PartialEq<Self> for HashMapTrieFreq<K, V>
where
    K: Clone + Eq + std::hash::Hash,
    V: PartialEq,
{
    fn eq(&self, rhs: &Self) -> bool {
        self.value == rhs.value
    }
}

/// WARN: `Debug` for [`HashMapTrieFreq`](HashMapTrieFreq) is quite expensive - the node will call
/// [`self.all_children_values`](crate::TrieNode::all_children_values) to traverse the entire trie
/// and collect all valued children of `self`. It should only be used when debugging.
impl<K, V> std::fmt::Debug for HashMapTrieFreq<K, V>
where
    K: Clone + Eq + std::hash::Hash + std::fmt::Debug,
    V: std::fmt::Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter) -> Result<(), std::fmt::Error> {
        f.debug_struct("TrieNode")
            .field("freq", &self.freq_count)
            .field("children", &self.all_children_values())
            .field("value", &self.value)
            .finish()
    }
}

impl<K, V> HashMapTrieFreq<K, V>
where
    K: Clone + Eq + std::hash::Hash,
{
    // Increments self.freq by 1
    #[inline(always)]
    fn inc_freq(&mut self) {
        self.freq_count += 1;
    }

    // Decrements self.freq by 1. Panics if usize overflows.
    #[inline(always)]
    fn de_freq(&mut self) {
        self.freq_count -= 1;
    }
}

impl<K, V> TrieNode<K, V> for HashMapTrieFreq<K, V>
where
    K: Clone + Eq + std::hash::Hash,
{
    #[inline(always)]
    fn new() -> Self {
        Self::default()
    }

    #[inline(always)]
    fn freq(&self) -> Option<usize> {
        Some(self.freq_count)
    }

    #[inline(always)]
    fn set_value(&mut self, value: V) {
        self.value = Some(value)
    }

    #[inline(always)]
    fn peek_value(&self) -> &Option<V> {
        &self.value
    }

    #[inline(always)]
    fn is_valued(&self) -> bool {
        self.value.is_some()
    }

    /// Returns `Some(Self)` if there's already child at key, otherwise inserts `child` and returns `None`
    /// It is a sister to [get_or_insert_direct_child](Self::get_or_insert_direct_child).
    #[inline(always)]
    fn insert_or_get_direct_child<Q>(&mut self, key: Q, child: Self) -> Option<Self>
    where
        Q: std::ops::Deref<Target = K>,
    {
        self.inc_freq();
        self.children.insert(key.clone(), child)
    }

    /// Returns the mutable reference of the existing child at key `key`.
    /// If it does not exist, inserts `child` to `self.children` and returning that new child.
    #[inline(always)]
    fn get_or_insert_direct_child<Q>(&mut self, key: Q, child: Self) -> &mut Self
    where
        Q: std::ops::Deref<Target = K>,
    {
        self.inc_freq();
        self.children.entry(key.clone()).or_insert(child)
    }

    /// Returns a reference to the direct child at key `key`.
    #[inline(always)]
    fn get_direct_child<Q>(&self, key: Q) -> Option<&Self>
    where
        Q: std::ops::Deref<Target = K>,
    {
        self.children.get(&key)
    }

    /// Returns a mutable reference to the direct child at key `key`.
    #[inline(always)]
    fn get_direct_child_mut<Q>(&mut self, key: Q) -> Option<&mut Self>
    where
        Q: std::ops::Deref<Target = K>,
    {
        self.children.get_mut(&key)
    }

    /// Removes and returns the direct owned child at key `key`.
    #[inline(always)]
    fn remove_direct_child<Q>(&mut self, key: Q) -> Option<Self>
    where
        Q: std::ops::Deref<Target = K>,
    {
        self.children.remove(&key)
    }

    /// Removes the child at path `path`, returning the owned child.
    /// If the child is `Some`, then it decrements `self.freq_count` counter.
    /// ```
    /// # use soytrie::{HashMapTrieFreq, TrieNode};
    /// let mut node = HashMapTrieFreq::new();
    /// node.insert_value("foobar".as_bytes(), "foobar value");
    /// node.remove("foo".as_bytes());
    /// assert!(node.all_valued_children().is_empty());
    /// ```
    #[inline(always)]
    fn remove(&mut self, path: &[K]) -> Option<Self> {
        let last_idx = path.len() - 1;

        let removed = self
            .get_child_mut(&path[..last_idx])
            .and_then(|child| child.remove_direct_child(&path[last_idx]));

        if removed.is_some() {
            self.de_freq();
        }

        removed
    }

    // Recursively collects all extant children of `node`.
    fn collect_children<'l, 's>(node: &'l Self, children: &mut Vec<&'s Self>)
    where
        'l: 's,
    {
        children.push(node);

        node.children
            .values()
            .for_each(|child| Self::collect_children(child, children));
    }

    /// Returns all values of valued children as a vector of references to the children.
    /// ```
    /// # use soytrie::{HashMapTrieFreq, TrieNode};
    /// let mut node = HashMapTrieFreq::new();
    ///
    /// node.insert_value(b"abc", "abc"); // This adds path nodes at "a" and "b", and valued node at "c"
    /// node.insert_value(b"xyz", "xyz"); // Adds path nodes at "x", "y", and valued node at "z"
    ///
    /// assert_eq!(node.all_valued_children().len(), 2); // valued nodes: "abc", "xyz"
    /// ```
    #[inline]
    fn all_children_values(&self) -> Vec<&V> {
        self.all_children()
            .iter()
            .filter_map(|child| child.value.as_ref())
            .collect()
    }

    /// Swaps self.value with `Some(value)`
    #[inline(always)]
    fn swap_node_value(&mut self, value: V) -> Option<V> {
        let mut tmp = Some(value);
        std::mem::swap(&mut self.value, &mut tmp);

        tmp
    }

    /// Returns the number of valued children
    #[inline(always)]
    fn num_children(&self) -> usize {
        self.freq_count
    }
}

/// This impl defines extra methods for [TrieNode<K, V>](TrieNode) where `V: Clone`. It methods in here
/// will receive or return a cloned value that had no reference to the previous parent trie.
/// ```
/// # use soytrie::{HashMapTrieFreq, TrieNode};
///
/// let mut node = HashMapTrieFreq::<u8, u8>::new();
/// node.insert_child(b"1", b'1'.into());
/// let mut cloned = node.get_child_clone(b"1").expect("no such child");
/// cloned.insert_child(b"2", b'2'.into());
///
/// // '2' was not insert into node's trie, only cloned's trie
///
/// assert_eq!(
///     node.all_children_values().len(),
///     1,
/// );
///
/// assert_eq!(
///     cloned.all_children_values().len(),
///     2,
/// );
/// ```
impl<K, V> HashMapTrieFreq<K, V>
where
    K: Clone + Eq + std::hash::Hash,
    V: Clone,
{
    /// Returns cloned child at key `key`.
    #[inline]
    pub fn get_direct_child_clone(&self, key: K) -> Option<Self> {
        self.get_direct_child(&key)
            .and_then(|child| Some(child.clone()))
    }

    /// Returns cloned child at path `path`.
    #[inline]
    pub fn get_child_clone(&self, path: &[K]) -> Option<Self> {
        path.is_empty().then_some(self.clone()).or_else(|| {
            self.get_child(path)
                .and_then(|child| child.get_child_clone(&path[1..]))
        })
    }
}

/// Creates a valued node` using [`Some(_)`](Some)
/// without children. Only the [value field](Self::value) is populated.
/// ```
/// # use soytrie::HashMapTrieFreq;
/// let node: HashMapTrieFreq<u8, _> = "node".to_string().into();
/// assert_eq!(node.value, Some("node".to_string()));
/// ```
impl<K, V> From<V> for HashMapTrieFreq<K, V>
where
    K: Clone + Eq + std::hash::Hash,
{
    fn from(value: V) -> Self {
        Self {
            value: Some(value),
            freq_count: 0,
            children: HashMap::new(),
        }
    }
}

/// Creates a node from [`Option<V>`](Option) without wrapping it in another [`Some(Some(_))`](Some).
///```
/// # use soytrie::{HashMapTrieFreq, TrieNode};
/// let node: HashMapTrieFreq<u8, _> = "node".to_string().into();
/// assert!(node == HashMapTrieFreq::from(Some("node".to_string())));
/// ```

impl<K, V> From<Option<V>> for HashMapTrieFreq<K, V>
where
    K: Clone + Eq + std::hash::Hash,
{
    fn from(opt: Option<V>) -> Self {
        Self {
            value: opt,
            freq_count: 0,
            children: HashMap::new(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::HashMapTrieFreq;
    use crate::TrieNode;

    #[test]
    fn test_trie() {
        crate::tests::test_trie(HashMapTrieFreq::new());
    }

    #[test]
    fn test_unique() {
        crate::tests::test_unique(HashMapTrieFreq::new());
    }
}
