use crate::TrieNode;

use std::collections::HashMap;

/// Minimal [`TrieNode`](TrieNode) backed by [HashMap](HashMap).
/// It only stores the value and children, and nothing else.
/// When counting children, this implementation will have to
/// traverse all the way down to the leave nodes.
pub struct HashMapTrie<K, V>
where
    K: Clone + Eq + std::hash::Hash,
{
    pub value: Option<V>,

    children: HashMap<K, HashMapTrie<K, V>>,
}

impl<K, V> Default for HashMapTrie<K, V>
where
    K: Clone + Eq + std::hash::Hash,
{
    fn default() -> Self {
        Self {
            children: HashMap::new(),
            value: None,
        }
    }
}

/// If `K` and `V` is Clone, then `TrieNode<K, V>` is also `Clone`.
impl<K, V> Clone for HashMapTrie<K, V>
where
    K: Clone + Eq + std::hash::Hash,
    V: Clone,
{
    fn clone(&self) -> Self {
        Self {
            value: self.value.clone(),
            children: self.children.clone(),
        }
    }
}

/// PartialEq for [`GasgNaoTrue`](Self) compares the [value field](Self::value)
/// for equality. As of now, the node's children is not taken into consideration.
/// ```
/// # use soytrie::{HashMapTrie, TrieNode};
/// let mut node1: HashMapTrie<u8, _> = "node".to_string().into();
/// node1.insert_value(b"e", "e".to_string());
///
/// let mut node2: HashMapTrie<u8, _> = "node".to_string().into();
/// node2.insert_value(b"f", "f".to_string());
///
/// assert!(node1 == node2) // ok, because we only compare values
/// ```
impl<K, V> PartialEq<Self> for HashMapTrie<K, V>
where
    K: Clone + Eq + std::hash::Hash,
    V: PartialEq,
{
    fn eq(&self, rhs: &Self) -> bool {
        self.value == rhs.value
    }
}

/// WARN: `Debug` for [`HashMapTrie`](Self) is quite expensive - the node will call
/// [`self.all_children_values`](TrieNode::all_children_values) to traverse the entire trie
/// and collect all valued children of `self`. It should only be used when debugging.
impl<K, V> std::fmt::Debug for HashMapTrie<K, V>
where
    K: Clone + Eq + std::hash::Hash + std::fmt::Debug,
    V: std::fmt::Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter) -> Result<(), std::fmt::Error> {
        f.debug_struct("TrieNode")
            .field("children", &self.all_children_values())
            .field("value", &self.value)
            .finish()
    }
}

/// # Non-`Clone` implementation usage examples
/// ```
/// # use soytrie::{HashMapTrie, TrieNode};
/// let mut root = HashMapTrie::new(); // Creates a root node with value None
/// let node = HashMapTrie::from("foo"); // Creates a node with value Some("foo")
/// root.insert_child(b"foo", node);
/// root.insert_value(b"foobar", "foobar");
/// root.insert_child(b"baz", "baz".into()); // TrieNode also implements From<T>
///
/// assert!(root.get_direct_child(&b'a').is_none());
///
/// {
///     let f_node = root.get_child_mut(b"f").unwrap();
///     f_node.insert_child(b"a", "fa".into());
/// }
///
/// assert_eq!(root.all_children_values().len(), 4); // "baz", "fa", "foo", "foobar"
/// assert_eq!(root.predict(b"f").unwrap().len(), 3); // "fa", "foo", "foobar"
///
/// root.remove(b"fo"); // deletes "foo", "foobar"
/// assert_eq!(root.all_children_values().len(), 2); // "baz", "fa"
///
/// {
///     let f_node = root.get_direct_child_mut(&b'f').unwrap();
///     assert_eq!(f_node.all_children_values().len(), 1); // "fa"
///     f_node.insert_value(b"z", "fz");
///     assert_eq!(f_node.all_children_values().len(), 2); // "fa" "fz"
/// }
///
/// assert_eq!(root.all_children_values().len(), 3); // "baz", "fa", "fz"
/// ```
impl<K, V> TrieNode<K, V> for HashMapTrie<K, V>
where
    K: Clone + Eq + std::hash::Hash,
{
    /// Creates new node with value set to [None](None).
    /// If you want to create a node from a value, use [`from`](From) instead:
    /// ```
    /// # use soytrie::{HashMapTrie, TrieNode};
    /// let mut root = HashMapTrie::new();
    /// let node = HashMapTrie::from("foo"); // Creates a node with value Some("foo")
    ///
    /// root.insert_child(b"foo", node);
    /// ```
    #[inline(always)]
    fn new() -> Self {
        Self::default()
    }

    #[inline(always)]
    fn set_value(&mut self, value: V) {
        self.value = Some(value)
    }

    #[inline(always)]
    fn peek_value(&self) -> &Option<V> {
        &self.value
    }

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
        self.children.insert(key.clone(), child)
    }

    /// Returns the mutable reference of the existing child at key `key`.
    /// If it does not exist, inserts `child` to `self.children` and returning that new child.
    #[inline(always)]
    fn get_or_insert_direct_child<Q>(&mut self, key: Q, child: Self) -> &mut Self
    where
        Q: std::ops::Deref<Target = K>,
    {
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
    /// # use soytrie::{HashMapTrie, TrieNode};
    /// let mut node = HashMapTrie::new();
    /// node.insert_value("foobar".as_bytes(), "foobar value");
    /// node.remove("foo".as_bytes());
    /// assert!(node.all_valued_children().is_empty());
    /// ```
    #[inline(always)]
    fn remove(&mut self, path: &[K]) -> Option<Self> {
        let last_idx = path.len() - 1;

        self.get_child_mut(&path[..last_idx])
            .and_then(|child| child.remove_direct_child(&path[last_idx]))
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

    /// Swaps self.value with `Some(value)`
    #[inline(always)]
    fn swap_node_value(&mut self, value: V) -> Option<V> {
        let mut tmp = Some(value);
        std::mem::swap(&mut self.value, &mut tmp);

        tmp
    }

    /// Returns all values of valued children as a vector of references to the children.
    /// ```
    /// # use soytrie::{HashMapTrie, TrieNode};
    /// let mut node = HashMapTrie::new();
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

    /// Returns the number of valued children
    #[inline(always)]
    fn num_children(&self) -> usize {
        self.all_valued_children().len()
    }
}

/// This impl defines extra methods for [TrieNode<K, V>](crate::TrieNode) where `V: Clone`. It methods in here
/// will receive or return a cloned value that had no reference to the previous parent trie.
/// ```
/// # use soytrie::{HashMapTrie, TrieNode};
/// let mut node = HashMapTrie::<u8, u8>::new();
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
impl<K, V> HashMapTrie<K, V>
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
    pub fn get_child_clone(&self, path: &[K]) -> Option<Self> {
        path.is_empty().then_some(self.clone()).or_else(|| {
            self.get_child(path)
                .and_then(|child| child.get_child_clone(&path[1..]))
        })
    }
}

/// Creates a valued [node](TrieNode) using [`Some(_)`](Some)
/// without children. Only the [value field](Self::value) is populated.
/// The node created will not count frequency. To create a freq node, use From<(V, bool)> instead.
/// ```
/// # use soytrie::{HashMapTrie, TrieNode};
/// let node: HashMapTrie<u8, _> = "node".to_string().into();
/// assert_eq!(node.value, Some("node".to_string()));
/// ```
impl<K, V> From<V> for HashMapTrie<K, V>
where
    K: Clone + Eq + std::hash::Hash,
{
    fn from(value: V) -> Self {
        Self {
            value: Some(value),
            children: HashMap::new(),
        }
    }
}

/// Creates a node from [`Option<V>`](Option) without wrapping it in another [`Some(Some(_))`](Some).
///```
/// # use soytrie::{HashMapTrie, TrieNode};
/// let node: HashMapTrie<u8, _> = "node".to_string().into();
/// assert!(node == HashMapTrie::from(Some("node".to_string())));
/// ```

impl<K, V> From<Option<V>> for HashMapTrie<K, V>
where
    K: Clone + Eq + std::hash::Hash,
{
    fn from(opt: Option<V>) -> Self {
        Self {
            value: opt,
            children: HashMap::new(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::HashMapTrie;
    use crate::TrieNode;

    #[test]
    fn test_trie() {
        crate::tests::test_trie(HashMapTrie::new());
    }

    #[test]
    fn test_unique() {
        crate::tests::test_unique(HashMapTrie::new());
    }
}
