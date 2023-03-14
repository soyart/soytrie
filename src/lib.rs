//! soytrie is a simple, generic Rust implementation of trie using Rust's built-in
//! [HashMap](std::collections::HashMap).
//!
//! soytrie aims to be minimal, flexible, efficient, and complete.
//!
//! # Features
//!
//! soytrie supports insertion, deep insertion, searching, prediction,
//! deletion, and deep deletion via trait [`TrieNode`](TrieNode).
//!
//! All operations [`TrieNode`](TrieNode) methods only traverse down the trie path once, except when
//! except when we need to retrieve information from all children.
//!
//! In addition to `TrieNode` nodes, soytrie also provides [`Trie`](Trie) for working with multiple nodes,
//! which is a `TrieNode` with root.
//!
//! soytrie provides 2 implementation of [`TrieNode`](TrieNode):
//!
//! ## [`HashMapTrie`](HashMapTrie)
//!     
//!	Basic implementation of `TrieNode`.
//!
//!	This implementation only stores node value and children. `HashMapTrie` is preferred for problems
//! that do not concern with unique prefixes or number of children.
//!
//! ## [`HashMapTrieFreq`](HashMapTrieFreq)
//!
//! A `TrieNode` implementation which stores everything [`HashMapTrie`](HashMapTrie) does,
//!	but it also counts its children.
//!
//! It increments the counter every time a child is inserted,
//! and decrements the counter every time a child is successfully removed.
//!
//!	`HashMapTrieFreq` is preferred when the problems revolve around determining shortest
//!	prefixes or counting the number of children.
//!
//! Users can implement their own `TrieNode` and use the `pub` tests provided.
//!
//! # Caveats: Rust ergonomic traits
//!
//! 1. [`PartialEq`](PartialEq) implementation for [`TrieNode`](TrieNode)
//!     only compares the values, not the nodes' children.
//!
//! 2. [`Debug`](Debug) implementation for [`TrieNode`](TrieNode) is expensive -
//!     it will traverse the whole trie to get all children values to display when debugging.
//!
//! 3. [`From`](From) implementation for [`TrieNode`](TrieNode) only uses the value to
//!     construct a node with [`Some(_)`](Some) value and 0 child.
//!
//! # Examples
//!
//! ```
//! use soytrie::{Trie, TrieNode, SearchMode, HashMapTrie};
//! let mut trie = Trie::from(HashMapTrie::new());
//!
//! // Keys and values are not related.
//! trie.insert_value(b"a", "This is the 'a' node");
//! trie.insert_value(b"ab", "This is the 'ab' node");
//! trie.insert_value(b"abc", "This is the 'abc' node");
//! trie.insert_value(b"foo", "This is the 'foo' node");
//! trie.insert_value(b"foobar", "This is the 'foobar' node");
//! trie.insert_value(b"foobar2000", "This is the 'foobar2000' node");
//!
//! assert_eq!(trie.predict(b"f").unwrap().len(), 3); // foo, foobar, foobar2000
//! assert_eq!(trie.predict(b"ab").unwrap().len(), 2); // ab, abc
//! assert_eq!(trie.predict(b"fa"), None);
//!
//! assert_eq!(trie.search(SearchMode::Prefix, b"a"), true);
//! assert_eq!(trie.search(SearchMode::Prefix, b"f"), true);
//! assert_eq!(trie.search(SearchMode::Prefix, b"fa"), false);
//! assert_eq!(trie.search(SearchMode::Prefix, b"bar"), false);
//!
//! assert_eq!(trie.search(SearchMode::Exact, b"f"), false);
//! assert_eq!(trie.search(SearchMode::Exact, b"foo"), true);
//!
//! // Node at f>o>o>b>a>r>2 only has 1 child with value: foobar2000
//! assert_eq!(
//!     trie.get_child_mut(b"foobar2")
//!         .expect("bad get_child_mut")
//!         .all_children_values().len(),
//!     1,
//! );
//!
//! // [a, ab, abc, foo, foobar, foobar2000]
//! assert_eq!(trie.all_children_values().len(), 6);
//!
//! trie.remove(b"abc"); // deletes abc
//! assert_eq!(trie.all_children_values().len(), 5);
//!
//! trie.remove(b"ab"); // deletes ab
//! assert_eq!(trie.all_children_values().len(), 4);
//!
//! trie.remove(b"ab"); // does nothing
//! assert_eq!(trie.all_children_values().len(), 4);
//!
//! trie.remove(b"fo");  // deletes foo, foobar, foobar2000
//! assert_eq!(trie.all_children_values().len(), 1);
//!
//! trie.remove(b"a");  // deletes a
//! assert_eq!(trie.all_children_values().len(), 0);
//!
//! // TrieNode<K, V> implements Clone if K and V is both Clone.
//! // If a node's value field is `Clone`, then the trie can clone the node as well:
//! trie.insert_value(b"1", "This will be cloned");
//! trie.insert_value(b"12", "While this will be removed");
//!
//! let cloned_1_node = trie.get_child_clone(b"1").unwrap();
//!
//! // Remove last node from the original trie:
//! trie.remove(b"12");
//! // And it was gone:
//! assert_eq!(trie.get_child(b"12"), None);
//!
//! // But the "1" node was cloned, and the cloned "12" lives on:
//! assert!(cloned_1_node.get_child(b"2").is_some());
//! ```

#![feature(is_some_and)]
#![feature(map_try_insert)]

// Implementations
mod hashmap_trie;
mod hashmap_trie_freq;

// Traits
mod trie;
mod trie_node;

pub use hashmap_trie::*;
pub use hashmap_trie_freq::*;
pub use trie::*;
pub use trie_node::*;
