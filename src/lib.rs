//! soytrie is a simple, generic Rust implementation of trie using Rust's built-in
//! [HashMap](std::collections::HashMap).
//!
//! soytrie aims to be minimal, flexible, efficient, and complete.
//!
//! soytrie does not depend on external crates, except in branch `develop`,
//! where benchmark code is added.
//!
//! # Features
//!
//! soytrie supports insertion, deep insertion, searching, prediction,
//! deletion, and deep deletion via struct [`TrieNode<K, V>`](TrieNode).
//!
//! All operations only traverse down the trie path once.
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
//! use soytrie::{Trie, SearchMode};
//! let mut trie: Trie<u8, &str> = Trie::new();
//! trie.insert_value(b"a", "a");
//! trie.insert_value(b"ab", "ab");
//! trie.insert_value(b"abc", "abc");
//! trie.insert_value(b"foo", "foo");
//! trie.insert_value(b"foobar", "foobar");
//! trie.insert_value(b"foobar2000", "foobar2000");
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
//! ```

mod trie;
pub use trie::*;
