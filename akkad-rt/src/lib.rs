//! Routing table for a Kademlia decentralized hash table.
//!
//! This crate only compiles on nightly due to the use of feature flags. When
//! [`const_generics`](https://github.com/rust-lang/rust/issues/44580) is
//! stabilized this will change.
//!
//! # Example
//!
//! ```
//! use akkad_rt::RoutingTable;
//!
//! let host_key = [0u8; 1];
//! let mut rt = RoutingTable::new(host_key.clone(), ());
//!
//! let key = [1u8; 1];
//! rt.update(key, ());
//!
//! let key = [2u8; 1];
//! rt.update(key, ());
//!
//! let mut closest = rt.closest(&host_key);
//!
//! let elem1 = closest.next().unwrap();
//! let elem2 = closest.next().unwrap();
//!
//! assert_eq!(elem1.0[0], 1);
//! assert_eq!(elem2.0[0], 2);
//! ```
#![allow(incomplete_features)]
#![feature(const_generics)]
#![deny(missing_docs)]

use core::cmp::Ordering;
use core::mem::{self, MaybeUninit};

/// The size of a KBucket.
const K_PARAM: usize = 20;

/// A Kademlia routing table for storing information about keys.
pub struct RoutingTable<I, const N: usize>(ExpandedRoutingTable<I, { N }, { N * 8 }>);

impl<I, const N: usize> RoutingTable<I, N> {
    /// Creates a new empty routing table with key and info belonging to the
    /// local node.
    ///
    /// # Example
    /// ```
    /// use akkad_rt::RoutingTable;
    ///
    /// let host_key = [0u8; 1];
    /// let mut rt = RoutingTable::new(host_key, ());
    /// ```
    pub fn new(key: [u8; N], info: I) -> Self {
        Self(ExpandedRoutingTable::new(key, info))
    }

    /// Update the routing table with key and info.
    ///
    /// If the table is full for the particular neighborhood of the key, the
    /// oldest info on the table is returned.
    ///
    /// # Example
    /// ```
    /// use akkad_rt::RoutingTable;
    ///
    /// let host_key = [0u8; 1];
    /// let mut rt = RoutingTable::new(host_key, ());
    ///
    /// let key = [1u8; 1];
    /// rt.update(key, ());
    /// ```
    pub fn update(&mut self, key: [u8; N], info: I) -> Option<([u8; N], I)> {
        self.0.update(key, info)
    }

    /// Returns an iterator through the table - ordered by closest to the key
    /// first.
    ///
    /// # Example
    /// ```
    /// use akkad_rt::RoutingTable;
    ///
    /// let host_key = [0u8; 1];
    /// let mut rt = RoutingTable::new(host_key.clone(), ());
    ///
    /// let key1 = [1u8; 1];
    /// let key2 = [2u8; 1];
    /// rt.update(key1, ());
    /// rt.update(key2, ());
    ///
    /// for elem in rt.closest(&host_key) {
    ///     // do something with the elements
    /// }
    /// ```
    pub fn closest(&self, key: &[u8; N]) -> impl Iterator<Item = &([u8; N], I)> {
        self.0.closest(key)
    }
}

struct ExpandedRoutingTable<I, const N: usize, const N8: usize> {
    key: [u8; N],
    _info: I,
    table: [KBucket<I, K_PARAM, N, N8>; N8],
}

impl<I, const N: usize, const N8: usize> ExpandedRoutingTable<I, N, N8> {
    fn new(key: [u8; N], _info: I) -> Self {
        let mut data: [MaybeUninit<KBucket<I, K_PARAM, N, N8>>; N8] =
            unsafe { MaybeUninit::uninit().assume_init() };

        for i in 0..N8 {
            data[i] = MaybeUninit::new(KBucket::default());
        }

        let table =
            unsafe { (&data as *const _ as *const [KBucket<I, K_PARAM, N, N8>; N8]).read() };
        Self { key, _info, table }
    }

    fn update(&mut self, key: [u8; N], info: I) -> Option<([u8; N], I)> {
        let index = Key::<N, N8>::index(&self.key, &key);
        self.table[index].update(key, info)
    }

    pub fn closest(&self, key: &[u8; N]) -> impl Iterator<Item = &([u8; N], I)> {
        ClosestIterator::<I, N, N8, { K_PARAM * N8 }>::new(key, self)
    }
}

struct ClosestIterator<'a, I, const N: usize, const N8: usize, const KN8: usize> {
    index: usize,
    len: usize,
    arr: [&'a ([u8; N], I); KN8],
}

impl<'a, 'b, I, const N: usize, const N8: usize, const KN8: usize>
    ClosestIterator<'a, I, N, N8, KN8>
{
    fn new(key: &[u8; N], ert: &'a ExpandedRoutingTable<I, N, N8>) -> Self {
        let mut len = 0;

        let arr = {
            let mut arr: [MaybeUninit<&([u8; N], I)>; KN8] =
                unsafe { MaybeUninit::uninit().assume_init() };

            for i in 0..N8 {
                let filled = ert.table[i].filled;
                for j in 0..filled {
                    let elem = unsafe { &*ert.table[i].arr[j].as_ptr() };
                    arr[len + j] = MaybeUninit::new(elem);
                }
                len += filled;
            }

            let mut arr = unsafe { (&arr as *const _ as *const [&([u8; N], I); KN8]).read() };

            arr[0..len].sort_by(|lhs, rhs| {
                let lhs_key = lhs.0;
                let rhs_key = rhs.0;

                for i in 0..N {
                    let lhs_xor = key[i] ^ lhs_key[i];
                    let rhs_xor = key[i] ^ rhs_key[i];

                    if lhs_xor < rhs_xor {
                        return Ordering::Less;
                    }

                    if rhs_xor > rhs_xor {
                        return Ordering::Greater;
                    }
                }

                Ordering::Equal
            });
            arr
        };

        let index = 0;
        Self { index, len, arr }
    }
}

impl<'a, I, const N: usize, const N8: usize, const KN8: usize> Iterator
    for ClosestIterator<'a, I, N, N8, KN8>
{
    type Item = &'a ([u8; N], I);

    fn next(&mut self) -> Option<Self::Item> {
        if self.index == self.len {
            return None;
        }

        let index = self.index;
        self.index += 1;

        Some(self.arr[index])
    }
}

/// A fixed-sized array-backed FIFO queue with insertion capabilities.
struct KBucket<I, const K_PARAM: usize, const N: usize, const N8: usize> {
    arr: [MaybeUninit<([u8; N], I)>; K_PARAM],
    filled: usize,
}

impl<I, const K_PARAM: usize, const N: usize, const N8: usize> Default
    for KBucket<I, K_PARAM, N, N8>
{
    fn default() -> Self {
        Self {
            arr: unsafe { MaybeUninit::uninit().assume_init() },
            filled: 0,
        }
    }
}

impl<I, const K_PARAM: usize, const N: usize, const N8: usize> KBucket<I, K_PARAM, N, N8> {
    fn update(&mut self, key: [u8; N], info: I) -> Option<([u8; N], I)> {
        if let Some(index) = self.index(&key) {
            let info = self.replace_with_until(index, key, info);
            unsafe { info.assume_init() };
            return None;
        }

        if self.filled == K_PARAM {
            let info = self.replace_with_until(K_PARAM - 1, key, info);
            return Some(unsafe { info.assume_init() });
        }

        self.replace_with_until(self.filled, key, info);
        self.filled += 1;

        None
    }

    /// Displaces the elements of the vector until and including `index`.
    fn replace_with_until(
        &mut self,
        index: usize,
        key: [u8; N],
        info: I,
    ) -> MaybeUninit<([u8; N], I)> {
        let mut info = MaybeUninit::new((key, info));
        for i in 0..=index {
            info = mem::replace(&mut self.arr[i], info);
        }
        info
    }

    /// `Some(index)` if a node with the same key is in the bucket, `None` if not.
    fn index(&self, key: &[u8; N]) -> Option<usize> {
        for i in 0..self.filled {
            let self_key = &unsafe { &*self.arr[i].as_ptr() }.0;
            if Key::<N, N8>::eq(self_key, key) {
                return Some(i);
            }
        }
        None
    }
}

struct Key<const N: usize, const N8: usize>;

impl<const N: usize, const N8: usize> Key<N, N8> {
    fn index(key: &[u8; N], other: &[u8; N]) -> usize {
        let mut zeros = 0;
        for i in 0..N {
            let inc = (key[i] ^ other[i]).leading_zeros() as usize;
            zeros += inc;

            if inc != 8 {
                break;
            }
        }

        if zeros == N8 {
            return N8 - 1;
        }
        zeros
    }

    fn eq(key: &[u8; N], other: &[u8; N]) -> bool {
        for i in 0..N {
            if key[i] != other[i] {
                return false;
            }
        }
        true
    }
}

#[cfg(test)]
const ZEROS: [u8; 8] = [
    0b10000000, 0b01000000, 0b00100000, 0b00010000, 0b00001000, 0b00000100, 0b00000010, 0b00000001,
];

#[test]
fn kbucket_fills_up_nicely() {
    const N: usize = 32;
    const N8: usize = 8 * N;
    const K: usize = N8;
    let mut key = [0u8; N];

    let mut kbucket = KBucket::<(), K, N, N8>::default();
    let mut fill = 0;
    for i in 0..N {
        for j in 0..8 {
            key[i] = ZEROS[j];
            assert_eq!(kbucket.filled, fill);

            kbucket.update(key.into(), ());
            fill += 1;
        }
    }
}

#[test]
fn kbucket_substitutes_same_key() {
    const N: usize = 32;
    const N8: usize = 8 * N;
    const K: usize = N8;

    let key = [0u8; N];
    let other_key = {
        let mut key = [0u8; N];
        key[0] = 1;
        key
    };

    let mut kbucket = KBucket::<(), K, N, N8>::default();
    kbucket.update(key.into(), ());
    kbucket.update(other_key, ());
    kbucket.update(key.into(), ());

    assert_eq!(kbucket.filled, 2);
}

#[test]
fn computed_key_index_correct() {
    const N: usize = 32;
    const N8: usize = 8 * N;

    let mut key = [0u8; N];
    let zero_key = [0u8; N];

    // because it's used as an index it should never be N*8
    assert_eq!(Key::<N, N8>::index(&key, &zero_key), 255);

    let mut leading = 0;
    for i in 0..N {
        for j in 0..8 {
            key[i] = ZEROS[j];
            assert_eq!(Key::<N, N8>::index(&key, &zero_key), leading);
            leading += 1;
        }
        key[i] = 0;
    }
}

#[test]
fn closest_iterator_ordering() {
    use rand::prelude::*;
    let mut rng = rand::thread_rng();

    const N: usize = 1;

    let mut key = [0u8; N];
    let host_key = key.clone();

    let mut rt = RoutingTable::new(host_key.clone(), ());

    rt.update([0], ());
    rt.update([1], ());
    for _ in 0..10 * N {
        rng.fill_bytes(&mut key[..]);
        rt.update(key.clone(), ());
    }

    let mut iter = rt.closest(&host_key);

    let mut tmp = iter
        .next()
        .expect("expected at least one element in the iterator");
    for elem in iter {
        assert_eq!(tmp.0[0] < elem.0[0], true);
        tmp = elem;
    }
}
