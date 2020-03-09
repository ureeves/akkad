//! Routing table for a Kademlia decentralized hash table.
//!
//! # Example
//!
//! ```
//! use akkad::rt::RoutingTable;
//!
//! let host_key = [0u8; 1];
//! let mut rt = RoutingTable::new(host_key.clone().into(), ());
//!
//! let key = [1u8; 1];
//! rt.update(key.into(), ());
//!
//! let key = [2u8; 1];
//! rt.update(key.into(), ());
//!
//! let mut closest = rt.closest(&host_key.into());
//!
//! let elem1 = closest.next().unwrap();
//! let elem2 = closest.next().unwrap();
//!
//! assert_eq!(elem1.0[0], 1);
//! assert_eq!(elem2.0[0], 2);
//! ```
use core::{cmp::Ordering, ops::Mul};
use generic_array::typenum::{Prod, Unsigned};

use crate::array::{
    consts::{U20, U8},
    Array, ArrayLength, ArrayVec,
};

// TODO Tweak this parameter. In the paper they say 20. Is this a good value?
type KParam = U20;

type Key<N> = Array<u8, N>;
type KBucket<I, N> = ArrayVec<(Key<N>, I), KParam>;

type N8<N> = Prod<N, U8>;
type KN8<N> = Prod<N8<N>, KParam>;

/// Routing table based on the XOR metric for a Kademlia DHT.
pub struct RoutingTable<I, N>
where
    N: ArrayLength<u8> + Mul<U8>,
    N8<N>: ArrayLength<KBucket<I, N>>,
{
    key: Key<N>,
    _info: I,
    table: ArrayVec<KBucket<I, N>, N8<N>>,
}

impl<I, N> RoutingTable<I, N>
where
    N: ArrayLength<u8> + Mul<U8>,
    N8<N>: ArrayLength<KBucket<I, N>> + Mul<KParam>,
    for<'a> KN8<N>: ArrayLength<&'a (Key<N>, I)>,
{
    /// Creates a new empty routing table with key and info belonging to the
    /// local node.
    ///
    /// # Example
    /// ```
    /// use akkad::rt::RoutingTable;
    ///
    /// let host_key = [0u8; 1];
    /// let mut rt = RoutingTable::new(host_key.into(), ());
    /// ```
    pub fn new(key: Key<N>, info: I) -> Self {
        let mut table = ArrayVec::new();
        for _ in 0..<N8<N>>::USIZE {
            table.push(ArrayVec::new());
        }

        let _info = info;
        Self { key, _info, table }
    }

    /// Update the routing table with key and info.
    ///
    /// If the table is full for the particular neighborhood of the key, the
    /// oldest info on the table is returned.
    ///
    /// # Example
    /// ```
    /// use akkad::rt::RoutingTable;
    ///
    /// let host_key = [0u8; 1];
    /// let mut rt = RoutingTable::new(host_key.into(), ());
    ///
    /// let key = [1u8; 1];
    /// rt.update(key.into(), ());
    /// ```
    pub fn update(&mut self, key: Key<N>, info: I) -> Option<(Key<N>, I)> {
        let bucket_index = rt_kbucket_index(&self.key, &key);

        // if table has key eject information and push new to the front of the
        // kbucket
        if let Some(index) = rt_kbucket_contains(&self.table[bucket_index], &key) {
            self.table[bucket_index].remove(index);
            self.table[bucket_index].insert(0, (key, info));
            return None;
        }

        if self.table[bucket_index].is_full() {
            let elem = self.table[bucket_index].pop();
            // absolutely sure this returns Some(_)
            return elem;
        }

        self.table[bucket_index].insert(0, (key, info));
        None
    }

    /// Returns an iterator through the table - ordered by closest to the key
    /// first.
    ///
    /// # Example
    /// ```
    /// use akkad::rt::RoutingTable;
    ///
    /// let host_key = [0u8; 1];
    /// let mut rt = RoutingTable::new(host_key.clone().into(), ());
    ///
    /// let key1 = [1u8; 1];
    /// let key2 = [2u8; 1];
    /// rt.update(key1.into(), ());
    /// rt.update(key2.into(), ());
    ///
    /// for elem in rt.closest(&host_key.into()) {
    ///     // do something with the elements
    /// }
    /// ```
    pub fn closest(&self, key: &Key<N>) -> impl Iterator<Item = &(Key<N>, I)> {
        ClosestIterator::new(key, self)
    }
}

fn rt_kbucket_contains<I, N>(bucket: &KBucket<I, N>, key: &Key<N>) -> Option<usize>
where
    N: ArrayLength<u8>,
{
    for (index, elem) in bucket.iter().enumerate() {
        if &elem.0 == key {
            return Some(index);
        }
    }
    None
}

fn rt_kbucket_index<N>(key: &Key<N>, other: &Key<N>) -> usize
where
    N: ArrayLength<u8>,
{
    let mut zeros = 0;
    for i in 0..N::USIZE {
        let inc = (key[i] ^ other[i]).leading_zeros() as usize;
        zeros += inc;

        if inc != 8 {
            break;
        }
    }

    if zeros == N::USIZE * 8 {
        return N::USIZE * 8 - 1;
    }
    zeros
}

struct ClosestIterator<'a, I, N>
where
    N: ArrayLength<u8> + Mul<U8>,
    N8<N>: ArrayLength<KBucket<I, N>> + Mul<KParam>,
    KN8<N>: ArrayLength<&'a (Key<N>, I)>,
{
    index: usize,
    len: usize,
    arr: ArrayVec<&'a (Key<N>, I), KN8<N>>,
}

impl<'a, I, N> ClosestIterator<'a, I, N>
where
    N: ArrayLength<u8> + Mul<U8>,
    N8<N>: ArrayLength<KBucket<I, N>> + Mul<KParam>,
    KN8<N>: ArrayLength<&'a (Key<N>, I)>,
{
    fn new(key: &Key<N>, rt: &'a RoutingTable<I, N>) -> Self {
        let mut len = 0;
        let mut arr = ArrayVec::new();

        for index in 0..<N8<N>>::USIZE {
            let filled = rt.table[index].len();
            for elem in &rt.table[index] {
                arr.push(elem);
            }
            len += filled;
        }

        Self::sort_by_distance(key, &mut arr);

        let index = 0;
        Self { index, len, arr }
    }

    fn sort_by_distance(key: &Key<N>, arr: &mut ArrayVec<&'a (Key<N>, I), KN8<N>>) {
        arr.sort_by(|lhs, rhs| {
            let lhs_key = &lhs.0;
            let rhs_key = &rhs.0;

            for i in 0..N::USIZE {
                let lhs_xor = key[i] ^ lhs_key[i];
                let rhs_xor = key[i] ^ rhs_key[i];
                if lhs_xor < rhs_xor {
                    return Ordering::Less;
                }
                if lhs_xor > rhs_xor {
                    return Ordering::Greater;
                }
            }
            Ordering::Equal
        });
    }
}

impl<'a, I, N> Iterator for ClosestIterator<'a, I, N>
where
    N: ArrayLength<u8> + Mul<U8>,
    N8<N>: ArrayLength<KBucket<I, N>> + Mul<KParam>,
    KN8<N>: ArrayLength<&'a (Key<N>, I)>,
{
    type Item = &'a (Key<N>, I);

    fn next(&mut self) -> Option<Self::Item> {
        if self.index == self.len {
            return None;
        }

        let index = self.index;
        self.index += 1;

        Some(self.arr[index])
    }
}

#[cfg(test)]
const ONES: [u8; 8] = [0x80, 0x40, 0x20, 0x10, 0x08, 0x04, 0x02, 0x01];

#[test]
fn kbucket_fills_up_nicely() {
    const N: usize = 32;
    let mut key = [0u8; N];

    let mut rt = RoutingTable::new(key.clone().into(), ());

    key[0] = 1;
    for _ in 0..KParam::USIZE {
        key[N - 1] += 1;
        rt.update(key.clone().into(), ());
    }
    assert_eq!(rt.table[7].len(), KParam::USIZE);
}

#[test]
fn kbucket_substitutes_same_key() {
    const N: usize = 32;
    const N8: usize = 8 * N;

    let key = [0u8; N];
    let other_key = {
        let mut key = [0u8; N];
        key[N - 1] = 1;
        key
    };

    let mut table = RoutingTable::new(key.clone().into(), ());

    table.update(key.into(), ());
    table.update(other_key.into(), ());
    table.update(key.into(), ());

    assert_eq!(table.table[N8 - 1].len(), 2);
}

#[test]
fn computed_key_index_correct() {
    const N: usize = 32;

    let mut key = [0u8; N];
    let zero_key = [0u8; N];

    // because it's used as an index it should never be N*8
    assert_eq!(
        rt_kbucket_index(&key.clone().into(), &zero_key.clone().into()),
        255
    );

    let mut leading = 0;
    for i in 0..N {
        for one in &ONES {
            key[i] = *one;
            assert_eq!(
                rt_kbucket_index(&key.clone().into(), &zero_key.clone().into()),
                leading
            );
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

    let host_key = [0u8; 1];
    let mut key = host_key;
    let mut rt = RoutingTable::new(host_key.into(), ());

    rt.update([0].into(), ());
    rt.update([1].into(), ());
    for _ in 0..10 * N {
        rng.fill_bytes(&mut key[..]);
        rt.update(key.clone().into(), ());
    }

    let mut iter = rt.closest(&host_key.into());

    let mut tmp = iter
        .next()
        .expect("expected at least one element in the iterator");
    for elem in iter {
        assert_eq!(tmp.0[0] <= elem.0[0], true);
        tmp = elem;
    }
}
