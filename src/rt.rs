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
use arrayvec::{Array as ArrayTrait, ArrayVec};
use core::{cmp::Ordering, ops::Mul};
use generic_array::{
    typenum::{
        consts::{U20, U8},
        Prod, Unsigned,
    },
    ArrayLength, GenericArray,
};

// TODO Tweak this parameter. In the paper they say 20. Is this a good value?
type KParam = U20;

type Key<N> = GenericArray<u8, N>;
type KBucket<I, N> = ArrayVec<Array<(Key<N>, I), KParam>>;

/// Routing table based on the XOR metric for a Kademlia DHT.
pub struct RoutingTable<I, N>
where
    N: ArrayLength<u8> + Mul<U8>,
    Prod<N, U8>: ArrayLength<KBucket<I, N>>,
{
    key: GenericArray<u8, N>,
    _info: I,
    table: ArrayVec<Array<KBucket<I, N>, Prod<N, U8>>>,
}

impl<I, N> RoutingTable<I, N>
where
    N: ArrayLength<u8> + Mul<U8>,
    Prod<N, U8>: ArrayLength<KBucket<I, N>> + Mul<KParam>,
    for<'a> Prod<Prod<N, U8>, KParam>: ArrayLength<&'a (Key<N>, I)>,
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
        for _ in 0..<Prod<N, U8>>::USIZE {
            table.push(ArrayVec::new());
        }

        let key = key.into();
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
        let key = key.into();
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

fn rt_keys_equal<N>(lhs: &Key<N>, rhs: &Key<N>) -> bool
where
    N: ArrayLength<u8>,
{
    for i in 0..N::USIZE {
        if lhs[i] != rhs[i] {
            return false;
        }
    }

    true
}

fn rt_kbucket_contains<I, N>(bucket: &KBucket<I, N>, key: &Key<N>) -> Option<usize>
where
    N: ArrayLength<u8>,
{
    for (index, elem) in bucket.iter().enumerate() {
        if rt_keys_equal(&elem.0, key) {
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
    Prod<N, U8>: ArrayLength<KBucket<I, N>> + Mul<KParam>,
    Prod<Prod<N, U8>, KParam>: ArrayLength<&'a (Key<N>, I)>,
{
    index: usize,
    len: usize,
    arr: ArrayVec<Array<&'a (Key<N>, I), Prod<Prod<N, U8>, KParam>>>,
}

impl<'a, I, N> ClosestIterator<'a, I, N>
where
    N: ArrayLength<u8> + Mul<U8>,
    Prod<N, U8>: ArrayLength<KBucket<I, N>> + Mul<KParam>,
    Prod<Prod<N, U8>, KParam>: ArrayLength<&'a (Key<N>, I)>,
{
    fn new(key: &Key<N>, rt: &'a RoutingTable<I, N>) -> Self {
        let mut len = 0;
        let mut arr = ArrayVec::new();

        for index in 0..<Prod<N, U8>>::USIZE {
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

    fn sort_by_distance(
        key: &Key<N>,
        arr: &mut ArrayVec<Array<&'a (Key<N>, I), Prod<Prod<N, U8>, KParam>>>,
    ) {
        arr.sort_by(|lhs, rhs| {
            let lhs_key = &lhs.0;
            let rhs_key = &rhs.0;

            for i in 0..N::USIZE {
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
    }
}

impl<'a, I, N> Iterator for ClosestIterator<'a, I, N>
where
    N: ArrayLength<u8> + Mul<U8>,
    Prod<N, U8>: ArrayLength<KBucket<I, N>> + Mul<KParam>,
    Prod<Prod<N, U8>, KParam>: ArrayLength<&'a (Key<N>, I)>,
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

/// An array type using [`generic_array::GenericArray`] and implementing
/// [`arrayvec::Array`].
///
/// Can be stored directly on the stack if needed.
///
/// This allows for an ArrayVec of any size to be constructed with any element
/// type - including another ArrayVec. It's used for the [`RoutingTable`].
pub struct Array<T, N: ArrayLength<T>>(GenericArray<T, N>);

unsafe impl<T, N: ArrayLength<T>> ArrayTrait for Array<T, N> {
    type Item = T;

    type Index = usize;

    const CAPACITY: usize = N::USIZE;

    fn as_slice(&self) -> &[Self::Item] {
        &self.0
    }

    fn as_mut_slice(&mut self) -> &mut [Self::Item] {
        &mut self.0
    }
}

#[cfg(test)]
const ZEROS: [u8; 8] = [
    0b10000000, 0b01000000, 0b00100000, 0b00010000, 0b00001000, 0b00000100, 0b00000010, 0b00000001,
];

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
        for j in 0..8 {
            key[i] = ZEROS[j];
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
    let mut key = host_key.clone();
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
