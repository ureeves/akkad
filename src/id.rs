//! Cryptographic identities for Kademlia nodes.
//!
//! In the initial [S/Kademlia paper](https://telematics.tm.kit.edu/publications/Files/267/SKademlia_2007.pdf),
//! two cryptographic puzzles are introduced. The first puzzle prevents
//! arbitrary generation of node Ids, and the second puzzle prevents the rapid
//! generation of these node Ids.
//!
//! No choice of hash algorithm is made - instead opting to keep it generic
//! by using the [`Digest`] trait.

use crate::array::{Array, ArrayLength};
use digest::Digest;
use rand::{Error as RngError, Rng};

/// The identity of a node on the network.
pub struct NodeId<D: Digest>(Array<u8, D::OutputSize>);

impl<D: Digest> NodeId<D> {
    /// Generates a new node id and a nonce by performing the static (can
    /// fail), and dynamic (takes a long time) puzzles described in the
    /// S/Kademlia paper.
    ///
    /// `static_prefix` and `dynamic_prefix` are parameters controlling the
    /// difficulty of their respective puzzle. They should be set to a number
    /// between 0 and D::OutputSize.
    pub fn generate<B, RNG>(
        rng: &mut RNG,
        public_key: B,
        static_prefix: usize,
        dynamic_prefix: usize,
    ) -> Result<(Self, Self)>
    where
        B: AsRef<[u8]>,
        RNG: Rng,
    {
        let node_id = Self::static_puzzle(public_key, static_prefix)?;
        let nonce = node_id.dynamic_puzzle(rng, dynamic_prefix)?;
        Ok((node_id, nonce))
    }

    /// Parses a public key and a nonce from parameters and from their byte
    /// formats.
    pub fn parse<KB, IB, NB>(
        node_id: IB,
        nonce: NB,
        public_key: KB,
        static_prefix: usize,
        dynamic_prefix: usize,
    ) -> Result<(Self, Self)>
    where
        NB: AsRef<[u8]>,
        IB: AsRef<[u8]>,
        KB: AsRef<[u8]>,
    {
        // check length of node_id and nonce
        let node_id = Self::parse_unchecked(node_id.as_ref()).ok_or(Error::InvalidKey)?;
        let nonce = Self::parse_unchecked(nonce.as_ref()).ok_or(Error::InvalidNonce)?;

        // static puzzle check
        if node_id.0 != Self::static_puzzle(public_key, static_prefix)?.0 {
            return Err(Error::InvalidKey);
        }

        // dynamic puzzle check
        let xor_arr = xor_arr(&node_id.0, &nonce.0);
        let p = D::digest(&xor_arr).into();
        if prefix_zeros(&p) < dynamic_prefix {
            return Err(Error::InvalidNonce);
        }

        Ok((node_id, nonce))
    }

    /// Parses only checking the length of the payload.
    fn parse_unchecked<B: AsRef<[u8]>>(bytes: B) -> Option<Self> {
        let bytes = bytes.as_ref();
        if bytes.len() != D::output_size() {
            return None;
        }

        let mut arr = zeroed_arr();
        for i in 0..D::output_size() {
            arr[i] = bytes[i];
        }

        Some(Self(arr))
    }

    /// Creates a new node id by solving the static puzzle. `prefix`
    /// characterizes how hard this is to do. Some keys may be rejected, and
    /// will return Error::Invalid key.
    fn static_puzzle<B>(public_key: B, prefix: usize) -> Result<Self>
    where
        B: AsRef<[u8]>,
    {
        let digest = D::digest(public_key.as_ref());
        let double_digest = D::digest(&digest).into();

        if prefix_zeros(&double_digest) < prefix {
            return Err(Error::InvalidKey);
        }

        Ok(Self(digest.into()))
    }

    /// Produces a nonce from the created node id by solving the dynamic
    /// puzzle. `prefix` is a characterizes how hard - meaning how much time it
    /// will take to create.
    fn dynamic_puzzle<RNG>(&self, rng: &mut RNG, prefix: usize) -> Result<Self>
    where
        RNG: Rng,
    {
        let mut nonce = zeroed_arr();

        loop {
            randomize_arr(rng, &mut nonce)?;
            let xor_arr = xor_arr(&self.0, &nonce);
            let p = D::digest(&xor_arr).into();

            if prefix < prefix_zeros(&p) {
                break;
            }
        }

        Ok(Self(nonce))
    }
}

impl<D: Digest> AsRef<[u8]> for NodeId<D> {
    fn as_ref(&self) -> &[u8] {
        &self.0
    }
}

impl<D: Digest> From<Array<u8, D::OutputSize>> for NodeId<D> {
    fn from(arr: Array<u8, D::OutputSize>) -> Self {
        Self(arr)
    }
}

impl<D: Digest> From<&Array<u8, D::OutputSize>> for NodeId<D> {
    fn from(arr_ref: &Array<u8, D::OutputSize>) -> Self {
        let mut arr = zeroed_arr();
        for i in 0..D::output_size() {
            arr[i] = arr_ref[i];
        }
        Self(arr)
    }
}

const ONES: [u8; 8] = [0x80, 0x40, 0x20, 0x10, 0x8, 0x4, 0x2, 0x1];

fn zeroed_arr<L: ArrayLength<u8>>() -> Array<u8, L> {
    Array::default()
}

fn randomize_arr<L, RNG>(rng: &mut RNG, arr: &mut Array<u8, L>) -> Result<()>
where
    L: ArrayLength<u8>,
    RNG: Rng,
{
    rng.try_fill_bytes(&mut arr[..])?;
    Ok(())
}

fn xor_arr<L: ArrayLength<u8>>(lhs: &Array<u8, L>, rhs: &Array<u8, L>) -> Array<u8, L> {
    let mut arr = zeroed_arr();
    for i in 0..L::to_usize() {
        arr[i] = lhs[i] ^ rhs[i];
    }
    arr
}

fn prefix_zeros<L: ArrayLength<u8>>(arr: &Array<u8, L>) -> usize {
    let mut prefix = 0;
    'outer: for byte in &arr[..] {
        for one in &ONES[..] {
            if byte & one != 0 {
                break 'outer;
            }
            prefix += 1;
        }
    }
    prefix
}

type Result<T> = std::result::Result<T, Error>;

/// Error type produced when generating node ids.
#[derive(Debug)]
pub enum Error {
    /// When the key is not a part of the key space.
    InvalidKey,

    /// The nonce doesn't meet the criteria.
    InvalidNonce,

    /// Produced by the random number generator.
    Rng(RngError),
}

impl From<RngError> for Error {
    fn from(err: RngError) -> Error {
        Self::Rng(err)
    }
}

#[test]
fn generate_node_id() {
    use secp256k1::{rand::rngs::OsRng, Secp256k1};
    use sha2::Sha256;

    let secp = Secp256k1::new();
    let mut rng = OsRng::new().expect("couldn't get OsRng");

    let mut done = false;
    while !done {
        let (_, public_key) = secp.generate_keypair(&mut rng);
        let public_key = &public_key.serialize()[..];

        match NodeId::<Sha256>::generate(&mut rng, public_key, 8, 16) {
            Ok((node_id, nonce)) => {
                done = true;
                // parsing generated node_id goes ok
                NodeId::<Sha256>::parse(node_id, nonce, public_key, 8, 16)
                    .expect("generated id doesn't parse");
            }
            Err(Error::InvalidKey) => {}
            Err(Error::InvalidNonce) => {}
            Err(Error::Rng(err)) => panic!(err),
        }
    }
}
