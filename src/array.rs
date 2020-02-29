//! Array-like types on the stack.
pub use arrayvec::{CapacityError, Drain, IntoIter as ArrayVecIter};
pub use generic_array::{ArrayLength, GenericArrayIter as ArrayIter};

use serde::{Deserialize, Deserializer, Serialize, Serializer};

use core::{
    borrow::{Borrow, BorrowMut},
    cmp::Ordering,
    convert::TryFrom,
    fmt::{self, Debug, Write},
    hash::{Hash, Hasher},
    iter::FromIterator,
    ops::{Deref, DerefMut, RangeBounds},
    slice,
};

/// A vector with a fixed capacity.
///
/// This type is a copy of [`arrayvec::ArrayVec`] backed by a
/// [`generic_array::GenericArray`].
///
/// The ArrayVec is a vector backed by a fixed size array. It keeps track of
/// the number of initialized elements.
///
/// The vector is a contiguous value that you can store directly on the stack
/// if needed.
///
/// It offers a simple API but also dereferences to a slice, so that the full
/// slice API is available.
///
/// ArrayVec can be converted into a by value iterator.
pub struct ArrayVec<T, N: ArrayLength<T>> {
    inner: arrayvec::ArrayVec<Array<T, N>>,
}

impl<T, N: ArrayLength<T>> ArrayVec<T, N> {
    /// Create a new empty `ArrayVec`.
    ///
    /// Capacity is inferred from the type parameter.
    ///
    /// ```
    /// use arrayvec::ArrayVec;
    ///
    /// let mut array = ArrayVec::<[_; 16]>::new();
    /// array.push(1);
    /// array.push(2);
    /// assert_eq!(&array[..], &[1, 2]);
    /// assert_eq!(array.capacity(), 16);
    /// ```
    pub fn new() -> ArrayVec<T, N> {
        Self {
            inner: arrayvec::ArrayVec::new(),
        }
    }

    /// Return the number of elements in the `ArrayVec`.
    ///
    /// ```
    /// use arrayvec::ArrayVec;
    ///
    /// let mut array = ArrayVec::from([1, 2, 3]);
    /// array.pop();
    /// assert_eq!(array.len(), 2);
    /// ```
    #[inline]
    pub fn len(&self) -> usize {
        self.inner.len()
    }

    /// Return the capacity of the `ArrayVec`.
    ///
    /// ```
    /// use arrayvec::ArrayVec;
    ///
    /// let array = ArrayVec::from([1, 2, 3]);
    /// assert_eq!(array.capacity(), 3);
    /// ```
    #[inline(always)]
    pub fn capacity(&self) -> usize {
        self.inner.capacity()
    }

    /// Return if the `ArrayVec` is completely filled.
    ///
    /// ```
    /// use arrayvec::ArrayVec;
    ///
    /// let mut array = ArrayVec::<[_; 1]>::new();
    /// assert!(!array.is_full());
    /// array.push(1);
    /// assert!(array.is_full());
    /// ```
    pub fn is_full(&self) -> bool {
        self.inner.is_full()
    }

    /// Returns the capacity left in the `ArrayVec`.
    ///
    /// ```
    /// use arrayvec::ArrayVec;
    ///
    /// let mut array = ArrayVec::from([1, 2, 3]);
    /// array.pop();
    /// assert_eq!(array.remaining_capacity(), 1);
    /// ```
    pub fn remaining_capacity(&self) -> usize {
        self.inner.remaining_capacity()
    }

    /// Push `element` to the end of the vector.
    ///
    /// ***Panics*** if the vector is already full.
    ///
    /// ```
    /// use arrayvec::ArrayVec;
    ///
    /// let mut array = ArrayVec::<[_; 2]>::new();
    ///
    /// array.push(1);
    /// array.push(2);
    ///
    /// assert_eq!(&array[..], &[1, 2]);
    /// ```
    pub fn push(&mut self, element: T) {
        self.inner.push(element)
    }

    /// Push `element` to the end of the vector.
    ///
    /// Return `Ok` if the push succeeds, or return an error if the vector
    /// is already full.
    ///
    /// ```
    /// use arrayvec::ArrayVec;
    ///
    /// let mut array = ArrayVec::<[_; 2]>::new();
    ///
    /// let push1 = array.try_push(1);
    /// let push2 = array.try_push(2);
    ///
    /// assert!(push1.is_ok());
    /// assert!(push2.is_ok());
    ///
    /// assert_eq!(&array[..], &[1, 2]);
    ///
    /// let overflow = array.try_push(3);
    ///
    /// assert!(overflow.is_err());
    /// ```
    pub fn try_push(&mut self, element: T) -> Result<(), CapacityError<T>> {
        Ok(self.inner.try_push(element)?)
    }

    /// Push `element` to the end of the vector without checking the capacity.
    ///
    /// It is up to the caller to ensure the capacity of the vector is
    /// sufficiently large.
    ///
    /// This method uses *debug assertions* to check that the arrayvec is not full.
    ///
    /// ```
    /// use arrayvec::ArrayVec;
    ///
    /// let mut array = ArrayVec::<[_; 2]>::new();
    ///
    /// if array.len() + 2 <= array.capacity() {
    ///     unsafe {
    ///         array.push_unchecked(1);
    ///         array.push_unchecked(2);
    ///     }
    /// }
    ///
    /// assert_eq!(&array[..], &[1, 2]);
    /// ```
    pub unsafe fn push_unchecked(&mut self, element: T) {
        self.inner.push_unchecked(element)
    }

    /// Insert `element` at position `index`.
    ///
    /// Shift up all elements after `index`.
    ///
    /// It is an error if the index is greater than the length or if the
    /// arrayvec is full.
    ///
    /// ***Panics*** if the array is full or the `index` is out of bounds. See
    /// `try_insert` for fallible version.
    ///
    /// ```
    /// use arrayvec::ArrayVec;
    ///
    /// let mut array = ArrayVec::<[_; 2]>::new();
    ///
    /// array.insert(0, "x");
    /// array.insert(0, "y");
    /// assert_eq!(&array[..], &["y", "x"]);
    ///
    /// ```
    pub fn insert(&mut self, index: usize, element: T) {
        self.inner.insert(index, element)
    }

    /// Insert `element` at position `index`.
    ///
    /// Shift up all elements after `index`; the `index` must be less than
    /// or equal to the length.
    ///
    /// Returns an error if vector is already at full capacity.
    ///
    /// ***Panics*** `index` is out of bounds.
    ///
    /// ```
    /// use arrayvec::ArrayVec;
    ///
    /// let mut array = ArrayVec::<[_; 2]>::new();
    ///
    /// assert!(array.try_insert(0, "x").is_ok());
    /// assert!(array.try_insert(0, "y").is_ok());
    /// assert!(array.try_insert(0, "z").is_err());
    /// assert_eq!(&array[..], &["y", "x"]);
    /// ```
    pub fn try_insert(&mut self, index: usize, element: T) -> Result<(), CapacityError<T>> {
        Ok(self.inner.try_insert(index, element)?)
    }

    /// Remove the last element in the vector and return it.
    ///
    /// Return `Some(` *element* `)` if the vector is non-empty, else `None`.
    ///
    /// ```
    /// use arrayvec::ArrayVec;
    ///
    /// let mut array = ArrayVec::<[_; 2]>::new();
    ///
    /// array.push(1);
    ///
    /// assert_eq!(array.pop(), Some(1));
    /// assert_eq!(array.pop(), None);
    /// ```
    pub fn pop(&mut self) -> Option<T> {
        self.inner.pop()
    }

    /// Remove the element at `index` and swap the last element into its place.
    ///
    /// This operation is O(1).
    ///
    /// Return the *element* if the index is in bounds, else panic.
    ///
    /// ***Panics*** if the `index` is out of bounds.
    ///
    /// ```
    /// use arrayvec::ArrayVec;
    ///
    /// let mut array = ArrayVec::from([1, 2, 3]);
    ///
    /// assert_eq!(array.swap_remove(0), 1);
    /// assert_eq!(&array[..], &[3, 2]);
    ///
    /// assert_eq!(array.swap_remove(1), 2);
    /// assert_eq!(&array[..], &[3]);
    /// ```
    pub fn swap_remove(&mut self, index: usize) -> T {
        self.inner.swap_remove(index)
    }

    /// Remove the element at `index` and swap the last element into its place.
    ///
    /// This is a checked version of `.swap_remove`.
    /// This operation is O(1).
    ///
    /// Return `Some(` *element* `)` if the index is in bounds, else `None`.
    ///
    /// ```
    /// use arrayvec::ArrayVec;
    ///
    /// let mut array = ArrayVec::from([1, 2, 3]);
    ///
    /// assert_eq!(array.swap_pop(0), Some(1));
    /// assert_eq!(&array[..], &[3, 2]);
    ///
    /// assert_eq!(array.swap_pop(10), None);
    /// ```
    pub fn swap_pop(&mut self, index: usize) -> Option<T> {
        self.inner.swap_pop(index)
    }

    /// Remove the element at `index` and shift down the following elements.
    ///
    /// The `index` must be strictly less than the length of the vector.
    ///
    /// ***Panics*** if the `index` is out of bounds.
    ///
    /// ```
    /// use arrayvec::ArrayVec;
    ///
    /// let mut array = ArrayVec::from([1, 2, 3]);
    ///
    /// let removed_elt = array.remove(0);
    /// assert_eq!(removed_elt, 1);
    /// assert_eq!(&array[..], &[2, 3]);
    /// ```
    pub fn remove(&mut self, index: usize) -> T {
        self.inner.remove(index)
    }

    /// Remove the element at `index` and shift down the following elements.
    ///
    /// This is a checked version of `.remove(index)`. Returns `None` if there
    /// is no element at `index`. Otherwise, return the element inside `Some`.
    ///
    /// ```
    /// use arrayvec::ArrayVec;
    ///
    /// let mut array = ArrayVec::from([1, 2, 3]);
    ///
    /// assert!(array.pop_at(0).is_some());
    /// assert_eq!(&array[..], &[2, 3]);
    ///
    /// assert!(array.pop_at(2).is_none());
    /// assert!(array.pop_at(10).is_none());
    /// ```
    pub fn pop_at(&mut self, index: usize) -> Option<T> {
        self.inner.pop_at(index)
    }

    /// Shortens the vector, keeping the first `len` elements and dropping
    /// the rest.
    ///
    /// If `len` is greater than the vector’s current length this has no
    /// effect.
    ///
    /// ```
    /// use arrayvec::ArrayVec;
    ///
    /// let mut array = ArrayVec::from([1, 2, 3, 4, 5]);
    /// array.truncate(3);
    /// assert_eq!(&array[..], &[1, 2, 3]);
    /// array.truncate(4);
    /// assert_eq!(&array[..], &[1, 2, 3]);
    /// ```
    pub fn truncate(&mut self, new_len: usize) {
        self.inner.truncate(new_len)
    }

    /// Remove all elements in the vector.
    pub fn clear(&mut self) {
        self.inner.clear()
    }

    /// Retains only the elements specified by the predicate.
    ///
    /// In other words, remove all elements `e` such that `f(&mut e)` returns false.
    /// This method operates in place and preserves the order of the retained
    /// elements.
    ///
    /// ```
    /// use arrayvec::ArrayVec;
    ///
    /// let mut array = ArrayVec::from([1, 2, 3, 4]);
    /// array.retain(|x| *x & 1 != 0 );
    /// assert_eq!(&array[..], &[1, 3]);
    /// ```
    pub fn retain<F>(&mut self, f: F)
    where
        F: FnMut(&mut T) -> bool,
    {
        self.inner.retain(f)
    }

    /// Set the vector’s length without dropping or moving out elements
    ///
    /// This method is `unsafe` because it changes the notion of the
    /// number of “valid” elements in the vector. Use with care.
    ///
    /// This method uses *debug assertions* to check that `length` is
    /// not greater than the capacity.
    pub unsafe fn set_len(&mut self, length: usize) {
        self.inner.set_len(length)
    }

    /// Copy and appends all elements in a slice to the `ArrayVec`.
    ///
    /// ```
    /// use arrayvec::ArrayVec;
    ///
    /// let mut vec: ArrayVec<[usize; 10]> = ArrayVec::new();
    /// vec.push(1);
    /// vec.try_extend_from_slice(&[2, 3]).unwrap();
    /// assert_eq!(&vec[..], &[1, 2, 3]);
    /// ```
    ///
    /// # Errors
    ///
    /// This method will return an error if the capacity left (see
    /// [`remaining_capacity`]) is smaller then the length of the provided
    /// slice.
    ///
    /// [`remaining_capacity`]: #method.remaining_capacity
    pub fn try_extend_from_slice(&mut self, other: &[T]) -> Result<(), CapacityError>
    where
        T: Copy,
    {
        Ok(self.inner.try_extend_from_slice(other)?)
    }

    /// Create a draining iterator that removes the specified range in the vector
    /// and yields the removed items from start to end. The element range is
    /// removed even if the iterator is not consumed until the end.
    ///
    /// Note: It is unspecified how many elements are removed from the vector,
    /// if the `Drain` value is leaked.
    ///
    /// **Panics** if the starting point is greater than the end point or if
    /// the end point is greater than the length of the vector.
    ///
    /// ```
    /// use arrayvec::ArrayVec;
    ///
    /// let mut v = ArrayVec::from([1, 2, 3]);
    /// let u: ArrayVec<[_; 3]> = v.drain(0..2).collect();
    /// assert_eq!(&v[..], &[3]);
    /// assert_eq!(&u[..], &[1, 2]);
    /// ```
    pub fn drain<R>(&mut self, range: R) -> Drain<Array<T, N>>
    where
        R: RangeBounds<usize>,
    {
        self.inner.drain(range).into()
    }

    /// Return the inner fixed size array, if it is full to its capacity.
    ///
    /// Return an `Ok` value with the array if length equals capacity,
    /// return an `Err` with self otherwise.
    pub fn into_inner(self) -> Result<Array<T, N>, Self> {
        let inner = match self.inner.into_inner() {
            Ok(inner) => inner.inner,
            Err(this) => return Err(Self { inner: this }),
        };

        Ok(Array { inner })
    }

    /// Return a slice containing all elements of the vector.
    pub fn as_slice(&self) -> &[T] {
        self.inner.as_slice()
    }

    /// Return a mutable slice containing all elements of the vector.
    pub fn as_mut_slice(&mut self) -> &mut [T] {
        self.inner.as_mut_slice()
    }

    /// Return a raw pointer to the vector's buffer.
    pub fn as_ptr(&self) -> *const T {
        self.inner.as_ptr()
    }

    /// Return a raw mutable pointer to the vector's buffer.
    pub fn as_mut_ptr(&mut self) -> *mut T {
        self.inner.as_mut_ptr()
    }
}

impl<T, N: ArrayLength<T>> AsRef<[T]> for ArrayVec<T, N> {
    fn as_ref(&self) -> &[T] {
        self.inner.as_ref()
    }
}

impl<T, N: ArrayLength<T>> AsMut<[T]> for ArrayVec<T, N> {
    fn as_mut(&mut self) -> &mut [T] {
        self.inner.as_mut()
    }
}

impl<T, N: ArrayLength<T>> From<Array<T, N>> for ArrayVec<T, N> {
    fn from(inner: Array<T, N>) -> Self {
        Self {
            inner: inner.into(),
        }
    }
}

impl<T, N: ArrayLength<T>> Extend<T> for ArrayVec<T, N> {
    fn extend<I: IntoIterator<Item = T>>(&mut self, iter: I) {
        self.inner.extend(iter)
    }
}

impl<'a, T, N: ArrayLength<T>> IntoIterator for &'a ArrayVec<T, N> {
    type Item = &'a T;
    type IntoIter = slice::Iter<'a, T>;
    fn into_iter(self) -> Self::IntoIter {
        self.inner.iter()
    }
}

impl<'a, T, N: ArrayLength<T>> IntoIterator for &'a mut ArrayVec<T, N> {
    type Item = &'a mut T;
    type IntoIter = slice::IterMut<'a, T>;
    fn into_iter(self) -> Self::IntoIter {
        self.inner.iter_mut()
    }
}

impl<T, N: ArrayLength<T>> IntoIterator for ArrayVec<T, N> {
    type Item = T;
    type IntoIter = ArrayVecIter<Array<T, N>>;
    fn into_iter(self) -> ArrayVecIter<Array<T, N>> {
        self.inner.into_iter()
    }
}

impl<T, N: ArrayLength<T>> Clone for ArrayVec<T, N>
where
    T: Clone,
{
    fn clone(&self) -> Self {
        Self {
            inner: self.inner.clone(),
        }
    }
}

impl<T, N: ArrayLength<T>> Default for ArrayVec<T, N> {
    fn default() -> Self {
        Self {
            inner: arrayvec::ArrayVec::default(),
        }
    }
}

impl<T, N: ArrayLength<T>> Eq for ArrayVec<T, N> where T: Eq {}

impl<T, N: ArrayLength<T>> Ord for ArrayVec<T, N>
where
    T: Ord,
{
    fn cmp(&self, other: &Self) -> Ordering {
        self.inner.cmp(&other.inner)
    }
}

impl<T, N: ArrayLength<T>> PartialEq<ArrayVec<T, N>> for ArrayVec<T, N>
where
    T: PartialEq,
{
    fn eq(&self, rhs: &ArrayVec<T, N>) -> bool {
        self.inner.eq(&rhs.inner)
    }
}

impl<T, N: ArrayLength<T>> PartialEq<[T]> for ArrayVec<T, N>
where
    T: PartialEq,
{
    fn eq(&self, rhs: &[T]) -> bool {
        self.inner.eq(rhs)
    }
}

impl<T, N: ArrayLength<T>> PartialOrd<ArrayVec<T, N>> for ArrayVec<T, N>
where
    T: PartialOrd,
{
    fn partial_cmp(&self, rhs: &ArrayVec<T, N>) -> Option<Ordering> {
        self.inner.partial_cmp(&rhs.inner)
    }
}

impl<T, N: ArrayLength<T>> Debug for ArrayVec<T, N>
where
    T: Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        Debug::fmt(&self.inner, f)
    }
}

impl<T, N: ArrayLength<T>> Deref for ArrayVec<T, N> {
    type Target = [T];
    fn deref(&self) -> &Self::Target {
        self.inner.deref()
    }
}

impl<T, N: ArrayLength<T>> DerefMut for ArrayVec<T, N> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.inner.deref_mut()
    }
}

impl<T, N: ArrayLength<T>> Hash for ArrayVec<T, N>
where
    T: Hash,
{
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.inner.hash(state)
    }
}

impl<T, N: ArrayLength<T>> FromIterator<T> for ArrayVec<T, N> {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        Self {
            inner: arrayvec::ArrayVec::from_iter(iter),
        }
    }
}

impl<T, N: ArrayLength<T>> Borrow<[T]> for ArrayVec<T, N> {
    fn borrow(&self) -> &[T] {
        arrayvec::ArrayVec::borrow(&self.inner)
    }
}

impl<T, N: ArrayLength<T>> BorrowMut<[T]> for ArrayVec<T, N> {
    fn borrow_mut(&mut self) -> &mut [T] {
        arrayvec::ArrayVec::borrow_mut(&mut self.inner)
    }
}

impl<N: ArrayLength<u8>> Write for ArrayVec<u8, N>
where
    arrayvec::ArrayVec<Array<u8, N>>: Write,
{
    fn write_str(&mut self, string: &str) -> Result<(), fmt::Error> {
        Write::write_str(&mut self.inner, string)
    }
}

impl<T: Serialize, N: ArrayLength<T>> Serialize for ArrayVec<T, N> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        self.inner.serialize(serializer)
    }
}

impl<'de, T: Deserialize<'de>, N: ArrayLength<T>> Deserialize<'de> for ArrayVec<T, N>
where
    arrayvec::ArrayVec<Array<T, N>>: Deserialize<'de>,
{
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        Ok(Self {
            inner: arrayvec::ArrayVec::<Array<T, N>>::deserialize(deserializer)?,
        })
    }
}

/// An array type of generic size. All elements of the array are initialized.
pub struct Array<T, N: ArrayLength<T>> {
    inner: generic_array::GenericArray<T, N>,
}

impl<T, N: ArrayLength<T>, Arr: Into<generic_array::GenericArray<T, N>>> From<Arr> for Array<T, N> {
    fn from(arr: Arr) -> Self {
        Self { inner: arr.into() }
    }
}

unsafe impl<T, N: ArrayLength<T>> arrayvec::Array for Array<T, N> {
    type Item = T;

    type Index = usize;

    const CAPACITY: usize = N::USIZE;

    fn as_slice(&self) -> &[Self::Item] {
        &self.inner
    }

    fn as_mut_slice(&mut self) -> &mut [Self::Item] {
        &mut self.inner
    }
}

impl<T, N: ArrayLength<T>> TryFrom<ArrayVec<T, N>> for Array<T, N> {
    type Error = ArrayVec<T, N>;

    fn try_from(vec: ArrayVec<T, N>) -> Result<Self, Self::Error> {
        vec.into_inner()
    }
}

impl<'a, T, N: ArrayLength<T>> IntoIterator for &'a Array<T, N> {
    type Item = &'a T;
    type IntoIter = slice::Iter<'a, T>;
    fn into_iter(self) -> Self::IntoIter {
        self.inner.iter()
    }
}

impl<'a, T, N: ArrayLength<T>> IntoIterator for &'a mut Array<T, N> {
    type Item = &'a mut T;
    type IntoIter = slice::IterMut<'a, T>;
    fn into_iter(self) -> Self::IntoIter {
        self.inner.iter_mut()
    }
}

impl<T, N: ArrayLength<T>> IntoIterator for Array<T, N> {
    type Item = T;
    type IntoIter = ArrayIter<T, N>;
    fn into_iter(self) -> ArrayIter<T, N> {
        self.inner.into_iter()
    }
}

impl<T, N: ArrayLength<T>> Clone for Array<T, N>
where
    T: Clone,
{
    fn clone(&self) -> Self {
        Self {
            inner: self.inner.clone(),
        }
    }
}

impl<T, N: ArrayLength<T>> Default for Array<T, N>
where
    T: Default + Debug,
{
    fn default() -> Self {
        let mut vec = ArrayVec::default();
        for _ in 0..N::USIZE {
            vec.push(T::default());
        }
        vec.into_inner().unwrap()
    }
}

impl<T, N: ArrayLength<T>> Eq for Array<T, N> where T: Eq {}

impl<T, N: ArrayLength<T>> Ord for Array<T, N>
where
    T: Ord,
{
    fn cmp(&self, other: &Self) -> Ordering {
        self.inner.cmp(&other.inner)
    }
}

impl<T, N: ArrayLength<T>> PartialEq<Array<T, N>> for Array<T, N>
where
    T: PartialEq,
{
    fn eq(&self, rhs: &Array<T, N>) -> bool {
        self.inner.eq(&rhs.inner)
    }
}

impl<T, N: ArrayLength<T>> PartialEq<[T]> for Array<T, N>
where
    T: PartialEq,
{
    fn eq(&self, rhs: &[T]) -> bool {
        self.inner.eq(rhs.into())
    }
}

impl<T, N: ArrayLength<T>> PartialOrd<Array<T, N>> for Array<T, N>
where
    T: PartialOrd,
{
    fn partial_cmp(&self, rhs: &Array<T, N>) -> Option<Ordering> {
        self.inner.partial_cmp(&rhs.inner)
    }
}

impl<T, N: ArrayLength<T>> Debug for Array<T, N>
where
    T: Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        Debug::fmt(&self.inner, f)
    }
}

impl<T, N: ArrayLength<T>> Deref for Array<T, N> {
    type Target = [T];
    fn deref(&self) -> &Self::Target {
        self.inner.deref()
    }
}

impl<T, N: ArrayLength<T>> DerefMut for Array<T, N> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.inner.deref_mut()
    }
}

impl<T, N: ArrayLength<T>> Hash for Array<T, N>
where
    T: Hash,
{
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.inner.hash(state)
    }
}

impl<T, N: ArrayLength<T>> FromIterator<T> for Array<T, N> {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        Self {
            inner: generic_array::GenericArray::from_iter(iter),
        }
    }
}

impl<T, N: ArrayLength<T>> Borrow<[T]> for Array<T, N> {
    fn borrow(&self) -> &[T] {
        generic_array::GenericArray::borrow(&self.inner)
    }
}

impl<T, N: ArrayLength<T>> BorrowMut<[T]> for Array<T, N> {
    fn borrow_mut(&mut self) -> &mut [T] {
        generic_array::GenericArray::borrow_mut(&mut self.inner)
    }
}

impl<N: ArrayLength<u8>> Write for Array<u8, N>
where
    generic_array::GenericArray<u8, N>: Write,
{
    fn write_str(&mut self, string: &str) -> Result<(), fmt::Error> {
        Write::write_str(&mut self.inner, string)
    }
}

impl<T: Serialize, N: ArrayLength<T>> Serialize for Array<T, N> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        self.inner.serialize(serializer)
    }
}

impl<'de, T: Deserialize<'de>, N: ArrayLength<T>> Deserialize<'de> for Array<T, N>
where
    generic_array::GenericArray<T, N>: Deserialize<'de>,
{
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        Ok(Self {
            inner: generic_array::GenericArray::deserialize(deserializer)?,
        })
    }
}
