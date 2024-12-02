
use std::collections::HashMap;
use std::hash::Hash;

/// The result of an algebraic operation on elements in a partial lattice
///
/// NOTE: For some operations, it is conceptually valid for both `Identity` and `None` results to be
/// simultaneously appropriate, for example `None.pmeet(Some)`. In these situations, `None` should take precedence
/// over `Identity`, but either of the results can be considered correct so your code must behave correctly in
/// either case.
///
/// NOTE 2: The following conditions for the Identity bitmask must be respected or the implementation may panic or
/// produce logically invalid results.
/// - The bit mask must be non-zero
/// - Bits beyond the number of operation arguments must not be set.  e.g. an arity-2 operation may only set bit 0
///     and bit 1, but never any additional bits.
/// - Setting two or more bits simultaneously asserts the arguments are identities of each other, so this must be
///     true in fact.
/// - The inverse of the above does not hold.  E.g. if multiple bits are not set, it may **not** be assumed that 
///     the arguments are not identities of each other.
/// - Non-commutative operations, such as [DistributiveLattice::psubtract], must never set bits beyond bit 0 ([SELF_IDENT])
#[derive(Clone, Copy, Default, Debug, PartialEq, Eq)]
pub enum AlgebraicResult<V> {
    /// A result indicating the input values perfectly annhilate and the output should be removed and discarded
    #[default]
    None,
    /// A result indicating the output element is identical to the input element(s) identified by the bit mask
    ///
    /// NOTE: The constants [SELF_IDENT] and [COUNTER_IDENT] can be used as conveniences when specifying the bitmask.
    Identity(u64),
    /// A new result element
    Element(V),
}

/// A bitmask value to `or` into the [AlgebraicResult::Identity] argument to specify the result is the identity of `self`
pub const SELF_IDENT: u64 = 0x1;

/// A bitmask value to `or` into the [AlgebraicResult::Identity] argument to specify the result is the identity of `other`
pub const COUNTER_IDENT: u64 = 0x2;

impl<V> AlgebraicResult<V> {
    /// Returns `true` is `self` is [AlgebraicResult::None], otherwise returns `false`
    #[inline]
    pub fn is_none(&self) -> bool {
        matches!(self, AlgebraicResult::None)
    }
    /// Returns `true` is `self` is [AlgebraicResult::Identity], otherwise returns `false`
    #[inline]
    pub fn is_identity(&self) -> bool {
        matches!(self, AlgebraicResult::Identity(_))
    }
    /// Returns `true` is `self` is [AlgebraicResult::Element], otherwise returns `false`
    #[inline]
    pub fn is_element(&self) -> bool {
        matches!(self, AlgebraicResult::Element(_))
    }
    /// Swaps the mask bits in an [AlgebraicResult::Identity] result, for an arity-2 operation, such that
    /// the [SELF_IDENT] bit becomes the [COUNTER_IDENT] bit, and vise-versa
    #[inline]
    pub fn invert_identity(self) -> Self {
        match self {
            Self::None => AlgebraicResult::None,
            Self::Identity(mask) => {
                let new_mask = ((mask & SELF_IDENT) << 1) | ((mask & COUNTER_IDENT) >> 1);
                AlgebraicResult::Identity(new_mask)
            },
            Self::Element(v) => AlgebraicResult::Element(v),
        }
    }
    /// Maps a `AlgebraicResult<V>` to `AlgebraicResult<U>` by applying a function to a contained value, if
    /// self is `AlgebraicResult::Element(V)`.  Otherwise returns the value of `self`
    #[inline]
    pub fn map<U, F>(self, f: F) -> AlgebraicResult<U>
        where F: FnOnce(V) -> U,
    {
        match self {
            Self::None => AlgebraicResult::None,
            Self::Identity(mask) => AlgebraicResult::Identity(mask),
            Self::Element(v) => AlgebraicResult::Element(f(v)),
        }
    }
    /// Converts from `&AlgebraicResult<V>` to `AlgebraicResult<&V>`
    #[inline]
    pub fn as_ref(&self) -> AlgebraicResult<&V> {
        match *self {
            Self::Element(ref v) => AlgebraicResult::Element(v),
            Self::None => AlgebraicResult::None,
            Self::Identity(mask) => AlgebraicResult::Identity(mask),
        }
    }
    /// Returns an option containing the `Element` value, substituting the result of the `ident_f` closure
    /// if `self` is [Identity](AlgebraicResult::Identity)
    ///
    /// The index of the first identity argument is passed to the closure.  E.g. `0` for self, etc.
    #[inline]
    pub fn map_into_option<IdentF>(self, ident_f: IdentF) -> Option<V>
        where IdentF: FnOnce(usize) -> Option<V>
    {
        match self {
            Self::Element(v) => Some(v),
            Self::None => None,
            Self::Identity(mask) => {
                ident_f(mask.trailing_zeros() as usize)
            },
        }
    }
    /// Returns an option containing the `Element` value, substituting the result from the corresponding
    /// index in the `idents` table if `self` is [Identity](AlgebraicResult::Identity)
    #[inline]
    pub fn into_option<I: AsRef<[Option<V>]>>(self, idents: I) -> Option<V>
        where V: Clone
    {
        match self {
            Self::Element(v) => Some(v),
            Self::None => None,
            Self::Identity(mask) => {
                let idents = idents.as_ref();
                idents[mask.trailing_zeros() as usize].clone()
            },
        }
    }
    /// Returns the contained `Element` value or one of the provided default values
    #[inline]
    pub fn unwrap_or(self, ident: V, none: V) -> V {
        match self {
            Self::Element(v) => v,
            Self::None => none,
            Self::Identity(_) => ident,
        }
    }
}

impl<V> AlgebraicResult<Option<V>> {
    /// Flattens a nested `Option<V>` inside an `AlgebraicResult<V>`, converting `AlgebraicResult::Element(None)`
    /// into `AlgebraicResult::None`
    #[inline]
    pub fn flatten(self) -> AlgebraicResult<V> {
        match self {
            Self::Element(v) => {
                match v {
                    Some(v) => AlgebraicResult::Element(v),
                    None => AlgebraicResult::None
                }
            },
            Self::None => AlgebraicResult::None,
            Self::Identity(mask) => AlgebraicResult::Identity(mask),
        }
    }
}

impl<V> From<FatAlgebraicResult<V>> for AlgebraicResult<V> {
    #[inline]
    fn from(src: FatAlgebraicResult<V>) -> Self {
        if src.identity_mask > 0 {
            AlgebraicResult::Identity(src.identity_mask)
        } else {
            match src.element {
                Some(element) => AlgebraicResult::Element(element),
                None => AlgebraicResult::None
            }
        }
    }
}

/// Internal result type that can be down-converted to an [AlgebraicResult], but carries additional information
#[derive(Clone, Copy, Default, Debug, PartialEq, Eq)]
pub(crate) struct FatAlgebraicResult<V> {
    /// An identity mask that maps to the [AlgebraicResult::Identity] value, or 0 if the result is not an identity
    pub identity_mask: u64,
    /// Carries the element value, irrespective of the identity information.  It is the discretion of the code using
    /// this struct as to whether or not to populate this field in the case of an identity result
    pub element: Option<V>,
}

impl<V> FatAlgebraicResult<V> {
    #[inline(always)]
    pub(crate) fn new(identity_mask: u64, element: Option<V>) -> Self {
        Self {identity_mask, element}
    }
    /// The result of an operation between non-none arguments that results in None
    #[inline(always)]
    pub(crate) fn annihilated() -> Self {
        Self {identity_mask: 0, element: None}
    }
    /// The result of an operation that generated a brand new result
    #[inline(always)]
    pub(crate) fn element(e: V) -> Self {
        Self {identity_mask: 0, element: Some(e)}
    }
}

/// Implements basic algebraic behavior (union & intersection) for a type
pub trait Lattice {
    /// Implements the union operation between two instances of a type, resulting in the creation of
    /// a third result instance
    fn join(&self, other: &Self) -> Self;

    /// Implements the union operation between two instances of a type, consuming one input operand,
    /// and modifying the other, resulting in one joined result instance
    fn join_into(&mut self, other: Self) where Self: Sized {
        *self = self.join(&other);
    }

    /// Implements the intersection operation between two instances of a type in a partial lattice
    fn pmeet(&self, other: &Self) -> AlgebraicResult<Self> where Self: Sized;

    //GOAT, we want a meet_with, that has the same semantics as join_into, e.g. mutating in-place.  I
    // don't think there is any benefit to consuming `other`, however, so we can still take `other: &Self`

    /// Returns the "least" value for the type in the lattice
    ///
    /// See [Boolean Algebra](https://en.wikipedia.org/wiki/Boolean_algebra_(structure)#Definition).
    fn bottom() -> Self;

    //GOAT, this should be temporarily deprecated until we work out the correct function prototype
    fn join_all(xs: &[&Self]) -> Self where Self: Sized {
        xs.iter().rfold(Self::bottom(), |x, y| x.join(y))
    }
}

/// Implements algebraic behavior on a reference to a [Lattice] type, such as a smart pointer that can't
/// hold ownership
pub trait LatticeRef {
    type T;
    fn join(&self, other: &Self) -> Self::T;
    fn pmeet(&self, other: &Self) -> AlgebraicResult<Self::T>;
}

/// Implements subtract behavior for a type
pub trait DistributiveLattice {
    /// Implements the partial subtract operation
    fn psubtract(&self, other: &Self) -> AlgebraicResult<Self> where Self: Sized;

    //GOAT, consider a psubtract_from that operates on a `&mut self`
}

/// Implements subtract behavior on a reference to a [DistributiveLattice] type
pub trait DistributiveLatticeRef {
    /// The type that is referenced
    type T;

    /// Implements the partial subtract operation on the referenced values, resulting in the potential
    /// creation of a new value
    fn psubtract(&self, other: &Self) -> AlgebraicResult<Self::T>;
}

// =-**-==-**-==-**-==-**-==-**-==-**-==-**-==-**-==-**-==-**-==-**-==-**-==-**-==-**-==-**-==-**-==-**-=
// Private traits
// =-**-==-**-==-**-==-**-==-**-==-**-==-**-==-**-==-**-==-**-==-**-==-**-==-**-==-**-==-**-==-**-==-**-=

/// Used to implement restrict operation.  TODO, come up with a better math-explanation about how this
/// is a quantale
///
/// Currently this trait isn't exposed because it's unclear what we degrees of felxibility really want
/// from restrict, and what performance we are willing to trade to get them
pub(crate) trait Quantale {
    /// TODO: Document this (currently internal-only)
    fn prestrict(&self, other: &Self) -> AlgebraicResult<Self> where Self: Sized;
}

/// An internal mirror of the [Lattice] trait, where the `self` and `other` types don't need to be
/// exactly the same type, in order to permit blanket implementations
pub(crate) trait HeteroLattice<OtherT> {
    fn join(&self, other: &OtherT) -> Self;
    fn join_into(&mut self, other: OtherT) where Self: Sized {
        *self = self.join(&other);
    }
    fn pmeet(&self, other: &OtherT) -> AlgebraicResult<Self> where Self: Sized;
    fn join_all(xs: &[&Self]) -> Self where Self: Sized;
}

/// An internal mirror of the [DistributiveLattice] trait, where the `self` and `other` types
/// don't need to be exactly the same type, to facilitate blanket impls
pub(crate) trait HeteroDistributiveLattice<OtherT> {
    fn psubtract(&self, other: &OtherT) -> AlgebraicResult<Self> where Self: Sized;
}

/// Internal mirror for [Quantale] See discussion on [HeteroLattice].
pub(crate) trait HeteroQuantale<OtherT> {
    fn prestrict(&self, other: &OtherT) -> AlgebraicResult<Self> where Self: Sized;
}

// =-**-==-**-==-**-==-**-==-**-==-**-==-**-==-**-==-**-==-**-==-**-==-**-==-**-==-**-==-**-==-**-==-**-=
// impls on primitive types
// =-**-==-**-==-**-==-**-==-**-==-**-==-**-==-**-==-**-==-**-==-**-==-**-==-**-==-**-==-**-==-**-==-**-=

impl<V: Lattice + Clone> Lattice for Option<V> {
    fn join(&self, other: &Option<V>) -> Option<V> {
        match self {
            None => { match other {
                None => { None }
                Some(r) => { Some(r.clone()) }
            } }
            Some(l) => match other {
                None => { Some(l.clone()) }
                Some(r) => { Some(l.join(r)) }
            }
        }
    }
    fn join_into(&mut self, other: Self) {
        match self {
            None => { match other {
                None => { }
                Some(r) => { *self = Some(r) }
            } }
            Some(l) => match other {
                None => { }
                Some(r) => { l.join_into(r) }
            }
        }
    }
    fn pmeet(&self, other: &Option<V>) -> AlgebraicResult<Option<V>> {
        match self {
            None => { AlgebraicResult::None }
            Some(l) => {
                match other {
                    None => { AlgebraicResult::None }
                    Some(r) => l.pmeet(r).map(|result| Some(result))
                }
            }
        }
    }
    fn bottom() -> Self {
        None
    }
}

impl<V: Lattice + Clone> LatticeRef for Option<&V> {
    type T = Option<V>;
    fn join(&self, other: &Option<&V>) -> Option<V> {
        match self {
            None => { match other {
                None => { None }
                Some(r) => { Some((*r).clone()) }
            } }
            Some(l) => match other {
                None => { Some((*l).clone()) }
                Some(r) => { Some(l.join(r)) }
            }
        }
    }
    fn pmeet(&self, other: &Option<&V>) -> AlgebraicResult<Option<V>> {
        match self {
            None => { AlgebraicResult::None }
            Some(l) => {
                match other {
                    None => { AlgebraicResult::None }
                    Some(r) => l.pmeet(r).map(|result| Some(result))
                }
            }
        }
    }
}

impl<V: DistributiveLattice + Clone> DistributiveLattice for Option<V> {
    fn psubtract(&self, other: &Self) -> AlgebraicResult<Self> {
        match self {
            None => { AlgebraicResult::None }
            Some(s) => {
                match other {
                    None => { AlgebraicResult::Identity(SELF_IDENT) }
                    Some(o) => { s.psubtract(o).map(|v| Some(v)) }
                }
            }
        }
    }
}

impl<V: DistributiveLattice + Clone> DistributiveLatticeRef for Option<&V> {
    type T = Option<V>;
    fn psubtract(&self, other: &Self) -> AlgebraicResult<Self::T> {
        match self {
            None => { AlgebraicResult::None }
            Some(s) => {
                match other {
                    None => { AlgebraicResult::Identity(SELF_IDENT) }
                    Some(o) => { s.psubtract(o).map(|v| Some(v)) }
                }
            }
        }
    }
}

#[test]
fn option_subtract_test() {
    assert_eq!(Some(()).psubtract(&Some(())), AlgebraicResult::None);
    assert_eq!(Some(()).psubtract(&None), AlgebraicResult::Identity(SELF_IDENT));
    assert_eq!(Some(Some(())).psubtract(&Some(Some(()))), AlgebraicResult::None);
    assert_eq!(Some(Some(())).psubtract(&None), AlgebraicResult::Identity(SELF_IDENT));
    assert_eq!(Some(Some(())).psubtract(&Some(None)), AlgebraicResult::Identity(SELF_IDENT));
    assert_eq!(Some(Some(Some(()))).psubtract(&Some(Some(None))), AlgebraicResult::Identity(SELF_IDENT));
    assert_eq!(Some(Some(Some(()))).psubtract(&Some(Some(Some(())))), AlgebraicResult::None);
}

impl <V: Lattice> Lattice for Box<V> {
    fn join(&self, other: &Self) -> Self {
        Box::new(self.as_ref().join(other.as_ref()))
    }

    fn pmeet(&self, other: &Self) -> AlgebraicResult<Self> {
        self.as_ref().pmeet(other.as_ref()).map(|result| Box::new(result))
    }

    fn bottom() -> Self {
        Box::new(V::bottom())
    }
}

//GOAT: We need to decide upon a strategy RE build-in types.
// I have a strong bias towards convenience - e.g. implement some reasonable behavior for the built-in
// types, with lots of provisos
//

impl Lattice for &str {
    fn join(&self, _other: &Self) -> Self { self }
    fn pmeet(&self, _other: &Self) -> AlgebraicResult<Self> { AlgebraicResult::Identity(SELF_IDENT) }
    fn bottom() -> Self { "" }
}

impl DistributiveLattice for &str {
    fn psubtract(&self, other: &Self) -> AlgebraicResult<Self> where Self: Sized {
        if self == other {AlgebraicResult::None }
        else { AlgebraicResult::Element(*self) }
    }
}

impl DistributiveLattice for () {
    fn psubtract(&self, _other: &Self) -> AlgebraicResult<Self> where Self: Sized {
        AlgebraicResult::None
    }
}

impl Lattice for () {
    fn join(&self, _other: &Self) -> Self { () }
    fn pmeet(&self, _other: &Self) -> AlgebraicResult<Self> { AlgebraicResult::Identity(SELF_IDENT | COUNTER_IDENT) }
    fn bottom() -> Self { () }
}

impl Lattice for usize {
    fn join(&self, _other: &usize) -> usize { *self }
    fn pmeet(&self, _other: &usize) -> AlgebraicResult<usize> { AlgebraicResult::Identity(SELF_IDENT) }
    fn bottom() -> Self { 0 }
}

impl Lattice for u64 {
    fn join(&self, _other: &u64) -> u64 { *self }
    fn pmeet(&self, _other: &u64) -> AlgebraicResult<u64> { AlgebraicResult::Identity(SELF_IDENT) }
    fn bottom() -> Self { 0 }
}

impl DistributiveLattice for u64 {
    fn psubtract(&self, other: &Self) -> AlgebraicResult<Self> where Self: Sized {
        if self == other { AlgebraicResult::None }
        else { AlgebraicResult::Element(*self) }
    }
}

impl Lattice for u32 {
    fn join(&self, _other: &u32) -> u32 { *self }
    fn pmeet(&self, _other: &u32) -> AlgebraicResult<u32> { AlgebraicResult::Identity(SELF_IDENT) }
    fn bottom() -> Self { 0 }
}

impl Lattice for u16 {
    fn join(&self, _other: &u16) -> u16 { *self }
    fn pmeet(&self, _other: &u16) -> AlgebraicResult<u16> { AlgebraicResult::Identity(SELF_IDENT) }
    fn bottom() -> Self { 0 }
}

impl DistributiveLattice for u16 {
    fn psubtract(&self, other: &Self) -> AlgebraicResult<Self> {
        if self == other { AlgebraicResult::None }
        else { AlgebraicResult::Element(*self) }
    }
}

impl Lattice for u8 {
    fn join(&self, _other: &u8) -> u8 { *self }
    fn pmeet(&self, _other: &u8) -> AlgebraicResult<u8> { AlgebraicResult::Identity(SELF_IDENT) }
    fn bottom() -> Self { 0 }
}

impl <K: Copy + Eq + Hash, V : Copy + Lattice> Lattice for HashMap<K, V> {
    fn join(&self, other: &HashMap<K, V>) -> HashMap<K, V> {
        let mut res = HashMap::<K, V>::new();
        for (key, value) in self.iter() {
            if !other.contains_key(key) {
                res.insert(*key, *value);
            }
        }
        for (key, value) in other.iter() {
            if !self.contains_key(key) {
                res.insert(*key, *value);
            }
        }
        for (key, value) in self.iter() {
            if other.contains_key(key) {
                res.insert(*key, value.join(other.get(key).unwrap()));
            }
        }
        return res
    }

    fn pmeet(&self, other: &HashMap<K, V>) -> AlgebraicResult<HashMap<K, V>> {
        let mut res = HashMap::<K, V>::new();
        for (key, value) in self.iter() {
            if other.contains_key(key) {
                res.insert(*key, value.join(other.get(key).unwrap()));
            }
        }

        let len = res.len();

        if len == 0 {
            AlgebraicResult::None
        } else {
            let mut mask = 0;
            if len == self.len() {
                mask |= SELF_IDENT;
            }
            if len == other.len() {
                mask |= COUNTER_IDENT;
            }
            if mask > 0 {
                AlgebraicResult::Identity(mask)
            } else {
                AlgebraicResult::Element(res)
            }
        }
    }

    fn bottom() -> Self {
        HashMap::new()
    }
}
