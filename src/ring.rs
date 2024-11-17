
use std::collections::HashMap;
use std::hash::Hash;

/// The result of an algebraic operation on elements in a partial lattice
#[derive(Clone, Copy, Default, Debug, PartialEq, Eq)]
pub enum AlgebraicResult<V> {
    /// A result indicating the input values perfectly annhilate and the output should be removed and discarded
    #[default]
    None,
    /// A result indicating the lvalue element was unmodified by the operation
    Identity,
    /// A new result element
    Element(V),
}

impl<V> AlgebraicResult<V> {
    /// Maps a `AlgebraicResult<V>` to `AlgebraicResult<U>` by applying a function to a contained value, if
    /// self is `AlgebraicResult::Element(V)`.  Otherwise returns the value of `self`
    #[inline]
    pub fn map<U, F>(self, f: F) -> AlgebraicResult<U>
        where F: FnOnce(V) -> U,
    {
        match self {
            Self::None => AlgebraicResult::None,
            Self::Identity => AlgebraicResult::Identity,
            Self::Element(v) => AlgebraicResult::Element(f(v)),
        }
    }
    /// Converts from `&AlgebraicResult<V>` to `AlgebraicResult<&V>`
    #[inline]
    pub fn as_ref(&self) -> AlgebraicResult<&V> {
        match *self {
            Self::Element(ref v) => AlgebraicResult::Element(v),
            Self::None => AlgebraicResult::None,
            Self::Identity => AlgebraicResult::Identity,
        }
    }
    /// Returns an option containing the `Element` value, substituting the result of the `ident_f`
    /// closure if `self` is [Identity](AlgebraicResult::Identity)
    #[inline]
    pub fn map_ident_into_option<F>(self, ident_f: F) -> Option<V>
        where F: FnOnce() -> Option<V>,
    {
        match self {
            Self::Element(v) => Some(v),
            Self::None => None,
            Self::Identity => ident_f(),
        }
    }
    /// Returns the contained `Element` value or one of the provided `ident` or `none` default values
    #[inline]
    pub fn unwrap_or(self, ident: V, none: V) -> V {
        match self {
            Self::Element(v) => v,
            Self::None => none,
            Self::Identity => ident,
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
            Self::Identity => AlgebraicResult::Identity,
        }
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

    /// Implements the intersection operation between two instances of a type
    //GOAT, this should be able to return None if the overlap is an empty type
    fn meet(&self, other: &Self) -> Self;

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
    fn meet(&self, other: &Self) -> Self::T;
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
    fn meet(&self, other: &OtherT) -> Self;
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
    fn meet(&self, other: &Option<V>) -> Option<V> {
        match self {
            None => { None }
            Some(l) => {
                match other {
                    None => { None }
                    Some(r) => Some(l.meet(r))
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
    fn meet(&self, other: &Option<&V>) -> Option<V> {
        match self {
            None => { None }
            Some(l) => {
                match other {
                    None => { None }
                    Some(r) => Some(l.meet(r))
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
                    None => { AlgebraicResult::Identity }
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
                    None => { AlgebraicResult::Identity }
                    Some(o) => { s.psubtract(o).map(|v| Some(v)) }
                }
            }
        }
    }
}

#[test]
fn option_subtract_test() {
    assert_eq!(Some(()).psubtract(&Some(())), AlgebraicResult::None);
    assert_eq!(Some(()).psubtract(&None), AlgebraicResult::Identity);
    assert_eq!(Some(Some(())).psubtract(&Some(Some(()))), AlgebraicResult::None);
    assert_eq!(Some(Some(())).psubtract(&None), AlgebraicResult::Identity);
    assert_eq!(Some(Some(())).psubtract(&Some(None)), AlgebraicResult::Identity);
    assert_eq!(Some(Some(Some(()))).psubtract(&Some(Some(None))), AlgebraicResult::Identity);
    assert_eq!(Some(Some(Some(()))).psubtract(&Some(Some(Some(())))), AlgebraicResult::None);
}

impl <V: Lattice> Lattice for Box<V> {
    fn join(&self, other: &Self) -> Self {
        Box::new(self.as_ref().join(other.as_ref()))
    }

    fn meet(&self, other: &Self) -> Self {
        Box::new(self.as_ref().meet(other.as_ref()))
    }

    fn bottom() -> Self {
        Box::new(V::bottom())
    }
}

//GOAT: We need to decide upon a strategy RE build-in types.
// I have a strong bias towards convenience - e.g. implement some reasonable behavior for the built-in
// types, with lots of provisos
//
//TODO: Roll a macro to impl lattice across all the primitive types without a blanket impl

impl Lattice for &str {
    fn join(&self, _other: &Self) -> Self { self }
    fn meet(&self, _other: &Self) -> Self { self }
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
    fn meet(&self, _other: &Self) -> Self { () }
    fn bottom() -> Self { () }
}

impl Lattice for usize {
    fn join(&self, _other: &usize) -> usize { *self }
    fn meet(&self, _other: &usize) -> usize { *self }
    fn bottom() -> Self { 0 }
}

impl Lattice for u64 {
    fn join(&self, _other: &u64) -> u64 { *self }
    fn meet(&self, _other: &u64) -> u64 { *self }
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
    fn meet(&self, _other: &u32) -> u32 { *self }
    fn bottom() -> Self { 0 }
}

impl Lattice for u16 {
    fn join(&self, _other: &u16) -> u16 { *self }
    fn meet(&self, other: &u16) -> u16 { *other }
    fn bottom() -> Self { 0 }
}

impl DistributiveLattice for u16 {
    fn psubtract(&self, other: &Self) -> AlgebraicResult<Self> where Self: Sized {
        if self == other { AlgebraicResult::None }
        else { AlgebraicResult::Element(*self) }
    }
}

impl Lattice for u8 {
    fn join(&self, _other: &u8) -> u8 { *self }
    fn meet(&self, _other: &u8) -> u8 { *self }
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

    fn meet(&self, other: &HashMap<K, V>) -> HashMap<K, V> {
        let mut res = HashMap::<K, V>::new();
        for (key, value) in self.iter() {
            if other.contains_key(key) {
                res.insert(*key, value.join(other.get(key).unwrap()));
            }
        }
        return res;
    }

    fn bottom() -> Self {
        HashMap::new()
    }
}
