
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
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
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
    ///
    /// Removes identity mask bits higher than 2
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
            Self::Identity(mask) => ident_f(mask.trailing_zeros() as usize),
        }
    }
    /// Returns an option containing the `Element` value, substituting the result from the corresponding
    /// index in the `idents` table if `self` is [Identity](AlgebraicResult::Identity)
    #[inline]
    pub fn into_option<I: AsRef<[VRef]>, VRef: std::borrow::Borrow<V>>(self, idents: I) -> Option<V>
        where V: Clone
    {
        match self {
            Self::Element(v) => Some(v),
            Self::None => None,
            Self::Identity(mask) => {
                let idents = idents.as_ref();
                Some(idents[mask.trailing_zeros() as usize].borrow().clone())
            },
        }
    }
    //GOAT, this interface feels like a foot-gun
    // /// Returns the contained `Element` value or one of the provided default values
    // #[inline]
    // pub fn unwrap_or(self, ident: V, none: V) -> V {
    //     match self {
    //         Self::Element(v) => v,
    //         Self::None => none,
    //         Self::Identity(_) => ident,
    //     }
    // }

    /// Returns the contained `Element` value or an identity value from the `idents` table.  Panics if `self`
    /// is [AlgebraicResult::None]
    #[inline]
    pub fn unwrap<I: AsRef<[VRef]>, VRef: std::borrow::Borrow<V>>(self, idents: I) -> V
        where V: Clone
    {
        match self {
            Self::Element(v) => v,
            Self::None => panic!(),
            Self::Identity(mask) => {
                let idents = idents.as_ref();
                idents[mask.trailing_zeros() as usize].borrow().clone()
            },
        }
    }
    /// Returns the contained `Element` value or runs one of the provided closures
    ///
    /// This is the most straightforward way to turn a partial lattice result into a complete lattice element
    #[inline]
    pub fn unwrap_or_else<IdentF, NoneF>(self, ident_f: IdentF, none_f: NoneF) -> V
        where
        IdentF: FnOnce(usize) -> V,
        NoneF: FnOnce() -> V
    {
        match self {
            Self::Element(v) => v,
            Self::None => none_f(),
            Self::Identity(mask) => ident_f(mask.trailing_zeros() as usize),
        }
    }
    /// Returns the contained `Element` value or one of the provided default values
    #[inline]
    pub fn unwrap_or<I: AsRef<[VRef]>, VRef: std::borrow::Borrow<V>>(self, idents: I, none: V) -> V
        where V: Clone
    {
        match self {
            Self::Element(v) => v,
            Self::None => none,
            Self::Identity(mask) => {
                let idents = idents.as_ref();
                idents[mask.trailing_zeros() as usize].borrow().clone()
            },
        }
    }
    /// Merges two `AlgebraicResult`s into a combined `AlgebraicResult<U>`.  This method is useful to compose a
    /// result for an operation on whole type arguments, from the results of separate operations on each field
    /// of the arguments.
    ///
    /// ```
    /// use pathmap::ring::{Lattice, AlgebraicResult};
    /// 
    /// struct Composed {
    ///     field0: bool,
    ///     field1: bool,
    /// }
    ///
    /// fn pjoin(a: &Composed, b: &Composed) -> AlgebraicResult<Composed> {
    ///     let result0 = a.field0.pjoin(&b.field0);
    ///     let result1 = a.field1.pjoin(&b.field1);
    ///     result0.merge(result1, |which_arg| {
    ///         match which_arg {
    ///             0 => Some(a.field0),
    ///             1 => Some(b.field0),
    ///             _ => unreachable!()
    ///         }
    ///     }, |which_arg| {
    ///         match which_arg {
    ///             0 => Some(a.field1),
    ///             1 => Some(b.field1),
    ///             _ => unreachable!()
    ///         }
    ///     }, |field0, field1| {
    ///         AlgebraicResult::Element(Composed{
    ///             field0: field0.unwrap(),
    ///             field1: field1.unwrap()
    ///         })
    ///     })
    /// }
    /// ```
    #[inline]
    pub fn merge<BV, U, MergeF, AIdent, BIdent>(self, b: AlgebraicResult<BV>, self_idents: AIdent, b_idents: BIdent, merge_f: MergeF) -> AlgebraicResult<U>
        where
        MergeF: FnOnce(Option<V>, Option<BV>) -> AlgebraicResult<U>,
        AIdent: FnOnce(usize) -> Option<V>,
        BIdent: FnOnce(usize) -> Option<BV>,
    {
        match self {
            Self::None => {
                match b {
                    AlgebraicResult::None => AlgebraicResult::None,
                    AlgebraicResult::Element(b_v) => merge_f(None, Some(b_v)),
                    AlgebraicResult::Identity(b_mask) => {
                        let self_ident = self_idents(0);
                        if self_ident.is_none() {
                            AlgebraicResult::Identity(b_mask)
                        } else {
                            let b_v = b_idents(b_mask.trailing_zeros() as usize);
                            merge_f(None, b_v)
                        }
                    },
                }
            },
            Self::Identity(self_mask) => {
                match b {
                    AlgebraicResult::None => {
                        let b_ident = b_idents(0);
                        if b_ident.is_none() {
                            AlgebraicResult::Identity(self_mask)
                        } else {
                            let self_v = self_idents(self_mask.trailing_zeros() as usize);
                            merge_f(self_v, None)
                        }
                    },
                    AlgebraicResult::Element(b_v) => {
                        let self_v = self_idents(self_mask.trailing_zeros() as usize);
                        merge_f(self_v, Some(b_v))
                    },
                    AlgebraicResult::Identity(b_mask) => {
                        let combined_mask = self_mask & b_mask;
                        if combined_mask > 0 {
                            AlgebraicResult::Identity(combined_mask)
                        } else {
                            let self_v = self_idents(self_mask.trailing_zeros() as usize);
                            let b_v = b_idents(b_mask.trailing_zeros() as usize);
                            merge_f(self_v, b_v)
                        }
                    }
                }
            },
            Self::Element(self_v) => {
                match b {
                    AlgebraicResult::None => merge_f(Some(self_v), None),
                    AlgebraicResult::Element(b_v) => merge_f(Some(self_v), Some(b_v)),
                    AlgebraicResult::Identity(b_mask) => {
                        let b_v = b_idents(b_mask.trailing_zeros() as usize);
                        merge_f(Some(self_v), b_v)
                    }
                }
            }
        }
    }
    /// Creates a new `AlgebraicResult` from an [AlgebraicStatus], and a method to create the element value
    #[inline]
    pub fn from_status<F>(status: AlgebraicStatus, element_f: F) -> Self
        where F: FnOnce() -> V
    {
        match status {
            AlgebraicStatus::None => Self::None,
            AlgebraicStatus::Identity => Self::Identity(SELF_IDENT),
            AlgebraicStatus::Element => Self::Element(element_f())
        }
    }
    /// Returns an [AlgebraicStatus] associated with the `AlgebraicResult`
    #[inline]
    pub fn status(&self) -> AlgebraicStatus {
        match self {
            AlgebraicResult::None => AlgebraicStatus::None,
            AlgebraicResult::Element(_) => AlgebraicStatus::Element,
            AlgebraicResult::Identity(mask) => {
                if mask & SELF_IDENT > 0 {
                    AlgebraicStatus::Identity
                } else {
                    AlgebraicStatus::Element
                }
            }
        }
    }
    //GOAT, may not be needed
    // /// Converts an AlgebraicResult into a FatAlgebraicResult
    // pub(crate) fn into_fat(self, arg0_ident: V, arg1_ident: V) -> FatAlgebraicResult<V> {
    //     match self {
    //         Self::None => FatAlgebraicResult::none(),
    //         Self::Element(v) => FatAlgebraicResult::element(v),
    //         Self::Identity(mask) => {
    //             if mask & SELF_IDENT > 0 {
    //                 FatAlgebraicResult::new(mask, Some(arg0_ident))
    //             } else {
    //                 debug_assert!(mask & COUNTER_IDENT > 0);
    //                 FatAlgebraicResult::new(mask, Some(arg1_ident))
    //             }
    //         }
    //     }
    // }
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

/// Status result that is returned from an in-place algebraic operation (a method that takes `&mut self`)
///
/// NOTE: For some operations, it is conceptually valid for both `Identity` and `None` results to be
/// simultaneously appropriate, for example `None.join_into(None)`. In these situations, `None` should take
/// precedence over `Identity`, but either of the results can be considered correct so your code must behave
/// correctly in either case.
///
/// This type mirrors [AlgebraicResult]
#[derive(Clone, Copy, Default, Debug, PartialEq, Eq)]
pub enum AlgebraicStatus {
    /// A result indicating `self` was completely annhilated and is now empty
    #[default]
    None,
    /// A result indicating `self` was unmodified by the operation
    Identity,
    /// A result indicating `self` was modified by the operation, and is not empty
    Element,
}

impl AlgebraicStatus {
    /// Returns `true` if the status is [AlgebraicStatus::None], otherwise returns `false`
    #[inline]
    pub fn is_none(&self) -> bool {
        matches!(self, Self::None)
    }
    /// Returns `true` if the status is [AlgebraicStatus::Identity], otherwise returns `false`
    #[inline]
    pub fn is_identity(&self) -> bool {
        matches!(self, Self::Identity)
    }
    /// Returns `true` if the status is [AlgebraicStatus::Element], otherwise returns `false`
    #[inline]
    pub fn is_element(&self) -> bool {
        matches!(self, Self::Element)
    }
    /// Merges two `AlgebraicStatus` values into one.  Useful when composing the status from operations on individual fields
    ///
    /// The `self_none` and `b_none` args indicate whether the `self` and `b` args, respectively, correspond to `None`
    /// values prior to the operation.
    ///
    /// See [AlgebraicResult::merge].
    #[inline]
    pub fn merge(self, b: Self, self_none: bool, b_none: bool) -> AlgebraicStatus {
        match self {
            Self::None => match b {
                Self::None => Self::None,
                Self::Element => Self::Element,
                Self::Identity => if self_none {
                    Self::Identity
                } else {
                    Self::Element
                },
            },
            Self::Identity => match b {
                Self::Element => Self::Element,
                Self::Identity => Self::Identity,
                Self::None => if b_none {
                    Self::Identity
                } else {
                    Self::Element
                },
            },
            Self::Element => Self::Element
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
    pub(crate) fn none() -> Self {
        Self {identity_mask: 0, element: None}
    }
    /// The result of an operation that generated a brand new result
    #[inline(always)]
    pub(crate) fn element(e: V) -> Self {
        Self {identity_mask: 0, element: Some(e)}
    }
    /// Merges two `FatAlgebraicResult<V>`s into an `AlgebraicResult<U>`.  See [AlgebraicResult::merge]
    #[inline]
    pub fn merge_and_convert<U, F>(self, other: Self, merge_f: F) -> AlgebraicResult<U>
        where F: FnOnce(Option<V>, Option<V>) -> AlgebraicResult<U>,
    {
        if self.element.is_none() && other.element.is_none() {
            return AlgebraicResult::None
        }
        let combined_mask = self.identity_mask & other.identity_mask;
        if combined_mask > 0 {
            return AlgebraicResult::Identity(combined_mask)
        }
        merge_f(self.element, other.element)
    }
    //GOAT, currently unused, but fully implemented and working
    // /// Intersects arg with the contents of self, and sets the arg_idx bit in the case of an identity result
    // pub fn meet(self, arg: &V, arg_idx: usize) -> Self where V: Lattice + Clone {
    //     match self.element {
    //         None => {
    //             debug_assert_eq!(self.identity_mask, 0);
    //             Self::new(self.identity_mask, None)
    //         },
    //         Some(self_element) => match self_element.pmeet(arg) {
    //             AlgebraicResult::None => Self::none(),
    //             AlgebraicResult::Element(e) => Self::element(e),
    //             AlgebraicResult::Identity(mask) => {
    //                 if mask & SELF_IDENT > 0 {
    //                     let new_mask = self.identity_mask | ((mask & COUNTER_IDENT) << (arg_idx-1));
    //                     Self::new(new_mask, Some(self_element))
    //                 } else {
    //                     debug_assert!(mask & COUNTER_IDENT > 0);
    //                     let new_mask = (mask & COUNTER_IDENT) << (arg_idx-1);
    //                     Self::new(new_mask, Some(arg.clone()))
    //                 }
    //             }
    //         }
    //     }
    // }
    /// Unions arg with the contents of self, and sets the arg_idx bit in the case of an identity result
    pub fn join(self, arg: &V, arg_idx: usize) -> Self where V: Lattice + Clone {
        match self.element {
            None => {
                Self::new(self.identity_mask | 1 << arg_idx, Some(arg.clone()))
            },
            Some(self_element) => match self_element.pjoin(&arg) {
                AlgebraicResult::None => Self::none(),
                AlgebraicResult::Element(e) => Self::element(e),
                AlgebraicResult::Identity(mask) => {
                    if mask & SELF_IDENT > 0 {
                        let new_mask = self.identity_mask | ((mask & COUNTER_IDENT) << (arg_idx-1));
                        Self::new(new_mask, Some(self_element))
                    } else {
                        debug_assert!(mask & COUNTER_IDENT > 0);
                        let new_mask = (mask & COUNTER_IDENT) << (arg_idx-1);
                        Self::new(new_mask, Some(arg.clone()))
                    }
                }
            }
        }
    }
}

/// Implements basic algebraic behavior (union & intersection) for a type
pub trait Lattice {
    /// Implements the union operation between two instances of a type in a partial lattice, resulting in
    /// the creation of a new result instance
    fn pjoin(&self, other: &Self) -> AlgebraicResult<Self> where Self: Sized;

    /// Implements the union operation between two instances of a type, consuming the `other` input operand,
    /// and modifying `self` to become the joined type
    fn join_into(&mut self, other: Self) -> AlgebraicStatus where Self: Sized {
        let result = self.pjoin(&other);
        in_place_default_impl(result, self, other, || Self::bottom(), |e| e)
        //GOAT trash
        // match self.pjoin(&other) {
        //     AlgebraicResult::None => {
        //         *self = Self::bottom();
        //         AlgebraicStatus::None
        //     },
        //     AlgebraicResult::Element(v) => {
        //         *self = v;
        //         AlgebraicStatus::Element
        //     },
        //     AlgebraicResult::Identity(mask) => {
        //         if mask & SELF_IDENT > 0 {
        //             AlgebraicStatus::Identity
        //         } else {
        //             *self = other;
        //             AlgebraicStatus::Element
        //         }
        //     },
        // }
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
    fn join_all<S: AsRef<Self>, Args: AsRef<[S]>>(xs: Args) -> AlgebraicResult<Self> where Self: Sized + Clone {
        let mut iter = xs.as_ref().into_iter().enumerate();
        let mut result = match iter.next() {
            None => return AlgebraicResult::None,
            Some((_, first)) => FatAlgebraicResult::new(SELF_IDENT, Some(first.as_ref().clone())),
        };
        for (i, next) in iter {
            result = result.join(next.as_ref(), i);
        }
        result.into()
    }
}

/// Internal function to implement the default behavior of `join_into`, `meet_into`, etc. in terms of `pjoin`, `pmeet`, etc.
fn in_place_default_impl<SelfT, OtherT, ConvertF, DefaultF>(result: AlgebraicResult<SelfT>, self_ref: &mut SelfT, other: OtherT, default_f: DefaultF, convert_f: ConvertF) -> AlgebraicStatus
    where
    DefaultF: FnOnce() -> SelfT,
    ConvertF: Fn(OtherT) -> SelfT
{
    match result {
        AlgebraicResult::None => {
            *self_ref = default_f();
            AlgebraicStatus::None
        },
        AlgebraicResult::Element(v) => {
            *self_ref = v;
            AlgebraicStatus::Element
        },
        AlgebraicResult::Identity(mask) => {
            if mask & SELF_IDENT > 0 {
                AlgebraicStatus::Identity
            } else {
                *self_ref = convert_f(other);
                AlgebraicStatus::Element
            }
        },
    }
}

/// Implements algebraic behavior on a reference to a [Lattice] type, such as a smart pointer that can't
/// hold ownership
pub trait LatticeRef {
    type T;
    fn pjoin(&self, other: &Self) -> AlgebraicResult<Self::T>;
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
    fn pjoin(&self, other: &OtherT) -> AlgebraicResult<Self> where Self: Sized;
    fn join_into(&mut self, other: OtherT) -> AlgebraicStatus where Self: Sized {
        let result = self.pjoin(&other);
        in_place_default_impl(result, self, other, || Self::bottom(), |e| Self::convert(e))
    }
    fn pmeet(&self, other: &OtherT) -> AlgebraicResult<Self> where Self: Sized;
    fn join_all(xs: &[&Self]) -> Self where Self: Sized;
    fn convert(other: OtherT) -> Self;
    fn bottom() -> Self;
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
    fn pjoin(&self, other: &Option<V>) -> AlgebraicResult<Self> {
        match self {
            None => match other {
                None => { AlgebraicResult::None }
                Some(_) => { AlgebraicResult::Identity(COUNTER_IDENT) }
            },
            Some(l) => match other {
                None => { AlgebraicResult::Identity(SELF_IDENT) }
                Some(r) => { l.pjoin(r).map(|result| Some(result)) }
            }
        }
    }
    fn join_into(&mut self, other: Self) -> AlgebraicStatus {
        match self {
            None => { match other {
                None => AlgebraicStatus::None,
                Some(r) => {
                    *self = Some(r);
                    AlgebraicStatus::Element
                }
            } }
            Some(l) => match other {
                None => AlgebraicStatus::Identity,
                Some(r) => {
                    l.join_into(r)
                }
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
    fn pjoin(&self, other: &Self) -> AlgebraicResult<Self::T> {
        match self {
            None => { match other {
                None => { AlgebraicResult::None }
                Some(_) => { AlgebraicResult::Identity(COUNTER_IDENT) }
            } }
            Some(l) => match other {
                None => { AlgebraicResult::Identity(SELF_IDENT) }
                Some(r) => { l.pjoin(r).map(|result| Some(result)) }
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
    fn pjoin(&self, other: &Self) -> AlgebraicResult<Self> {
        self.as_ref().pjoin(other.as_ref()).map(|result| Box::new(result))
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

//GOAT, LatticeCounter and LatticeBitfield should be traits.
// BitfieldLattice should be implemented on bool
// Make monad types that can implement these traits on all prim types
// Make a "convertable_to" trait across all prim types

//GOAT, I don't know what a Lattice on &str looks like.  We could make a Lattice impl for a String as a set of chars,
// but on the other hand, I think we'd be better off with a "LatticeSet" trait, and then it would make more sense
// to implement that on a HashSet and HashMap
impl Lattice for &str {
    fn pjoin(&self, _other: &Self) -> AlgebraicResult<Self> { AlgebraicResult::Identity(SELF_IDENT) }
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
    fn pjoin(&self, _other: &Self) -> AlgebraicResult<Self> { AlgebraicResult::Identity(SELF_IDENT | COUNTER_IDENT) }
    fn pmeet(&self, _other: &Self) -> AlgebraicResult<Self> { AlgebraicResult::Identity(SELF_IDENT | COUNTER_IDENT) }
    fn bottom() -> Self { () }
}

impl Lattice for usize {
    fn pjoin(&self, _other: &usize) -> AlgebraicResult<usize> { AlgebraicResult::Identity(SELF_IDENT) }
    fn pmeet(&self, _other: &usize) -> AlgebraicResult<usize> { AlgebraicResult::Identity(SELF_IDENT) }
    fn bottom() -> Self { 0 }
}

impl Lattice for u64 {
    fn pjoin(&self, _other: &u64) -> AlgebraicResult<u64> { AlgebraicResult::Identity(SELF_IDENT) }
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
    fn pjoin(&self, _other: &u32) -> AlgebraicResult<u32> { AlgebraicResult::Identity(SELF_IDENT) }
    fn pmeet(&self, _other: &u32) -> AlgebraicResult<u32> { AlgebraicResult::Identity(SELF_IDENT) }
    fn bottom() -> Self { 0 }
}

impl Lattice for u16 {
    fn pjoin(&self, _other: &u16) -> AlgebraicResult<u16> { AlgebraicResult::Identity(SELF_IDENT) }
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
    fn pjoin(&self, _other: &u8) -> AlgebraicResult<u8> { AlgebraicResult::Identity(SELF_IDENT) }
    fn pmeet(&self, _other: &u8) -> AlgebraicResult<u8> { AlgebraicResult::Identity(SELF_IDENT) }
    fn bottom() -> Self { 0 }
}

impl DistributiveLattice for bool {
    fn psubtract(&self, other: &bool) -> AlgebraicResult<Self> {
        if *self && *other {
            AlgebraicResult::Element(false)
        } else {
            AlgebraicResult::Identity(SELF_IDENT)
        }
    }
}

impl Lattice for bool {
    fn pjoin(&self, other: &bool) -> AlgebraicResult<bool> {
        if !*self && *other {
            AlgebraicResult::Identity(COUNTER_IDENT) //result is true
        } else {
            AlgebraicResult::Identity(SELF_IDENT)
        }
    }
    fn pmeet(&self, other: &bool) -> AlgebraicResult<bool> {
        if *self && !*other {
            AlgebraicResult::Identity(COUNTER_IDENT) //result is false
        } else {
            AlgebraicResult::Identity(SELF_IDENT)
        }
    }
    fn bottom() -> Self { false }
}

impl <K: Clone + Eq + Hash, V: Clone + Lattice> Lattice for HashMap<K, V> {
    fn pjoin(&self, other: &HashMap<K, V>) -> AlgebraicResult<HashMap<K, V>> {
        let mut result = HashMap::<K, V>::new();
        let mut is_ident = self.len() >= other.len();
        let mut is_counter_ident = self.len() <= other.len();
        for (key, self_val) in self.iter() {
            if let Some(other_val) = other.get(key) {
                // A key in both HashMaps
                let inner_result = self_val.pjoin(other_val);
                hashmap_update_ident_flags_with_result(
                    &mut result, inner_result, key, self_val, other_val, &mut is_ident, &mut is_counter_ident
                );
            } else {
                // A key in self, but not in other
                result.insert(key.clone(), self_val.clone());
                is_counter_ident = false;
            }
        }
        for (key, value) in other.iter() {
            if !self.contains_key(key) {
                // A key in other, but not in self
                result.insert(key.clone(), value.clone());
                is_ident = false;
            }
        }
        hashmap_integrate_into_result(result, is_ident, is_counter_ident, self.len(), other.len())
    }

    fn pmeet(&self, other: &HashMap<K, V>) -> AlgebraicResult<HashMap<K, V>> {
        let mut result = HashMap::<K, V>::new();
        let mut is_ident = true;
        let mut is_counter_ident = true;
        for (key, self_val) in self.iter() {
            if let Some(other_val) = other.get(key) {
                let inner_result = self_val.pmeet(other_val);
                hashmap_update_ident_flags_with_result(
                    &mut result, inner_result, key, self_val, other_val, &mut is_ident, &mut is_counter_ident
                );
            } else {
                is_ident = false;
            }
        }
        hashmap_integrate_into_result(result, is_ident, is_counter_ident, self.len(), other.len())
    }

    fn bottom() -> Self {
        HashMap::new()
    }
}

/// Internal function to integrate an `AlgebraicResult` from an element in a HashMap into the HashMap's own result
#[inline]
fn hashmap_update_ident_flags_with_result<K: Clone + Eq + Hash, V: Clone>(
    result_map: &mut HashMap<K, V>,
    result: AlgebraicResult<V>,
    key: &K,
    self_val: &V,
    other_val: &V,
    is_ident: &mut bool,
    is_counter_ident: &mut bool
) {
    match result {
        AlgebraicResult::None => {
            *is_ident = false;
            *is_counter_ident = false;
        },
        AlgebraicResult::Element(new_val) => {
            *is_ident = false;
            *is_counter_ident = false;
            result_map.insert(key.clone(), new_val);
        },
        AlgebraicResult::Identity(mask) => {
            if mask & SELF_IDENT > 0 {
                result_map.insert(key.clone(), self_val.clone());
            } else {
                *is_ident = false;
            }
            if mask & COUNTER_IDENT > 0 {
                if mask & SELF_IDENT == 0 {
                    result_map.insert(key.clone(), other_val.clone());
                }
            } else {
                *is_counter_ident = false;
            }
        }
    }
}

/// Internal function to make an `AlgebraicResult` from a new result HashMap and flags
#[inline]
fn hashmap_integrate_into_result<K: Clone + Eq + Hash, V: Clone>(
    result_map: HashMap<K, V>,
    is_ident: bool,
    is_counter_ident: bool,
    self_map_len: usize,
    other_map_len: usize,
) -> AlgebraicResult<HashMap<K, V>> {
    let result_len = result_map.len();
    if result_len == 0 {
        AlgebraicResult::None
    } else {
        let mut ident_mask = 0;
        if is_ident && self_map_len == result_len {
            ident_mask |= SELF_IDENT;
        }
        if is_counter_ident && other_map_len == result_len {
            ident_mask |= COUNTER_IDENT;
        }
        if ident_mask > 0 {
            AlgebraicResult::Identity(ident_mask)
        } else {
            AlgebraicResult::Element(result_map)
        }
    }
}



//GOAT, do a test for the HashMap impl of Lattice & DeistributiveLattice

//GOAT, implement Lattice on HashSet

//GOAT, think about impl on Vec (ordered collection) vs. impl on Vec (indexed set)
//    I see how the indexed_set impl would work, but I don't see how an ordered collection works at all