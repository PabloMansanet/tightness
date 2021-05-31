use std::{
    borrow::Borrow,
    fmt::Debug,
    marker::PhantomData,
    ops::{Deref, Index},
};

use thiserror::Error;

#[derive(Error)]
#[error("Value supplied did not satisfy the type invariant")]
/// The result of a failed invariant check on construction. Contains the value
/// that failed to uphold the invariant.
pub struct ConstructionError<T>(pub T);
impl<T> Debug for ConstructionError<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("ConstructionError").finish()
    }
}

/// The result of a failed invariant check at the end of mutation.
///
/// In the cases where it's recoverable, this error contains the value
/// that failed to uphold the invariant.
#[derive(Error)]
#[error("Value did not satisfy the type invariant after mutation")]
pub struct MutationError<T>(pub Option<T>);
impl<T> Debug for MutationError<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("MutationError")
    }
}

/// The result of a broken invariant at some unspecified point in the
/// past. This can only happen as a consequence of incorrect usage of
/// `unsafe` accessors enabled with the `unsafe_access` flag
#[cfg(feature = "unsafe_access")]
#[derive(Error, Debug)]
#[error("Invariant was broken at some point in the past")]
pub struct BrokenInvariantError;

/// Trait for an arbitrary condition that a bounded type must guarantee
/// to uphold at all times.
pub trait Bound {
    /// The type that the invariant is predicated on.
    type Target;
    /// The condition that the target type must verify at all times.
    fn check(target: &Self::Target) -> bool;
}

/// A bounded type, i.e. a thin wrapper around an inner type that guarantees a
/// specific invariant is always held. Generic over an inner type `T` and a
/// [`Bound`](Bound) that targets it.
///
/// Bounded types can be constructed directly or through the [`bound`](bound)
/// macro:
/// ```
/// // Defined directly
/// use tightness::{Bounded, Bound};
///
/// #[derive(Debug)]
/// pub struct LetterBound;
///
/// impl tightness::Bound for LetterBound {
///     type Target = char;
///     fn check(target: &char) -> bool { target.is_alphabetic() }
/// }
///
/// pub type Letter = tightness::Bounded<char, LetterBound>;
///
/// ```
///
/// ```
/// // Defined via macro
/// use tightness::{bound, Bounded};
/// bound!(pub Letter: char where |l| l.is_alphabetic());
/// ```
#[derive(Debug)]
pub struct Bounded<T, B: Bound<Target = T>>(T, PhantomData<B>);

impl<T, B: Bound<Target = T>> Bounded<T, B> {
    /// Fallible constructor. Will return an error if the argument `t`
    /// doesn't fulfill the conditions of the bound.
    ///
    /// ```
    /// # use tightness::{bound, Bounded, ConstructionError};
    /// bound!(Letter: char where |c| c.is_alphabetic());
    /// assert!(Letter::new('a').is_ok());
    /// assert!(matches!(Letter::new('5'), Err(ConstructionError('5'))));
    /// ```
    pub fn new(t: T) -> Result<Self, ConstructionError<T>> {
        if B::check(&t) {
            Ok(Self(t, Default::default()))
        } else {
            Err(ConstructionError(t))
        }
    }

    /// Will panic if the conditions of the bound don't hold after mutation.
    ///
    /// ```should_panic
    /// # use tightness::{bound, Bounded};
    /// bound!(Letter: char where |c| c.is_alphabetic());
    /// let mut letter = Letter::new('a').unwrap();
    /// letter.mutate(|l| *l = 'b');
    ///
    /// // Panics:
    /// letter.mutate(|l| *l = '5');
    /// ```
    pub fn mutate(&mut self, f: impl FnOnce(&mut T)) {
        self.assume_invariant();
        f(&mut self.0);
        assert!(B::check(&self.0));
    }

    /// If the conditions of the bound don't hold after mutation, will restore to a given value.
    ///
    /// ```
    /// # use tightness::{bound, Bounded};
    /// bound!(Letter: char where |c| c.is_alphabetic());
    /// let mut letter = Letter::new('a').unwrap();
    /// let mut fallback = Letter::new('b').unwrap();
    ///
    /// letter.mutate_or(fallback, |l| *l = '5').unwrap_err();
    /// assert_eq!(*letter, 'b');
    /// ```
    pub fn mutate_or(
        &mut self,
        default: Self,
        f: impl FnOnce(&mut T),
    ) -> Result<(), MutationError<T>> {
        self.assume_invariant();
        f(&mut self.0);
        if B::check(&self.0) {
            Ok(())
        } else {
            *self = default;
            Err(MutationError(None))
        }
    }

    /// The value is dropped if the conditions of the bound don't hold after mutation.
    /// ```
    /// # use tightness::{bound, Bounded, MutationError};
    /// bound!(Letter: char where |c| c.is_alphabetic());
    /// let mut letter = Letter::new('a').unwrap();
    ///
    /// let letter = letter.into_mutated(|l| *l = 'b').unwrap();
    /// let result = letter.into_mutated(|l| *l = '5');
    ///
    /// assert!(matches!(result, Err(MutationError(Some('5')))));
    /// ```
    pub fn into_mutated(mut self, f: impl FnOnce(&mut T)) -> Result<Self, MutationError<T>> {
        self.assume_invariant();
        f(&mut self.0);
        if B::check(&self.0) {
            Ok(self)
        } else {
            Err(MutationError(Some(self.0)))
        }
    }

    /// Access the inner value through an immutable reference.
    #[inline(always)]
    pub fn get(&self) -> &T {
        self.assume_invariant();
        &self.0
    }

    /// Retrieve the inner, unprotected value.
    #[inline(always)]
    pub fn into_inner(self) -> T {
        self.assume_invariant();
        self.0
    }

    /// Invariant must be upheld manually!
    ///
    /// ## Safety
    ///
    /// You must be certain that the value passed to this function satisfies
    /// the conditions of the bound.
    ///
    /// Creating a `Bounded` type that does not satisfy the invariant
    /// is **always** Undefined Behaviour. Don't construct a `Bounded` object
    /// with the intention of enforcing the invariant later.
    ///
    /// Consider using the safe `new` constructor instead unless you
    /// *absolutely* need the performance gain from skipping the check.
    ///
    /// ```ignore
    /// tightness::bound!(Restricted: u32 where |u| *u > 10);
    /// // This is correct
    /// let mut foo = unsafe { Restricted::new_unchecked(20) };
    /// // This is already undefined behaviour!
    /// let mut foo = unsafe { Restricted::new_unchecked(5) };
    /// ```
    #[cfg(feature = "unsafe_access")]
    pub unsafe fn new_unchecked(t: T) -> Self { Self(t, Default::default()) }

    /// Invariant must be upheld manually!
    ///
    /// ## Safety
    ///
    /// You must be certain that the final value, after mutation, satisfies the
    /// conditions of the bound **in every possible case**.
    ///
    /// Creating a `Bounded` type that does not satisfy the invariant
    /// is **always** undefined behaviour. Don't construct a `Bounded` object
    /// with the intention of enforcing the invariant later; this crate makes
    /// liberal use of compiler hints to guarantee the compiler the invariant
    /// is always upheld.
    ///
    /// ```
    /// tightness::bound!(Restricted: u32 where |u| *u > 10);
    /// let mut foo = Restricted::new(20).unwrap();
    /// // This is correct, as we know the invariants always hold after mutation
    /// unsafe { foo.mutate_unchecked(|u| *u = u.saturating_add(1)); }
    /// ```
    ///
    /// ```ignore
    /// tightness::bound!(Restricted: u32 where |u| *u > 10);
    /// let mut foo = Restricted::new(20).unwrap();
    /// // This **is undefined behaviour**, even if there is no risk of
    /// // misuse. a `Bounded` object must not exist with broken
    /// // invariants at any time.
    /// unsafe { foo.mutate_unchecked(|u| *u = 0); }
    /// unsafe { foo.mutate_unchecked(|u| *u = 20); }
    /// ```
    #[cfg(feature = "unsafe_access")]
    pub unsafe fn mutate_unchecked(&mut self, f: impl FnOnce(&mut T)) {
        self.assume_invariant();
        f(&mut self.0);
        self.assume_invariant();
    }

    /// Gives mutable access to the internals without upholding invariants.
    /// They must be upheld manually at the point the reference is dropped!
    ///
    /// ## Safety
    ///
    /// The value must satisfy the invariant at the point the mutable reference
    /// is dropped. It is valid to break the invariant while the reference lives,
    /// but it must be restored before dropping it or risk undefined behaviour.
    ///
    /// tightness::bound!(Restricted: u32 where |u| *u > 10);
    /// let mut foo = Restricted::new(20).unwrap();
    ///
    /// {
    ///    let foo_ref = foo.get_mut();
    ///    *foo_ref = 5; // This is valid, though it must be fixed
    ///    *foo_ref = 20; // Invariant is restored in time
    /// }
    #[cfg(feature = "unsafe_access")]
    pub unsafe fn get_mut(&mut self) -> &mut T {
        self.assume_invariant();
        &mut self.0
    }

    /// Verifies invariants. This is guaranteed to succeed unless you've used
    /// one of the `unsafe` methods that require variants to be manually upheld.
    ///
    /// Note: You should *not* rely on `verify` to make your `Bounded` type "catch up"
    /// to its broken invariants. A `Bounded` type that broke its invariants in the
    /// past is **always** undefined behaviour. This function should be an absolute last
    /// resort escape hatch, mainly useful for debugging.
    #[cfg(feature = "unsafe_access")]
    pub fn verify(&self) -> Result<(), BrokenInvariantError> {
        if B::check(&self.0) {
            Ok(())
        } else {
            Err(BrokenInvariantError)
        }
    }

    /// Assumes the invariant conditions hold. This grants the compiler additional
    /// information to optimize code that uses `Bound` types.
    ///
    /// ## Safety
    /// `assume_invariant` is private, and carefully called only at the points where
    /// the invariant is guaranteed to hold. The only situation where the invariants may
    /// not hold at the point of call is through misuse of any of the following functions:
    ///
    /// * `get_mut`
    /// * `new_unchecked`
    /// * `mutate_unchecked`
    ///
    /// They are all `unsafe` and gated behind the `unsafe_access` flags, so it is correct
    /// to always assume the invariants hold.
    #[inline(always)]
    fn assume_invariant(&self) {
        if !B::check(&self.0) { unsafe { std::hint::unreachable_unchecked() } }
    }
}

impl<T: Clone, B: Bound<Target = T>> Bounded<T, B> {
    /// Preserves invariants after mutation, erroring out if the attempt to mutate was
    /// invalid. Requires a copy to ensure the value is recoverable.
    ///
    /// ```
    /// # use tightness::{bound, Bounded, MutationError};
    /// bound!(Letter: char where |c| c.is_alphabetic());
    /// let mut letter = Letter::new('a').unwrap();
    ///
    /// letter.try_mutate(|l| *l = 'b').unwrap();
    /// let result = letter.into_mutated(|l| *l = '5').unwrap_err();
    /// assert!(matches!(result, MutationError(Some('5'))));
    /// assert_eq!(*letter, 'b');
    /// ```
    pub fn try_mutate(&mut self, f: impl FnOnce(&mut T)) -> Result<(), MutationError<T>> {
        self.assume_invariant();
        let mut duplicate = self.0.clone();
        f(&mut duplicate);
        if B::check(&duplicate) {
            self.0 = duplicate;
            Ok(())
        } else {
            Err(MutationError(None))
        }
    }
}

impl<T: Clone, B: Bound<Target = T>> Clone for Bounded<T, B> {
    #[inline(always)]
    fn clone(&self) -> Self {
        self.assume_invariant();
        Self(self.0.clone(), Default::default())
    }
}

impl<T, B: Bound<Target = T>> Borrow<T> for Bounded<T, B> {
    #[inline(always)]
    fn borrow(&self) -> &T {
        self.assume_invariant();
        &self.0
    }
}

impl<T, B: Bound<Target = T>> AsRef<T> for Bounded<T, B> {
    #[inline(always)]
    fn as_ref(&self) -> &T {
        self.assume_invariant();
        &self.0
    }
}

impl<T, B: Bound<Target = T>> Deref for Bounded<T, B> {
    type Target = T;
    #[inline(always)]
    fn deref(&self) -> &Self::Target {
        self.assume_invariant();
        &self.0
    }
}

impl<T: PartialEq, B: Bound<Target = T>> PartialEq for Bounded<T, B> {
    fn eq(&self, other: &Self) -> bool {
        self.assume_invariant();
        other.assume_invariant();
        self.0.eq(&other.0)
    }
}

impl<T: Eq, B: Bound<Target = T>> Eq for Bounded<T, B> {}

impl<T: PartialOrd, B: Bound<Target = T>> PartialOrd for Bounded<T, B> {
    #[inline(always)]
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        self.assume_invariant();
        other.assume_invariant();
        self.0.partial_cmp(&other.0)
    }
}

impl<T: Ord, B: Bound<Target = T>> Ord for Bounded<T, B> {
    #[inline(always)]
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.assume_invariant();
        other.assume_invariant();
        self.0.cmp(&other.0)
    }
}

impl<T: Copy, B: Bound<Target = T>> Copy for Bounded<T, B> {}
impl<T: core::hash::Hash, B: Bound<Target = T>> core::hash::Hash for Bounded<T, B> {
    #[inline(always)]
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.assume_invariant();
        self.0.hash(state)
    }
}

impl<T: Index<U>, U, B: Bound<Target = T>> Index<U> for Bounded<T, B> {
    type Output = T::Output;

    #[inline(always)]
    fn index(&self, index: U) -> &Self::Output {
        self.assume_invariant();
        self.0.index(index)
    }
}

#[cfg(test)]
mod tests {
    #[derive(Debug)]
    struct IsPositive;
    impl Bound for IsPositive {
        type Target = i32;
        fn check(x: &i32) -> bool { *x >= 0 }
    }

    use super::*;
    #[test]
    fn constructing_with_passing_bounds_succeeds() { Bounded::<i32, IsPositive>::new(1).unwrap(); }

    #[test]
    fn constructing_with_failing_bounds_fails() {
        assert!(Bounded::<i32, IsPositive>::new(-5).is_err());
    }

    #[test]
    fn mutating_with_passing_bounds_succeeds() {
        let mut bounded = Bounded::<i32, IsPositive>::new(5i32).unwrap();
        bounded.mutate(|i| *i = 2 * *i);
    }

    #[test]
    #[should_panic]
    fn mutating_with_failing_bounds_panics() {
        let mut bounded = Bounded::<i32, IsPositive>::new(5i32).unwrap();
        bounded.mutate(|i| *i = -5);
    }
}
