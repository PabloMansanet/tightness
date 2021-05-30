use std::{borrow::Borrow, fmt::Debug, marker::PhantomData, ops::{Deref, Index}};

use thiserror::Error;

#[derive(Error)]
#[error("Value supplied did not satisfy the type invariant")]
/// The result of a failed invariant check on construction. Contains the value
/// that failed to uphold the invariant.
pub struct ConstructionError<T> (pub T);
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
/// to upheld at all times.
pub trait Bound {
    type Target;
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
    pub fn mutate_or(&mut self, default: Self, f: impl FnOnce(&mut T)) -> Result<(), MutationError<T>> {
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
        f(&mut self.0);
        if B::check(&self.0) {
            Ok(self)
        } else {
            Err(MutationError(Some(self.0)))
        }
    }

    /// Access the inner value through an immutable reference.
    pub fn get(&self) -> &T { &self.0 }

    /// Retrieve the inner, unprotected value.
    pub fn into_inner(self) -> T { self.0 }

    /// Invariant must be upheld manually!
    #[cfg(feature = "unsafe_access")]
    pub unsafe fn new_unchecked(t: T) -> Self { Self(t, Default::default()) }

    /// Invariant must be upheld manually!
    #[cfg(feature = "unsafe_access")]
    pub unsafe fn mutate_unchecked(&mut self, f: impl FnOnce(&mut T)) { f(&mut self.0) }

    /// Gives mutable access to the internals without upholding invariants.
    /// They must continue to be upheld manually while the reference lives!
    #[cfg(feature = "unsafe_access")]
    pub unsafe fn get_mut(&mut self) -> &mut T { &mut self.0 }

    /// Verifies invariants. This is guaranteed to succeed unless you've used
    /// one of the `unsafe` methods that require variants to be manually upheld.
    #[cfg(feature = "unsafe_access")]
    pub fn verify(&self) -> Result<(), BrokenInvariantError> {
        if B::check(&self.0) {
            Ok(())
        } else {
            Err(BrokenInvariantError)
        }
    }
}

impl<T: Clone, B: Bound<Target = T>> Bounded<T, B> {
    /// Preserves invariants after mutation, erroring out if the attempt to mutate was
    /// invalid. Requires a copy to ensure the value is recoverable.
    pub fn try_mutate(&mut self, f: impl FnOnce(&mut T)) -> Result<(), MutationError<T>> {
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
    fn clone(&self) -> Self { Self(self.0.clone(), Default::default()) }
}

impl<T, B: Bound<Target = T>> Borrow<T> for Bounded<T, B> {
    fn borrow(&self) -> &T { &self.0 }
}

impl<T, B: Bound<Target = T>> AsRef<T> for Bounded<T, B> {
    fn as_ref(&self) -> &T { &self.0 }
}

impl<T, B: Bound<Target = T>> Deref for Bounded<T, B> {
    type Target = T;
    fn deref(&self) -> &Self::Target { &self.0 }
}

impl<T: PartialEq, B: Bound<Target = T>> PartialEq for Bounded<T, B> {
    fn eq(&self, other: &Self) -> bool { self.0.eq(&other.0) }
}

impl<T: Eq, B: Bound<Target = T>> Eq for Bounded<T, B> {}

impl<T: PartialOrd, B: Bound<Target = T>> PartialOrd for Bounded<T, B> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        self.0.partial_cmp(&other.0)
    }
}

impl<T: Ord, B: Bound<Target = T>> Ord for Bounded<T, B> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.0.cmp(&other.0)
    }
}

impl<T: Copy, B: Bound<Target = T>> Copy for Bounded<T, B> {}
impl<T: core::hash::Hash, B: Bound<Target = T>> core::hash::Hash for Bounded<T, B> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.0.hash(state)
    }
}

impl<T: Index<U>, U, B: Bound<Target = T>> Index<U> for Bounded<T, B> {
    type Output = T::Output;

    fn index(&self, index: U) -> &Self::Output { self.0.index(index) }
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
