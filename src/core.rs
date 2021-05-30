use std::{borrow::Borrow, convert::TryFrom, marker::PhantomData, ops::{Deref, Index, RangeBounds}};

use thiserror::Error;

#[derive(Debug, Error)]
pub enum Error {
    #[error("Invariant broken on construction")]
    ConstructionFailed,
    #[error("Invariant broken on mutation")]
    MutationFailed,
    #[error("Invariant broken at an unspecified point")]
    BrokenInvariant,
}

pub trait Bound {
    type Target;
    fn check(target: &Self::Target) -> bool;
}

#[derive(Debug)]
pub struct Bounded<T, B: Bound<Target = T>>(T, PhantomData<B>);

impl<T, B: Bound<Target = T>> Bounded<T, B> {
    pub fn new(t: T) -> Result<Self, Error> {
        if B::check(&t) {
            Ok(Self(t, Default::default()))
        } else {
            Err(Error::ConstructionFailed)
        }
    }

    /// Preserves invariants after mutation. Panics if invariants are not upheld
    pub fn mutate(&mut self, f: impl FnOnce(&mut T)) {
        f(&mut self.0);
        assert!(B::check(&self.0));
    }

    /// If invariants aren't preserved after mutation, restores to a given value
    pub fn mutate_or(&mut self, f: impl FnOnce(&mut T), default: Self) -> Result<(), Error> {
        f(&mut self.0);
        if B::check(&self.0) {
            Ok(())
        } else {
            *self = default;
            Err(Error::MutationFailed)
        }
    }

    /// Inner value is dropped if mutation fails
    pub fn into_mutated(mut self, f: impl FnOnce(&mut T)) -> Result<Self, Error> {
        f(&mut self.0);
        if B::check(&self.0) {
            Ok(self)
        } else {
            Err(Error::MutationFailed)
        }
    }

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
    /// one of the `unsafe` methods that require variants to be manually upheld
    #[cfg(feature = "unsafe_access")]
    pub fn verify(&self) -> Result<(), Error> {
        if B::check(&self.0) {
            Ok(())
        } else {
            Err(Error::BrokenInvariant)
        }
    }
}

impl<T: Clone, B: Bound<Target = T>> Bounded<T, B> {
    /// Preserves invariants after mutation, erroring out if the mutation broke
    /// the invariants. Requires a copy to ensure the actual value is recoverable
    pub fn try_mutate(&mut self, f: impl FnOnce(&mut T)) -> Result<(), Error> {
        let mut duplicate = self.0.clone();
        f(&mut duplicate);
        if B::check(&duplicate) {
            self.0 = duplicate;
            Ok(())
        } else {
            Err(Error::MutationFailed)
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

    #[test]
    #[should_panic]
    fn expressive_mutating_with_failing_bounds_panics() {
        let mut bounded = Bounded::<i32, IsPositive>::new(5i32).unwrap();
        bounded.mutate(|i| *i = -5);
    }
}
