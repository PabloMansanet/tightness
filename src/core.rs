use std::{borrow::Borrow, marker::PhantomData, ops::Deref};

use thiserror::Error;

#[derive(Debug, Error)]
pub enum Error {
    #[error("Invariant broken on construction")]
    ConstructionFailed,
    #[error("Invariant broken on mutation")]
    MutationFailed
}

pub trait Bound {
    type Target;
    fn check(target: &Self::Target) -> bool;
}

#[derive(Debug)]
pub struct Bounded<T, B: Bound<Target=T>> {
    inner: T,
    _marker: PhantomData<B>
}

impl<T, B: Bound<Target=T>> Bounded<T, B> {
    pub fn new(t: T) -> Result<Self, Error> {
        if B::check(&t) { Ok(Self{ inner: t, _marker: Default::default() }) } else { Err(Error::ConstructionFailed) }
    }

    /// Preserves invariants after mutation. Panics if invariants are not upheld
    pub fn mutate(&mut self, f: impl FnOnce(&mut T)) {
        f(&mut self.inner);
        assert!(B::check(&self.inner));
    }

    /// If invariants aren't preserved after mutation, restores to a given value
    pub fn mutate_or(&mut self, f: impl FnOnce(&mut T), default: Self) -> Result<(), Error> {
        f(&mut self.inner);
        if B::check(&self.inner) { Ok(()) } else {
            *self = default;
            Err(Error::MutationFailed)
        }
    }

    /// Invariant must be upheld manually!
    pub unsafe fn new_unchecked(t: T) -> Self {
        Self { inner: t, _marker: Default::default() }
    }

    /// Invariant must be upheld manually!
    pub unsafe fn mutate_unchecked(&mut self, f: impl FnOnce(&mut T)){
        f(&mut self.inner)
    }
}

impl<T: Clone, B: Bound<Target=T>> Bounded<T, B> {
    /// Preserves invariants after mutation, erroring out if the mutation broke
    /// the invariants. Requires a copy to ensure the actual value is recoverable
    pub fn try_mutate(&mut self, f: impl FnOnce(&mut T)) -> Result<(), Error> {
        let mut duplicate = self.inner.clone();
        f(&mut duplicate);
        if B::check(&duplicate) {
            self.inner = duplicate;
            Ok(())
        } else {
            Err(Error::MutationFailed)
        }
    }
}

impl<T: Clone, B: Bound<Target=T>> Clone for Bounded<T, B> {
    fn clone(&self) -> Self {
        Self { inner: self.inner.clone(), _marker: Default::default()  }
    }
}

impl<T, B: Bound<Target=T>> Borrow<T> for Bounded<T, B> {
    fn borrow(&self) -> &T { &self.inner }
}

impl<T, B: Bound<Target=T>> Deref for Bounded<T, B> {
    type Target = T;
    fn deref(&self) -> &Self::Target { &self.inner }
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
    fn constructing_with_passing_bounds_succeeds() {
       Bounded::<i32, IsPositive>::new(1).unwrap();
    }

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
