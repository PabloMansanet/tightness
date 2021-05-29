#![forbid(unsafe_code)]
use std::{marker::PhantomData, ops::Deref};


#[derive(Debug)]
pub struct Error;

pub trait Bound {
    type Target;
    fn check(target: &Self::Target) -> bool;
}

pub trait ExpressiveBound {
    type Target;
    type Error;
    fn check(target: &Self::Target) -> Result<(), Self::Error> ;
}

#[derive(Debug)]
pub struct Bounded<T, B: Bound<Target=T>> {
    inner: T,
    _marker: PhantomData<B>
}

#[derive(Debug)]
pub struct ExpressiveBounded<T, B: ExpressiveBound<Target=T>> {
    inner: T,
    _marker: PhantomData<B>
}

impl<T, B: ExpressiveBound<Target=T>> ExpressiveBounded<T, B> {
    pub fn new(t: T) -> Result<Self, B::Error> {
        match B::check(&t) {
            Ok(_) => Ok(Self{ inner: t, _marker: Default::default() }),
            Err(e) => Err(e),
        }
    }

    /// Preserves invariants after mutation. Panics if invariants are not upheld
    pub fn mutate(&mut self, f: impl FnOnce(&mut T)) {
        f(&mut self.inner);
        assert!(B::check(&self.inner).is_ok());
    }

    /// If invariants aren't preserved after mutation, restores to a given value
    pub fn mutate_or(&mut self, f: impl FnOnce(&mut T), default: Self) -> Result<(), B::Error> {
        f(&mut self.inner);

        match B::check(&self.inner) {
            Ok(_) => Ok(()),
            Err(e) => {
                *self = default;
                Err(e)
            }
        }
    }
}

impl<T, B: Bound<Target=T>> Bounded<T, B> {
    pub fn new(t: T) -> Result<Self, Error> {
        if B::check(&t) { Ok(Self{ inner: t, _marker: Default::default() }) } else { Err(Error) }
    }

    /// Preserves invariants after mutation. Panics if invariants are not upheld
    pub fn mutate(&mut self, f: impl FnOnce(&mut T)) {
        f(&mut self.inner);
        assert!(B::check(&self.inner));
    }

    /// If invariants aren't preserved after mutation, restores to a given value
    pub fn mutate_or(&mut self, f: impl FnOnce(&mut T), default: Self) -> Result<(), Error> {
        f(&mut self.inner);
        if B::check(&self.inner) { Ok(()) } else { *self = default; Err(Error) }
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
            Err(Error)
        }
    }
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

    #[derive(Debug)]
    struct IsPositiveExpressive;
    impl ExpressiveBound for IsPositiveExpressive {
        type Target = i32;
        type Error = ();
        fn check(x: &i32) -> Result<(), Self::Error> {
            if *x >= 0 { Ok(()) } else { Err(())}
        }

    }

    use super::*;
    #[test]
    fn constructing_with_passing_bounds_succeeds() {
       Bounded::<i32, IsPositive>::new(1).unwrap();
       ExpressiveBounded::<i32, IsPositiveExpressive>::new(1).unwrap();
    }

    #[test]
    fn constructing_with_failing_bounds_fails() {
       assert!(Bounded::<i32, IsPositive>::new(-5).is_err());
       assert!(matches!(ExpressiveBounded::<i32, IsPositiveExpressive>::new(-1), Err(_)));
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
