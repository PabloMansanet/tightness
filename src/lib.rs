use std::{convert::{TryFrom, TryInto}, marker::PhantomData, ops::Deref};

trait Bound {
    type Target;
    fn check(target: &Self::Target) -> bool;
}

#[derive(Debug)]
struct Bounded<T, B: Bound<Target=T>> {
    inner: T,
    _marker: PhantomData<B>
}

#[derive(Debug, Copy, Clone)]
struct Error;

impl<T, B: Bound<Target=T>> Bounded<T, B> {
    pub fn new(t: T) -> Result<Self, Error> {
        if B::check(&t) { Ok(Self{ inner: t, _marker: Default::default() }) } else { Err(Error) }
    }

    /// Preserves invariants after mutation. Panics if invariants are not upheld
    pub fn mutate(&mut self, f: impl FnOnce(&mut T)) {
        f(&mut self.inner);
        assert!(B::check(&self.inner));
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

struct IsPositive;
impl Bound for IsPositive {
    type Target = i32;
    fn check(x: &i32) -> bool { *x >= 0 }
}


#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn it_works() {
        let my_int = Bounded::<i32, IsPositive>::new(5i32).unwrap();
    }
}
