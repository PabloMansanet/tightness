//! This crate provides a way to define type wrappers that behave
//! as close as possible to the underlying type, but guarantee to
//! uphold arbitrary invariants at all times.
//!
//! # Example
//! ```
//! use tightness::{bound, Bounded};
//! bound!(Username: String where |s| s.len() < 8);
//! ```
//!
//! The [`bound`](bound) macro invocation above defines a `Username` type (actually,
//! a type alias of [`Bounded<String, UsernameBound>`](Bounded)) that is
//! a thin wrapper around String, with the added promise that it will
//! always have less than eight characters.
//!
//! Immutable access behaves as close as possible to the underlying type,
//! with all traits you'd expect from a newtype wrapper already implemented:
//!
//! ```
//! # use tightness::{bound, Bounded};
//! # bound!(Username: String where |s| s.len() < 8);
//! # let username = Username::new("Admin".to_string()).unwrap();
//! assert!(username.chars().all(char::is_alphanumeric));
//! let solid_credentials = format!("{}:{}", *username, "Password");
//! ```
//!
//! However, construction and mutable access must be done through a fixed set of forms that
//! ensure the invariants are *always* upheld:
//!
//! ```
//! use tightness::{self, bound, Bounded};
//! bound!(Username: String where |s| s.len() < 8);
//!
//! // The only constructor is fallible, and the input value must satisfy
//! // the bound conditions for it to succeed.
//! assert!(matches!(Username::new("Far_too_long".to_string()),
//!    Err(tightness::ConstructionError(_))));
//! let mut username = Username::new("Short".to_string()).unwrap();
//!
//! // In-place mutation panics if the invariant is broken:
//! // Would panic: `username.mutate(|u| u.push_str("Far_too_long"))`
//! username.mutate(|u| *u = u.to_uppercase());
//! assert_eq!(*username, "SHORT");
//!
//! // If the underlying type implements `clone`, you can try non-destructive,
//! // fallible mutation at the cost of one copy:
//! assert!(matches!(username.try_mutate(|u| u.push_str("Far_too_long")),
//!    Err(tightness::MutationError(None))));
//! assert_eq!(*username, "SHORT");
//!
//! // You can also attempt mutation by providing a fallback value
//! let fallback = username.clone();
//! assert!(matches!(username.mutate_or(fallback, |u| u.push_str("Far_too_long")),
//!    Err(tightness::MutationError(None))));
//! assert_eq!(*username, "SHORT");
//!
//! // Finally, you can just pass by value, and the inner will be recoverable if mutation fails
//! assert!(matches!(username.into_mutated(|u| u.push_str("Far_too_long")),
//!     Err(tightness::MutationError(Some(_)))));
//! ```
//!
//! # Performance
//!
//! Since invariants are arbitrarily complex, it's not possible to guarantee they're evaluated at
//! compile time. Using a [`Bounded`](Bounded) type incurs the cost of invoking the invariant
//! function on construction and after every mutation. However, the function is known at compile
//! time, so it's possible for the compiler to elide it in the trivial cases.
//!
//! Complex mutations consisting of multiple operations can be batched in a single closure, so that
//! the invariant is enforced only once at the end. Be careful however: while the closure is
//! executing, the value is considered to be mid-mutation and the invariant may not hold. Don't use
//! the inner value to trigger any side effects that depend on it being correct.
//!
//! Enabling the feature flag `unsafe_access` expands [`Bounded`](Bounded) types with a set of
//! methods that allow unsafe construction and mutation, requiring you to uphold the invariants
//! manually. It also offers a `verify` method that allows you to check the invariants at any time.
//! This can help in the cases where maximum performance is needed, but it must be used with
//! caution.
//!
//! # Without Macros
//!
//! The [`bound`](bound) macro simplifies defining bound types, but it's also possible to define
//! them directly. The following is equivalent to `bound!(pub NonZero: usize where |u| u > 0)`;
//!
//! ```
//! #[derive(Debug)]
//! pub struct NonZeroBound;
//!
//! impl tightness::Bound for NonZeroBound {
//!     type Target = usize;
//!     fn check(target: &usize) -> bool { *target > 0 }
//! }
//!
//! pub type NonZero = tightness::Bounded<usize, NonZeroBound>;
//! ```
//!
//! The bound is associated to the type, and will then be called on construction and after mutation
//! of any value of type `NonZero`.

#![cfg_attr(not(feature = "unsafe_access"), forbid(unsafe_code))]
pub use crate::core::*;
mod core;

/// Convenience macro that defines a bounded type, which is guaranteed to always uphold an
/// invariant expressed as a boolean function. The resulting type is an alias of [`Bounded<BaseType,
/// TypeNameBound>`](Bounded).
///
/// # Examples
/// ```
/// use tightness::{bound, Bounded};
///
/// // Defines a public `Letter` type that wraps `char`, ensuring it's always alphabetic.
/// bound!(pub Letter: char where |c| c.is_alphabetic());
///
/// // Defines a private `XorPair` type that wraps a pair of bools, so that they're never both true
/// // or false.
/// bound!(XorPair: (bool, bool) where |(a, b)| a ^ b);
/// ```
#[macro_export]
macro_rules! bound {
    ($visib:vis $name:ident: $type:ty where $check:expr) => {
        paste::paste! {
            #[derive(Debug)]
            $visib struct [<$name Bound>];

            impl $crate::Bound for [<$name Bound>] {
                type Target = $type;
                fn check(target: &Self::Target) -> bool {
                    let check: fn(&Self::Target) -> bool = $check;
                    check(target)
                }
            }

            $visib type $name = Bounded<$type, [<$name Bound>]>;
        }
    };
}

#[cfg(test)]
mod tests {
    use super::*;
    bound!(Password: String where |p| p.len() < 8 && p.chars().all(char::is_alphanumeric));
    bound!(Month: usize where |m| *m < 12usize);
    bound!(XorPair: (bool, bool) where |(a, b)| a ^ b);

    impl std::ops::Add<usize> for Month {
        type Output = Self;

        fn add(mut self, rhs: usize) -> Self::Output {
            self.mutate(|m| *m = (*m + rhs) & 12usize);
            self
        }
    }

    #[test]
    #[should_panic]
    fn invalid_bound_string_operation_panics() {
        let mut password = Password::new("Hello".to_owned()).unwrap();
        password.mutate(|p| p.push_str("World"));
    }

    #[test]
    fn fallible_constructions_fail_on_invalid_input() {
        assert!(Month::new(22).is_err());
        assert!(Password::new("---".to_owned()).is_err());
        assert!(XorPair::new((true, true)).is_err());
    }

    #[test]
    fn fallible_mutations_fail_on_invalid_final_values() {
        let mut month = Month::new(7).unwrap();
        let impossible_mutation = |m: &mut usize| *m = *m + 13;
        assert!(matches!(month.try_mutate(impossible_mutation), Err(MutationError(None))));
        assert!(matches!(
            month.mutate_or(month.clone(), impossible_mutation),
            Err(MutationError(None))
        ));
        assert!(matches!(month.into_mutated(impossible_mutation), Err(MutationError(Some(20)))));

        let mut xor_pair = XorPair::new((true, false)).unwrap();
        assert!(matches!(xor_pair.try_mutate(|(a, b)| *a = *b), Err(MutationError(None))));
    }

    #[test]
    fn fallible_mutations_succeed_on_valid_final_values() {
        let mut month = Month::new(7).unwrap();
        month.try_mutate(|m| *m += 1).unwrap();
        assert_eq!(*month, 8);
        month.mutate_or(month.clone(), |m| *m += 1).unwrap();
        assert_eq!(*month, 9);
        let month = month.into_mutated(|m| *m += 1).unwrap();
        assert_eq!(*month, 10);
    }

    #[test]
    fn convenient_operators_on_bounded_types() {
        fn takes_as_ref<T: AsRef<usize>>(_: &T) {}
        let month = Month::new(1).unwrap();
        takes_as_ref(&month);
        assert_eq!(month, month.clone());

        bound!(FixedVec: Vec<bool> where |v| v.len() == 4);
        let fixed = FixedVec::new(vec![false, true, false, false]).unwrap();
        assert_eq!(fixed[1], true);
    }
}
