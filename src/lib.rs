#[forbid(unsafe_code)]
pub use paste::paste;
pub use crate::core::*;

mod core;

#[macro_export]
macro_rules! bound {
    ($name:ident: $type:ty where $check:expr) => { $crate::paste! {
        #[derive(Debug)]
        pub struct [<$name Bound>];

        impl $crate::Bound for [<$name Bound>] {
            type Target = $type;
            fn check(target: &Self::Target) -> bool {
                let check: fn(&Self::Target) -> bool = $check;
                check(target)
            }
        }

        pub type $name = Bounded<$type, [<$name Bound>]>;
    }}
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
        assert!(matches!(month.try_mutate(impossible_mutation), Err(Error::MutationFailed)));
        assert!(matches!(month.mutate_or(impossible_mutation, month.clone()), Err(Error::MutationFailed)));
        assert!(matches!(month.into_mutated(impossible_mutation), Err(Error::MutationFailed)));

        let mut xor_pair = XorPair::new((true, false)).unwrap();
        assert!(matches!(xor_pair.try_mutate(|(a, b)| *a = *b), Err(Error::MutationFailed)));
    }

    #[test]
    fn fallible_mutations_succeed_on_valid_final_values() {
        let mut month = Month::new(7).unwrap();
        month.try_mutate(|m| *m += 1).unwrap();
        assert_eq!(*month, 8);
        month.mutate_or(|m| *m += 1, month.clone()).unwrap();
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
