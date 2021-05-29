#[forbid(unsafe_code)]
pub use paste::paste;
pub use crate::core::*;


mod core;
mod impls;

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
    }

    #[test]
    fn fallible_mutations_fail_on_invalid_final_values() {
        let mut month = Month::new(7).unwrap();
        let impossible_mutation = |m: &mut usize| *m = *m + 13;
        assert!(matches!(month.try_mutate(impossible_mutation), Err(Error::MutationFailed)));
        assert!(month.mutate_or(impossible_mutation, month.clone()).is_err());
    }

    #[test]
    fn convenient_operators_on_bounded_types() {
        let password = Password::new("Hello".to_owned()).unwrap();
        assert_eq!(password, "Hello");
    }
}
