use proc_macro::TokenStream;
use quote::quote;
use syn::{parse_macro_input, ItemTrait};

#[proc_macro]
pub fn bound(_input: TokenStream) -> TokenStream {
    todo!()
}

#[cfg(test)]
mod tests {
    #[test]
    fn it_works() {
        assert_eq!(2 + 2, 4);
    }
}
