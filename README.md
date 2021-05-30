# Tightness

This library provides a convenient way to define types bound by arbitrary
conditions.

``` rust
bound!(pub Letter: char where |c| c.is_alphabetic());
bound!(XorPair: (bool, bool) where |(a, b)| a ^ b);
bound!(Username: String where |s| s.len() < 8);
```

The above defines three types (`Letter`, `XorPair` and `Username`) that are
guaranteed to always fulfill the given conditions. This is enforced
by checking the conditions after construction and once after mutation.

Immutably, bounded types get out of the way and act as close as possible to the
underlying type, implementing all traits that a typical `Newtype` wrapper would.

Check out the [documentation](./) for more details!

# Caveat Emptor

This crate offers a one-size-fits-all solution. This means it's probably a
lot better to use specialized restricted types when possible (e.g. the standard
library's `NonZeroUSize` type). These types will be further specialized and
offer performance and size gains, implement more traits, and maximize the number
of decisions made at compile time.

If you're not particularly worried about the performance of checking the
invariant after every mutation, there's no alternative in the ecosystem for the
particular type restriction you want, or you just need something quick and
convenient to protect your types, `tightness` may be for you!
