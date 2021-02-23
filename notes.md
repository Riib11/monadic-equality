# Notes

## January 30

Maybe propositional equality is enough to handle monads? Its true that the monad
may be a function or not a function, but propositional equality handles both
cases. The tricky part is that when I want to prove specific equalities between
monadic terms, I have to just do it in terms of the monad laws and can't depend
on them being functions or not anywhere. Which should be fine right?

TODO: Make a new branch where I encode propositional equality in roughly the
same way as Niki's paper. Then try to prove associativity of `>>` or something
simple like that.

## February 23

So I've spend plenty of time trying to generalize the equality properties
(reflexivity, symmety, transitivity, substitutability). But this is very
difficult to do with abstract predicates (especially substitutability). So, I
have opted that there are not enough interesting equalities to justify this
generalization work.

Without this generalization of equality properties, the formalization becomes
much flatter. I just need one layer for small properties of SMT equality, and
then one more layer where I do everything related to propositional equality. In
particular, I don't need to name things wierdly like `<property>_EqualitySMT`
and `<property>_EqualityProp`, since Im only proving thoes interesting things
for propositional equality.

Some properties I'm not sure how to handle:

- retractability i.e. un-extensionality
-
