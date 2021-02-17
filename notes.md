# Notes

Maybe propositional equality is enough to handle monads? Its true that the monad
may be a function or not a function, but propositional equality handles both
cases. The tricky part is that when I want to prove specific equalities between
monadic terms, I have to just do it in terms of the monad laws and can't depend
on them being functions or not anywhere. Which should be fine right?

TODO: Make a new branch where I encode propositional equality in roughly the
same way as Niki's paper. Then try to prove associativity of `>>` or something
simple like that.
