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

In summary, Im admitting that the generalization of properties using abstract
predicates was:

- unwieldy
- seems to end up requiring much more in the way of assumptions and auxiliary
  functions that the original source code (from Niki’s paper’s supplementary),
  which is what I was trying to avoid in the first place
- is an abstraction that isnt very useful because, beyond SMT and propositional
  equality, there arent really any other interesting equalities (not just
  equivalences relations) to instantiate

Given these findings, and my experience so far, I was able to fairly easily
condense the necessary into a simple framework, which fits nicely into basically
just one file, `Relation.Equality.Prop`.

I’ve broken the properties I need into the following classes:

- `Concrete` provides “concretization” of a propositional equality into an SMT
  equality. `Concrete a` is instantiated for each type a for which SMT equality
  can be used (roughly parallel to Niki’s `SMTEq` class).
- `Retractable` provides the ability to use an extensional equality of f and g
  to derive `f x = g x` for a given `x`. This should directly follow from the
  definition of extensionality (the `Extensionality` constructor of
  EqualityProp, but because we can’t usefully pattern-match on instances of
  `EqualityProp`, this has to be posed as a separate property. It should be
  possible to instantiate `forall a b. Retractable a b`, (via a use of the
  `Substitutability` constructor of `EqualityProp` but I’m having a problem
  getting it to type-check. so, its a work-in-progress). Perhaps this should be
  posed simply as a function rather than a class, since its instantiated for all
  types. But for the first pass I just defined it in the same form as the other
  properties.

- `Reflexive` provides `reflexivity` and is instantiated for all types using
  classy induction.
- `Symmetric` provides `symmetry` and is instantiated for all types using classy
  induction.
- `Transitive` provides `transitivity` and is instantiated for all types using
  classy induction.

- `Substitutable` provides `substitutability` and is derived directly from the
  `Substitutability` constructor of `EqualityProp`. In Niki's supplementary
  source, it looks like this property (called `Congruence`) is derived in a more
  complicated way. But does it not just follow from the `EqCtx` constructor?

The result is a somewhat simpler implementation of the supplementary source from
Niki’s paper, so it’s something. (But I still need to do some testing with it to
see, for example, how straightforward it is to prove the kinds of things done as
an example in the paper.) The main departures I made are:

- rather than having `ToSMT` rather than having `SMTEq` and `AEq`, I just have
  `Concrete`. It seems like the reason for `AEq` was to expose a concrete
  equality operator to proxy for the uninterpreted equality (they are typed to
  correspond via `<=>`) as well as the equivalence properties. However, I don’t
  see where I would actually need this if I can just convert to SMT equality via
  my
  `concretization :: Concrete a => x:a -> y:a -> EqualProp a {x} {y} -> {x = y}`
  and the equivalence properties are trivially SMT solvable from there.
- `AEq` is also used to correspond to the `Eq` class from Haskell, but this fact
  isnt actually used anywhere in your source. I think that this is because its
  just easier to use the fact that SMT equality already corresponds to Haskell’s
  `Eq`, and you only ever need this when you can convert your equality to SMT
  equality (via my concretization or your `toSMT`) anyway.
- The paper doesn’t seem to directly address how congruence interacts at the SMT
  level. Since preserving congruencies isnt a property of `AEq`, however it is a
  property of SMT equality. Propositional equality does take account of
  congruency-preservation with the `EqCtx` constructor. You could just assume
  that the instances of `AEq` are properly congruence-preserving, in the same
  way that Haskell assumes that Eq instances are proper equalities, but my
  approach with just relying on `Concrete` is simpler and I dont think it relies
  on assumptions of the user other than the one’s already baked into `Eq`.
