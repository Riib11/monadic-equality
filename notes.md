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
  equality. `Concreteness a` is instantiated for each type a for which SMT
  equality can be used (roughly parallel to Niki’s `SMTEq` class).
- `Retractable` provides the ability to use an extensional equality of f and g
  to derive `f x = g x` for a given `x`. This should directly follow from the
  definition of extensionality (the `Extensionality` constructor of
  EqualityProp, but because we can’t usefully pattern-match on instances of
  `EqualityProp`, this has to be posed as a separate property. It should be
  possible to instantiate `forall a b. Retractability a b`, (via a use of the
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
  `concretization :: Concreteness a => x:a -> y:a -> EqualProp a {x} {y} -> {x = y}`
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

## February 24

- response to Nikki
- explanation of why abandoned abstract refinements
- retractable instance (use implcit instance )
- why not type-indexed equality default in LH?
  - as a proof of concept, just turn everything into propositional equalities,
    and convert to SMT equality when there is Concreteness instance
  - does type-indexed equality require handing off type unificiation (including
    for refinement types) to the SMT solver? because that would be very
    difficult/impossible.
  - Niki does not think that allowing type-indexed equality in native LH would
    work -- why exactly?
- going forward: examples in paper and monadic quicksort
- going forward: is my work a good improvmeent over the supp impl? can this
  replace some things, or not?
  - how to make use of my work -- perhaps present it on its own? or have the
    monadic quicksort proof stuff on top to show it working?

### March 3

- [new problem with constraining quantified types in record fields](https://liquidhaskell.slack.com/archives/C54QAL9RR/p1614785461049900)
- this is needed in order to write a refined `Monad` class looking something
  like

```haskell
{-@
data Monad m = Monad
  { unit :: forall a. a -> m a,
    bind :: forall a b. m a -> (a -> m b) -> m b,
    identityLeft ::
      forall a b.
      (y:b -> EqualProp b {y} {y}) ->
      x:a ->
      k:(a -> m b) ->
      EqualProp (m b) {bind (unit x) k} {k x},
    identityRight ::
      forall a.
      (x:a -> EqualProp a {x} {x}) ->
      m:m a ->
      EqualProp (m a) {bind m unit} {m},
    associativity ::
      forall a b c.
      (x:c -> EqualProp c {x} {x}) ->
      (x:c -> y:c -> z:c -> EqualProp c {x} {y} -> EqualProp c {y} {z} -> EqualProp c {x} {z}) ->
      m:m a ->
      k1:(a -> m b) ->
      k2:(b -> m c) ->
      EqualProp (m c) {bind (bind m k1) k2} {bind m (\x:a -> bind (k1 x) k2)}
  }
@-}
data Monad m = Monad
  { unit :: forall a. a -> m a,
    bind :: forall a b. m a -> (a -> m b) -> m b,
    identityLeft ::
      forall a b.
      Equality b ->
      (b -> EqualityProp b) ->
      a ->
      (a -> m b) ->
      EqualityProp (m b),
    identityRight ::
      forall a.
      Equality a ->
      (a -> EqualityProp a) ->
      m a ->
      EqualityProp (m a),
    associativity ::
      forall a b c.
      (Equality c, Equality c) ->
      (c -> EqualityProp c) ->
      (c -> c -> c -> EqualityProp c -> EqualityProp c -> EqualityProp c) ->
      m a ->
      (a -> m b) ->
      (b -> m c) ->
      EqualityProp (m c)
  }
```

- I need to quality `Equal x`, which provides `Reflexivity x`, etc because class
  induction doesnt give me a `forall x. Reflexivity x` instance. It needs to use
  the induction as a constraint.
- for some reason, the above code gives a liquid error, the simplest example in
  the link above. it should work in normal haskell, so idk why its causing an
  issue in LH
- one way to overcome this would be to actually somehow get a
  `forall x. Reflexivity x` like instanec. this would be very clean, but how?

- added `EqSMT` as a proxy for SMT equality when assuming derivation for
  `EqSMT a => Concreteness a`. I need to assume because i cant pattern match on
  `EqualProp`. previously i was relying on just `Eq`, but that is actually an
  extra assumption i shouldnt make because `Eq` instances may not be in line
  with SMT equality. `EqSMT` ensures this by providing a function that must
  correspond to SMT equality
  `eqSMT :: x:a -> y:a -> {b:Bool | ((x = y) => b) && (b => (x = y))}`

### March 11

I implemented `Relation.Equality.Prop.Reasoning` to provide some nice syntax for
comfortably writing chains of `EqualityProp`s. But I've run into some funny
refinement issues.

The impl looks like this:

```haskell
module Relation.Equality.Prop.Reasoning where

import Function
import Language.Haskell.Liquid.ProofCombinators
import Relation.Equality.Prop

infixl 4 ?~

infixl 3 =~

infixl 3 ~=~

infixl 3 ~**

(?~) :: Equality a => a -> EqualityProp a -> (a, EqualityProp a)
y ?~ exy = (y, exy)
{-# INLINE (?~) #-}

{-@
(=~) ::
  Equality a =>
  x:a ->
  {y_exy:(a, EqualityProp a) | eqprop x (fst y_exy)} ->
  {x_y_kxz:((a, a), z:a -> {_:EqualityProp a | eqprop (fst y_exy) z} -> {_:EqualityProp a | eqprop x z}) | fst (fst x_y_kxz) = x && snd (fst x_y_kxz) = fst y_exy}
@-}
(=~) ::
  Equality a =>
  a ->
  (a, EqualityProp a) ->
  ((a, a), a -> EqualityProp a -> EqualityProp a)
x =~ (y, exy) = ((x, y), \z eyz -> transitivity x y z exy eyz)

{-@
(~=~) ::
  Equality a =>
  x_y_kxz:(x_y::(a, a), z:a -> {_:EqualityProp a | eqprop (snd x_y) z} -> {_:EqualityProp a | eqprop (fst x_y) z}) ->
  {z_eyz:(a, EqualityProp a) | eqprop (snd (fst x_y_kxz)) (fst z_eyz)} ->
  {x_z_kxw:((a, a), w:a -> {_:EqualityProp a | eqprop (fst z_eyz) w} -> {_:EqualityProp a | eqprop (fst (fst x_y_kxz)) w}) | fst (fst x_z_kxw) = fst (fst x_y_kxz) && snd (fst x_z_kxw) = fst z_eyz}
@-}
(~=~) ::
  Equality a =>
  ((a, a), a -> EqualityProp a -> EqualityProp a) ->
  (a, EqualityProp a) ->
  ((a, a), a -> EqualityProp a -> EqualityProp a)
((x, y), kxz) ~=~ (z, eyz) = ((x, z), \w ezw -> transitivity x z w (kxz z eyz) ezw)

{-@ assume
(~**) ::
  Equality a =>
  x_y_kxz:(x_y::(a, a), z:a -> {_:EqualityProp a | eqprop (snd x_y) z} -> {_:EqualityProp a | eqprop (fst x_y) z}) ->
  qed:QED ->
  {_:EqualityProp a | if (isAdmit qed) then false else eqprop (fst (fst x_y_kxz)) (snd (fst x_y_kxz))}
@-}
(~**) ::
  Equality a =>
  ((a, a), a -> EqualityProp a -> EqualityProp a) ->
  QED ->
  EqualityProp a
((x, y), kxz) ~** _ = kxz y (reflexivity y)
```

Then I try some examples.

First, `ex` is SAFE, although needlessly verbose.

```haskell
{-@
ex1 :: Equality a => x:a -> EqualProp a {x} {x}
@-}
ex1 :: Equality a => a -> EqualityProp a
ex1 x =
  let ((x1, x2), kx1x3) = x =~ (x, reflexivity x)
      ((x1', x3), kx1x4) = ((x1, x2), kx1x3) ~=~ (x, reflexivity x)
   in ((x1', x3), kx1x4) ~** QED
```

Second, `ex2` is UNSAFE- but it should typecheck right?! It is exactly the same
as `ex1`, but inlined rather than explicitly naming each of the intermediate
results.

It produces the following error:

```
The inferred type

  VV : (Relation.Equality.Prop.EqualityProp a)

is not a subtype of the required type

  VV : {VV : (Relation.Equality.Prop.EqualityProp a) | eqprop (fst ?a) z}
```

```haskell
-}
{-@
ex2 :: Equality a => x:a -> EqualProp a {x} {x}
@-}
ex2 :: Equality a => a -> EqualityProp a
ex2 x =
  x
    =~ (x, reflexivity x)
    ~=~ (x, reflexivity x)
    ~** QED
```

Third, `ex3` is UNSAFE as well... with its only difference from the SAFE `ex1`
being the use of `?~` rather that tuple syntax. Since `?~` is inlined (at the
Haskell level) I expected that there wouldn't be refinement problems rising from
the fact that `?~` doesn't deal with refinement info (and it couldn't lifted to
the refinement level, since its second argument `exy` mentions a refinement-
level variable that is not in `~?`'s scope. This sort of pattern works with the
liquid-prelude's `?` though... so I was trying to mimic that.)

It produces the following error:

```
The inferred type
  VV : {v : (a, (Relation.Equality.Prop.EqualityProp a)) | v == ?~ x (reflexivity x)}

is not a subtype of the required type
  VV : {VV : (a, (Relation.Equality.Prop.EqualityProp a)) | eqprop x (fst VV)}

in the context
  x : a
    |
129 |   let ((x1, x2), kx1x3) = x =~ x ?~ reflexivity x
    |                                ^^^^^^^^^^^^^^^^^^
```

```haskell
{-@
ex3 :: Equality a => x:a -> EqualProp a {x} {x}
@-}
ex3 :: Equality a => a -> EqualityProp a
ex3 x =
  let ((x1, x2), kx1x3) = x =~ x ?~ reflexivity x
      ((x1', x3), kx1x4) = ((x1, x2), kx1x3) ~=~ x ?~ reflexivity x
   in ((x1', x3), kx1x4) ~** QED
```
