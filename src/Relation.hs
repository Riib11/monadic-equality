module Relation where

import ProofCombinators

{-
# Relation

A relation is encoded by
  - a witness GADT `r :: * -> *`
  - a relation measure `re :: a -> a -> r a -> Bool`
  - a domain type `a :: *`

A witness that `x :: a` and `y :: a` are related has the form
```
  w:(r a) <re x y>
```
encoding that `w :: r a` is a witness refined by `re x y`.
-}

-- => x ~ x
{-@
data IsReflexive r a <re :: a -> a -> r a -> Bool> =
  IsReflexive
    { reflexivity ::
        x:a ->
        (r a) <re x x>
    }
@-}
data IsReflexive r a = IsReflexive (a -> r a)

reflexivity :: IsReflexive r a -> (a -> r a)
reflexivity (IsReflexive reflexivity_) = reflexivity_

-- x ~ y  =>  y ~ x
{-@
data IsSymmetric r a <re :: a -> a -> r a -> Bool> =
  IsSymmetric
    { symmetry ::
        x:a -> y:a ->
        (r a) <re x y> ->
        (r a) <re y x>
    }
@-}
data IsSymmetric r a = IsSymmetric (a -> a -> r a -> r a)

symmetry :: IsSymmetric r a -> (a -> a -> r a -> r a)
symmetry (IsSymmetric symmetry_) = symmetry_

-- x ~ y, y ~ z  =>  x ~ z
{-@
data IsTransitive r a <re :: a -> a -> r a -> Bool> =
  IsTransitive
    { transitivity ::
        x:a -> y:a -> z:a ->
        (r a) <re x y> ->
        (r a) <re y z> ->
        (r a) <re x z>
    }
@-}
data IsTransitive r a = IsTransitive (a -> a -> a -> r a -> r a -> r a)

transitivity :: IsTransitive r a -> (a -> a -> a -> r a -> r a -> r a)
transitivity (IsTransitive transitivity_) = transitivity_

-- x ~ y  =>  f x ~ f y
{-@
data IsSubstitutive r a b <re :: forall c. c -> c -> r c -> Bool> =
  IsSubstitutive
    { substitution ::
        x:a -> y:a -> c:(a -> b) ->
        (r a) <re x y> ->
        (r b) <re (c x) (c y)>
    }
@-}
data IsSubstitutive r a b = IsSubstitutive (a -> a -> (a -> b) -> r a -> r b)

substitution :: IsSubstitutive r a b -> a -> a -> (a -> b) -> r a -> r b
substitution (IsSubstitutive substitution_) = substitution_
