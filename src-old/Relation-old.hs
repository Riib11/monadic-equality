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
data IsReflexive r a <re :: a -> a -> r a -> Bool> = IsReflexive
@-}
data IsReflexive (r :: * -> *) a = IsReflexive

{-@
assume constructIsReflexive ::
  forall <re :: a -> a -> r a -> Bool>.
  (x:a -> (r a) <re x x>) ->
  IsReflexive <re> r a
@-}
constructIsReflexive :: (a -> r a) -> IsReflexive r a
constructIsReflexive _ = undefined

{-@
assume reflexivity ::
  forall <re :: a -> a -> r a -> Bool>.
  IsReflexive <re> r a ->
  (x:a -> (r a) <re x x>)
@-}
reflexivity :: IsReflexive r a -> (a -> r a)
reflexivity _ = undefined

-- x ~ y  =>  y ~ x
{-@
data IsSymmetric r a <re :: a -> a -> r a -> Bool> = IsSymmetric
@-}
data IsSymmetric (r :: * -> *) a = IsSymmetric

{-@
assume constructIsSymmetric ::
  forall <re :: a -> a -> r a -> Bool>.
  (x:a -> y:a -> (r a) <re x y> -> (r a) <re y x>) ->
  IsSymmetric <re> r a
@-}
constructIsSymmetric :: (a -> a -> r a -> r a) -> IsSymmetric r a
constructIsSymmetric _ = undefined

{-@
assume symmetry ::
  forall <re :: a -> a -> r a -> Bool>.
  IsSymmetric <re> r a ->
  (x:a -> y:a -> (r a) <re x y> -> (r a) <re y x>)
@-}
symmetry :: IsSymmetric r a -> (a -> a -> r a -> r a)
symmetry _ = undefined

-- x ~ y, y ~ z  =>  x ~ z
{-@
data IsTransitive r a <re :: a -> a -> r a -> Bool> = IsTransitive
@-}
data IsTransitive (r :: * -> *) a = IsTransitive

{-@
assume constructIsTransitive ::
  forall <re :: a -> a -> r a -> Bool>.
  (x:a -> y:a -> z:a -> (r a) <re x y> -> (r a) <re y z> -> (r a) <re x z>) ->
  IsTransitive <re> r a
@-}
constructIsTransitive :: (a -> a -> a -> r a -> r a -> r a) -> IsTransitive r a
constructIsTransitive _ = undefined

{-@
assume transitivity ::
  forall <re :: a -> a -> r a -> Bool>.
  IsTransitive <re> r a ->
  (x:a -> y:a -> z:a -> (r a) <re x y> -> (r a) <re y z> -> (r a) <re x z>)
@-}
transitivity :: IsTransitive r a -> (a -> a -> a -> r a -> r a -> r a)
transitivity _ = undefined

-- x ~ y  =>  f x ~ f y
{-@
data IsSubstitutive
  r1 r2 a1 a2 <re1 :: a1 -> a1 -> r1 a1 -> Bool, re2 :: a2 -> a2 -> r2 a2 -> Bool> = IsSubstitutive
@-}
data IsSubstitutive (r1 :: * -> *) (r2 :: * -> *) a1 a2 = IsSubstitutive

{-@
assume constructIsSubstitutive ::
  forall r1 r2 a1 a2 <re1 :: a1 -> a1 -> r1 a1 -> Bool, re2 :: a2 -> a2 -> r2 a2 -> Bool>.
  (x:a1 -> y:a1 -> c:(a1 -> a2) -> (r1 a1) <r1 x y> -> (r2 a2) <re2 (c x) (c y)>) ->
  IsSubstitutive <re1, re2> r1 r2 a1 a2
@-}
constructIsSubstitutive ::
  forall r1 r2 a1 a2.
  (a1 -> a1 -> (a1 -> a2) -> r1 a1 -> r2 a2) ->
  IsSubstitutive r1 r2 a1 a2
constructIsSubstitutive _ = undefined

{-@
assume substitution ::
  forall r1 r2 a1 a2 <re1 :: a1 -> a1 -> r1 a1 -> Bool, re2 :: a2 -> a2 -> r2 a2 -> Bool>.
  IsSubstitutive <re1, re2> r1 r2 a1 a2 ->
  (x:a1 -> y:a1 -> c:(a1 -> a2) -> (r1 a1) <r1 x y> -> (r2 a2) <re2 (c x) (c y)>)
@-}
substitution ::
  forall r1 r2 a1 a2.
  IsSubstitutive r1 r2 a1 a2 ->
  (a1 -> a1 -> (a1 -> a2) -> r1 a1 -> r2 a2)
substitution _ = undefined
