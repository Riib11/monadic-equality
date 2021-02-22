module Relation.Equality.Prop where

import ProofCombinators
import Relation.Equality.SMT

{-
# Propositional Equality
-}

{-@
measure eqprop :: a -> a -> EqualityProp a -> Bool
@-}

{-@
type EqualProp a X Y = {w:EqualityProp a | eqprop X Y w}
@-}

{-@
data EqualityProp :: * -> * where
    FromSMT :: x:a -> y:a -> EqualSMT a {x} {y} -> EqualProp a {x} {y}
  | Extensionality :: f:(a -> b) -> g:(a -> b) -> (x:a -> EqualProp a {f x} {g x}) -> EqualProp (a -> b) {f} {g}
  | SubstitutitivityProp :: x:a -> y:a -> c:(a -> b) -> EqualProp a {x} {y} -> EqualProp b {c x} {c y}
@-}
data EqualityProp :: * -> * where
  FromSMT :: a -> a -> EqualitySMT a -> EqualityProp a
  Extensionality :: (a -> b) -> (a -> b) -> (a -> EqualityProp a) -> EqualityProp (a -> b)
  SubstitutitivityProp :: a -> a -> (a -> b) -> EqualityProp a -> EqualityProp b

{-@
toEqualityProp ::
  x:a -> y:a ->
  EqualSMT a {x} {y} ->
  EqualProp a {x} {y}
@-}
toEqualityProp :: a -> a -> EqualitySMT a -> EqualityProp a
toEqualityProp x y eSMT = FromSMT x y eSMT

{-@
fromEqualityProp ::
  EqSMT a =>
  x:a -> y:a ->
  EqualProp a {x} {y} ->
  EqualSMT a {x} {y}
@-}
fromEqualityProp :: EqSMT a => a -> a -> EqualityProp a -> EqualitySMT a
fromEqualityProp x y eProp = FromPrim x y (trust_me x y)
  where
    {-@
    assume trust_me :: x:a -> y:a -> {_:Proof | x = y}
    @-}
    trust_me :: a -> a -> Proof
    trust_me _ _ = ()

{-
TODO:

- reflexivity
- symmetry
- transitivity
- substitutitivity
-}

{-@
class ReflexivityEqualityProp a where
  reflexivityEqualityProp :: x:a -> EqualProp a {x} {x}
@-}
class ReflexivityEqualityProp a where
  reflexivityEqualityProp :: a -> EqualityProp a

instance EqSMT a => ReflexivityEqualityProp a where
  reflexivityEqualityProp x = FromSMT x x (FromPrim x x trivial)

{-
TODO: causes error

    • Couldn't match type ‘b’ with ‘a’
      ‘b’ is a rigid type variable bound by
        the instance declaration
        at src/Relation/Equality/Prop.hs:73:10-70
      ‘a’ is a rigid type variable bound by
        the instance declaration
        at src/Relation/Equality/Prop.hs:73:10-70
      Expected type: EqualityProp a
        Actual type: EqualityProp b
    • In the expression: reflexivityEqualityProp (f x)
      In the third argument of ‘Extensionality’, namely
        ‘(\ x -> reflexivityEqualityProp (f x))’
      In the expression:
        Extensionality f f (\ x -> reflexivityEqualityProp (f x))
    • Relevant bindings include
        x :: a (bound at src/Relation/Equality/Prop.hs:75:26)
        f :: a -> b (bound at src/Relation/Equality/Prop.hs:74:27)
        reflexivityEqualityProp :: (a -> b) -> EqualityProp (a -> b)
          (bound at src/Relation/Equality/Prop.hs:74:3)
   |
75 |     Extensionality f f (\x -> reflexivityEqualityProp (f x))
   |                               ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

-}

instance ReflexivityEqualityProp b => ReflexivityEqualityProp (a -> b) where
  reflexivityEqualityProp f =
    Extensionality f f (\x -> reflexivityEqualityProp (f x))
