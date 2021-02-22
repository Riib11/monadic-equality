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
  | Extensionality :: f:(a -> b) -> g:(a -> b) -> (x:a -> EqualProp b {f x} {g x}) -> EqualProp (a -> b) {f} {g}
  | SubstitutitivityProp :: x:a -> y:a -> c:(a -> b) -> EqualProp a {x} {y} -> EqualProp b {c x} {c y}
@-}
data EqualityProp :: * -> * where
  FromSMT :: a -> a -> EqualitySMT a -> EqualityProp a
  Extensionality :: (a -> b) -> (a -> b) -> (a -> EqualityProp b) -> EqualityProp (a -> b)
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

instance ReflexivityEqualityProp b => ReflexivityEqualityProp (a -> b) where
  reflexivityEqualityProp f =
    Extensionality f f (\x -> reflexivityEqualityProp (f x))
