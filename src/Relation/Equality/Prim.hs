module Relation.Equality.Prim where

import ProofCombinators

{-@
reflexivity_EqualityPrim :: x:a -> {_:Proof | x = x}
@-}
reflexivity_EqualityPrim :: a -> Proof
reflexivity_EqualityPrim x = trivial

{-@
symmetry_EqualityPrim :: x:a -> y:a -> {_:Proof | x = y} -> {_:Proof | y = x}
@-}
symmetry_EqualityPrim :: a -> a -> Proof -> Proof
symmetry_EqualityPrim x y e_x_y = e_x_y

{-@
transitivity_EqualityPrim :: x:a -> y:a -> z:a -> {_:Proof | x = y} -> {_:Proof | y = z} -> {_:Proof | x = z}
@-}
transitivity_EqualityPrim :: a -> a -> a -> Proof -> Proof -> Proof
transitivity_EqualityPrim x y z e_x_y e_y_z = e_x_y &&& e_y_z

{-@
substitutability_Prim ::
  x:a -> y:a -> c:(a -> b) -> {_:Proof | x = y} -> {_:Proof | c x = c y}
@-}
substitutability_Prim :: a -> a -> (a -> b) -> Proof -> Proof
substitutability_Prim x y c e = e

-- -- must be instantiated for each instance of concrete SMT equality
-- {-@
-- class Concrete_EqualitySMT a where
--   concreteness_EqualitySMT :: x:a -> y:a -> EqualSMT a {x} {y} -> {_:Proof | x = y}
-- @-}
-- class Concrete_EqualitySMT a where
--   concreteness_EqualitySMT :: a -> a -> EqualitySMT a -> Proof
