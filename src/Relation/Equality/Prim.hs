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
substitutivity_Prim ::
  x:a -> y:a -> c:(a -> b) -> {_:Proof | x = y} -> {_:Proof | c x = c y}
@-}
substitutivity_Prim :: a -> a -> (a -> b) -> Proof -> Proof
substitutivity_Prim x y c e = e
