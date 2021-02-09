module Relation where

import ProofCombinators

{-
type Re r a RE X Y :: * where
  r :: * -> *
  a :: *
  RE :: r a -> a -> a -> Bool
  X, Y :: a
-}
{-@
type Re r a RE X Y = {w:r a | RE w x y}
@-}

{-@
data IsReflexive r a <re :: r a -> a -> a -> Bool> = IsReflexive
  { reflexivity ::
      x:a ->
      Re r a {re} {x} {x}
  }
@-}
data IsReflexive r a = IsReflexive (a -> r a)

reflexivity :: IsReflexive r a -> (a -> r a)
reflexivity (IsReflexive reflexivity_) = reflexivity_

{-@
data IsSymmetric r a <re :: r a -> a -> a -> Bool> = IsSymmetric
  { symmetry ::
      x:a -> y:a ->
      Re r a {re} {x} {y} ->
      Re r a {re} {y} {x}
  }
@-}
data IsSymmetric r a = IsSymmetric (a -> a -> r a -> r a)

symmetry :: IsSymmetric r a -> (a -> a -> r a -> r a)
symmetry (IsSymmetric symmetry_) = symmetry_

{-@
data IsTransitive r a <re :: r a -> a -> a -> Bool> = IsTransitive
  { transitivity ::
      x:a -> y:a -> z:a ->
      Re r a {re} {x} {y} ->
      Re r a {re} {y} {z} ->
      Re r a {re} {x} {z}
  }
@-}
data IsTransitive r a = IsTransitive (a -> a -> a -> r a -> r a -> r a)

transitivity :: IsTransitive r a -> (a -> a -> a -> r a -> r a -> r a)
transitivity (IsTransitive transitivity_) = transitivity_
