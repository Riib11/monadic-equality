module Relation.Equality.SMT where

import ProofCombinators

{-
# SMT Equality
-}

{-@
measure eqsmt :: a -> a -> EqualitySMT a -> Bool
@-}

{-@
type EqualSMT a X Y = {w:EqualitySMT a | eqsmt X Y w}
@-}

{-@
data EqualitySMT :: * -> * where
  FromPrim :: EqSMT a => x:a -> y:a -> {_:Proof | x = y} -> EqualSMT a {x} {y}
@-}
data EqualitySMT :: * -> * where
  FromPrim :: EqSMT a => a -> a -> Proof -> EqualitySMT a

-- TODO: dont think i actually need this
-- {-@
-- data EqualitySMT :: * -> * where
--     FromPrim :: EqSMT a => x:a -> y:a -> {_:Proof | x = y} -> EqualSMT a {x} {y}
--   | SubstitutitivitySMT :: (EqSMT a, EqSMT b) -> x:a -> y:a -> c:(a -> b) -> EqualSMT a {x} {y} -> EqualSMT a {c x} {c y}
-- @-}
-- data EqualitySMT :: * -> * where
--   FromPrim :: EqSMT a => a -> a -> Proof -> EqualitySMT a
--   SubstitutitivitySMT :: (EqSMT a, EqSMT b) => a -> a -> (a -> b) -> EqualitySMT a -> EqualitySMT b

{-@
toEqualitySMT ::
  EqSMT a =>
  x:a -> y:a ->
  {_:Proof | x = y} ->
  {w:EqualitySMT a | eqsmt x y w}
@-}
toEqualitySMT :: EqSMT a => a -> a -> Proof -> EqualitySMT a
toEqualitySMT x y e = FromPrim x y e

{-@
class EqSMT a where
  fromEqualitySMT :: x:a -> y:a -> EqualSMT a {x} {y} -> {_:Proof | x = y}
@-}
class EqSMT a where
  fromEqualitySMT :: a -> a -> EqualitySMT a -> Proof

{-
## Properties
-}

{-@
reflexivityEqualitySMT ::
  EqSMT a =>
  x:a ->
  EqualSMT a {x} {x}
@-}
reflexivityEqualitySMT ::
  EqSMT a => a -> EqualitySMT a
reflexivityEqualitySMT x =
  let e_x_x = trivial
   in FromPrim x x e_x_x

{-@
symmetricEqualityPrim :: x:a -> y:a -> {_:Proof | x = y} -> {_:Proof | y = x}
@-}
symmetricEqualityPrim :: a -> a -> Proof -> Proof
symmetricEqualityPrim x y e = e

{-@
symmetricEqualitySMT ::
  EqSMT a =>
  x:a -> y:a ->
  EqualSMT a {x} {y} ->
  EqualSMT a {y} {x}
@-}
symmetricEqualitySMT ::
  EqSMT a => a -> a -> EqualitySMT a -> EqualitySMT a
symmetricEqualitySMT x y eSMT_x_y =
  let e_x_y = fromEqualitySMT x y eSMT_x_y
      e_y_x = symmetricEqualityPrim x y e_x_y
   in FromPrim y x e_y_x

{-@
transitiveEqualitySMT ::
  EqSMT a =>
  x:a -> y:a -> z:a ->
  EqualSMT a {x} {y} ->
  EqualSMT a {y} {z} ->
  EqualSMT a {x} {z}
@-}
transitiveEqualitySMT ::
  EqSMT a => a -> a -> a -> EqualitySMT a -> EqualitySMT a -> EqualitySMT a
transitiveEqualitySMT x y z eSMT_x_y eSMT_y_z =
  let e_x_y = fromEqualitySMT x y eSMT_x_y
      e_y_z = fromEqualitySMT y z eSMT_y_z
      e_x_z = e_x_y &&& e_y_z
   in FromPrim x z e_x_z

{-@
substitutivePrim ::
  x:a -> y:a -> c:(a -> b) -> {_:Proof | x = y} -> {_:Proof | c x = c y}
@-}
substitutivePrim :: a -> a -> (a -> b) -> Proof -> Proof
substitutivePrim x y c e = e

{-@
substitutiveSMT ::
  (EqSMT a, EqSMT b) =>
  x:a -> y:a -> c:(a -> b) ->
  EqualSMT a {x} {y} ->
  EqualSMT b {c x} {c y}
@-}
substitutiveSMT ::
  (EqSMT a, EqSMT b) => a -> a -> (a -> b) -> EqualitySMT a -> EqualitySMT b
substitutiveSMT x y c eSMT_x_y =
  let e_x_y = fromEqualitySMT x y eSMT_x_y
      e_cx_cy = substitutivePrim x y c e_x_y
   in FromPrim (c x) (c y) e_cx_cy
