module Relation.Equality.SMT where

import ProofCombinators

{-
# SMT Equality
-}

{-
## Definition
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

{-@
toEqualitySMT :: EqSMT a => x:a -> y:a -> {_:Proof | x = y} -> {w:EqualitySMT a | eqsmt x y w}
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

{-
### Reflexivity
-}

{-@
class Reflexive_EqualitySMT a where
  reflexivity_EqualitySMT :: x:a -> EqualSMT a {x} {x}
@-}
class Reflexive_EqualitySMT a where
  reflexivity_EqualitySMT :: a -> EqualitySMT a

instance EqSMT a => Reflexive_EqualitySMT a where
  reflexivity_EqualitySMT x =
    let e_x_x = trivial
     in FromPrim x x e_x_x

{-
### Symmetry
-}

{-@
class Symmetric_EqualitySMT a where
  symmetry_EqualitySMT :: x:a -> y:a -> EqualSMT a {x} {y} -> EqualSMT a {y} {x}
@-}
class Symmetric_EqualitySMT a where
  symmetry_EqualitySMT :: a -> a -> EqualitySMT a -> EqualitySMT a

instance EqSMT a => Symmetric_EqualitySMT a where
  symmetry_EqualitySMT x y eSMT_x_y =
    let e_x_y = fromEqualitySMT x y eSMT_x_y
        e_y_x = symmetry_EqualityPrim x y e_x_y
     in FromPrim y x e_y_x

{-@
symmetry_EqualityPrim :: x:a -> y:a -> {_:Proof | x = y} -> {_:Proof | y = x}
@-}
symmetry_EqualityPrim :: a -> a -> Proof -> Proof
symmetry_EqualityPrim x y e_x_y = e_x_y

{-
### Transitivity
-}

{-@
class Transitive_EqualitySMT a where
  transitivity_EqualitySMT :: x:a -> y:a -> z:a -> EqualSMT a {x} {y} -> EqualSMT a {y} {z} -> EqualSMT a {x} {z}
@-}
class Transitive_EqualitySMT a where
  transitivity_EqualitySMT :: a -> a -> a -> EqualitySMT a -> EqualitySMT a -> EqualitySMT a

instance EqSMT a => Transitive_EqualitySMT a where
  transitivity_EqualitySMT x y z eSMT_x_y eSMT_y_z =
    let e_x_y = fromEqualitySMT x y eSMT_x_y
        e_y_z = fromEqualitySMT y z eSMT_y_z
        e_x_z = e_x_y &&& e_y_z
     in FromPrim x z e_x_z

{-
### Substitutivity
-}

{-@
class Substitutitive_EqualitySMT a b where
  substitutivity_EqualitySMT :: x:a -> y:a -> c:(a -> b) -> EqualSMT a {x} {y} -> EqualSMT b {c x} {c y}
@-}
class Substitutitive_EqualitySMT a b where
  substitutivity_EqualitySMT :: a -> a -> (a -> b) -> EqualitySMT a -> EqualitySMT b

instance (EqSMT a, EqSMT b) => Substitutitive_EqualitySMT a b where
  substitutivity_EqualitySMT x y c eSMT_x_y =
    let e_x_y = fromEqualitySMT x y eSMT_x_y
        e_cx_cy = substitutivity_Prim x y c e_x_y
     in FromPrim (c x) (c y) e_cx_cy

{-@
substitutivity_Prim ::
  x:a -> y:a -> c:(a -> b) -> {_:Proof | x = y} -> {_:Proof | c x = c y}
@-}
substitutivity_Prim :: a -> a -> (a -> b) -> Proof -> Proof
substitutivity_Prim x y c e = e
