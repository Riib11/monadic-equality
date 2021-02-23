module Relation.Equality.Prop where

import ProofCombinators
import Relation.Equality.Prim
import Relation.Equality.SMT

{-
# Propositional Equality
-}

{-
## Definition
-}

{-@
measure eqprop :: a -> a -> EqualityProp a -> Bool
@-}

{-@
type EqualProp a X Y = {w:EqualityProp a | eqprop X Y w}
@-}

{-@
data EqualityProp :: * -> * where
    FromSMT :: x:a -> y:a -> {_:Proof | x = y} -> EqualProp a {x} {y}
  | Extensionality :: f:(a -> b) -> g:(a -> b) -> (x:a -> EqualProp b {f x} {g x}) -> EqualProp (a -> b) {f} {g}
  | Substitutivity :: x:a -> y:a -> c:(a -> b) -> EqualProp a {x} {y} -> EqualProp b {c x} {c y}
@-}
data EqualityProp :: * -> * where
  FromSMT :: a -> a -> Proof -> EqualityProp a
  Extensionality :: (a -> b) -> (a -> b) -> (a -> EqualityProp b) -> EqualityProp (a -> b)
  Substitutivity :: a -> a -> (a -> b) -> EqualityProp a -> EqualityProp b

{-
## Properties
-}

{-
### Concreteness
-}

{-@
class Concrete_EqualityProp a where
  concreteness_EqualityProp :: x:a -> y:a -> EqualProp a {x} {y} -> {_:Proof | x = y}
@-}
class Concrete_EqualityProp a where
  concreteness_EqualityProp :: a -> a -> EqualityProp a -> Proof

{-
### Retractability
-}

{-@
class Retractable_EqualityProp a b where
  retractability_EqualityProp :: f:(a -> b) -> g:(a -> b) -> EqualProp (a -> b) {f} {g} -> (x:a -> EqualProp b {f x} {g x})
@-}
class Retractable_EqualityProp a b where
  retractability_EqualityProp :: (a -> b) -> (a -> b) -> EqualityProp (a -> b) -> (a -> EqualityProp b)

instance Retractable_EqualityProp a b where
  retractability_EqualityProp = retractability_EqualityProp_

-- TODO: must be assumed?
{-@
assume retractability_EqualityProp_ :: f:(a -> b) -> g:(a -> b) -> EqualProp (a -> b) {f} {g} -> (x:a -> EqualProp b {f x} {g x})
@-}
retractability_EqualityProp_ :: (a -> b) -> (a -> b) -> EqualityProp (a -> b) -> (a -> EqualityProp b)
retractability_EqualityProp_ f g eProp_f_g x =
  case eProp_f_g of
    Extensionality _ _ eProp_fx_gx -> eProp_fx_gx x
    _ -> undefined -- impossible to have non-extensional equality over a function type

{-
### Reflexivity
-}

{-@
class Reflexive_EqualityProp a where
  reflexivity_EqualityProp :: x:a -> EqualProp a {x} {x}
@-}
class Reflexive_EqualityProp a where
  reflexivity_EqualityProp :: a -> EqualityProp a

instance Concrete_EqualityProp a => Reflexive_EqualityProp a where
  reflexivity_EqualityProp x = FromSMT x x trivial

instance Reflexive_EqualityProp b => Reflexive_EqualityProp (a -> b) where
  reflexivity_EqualityProp f =
    Extensionality f f (\x -> reflexivity_EqualityProp (f x))

{-
### Symmetry
-}

{-@
class Symmetric_EqualityProp a where
  symmetry_EqualityProp :: x:a -> y:a -> EqualProp a {x} {y} -> EqualProp a {y} {x}
@-}
class Symmetric_EqualityProp a where
  symmetry_EqualityProp :: a -> a -> EqualityProp a -> EqualityProp a

instance Concrete_EqualityProp a => Symmetric_EqualityProp a where
  symmetry_EqualityProp x y eProp_x_y =
    let e_x_y = concreteness_EqualityProp x y eProp_x_y
        e_y_x = symmetry_EqualityPrim x y e_x_y
     in FromSMT y x e_y_x

instance Symmetric_EqualityProp b => Symmetric_EqualityProp (a -> b) where
  symmetry_EqualityProp f g eProp_f_g =
    let eProp_fx_gx = retractability_EqualityProp f g eProp_f_g
        eProp_gx_fx x = symmetry_EqualityProp (f x) (g x) (eProp_fx_gx x)
     in Extensionality g f eProp_gx_fx

{-
### Transitivity
-}

{-@
class Transitive_EqualityProp a where
  transitivity_EqualityProp :: x:a -> y:a -> z:a -> EqualProp a {x} {y} -> EqualProp a {y} {z} -> EqualProp a {x} {z}
@-}
class Transitive_EqualityProp a where
  transitivity_EqualityProp :: a -> a -> a -> EqualityProp a -> EqualityProp a -> EqualityProp a

instance Concrete_EqualityProp a => Transitive_EqualityProp a where
  transitivity_EqualityProp x y z eProp_x_y eProp_y_z =
    let e_x_y = concreteness_EqualityProp x y eProp_x_y
        e_y_z = concreteness_EqualityProp y z eProp_y_z
        e_x_z = transitivity_EqualityPrim x y z e_x_y e_y_z
     in FromSMT x z e_x_z

instance Transitive_EqualityProp b => Transitive_EqualityProp (a -> b) where
  transitivity_EqualityProp f g h eProp_f_g eProp_g_h =
    let eSMT_fx_gx = retractability_EqualityProp f g eProp_f_g
        eSMT_gx_hx = retractability_EqualityProp g h eProp_g_h
        eSMT_fx_hx x = transitivity_EqualityProp (f x) (g x) (h x) (eSMT_fx_gx x) (eSMT_gx_hx x)
     in Extensionality f h eSMT_fx_hx

{-
### Substitutivity
-}

{-@
class Substitutitive_EqualityProp a where
  substitutivity_EqualityProp :: forall b. x:a -> y:a -> c:(a -> b) -> EqualProp a {x} {y} -> EqualProp b {c x} {c y}
@-}
class Substitutitive_EqualityProp a where
  substitutivity_EqualityProp :: forall b. a -> a -> (a -> b) -> EqualityProp a -> EqualityProp b

instance Substitutitive_EqualityProp a where
  substitutivity_EqualityProp x y c eProp_x_y = Substitutivity x y c eProp_x_y
