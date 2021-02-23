{-# LANGUAGE ScopedTypeVariables #-}

module Relation.Equality.Prop where

import Function
import ProofCombinators

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
  | Substitutability :: x:a -> y:a -> c:(a -> b) -> EqualProp a {x} {y} -> EqualProp b {c x} {c y}
@-}
data EqualityProp :: * -> * where
  FromSMT :: a -> a -> Proof -> EqualityProp a
  Extensionality :: (a -> b) -> (a -> b) -> (a -> EqualityProp b) -> EqualityProp (a -> b)
  Substitutability :: a -> a -> (a -> b) -> EqualityProp a -> EqualityProp b

{-
## Properties
-}

{-
### Concreteness
-}

{-@
class Concrete a where
  concreteness :: x:a -> y:a -> EqualProp a {x} {y} -> {_:Proof | x = y}
@-}
class Concrete a where
  concreteness :: a -> a -> EqualityProp a -> Proof

{-
### Retractability
-}

{-@
class Retractable a b where
  retractability :: f:(a -> b) -> g:(a -> b) -> EqualProp (a -> b) {f} {g} -> (x:a -> EqualProp b {f x} {g x})
@-}
class Retractable a b where
  retractability :: (a -> b) -> (a -> b) -> EqualityProp (a -> b) -> (a -> EqualityProp b)

-- TODO: why does this not type-check?
instance Retractable a b where
  retractability f g e_f_g x =
    Substitutability f g (given x) e_f_g

{-
### Reflexivity
-}

{-@
class Reflexive a where
  reflexivity :: x:a -> EqualProp a {x} {x}
@-}
class Reflexive a where
  reflexivity :: a -> EqualityProp a

instance Concrete a => Reflexive a where
  reflexivity x = FromSMT x x trivial

instance Reflexive b => Reflexive (a -> b) where
  reflexivity f =
    Extensionality f f (\x -> reflexivity (f x))

{-
### Symmetry
-}

{-@
class Symmetric a where
  symmetry :: x:a -> y:a -> EqualProp a {x} {y} -> EqualProp a {y} {x}
@-}
class Symmetric a where
  symmetry :: a -> a -> EqualityProp a -> EqualityProp a

instance Concrete a => Symmetric a where
  symmetry x y eProp_x_y =
    let e_x_y = concreteness x y eProp_x_y
        e_y_x = e_x_y -- by SMT
     in FromSMT y x e_y_x

instance (Symmetric b, Retractable a b) => Symmetric (a -> b) where
  symmetry f g eProp_f_g =
    let eProp_fx_gx = retractability f g eProp_f_g
        eProp_gx_fx x = symmetry (f x) (g x) (eProp_fx_gx x)
     in Extensionality g f eProp_gx_fx

-- instance Symmetric b => Symmetric (a -> b) where
--   symmetry f g eProp_f_g =
--     Extensionality g f $ \x ->
--       let {-@
--           eProp_f_g_ :: EqualProp (a -> b) {f} {g}
--           @-}
--           eProp_f_g_ :: EqualityProp (a -> b)
--           eProp_f_g_ = eProp_f_g

--           {-@
--           eProp_fx_gx :: EqualProp b {given x f} {given x g}
--           @-}
--           eProp_fx_gx :: EqualityProp b
--           eProp_fx_gx = Substitutability g f (given x) eProp_f_g_ ? (given x f) ? (given x g)
--        in symmetry (f x) (g x) eProp_fx_gx

{-
### Transitivity
-}

{-@
class Transitive a where
  transitivity :: x:a -> y:a -> z:a -> EqualProp a {x} {y} -> EqualProp a {y} {z} -> EqualProp a {x} {z}
@-}
class Transitive a where
  transitivity :: a -> a -> a -> EqualityProp a -> EqualityProp a -> EqualityProp a

instance Concrete a => Transitive a where
  transitivity x y z eProp_x_y eProp_y_z =
    let e_x_y = concreteness x y eProp_x_y
        e_y_z = concreteness y z eProp_y_z
        e_x_z = e_x_y &&& e_y_z -- by SMT
     in FromSMT x z e_x_z

instance (Transitive b, Retractable a b) => Transitive (a -> b) where
  transitivity f g h eProp_f_g eProp_g_h =
    let eSMT_fx_gx = retractability f g eProp_f_g
        eSMT_gx_hx = retractability g h eProp_g_h
        eSMT_fx_hx x = transitivity (f x) (g x) (h x) (eSMT_fx_gx x) (eSMT_gx_hx x)
     in Extensionality f h eSMT_fx_hx

{-
### Substitutability
-}

{-@
class Substitutability a where
  substitutability :: forall b. x:a -> y:a -> c:(a -> b) -> EqualProp a {x} {y} -> EqualProp b {c x} {c y}
@-}
class Substitutability a where
  substitutability :: forall b. a -> a -> (a -> b) -> EqualityProp a -> EqualityProp b

instance Substitutability a where
  substitutability x y c eProp_x_y = Substitutability x y c eProp_x_y
