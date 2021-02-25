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

instance Eq a => Concrete a where
  concreteness = concreteness_Eq

{-@ assume
concreteness_Eq :: Eq a => x:a -> y:a -> EqualProp a {x} {y} -> {_:Proof | x = y}
@-}
concreteness_Eq :: Eq a => a -> a -> EqualityProp a -> Proof
concreteness_Eq _ _ _ = ()

{-
### Retractability
-}

{-@
class Retractable a b where
  retractability :: f:(a -> b) -> g:(a -> b) -> EqualProp (a -> b) {f} {g} -> (x:a -> EqualProp b {f x} {g x})
@-}
class Retractable a b where
  retractability :: (a -> b) -> (a -> b) -> EqualityProp (a -> b) -> (a -> EqualityProp b)

instance Retractable a b where
  retractability f g eqProp_f_g x =
    Substitutability f g (given x) eqProp_f_g
      ? (given x f) -- instantiate `f x`
      ? (given x g) -- instantiate `g x`

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
    let eqProp_fx_fx x = reflexivity (f x)
     in Extensionality f f eqProp_fx_fx

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
  symmetry x y eqProp_x_y =
    let eq_x_y = concreteness x y eqProp_x_y
        eq_y_x = eq_x_y -- by SMT
     in FromSMT y x eq_y_x

instance (Symmetric b, Retractable a b) => Symmetric (a -> b) where
  symmetry f g eqProp_f_g =
    let eqProp_fx_gx = retractability f g eqProp_f_g
        eqProp_gx_fx x = symmetry (f x) (g x) (eqProp_fx_gx x)
     in Extensionality g f eqProp_gx_fx

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
  transitivity x y z eqProp_x_y eqProp_y_z =
    let eq_x_y = concreteness x y eqProp_x_y
        eq_y_z = concreteness y z eqProp_y_z
        eq_x_z = eq_x_y &&& eq_y_z -- by SMT
     in FromSMT x z eq_x_z

instance (Transitive b, Retractable a b) => Transitive (a -> b) where
  transitivity f g h eqProp_f_g eqProp_g_h =
    let eSMT_fx_gx = retractability f g eqProp_f_g
        eSMT_gx_hx = retractability g h eqProp_g_h
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
  substitutability x y c eqProp_x_y = Substitutability x y c eqProp_x_y
