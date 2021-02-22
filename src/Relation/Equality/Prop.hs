module Relation.Equality.Prop where

import ProofCombinators
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
    FromSMT :: x:a -> y:a -> EqualSMT a {x} {y} -> EqualProp a {x} {y}
  | Extensionality :: f:(a -> b) -> g:(a -> b) -> (x:a -> EqualProp b {f x} {g x}) -> EqualProp (a -> b) {f} {g}
  | Substitutivity :: x:a -> y:a -> c:(a -> b) -> EqualProp a {x} {y} -> EqualProp b {c x} {c y}
@-}
data EqualityProp :: * -> * where
  FromSMT :: a -> a -> EqualitySMT a -> EqualityProp a
  Extensionality :: (a -> b) -> (a -> b) -> (a -> EqualityProp b) -> EqualityProp (a -> b)
  Substitutivity :: a -> a -> (a -> b) -> EqualityProp a -> EqualityProp b

{-@
toEqualityProp :: x:a -> y:a -> EqualSMT a {x} {y} -> EqualProp a {x} {y}
@-}
toEqualityProp :: a -> a -> EqualitySMT a -> EqualityProp a
toEqualityProp x y eSMT = FromSMT x y eSMT

{-@
fromEqualityProp :: EqSMT a => x:a -> y:a -> EqualProp a {x} {y} -> EqualSMT a {x} {y}
@-}
fromEqualityProp :: EqSMT a => a -> a -> EqualityProp a -> EqualitySMT a
fromEqualityProp x y eProp = FromPrim x y (trust_me x y)
  where
    {-@
    assume trust_me :: x:a -> y:a -> {_:Proof | x = y}
    @-}
    trust_me :: a -> a -> Proof
    trust_me _ _ = ()

{-@
assume fromEqualityExtensional :: f:(a -> b) -> g:(a -> b) -> EqualProp (a -> b) {f} {g} -> x:a -> EqualProp b {f x} {g x}
@-}
fromEqualityExtensional ::
  (a -> b) ->
  (a -> b) ->
  EqualityProp (a -> b) ->
  a ->
  EqualityProp b
fromEqualityExtensional f g eProp_f_g x = case eProp_f_g of
  Extensionality _ _ eProp_fx_gx -> eProp_fx_gx x
  _ -> undefined -- "impossible"

{-
## Properties
-}

{-
### Reflexivity
-}

{-@
class Reflexive_EqualityProp a where
  reflexivity_EqualityProp :: x:a -> EqualProp a {x} {x}
@-}
class Reflexive_EqualityProp a where
  reflexivity_EqualityProp :: a -> EqualityProp a

instance EqSMT a => Reflexive_EqualityProp a where
  reflexivity_EqualityProp x = FromSMT x x (FromPrim x x trivial)

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

instance EqSMT a => Symmetric_EqualityProp a where
  symmetry_EqualityProp x y eProp_x_y =
    let eSMT_x_y = fromEqualityProp x y eProp_x_y
        eSMT_y_x = symmetry_EqualitySMT x y eSMT_x_y
     in FromSMT y x eSMT_y_x

instance Symmetric_EqualityProp b => Symmetric_EqualityProp (a -> b) where
  symmetry_EqualityProp f g eProp_f_g =
    let eProp_fx_gx = fromEqualityExtensional f g eProp_f_g
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

instance EqSMT a => Transitive_EqualityProp a where
  transitivity_EqualityProp x y z eProp_x_y eProp_y_z =
    let eSMT_x_y = fromEqualityProp x y eProp_x_y
        eSMT_y_z = fromEqualityProp y z eProp_y_z
        eSMT_x_z = transitivity_EqualitySMT x y z eSMT_x_y eSMT_y_z
     in FromSMT x z eSMT_x_z

instance Transitive_EqualityProp b => Transitive_EqualityProp (a -> b) where
  transitivity_EqualityProp f g h eProp_f_g eProp_g_h =
    let eSMT_fx_gx = fromEqualityExtensional f g eProp_f_g
        eSMT_gx_hx = fromEqualityExtensional g h eProp_g_h
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
