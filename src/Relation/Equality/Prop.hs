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
  | Substitutivity :: x:a -> y:a -> c:(a -> b) -> EqualProp a {x} {y} -> EqualProp b {c x} {c y}
@-}
data EqualityProp :: * -> * where
  FromSMT :: a -> a -> EqualitySMT a -> EqualityProp a
  Extensionality :: (a -> b) -> (a -> b) -> (a -> EqualityProp b) -> EqualityProp (a -> b)
  Substitutivity :: a -> a -> (a -> b) -> EqualityProp a -> EqualityProp b

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

{-@
assume fromEqualityExtensional ::
  f:(a -> b) -> g:(a -> b) ->
  EqualProp (a -> b) {f} {g} ->
  x:a -> EqualProp b {f x} {g x}
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
TODO:

- symmetry
- transitivity
- substitutivity
-}

{-@
class ReflexiveEqualityProp a where
  reflexivityEqualityProp :: x:a -> EqualProp a {x} {x}
@-}
class ReflexiveEqualityProp a where
  reflexivityEqualityProp :: a -> EqualityProp a

instance EqSMT a => ReflexiveEqualityProp a where
  reflexivityEqualityProp x = FromSMT x x (FromPrim x x trivial)

instance ReflexiveEqualityProp b => ReflexiveEqualityProp (a -> b) where
  reflexivityEqualityProp f =
    Extensionality f f (\x -> reflexivityEqualityProp (f x))

{-@
class SymmetricEqualityProp a where
  symmetryEqualityProp :: x:a -> y:a -> EqualProp a {x} {y} -> EqualProp a {y} {x}
@-}
class SymmetricEqualityProp a where
  symmetryEqualityProp :: a -> a -> EqualityProp a -> EqualityProp a

instance EqSMT a => SymmetricEqualityProp a where
  symmetryEqualityProp x y eProp_x_y =
    let eSMT_x_y = fromEqualityProp x y eProp_x_y
        eSMT_y_x = symmetryEqualitySMT x y eSMT_x_y
     in FromSMT y x eSMT_y_x

instance SymmetricEqualityProp b => SymmetricEqualityProp (a -> b) where
  symmetryEqualityProp f g eProp_f_g =
    let eProp_fx_gx = fromEqualityExtensional f g eProp_f_g
        eProp_gx_fx x = symmetryEqualityProp (f x) (g x) (eProp_fx_gx x)
     in Extensionality g f eProp_gx_fx

{-@
class TransitiveEqualityProp a where
  transitivityEqualityProp :: x:a -> y:a -> z:a -> EqualProp a {x} {y} -> EqualProp a {y} {z} -> EqualProp a {x} {z}
@-}
class TransitiveEqualityProp a where
  transitivityEqualityProp :: a -> a -> a -> EqualityProp a -> EqualityProp a -> EqualityProp a

instance EqSMT a => TransitiveEqualityProp a where
  transitivityEqualityProp x y z eProp_x_y eProp_y_z =
    let eSMT_x_y = fromEqualityProp x y eProp_x_y
        eSMT_y_z = fromEqualityProp y z eProp_y_z
        eSMT_x_z = transitivityEqualitySMT x y z eSMT_x_y eSMT_y_z
     in FromSMT x z eSMT_x_z

instance TransitiveEqualityProp b => TransitiveEqualityProp (a -> b) where
  transitivityEqualityProp f g h eProp_f_g eProp_g_h =
    let eSMT_fx_gx = fromEqualityExtensional f g eProp_f_g
        eSMT_gx_hx = fromEqualityExtensional g h eProp_g_h
        eSMT_fx_hx x = transitivityEqualityProp (f x) (g x) (h x) (eSMT_fx_gx x) (eSMT_gx_hx x)
     in Extensionality f h eSMT_fx_hx

{-@
class SubstitutitiveEqualityProp a where
  substitutivityEqualityProp :: forall b. x:a -> y:a -> c:(a -> b) -> EqualProp a {x} {y} -> EqualProp b {c x} {c y}
@-}
class SubstitutitiveEqualityProp a where
  substitutivityEqualityProp :: forall b. a -> a -> (a -> b) -> EqualityProp a -> EqualityProp b

instance SubstitutitiveEqualityProp a where
  substitutivityEqualityProp x y c eProp_x_y = Substitutivity x y c eProp_x_y
