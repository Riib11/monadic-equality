module Relation.Equality.Prop where

import Function
import Language.Haskell.Liquid.ProofCombinators

{-
# Propositional Equality
-}

{-
## Definition
-}

data EqualityProp a = EqualityProp

{-@
type EqualProp a X Y = {w:EqualityProp a | X = Y}
@-}

{-
### Axioms
-}

{-@ assume
reflexivity :: x:a -> EqualProp a {x} {x}
@-}
reflexivity :: a -> EqualityProp a
reflexivity x = EqualityProp

{-@
fromSMT :: x:a -> y:a -> {_:Proof | x = y} -> EqualProp a {x} {y}
@-}
fromSMT :: a -> a -> Proof -> EqualityProp a
fromSMT x y pf = reflexivity x

{-@ assume
extensionality :: f:(a -> b) -> g:(a -> b) -> (x:a -> EqualProp b {f x} {g x}) -> EqualProp (a -> b) {f} {g}
@-}
extensionality :: (a -> b) -> (a -> b) -> (a -> EqualityProp b) -> EqualityProp (a -> b)
extensionality f g pf = EqualityProp

{-@ assume
substitutability :: f:(a -> b) -> x:a -> y:a -> EqualProp a {x} {y} -> EqualProp b {f x} {f y}
@-}
substitutability :: (a -> b) -> a -> a -> EqualityProp a -> EqualityProp b
substitutability f x y pf = EqualityProp

{-
### Witnesses
-}

{-@ assume
toWitness :: x:a -> y:a -> {_:t | x = y} -> EqualProp a {x} {y}
@-}
toWitness :: a -> a -> t -> EqualityProp a
toWitness x y pf = EqualityProp

{-@
fromWitness :: x:a -> y:a -> EqualProp a {x} {y} -> {_:Proof | x = y}
@-}
fromWitness :: a -> a -> EqualityProp a -> Proof
fromWitness x y pf = trivial

{-
## Properties
-}

{-
### Equality

Combines together the equality properties:
- reflexivity -- TODO: now axiomatized
- symmetry
- transitivity
- substitutability
-}

{-@
class (Symmetry a, Transitivity a) => Equality a where
  __Equality :: {v:Maybe a | v = Nothing}
@-}
class (Symmetry a, Transitivity a) => Equality a where
  __Equality :: Maybe a

{-
### SMT Equality
-}

{-@
class EqSMT a where
  eqSMT :: x:a -> y:a -> {b:Bool | ((x = y) => b) && (b => (x = y))}
@-}
class EqSMT a where
  eqSMT :: a -> a -> Bool

{-
### Concreteness
-}

{-@
class Concreteness a where
  concreteness :: x:a -> y:a -> EqualProp a {x} {y} -> {_:Proof | x = y}
@-}
class Concreteness a where
  concreteness :: a -> a -> EqualityProp a -> Proof

instance EqSMT a => Concreteness a where
  concreteness x y pf = concreteness_EqSMT x y pf

{-@ assume
concreteness_EqSMT :: EqSMT a => x:a -> y:a -> EqualProp a {x} {y} -> {_:Proof | x = y}
@-}
concreteness_EqSMT :: EqSMT a => a -> a -> EqualityProp a -> Proof
concreteness_EqSMT _ _ _ = ()

{-
### Retractability
-}

{-@
class Retractability a b where
  retractability :: f:(a -> b) -> g:(a -> b) -> EqualProp (a -> b) {f} {g} -> (x:a -> EqualProp b {f x} {g x})
@-}
class Retractability a b where
  retractability :: (a -> b) -> (a -> b) -> EqualityProp (a -> b) -> (a -> EqualityProp b)

instance Retractability a b where
  retractability f g efg x =
    substitutability (given x) f g efg
      ? (given x f) -- instantiate `f x`
      ? (given x g) -- instantiate `g x`

-- {-
-- ### Reflexivity

-- * redundant, since now axiomatized

-- -}

-- {-@
-- class Reflexivity a where
--   reflexivity :: x:a -> EqualProp a {x} {x}
-- @-}
-- class Reflexivity a where
--   reflexivity :: a -> EqualityProp a

-- instance Concreteness a => Reflexivity a where
--   reflexivity x = fromSMT x x trivial

-- instance Reflexivity b => Reflexivity (a -> b) where
--   reflexivity f =
--     let efxfx x = reflexivity (f x)
--      in extensionality f f efxfx

{-
### Symmetry
-}

{-@
class Symmetry a where
  symmetry :: x:a -> y:a -> EqualProp a {x} {y} -> EqualProp a {y} {x}
@-}
class Symmetry a where
  symmetry :: a -> a -> EqualityProp a -> EqualityProp a

instance Concreteness a => Symmetry a where
  symmetry x y exy =
    reflexivity x ? concreteness x y exy

-- symmetry x y exy =
--   let e_x_y = concreteness x y exy
--       e_y_x = e_x_y -- by SMT
--    in fromSMT y x e_y_x

instance (Symmetry b, Retractability a b) => Symmetry (a -> b) where
  symmetry f g efg =
    let efxgx = retractability f g efg
        egxfx x = symmetry (f x) (g x) (efxgx x)
     in extensionality g f egxfx

{-
### Transitivity
-}

{-@
class Transitivity a where
  transitivity :: x:a -> y:a -> z:a -> EqualProp a {x} {y} -> EqualProp a {y} {z} -> EqualProp a {x} {z}
@-}
class Transitivity a where
  transitivity :: a -> a -> a -> EqualityProp a -> EqualityProp a -> EqualityProp a

instance Concreteness a => Transitivity a where
  transitivity x y z exy eyz =
    reflexivity x
      ? concreteness x y exy
      ? concreteness y z eyz

-- let e_x_y = concreteness x y exy
--     e_y_z = concreteness y z eyz
--     e_x_z = e_x_y &&& e_y_z -- by SMT
--  in reflexivity x -- fromSMT x z e_x_z

instance (Transitivity b, Retractability a b) => Transitivity (a -> b) where
  transitivity f g h efg egh =
    let es_fx_gx = retractability f g efg
        es_gx_hx = retractability g h egh
        es_fx_hx x = transitivity (f x) (g x) (h x) (es_fx_gx x) (es_gx_hx x)
     in extensionality f h es_fx_hx

{-
## Lemmas
-}

{-@
alphaEquivalency :: Equality b => f:(a -> b) -> EqualProp (a -> b) {f} {apply (\x:a -> f x)}
@-}
alphaEquivalency :: Equality b => (a -> b) -> EqualityProp (a -> b)
alphaEquivalency f =
  extensionality f (apply (\x -> f x)) $ \y ->
    reflexivity (f y) ? apply (\x -> f x) y

{-@
betaEquivalencyTrivial :: Equality b => x:a -> y:b -> EqualProp b {y} {apply (\_:a -> y) x}
@-}
betaEquivalencyTrivial :: Equality b => a -> b -> EqualityProp b
betaEquivalencyTrivial x y =
  reflexivity y ? apply (\_ -> y) x
