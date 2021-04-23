module Relation.Equality.PropI where

import Function
import Language.Haskell.Liquid.ProofCombinators

-- a distinct instance for each base type must be posulated
-- `a` is bivariant!!
data EqualPropSing a

class EqualPropSingI a where
  sing :: EqualPropSing a

{-@
measure eqp :: EqualPropSing a -> a -> a -> Bool
@-}

{-@
type EqualProp S X Y = {_:Proof | eqp S X Y}
@-}

{-@ assume
reflexivity :: sing:EqualPropSing a ->
  x:a -> EqualProp {sing} {x} {x}
@-}
reflexivity :: EqualPropSing a -> a -> Proof
reflexivity _ _ = ()

{-@ assume
extensionality :: sing_b:EqualPropSing b -> sing_a_to_b:EqualPropSing (a -> b) ->
  f:(a -> b) -> g:(a -> b) -> (x:a -> EqualProp {sing_b} {f x} {g x}) -> EqualProp {sing_a_to_b} {f} {g}
@-}
extensionality :: EqualPropSing b -> EqualPropSing (a -> b) -> (a -> b) -> (a -> b) -> (a -> Proof) -> Proof
extensionality _ _ _ _ _ = ()

{-@
retractability :: sing_b:EqualPropSing b -> sing_a_to_b:EqualPropSing (a -> b) ->
  f:(a -> b) -> g:(a -> b) -> EqualProp {sing_a_to_b} {f} {g} -> x:a -> EqualProp {sing_b} {f x} {g x}
@-}
retractability :: EqualPropSing b -> EqualPropSing (a -> b) -> (a -> b) -> (a -> b) -> Proof -> a -> Proof
retractability sing_b sing_a_to_b f g efg x =
  substitutability sing_a_to_b sing_b (given x) f g efg
    ? given x f
    ? given x g

{-
## Properties
-}

{-
### EqP
Typeclass that combines together the equality properties of propositional equality:
- reflexivity (axiom)
- symmetry
- transitivity
- substitutability (aixom)
-}

-- reflexivity and substituability are axioms
-- type EqP a = (Symmetry a, Transitivity a)

{-
### SMT EqP
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
  concreteness :: sing:EqualPropSing a ->
      x:a -> y:a -> EqualProp {sing} {x} {y} -> {_:Proof | x = y}
@-}
class Concreteness a where
  concreteness :: EqualPropSing a -> a -> a -> Proof -> Proof

instance EqSMT a => Concreteness a where
  concreteness sing x y pf = concreteness_EqSMT sing x y pf

{-@ assume
concreteness_EqSMT :: EqSMT a => sing:EqualPropSing a ->
  x:a -> y:a -> EqualProp {sing} {x} {y} -> {_:Proof | x = y}
@-}
concreteness_EqSMT :: EqSMT a => EqualPropSing a -> a -> a -> Proof -> Proof
concreteness_EqSMT _ _ _ _ = ()

{-
### Symmetry
-}

{-@
class Symmetry a where
  symmetry :: sing:EqualPropSing a ->
    x:a -> y:a -> EqualProp {sing} {x} {y} -> EqualProp {sing} {y} {x}
@-}
class Symmetry a where
  symmetry :: EqualPropSing a -> a -> a -> Proof -> Proof

instance Concreteness a => Symmetry a where
  symmetry sing x y exy =
    reflexivity sing x ? concreteness sing x y exy

instance (Symmetry b, EqualPropSingI b) => Symmetry (a -> b) where
  symmetry sing_a_to_b f g efg =
    let sing_b = sing :: EqualPropSing b
        efxgx :: a -> Proof
        efxgx x = retractability sing_b sing_a_to_b f g efg x
        egxfx :: a -> Proof
        egxfx x = symmetry sing_b (f x) (g x) (efxgx x)
     in extensionality sing_b sing_a_to_b g f egxfx

{-
### Transitivity
-}

{-@
class Transitivity a where
  transitivity :: sing:EqualPropSing a ->
    x:a -> y:a -> z:a -> EqualProp {sing} {x} {y} -> EqualProp {sing} {y} {z} -> EqualProp  {sing} {x} {z}
@-}
class Transitivity a where
  transitivity :: EqualPropSing a -> a -> a -> a -> Proof -> Proof -> Proof

instance Concreteness a => Transitivity a where
  transitivity sing x y z exy eyz =
    reflexivity sing x
      ? concreteness sing x y exy
      ? concreteness sing y z eyz

instance (Transitivity b, EqualPropSingI b) => Transitivity (a -> b) where
  transitivity sing_a_to_b f g h efg egh =
    let sing_b = sing :: EqualPropSing b
        es_fx_gx :: a -> Proof
        es_fx_gx x = retractability sing_b sing_a_to_b f g efg x
        es_gx_hx :: a -> Proof
        es_gx_hx x = retractability sing_b sing_a_to_b g h egh x
        es_fx_hx :: a -> Proof
        es_fx_hx x = transitivity sing_b (f x) (g x) (h x) (es_fx_gx x) (es_gx_hx x)
     in extensionality sing_b sing_a_to_b f h es_fx_hx
          ? undefined -- TODO: wierd SMT error going on somewhere here...

{-
### Substitutability
-}

{-@ assume
substitutability :: sing_a:EqualPropSing a -> sing_b:EqualPropSing b ->
  f:(a -> b) -> x:a -> y:a -> EqualProp {sing_a} {x} {y} -> EqualProp {sing_b} {f x} {f y}
@-}
substitutability :: EqualPropSing a -> EqualPropSing b -> (a -> b) -> a -> a -> Proof -> Proof
substitutability _ _ _ _ _ _ = ()

{-
## Lemmas
-}

{-@
alphaEquivalency :: forall a b. EqualPropSingI b => sing_a_to_b:EqualPropSing (a -> b) ->
  f:(a -> b) -> EqualProp {sing_a_to_b} {f} {apply (\x:a -> f x)}
@-}
alphaEquivalency :: forall a b. EqualPropSingI b => EqualPropSing (a -> b) -> (a -> b) -> Proof
alphaEquivalency sing_a_to_b f =
  let sing_b = sing :: EqualPropSing b
   in extensionality sing_b sing_a_to_b f (apply (\x -> f x)) $ \y ->
        reflexivity sing_b (f y)
          ? apply (\x -> f x) y
