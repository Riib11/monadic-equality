module Relation.Equality.Prop where

import Function
import Language.Haskell.Liquid.ProofCombinators

{-
# Propositional Equality
-}

{-
## Definition
-}

{-@
type EqualProp a X Y = {w:EqualityProp a | X = Y}
@-}
data EqualityProp a = EqualityProp

-- TODO: might need to use this GADT in order to solve paper's problem example
-- data EqualityProp a where
--   Reflexivity :: x:a -> EqualProp

{-
### Axioms
-}

{-@ assume
extensionality :: f:(a -> b) -> g:(a -> b) -> (x:a -> EqualProp b {f x} {g x}) -> EqualProp (a -> b) {f} {g}
@-}
extensionality :: (a -> b) -> (a -> b) -> (a -> EqualityProp b) -> EqualityProp (a -> b)
extensionality f g pf = EqualityProp

{-
#### Previously-assumed axioms that are now derived
-}

{-@
substitutability :: f:(a -> b) -> x:a -> y:a -> EqualProp a {x} {y} -> EqualProp b {f x} {f y}
@-}
substitutability :: (a -> b) -> a -> a -> EqualityProp a -> EqualityProp b
substitutability f x y pf = EqualityProp

{-
### Witnesses
-}

-- ? replaced fromSMT
{-@
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
### Retractability
-}

{-@
retractability :: f:(a -> b) -> g:(a -> b) -> EqualProp (a -> b) {f} {g} -> (x:a -> EqualProp b {f x} {g x})
@-}
retractability :: (a -> b) -> (a -> b) -> EqualityProp (a -> b) -> (a -> EqualityProp b)
retractability f g efg x =
  substitutability (given x) f g efg
    ? (given x f) -- instantiate `f x`
    ? (given x g) -- instantiate `g x`

{-
### Reflexivity
-}

{-@
reflexivity :: x:a -> EqualProp a {x} {x}
@-}
reflexivity :: a -> EqualityProp a
reflexivity x = toWitness x x trivial

{-
### Symmetry
-}

{-@
symmetry :: x:a -> y:a -> EqualProp a {x} {y} -> EqualProp a {y} {x}
@-}
symmetry :: a -> a -> EqualityProp a -> EqualityProp a
symmetry x y _ = toWitness y x trivial

{-
### Transitivity
-}

{-@
transitivity :: x:a -> y:a -> z:a -> EqualProp a {x} {y} -> EqualProp a {y} {z} -> EqualProp a {x} {z}
@-}
transitivity :: a -> a -> a -> EqualityProp a -> EqualityProp a -> EqualityProp a
transitivity x y z _ _ = toWitness x z trivial

{-
## Lemmas
-}

{-@
alphaEquivalency :: f:(a -> b) -> EqualProp (a -> b) {f} {apply (\x:a -> f x)}
@-}
alphaEquivalency :: (a -> b) -> EqualityProp (a -> b)
alphaEquivalency f =
  extensionality f (apply (\x -> f x)) $ \y ->
    reflexivity (f y) ? apply (\x -> f x) y

{-@
betaEquivalencyTrivial :: x:a -> y:b -> EqualProp b {y} {apply (\_:a -> y) x}
@-}
betaEquivalencyTrivial :: a -> b -> EqualityProp b
betaEquivalencyTrivial x y =
  reflexivity y ? apply (\_ -> y) x
