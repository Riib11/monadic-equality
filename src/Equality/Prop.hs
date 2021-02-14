module Equality.Prop where

import qualified Equality
import Equality.SMT
import ProofCombinators
import Relation

-- TODO: build with liquidhaskell develop branch

{-
# Propositional Equality
-}

-- Measure. Uninterpreted measure for propositional equality.
{-@
measure eqprop :: x:a -> y:a -> EqualProp a -> Bool
@-}

-- Type Synonym. Witness to `a`-equality between `X` and `Y`.
{-@
type EqProp a X Y = (EqualProp a)<eqprop X Y>
@-}

-- Inductive Datatype.
{-@
data EqualProp :: * -> * where
    InjectSMT ::
      x:a -> y:a ->
      EqSMT a {x} {y} ->
      EqProp a {x} {y}
  | Extensionality ::
      f:(a -> b) -> g:(a -> b) ->
      (x:a -> EqProp a {f x} {g x}) ->
      EqProp a {f} {g}
  | Congruency ::
      x:a -> y:a -> c:(a -> b) ->
      EqProp a {x} {y} ->
      EqProp b {f x} {f y}
@-}
data EqualProp :: * -> * where
  InjectSMT :: a -> a -> EqualSMT a -> EqualProp a
  Extensionality :: (a -> b) -> (a -> b) -> (a -> EqualProp a) -> EqualProp a
  Congruency :: a -> a -> (a -> b) -> EqualProp a -> EqualProp b

{-
## Properties
-}

{-@
type IsReflexiveEqualProp a = IsReflexive <{\x y w -> eqprop x y w}> EqualProp a
@-}
type IsReflexiveEqualProp a = IsReflexive EqualProp a

{-@
isReflexive_base :: IsReflexiveEqualSMT a -> IsReflexiveEqualProp a
@-}
isReflexive_base :: IsReflexiveEqualSMT a -> IsReflexiveEqualProp a

isReflexive IsReflexiveEqualSMT =
  IsReflexive
    ( \x ->
        let eSMTxx = reflexivity IsReflexiveEqualSMT x
         in SMT x x eSMTxx
    )

-- TODO: implement
{-@
isReflexive_induct :: IsReflexiveEqualProp b -> IsReflexiveEqualProp (a -> b)
@-}
isReflexive_induct :: IsReflexiveEqualProp b -> IsReflexiveEqualProp (a -> b)
isReflexive_induct = undefined

-- TODO: implement
{-@
isSymmetricEqualProp_base :: IsSymmetricEqualSMT a -> IsSymmetricEqualProp a
@-}
isSymmetricEqualProp_base :: IsSymmetricEqualSMT a -> IsSymmetricEqualProp a
isSymmetricEqualProp_base = undefined

-- TODO: implement
{-@
isSymmetricEqualProp_induct ::
  IsSymmetricEqualProp b -> IsSymmetricEqualProp (a -> b)
@-}
isSymmetricEqualProp_induct ::
  IsSymmetricEqualProp b -> IsSymmetricEqualProp (a -> b)
isSymmetricEqualProp_induct = undefined

-- TODO: implement
{-@
isTransitiveEqualProp_base :: IsTransitiveEqualSMT a -> IsTransitiveEqualProp a
@-}
isTransitiveEqualProp_base :: IsTransitiveEqualSMT a -> IsTransitiveEqualProp a
isTransitiveEqualProp_base = undefined

-- TODO: implement
{-@
isTransitiveEqualProp_induct ::
  IsTransitiveEqualSMT b -> IsTransitiveEqualProp (a -> b)
@-}
isTransitiveEqualProp_induct ::
  IsTransitiveEqualSMT b -> IsTransitiveEqualProp (a -> b)
isTransitiveEqualProp_induct = undefined

-- TODO: implement
{-@
isEqualityEqualProp_base :: IsEqualityEqualSMT a -> IsEqualityEqualProp a
@-}
isEqualityEqualProp_base :: IsEqualityEqualSMT a -> IsEqualityEqualProp a
isEqualityEqualProp_base = undefined

-- TODO: implement
{-@
isEqualityEqualProp_induct ::
  IsEqualityEqualSMT b -> IsEqualityEqualProp (a -> b)
@-}
isEqualityEqualProp_induct ::
  IsEqualityEqualSMT b -> IsEqualityEqualProp (a -> b)
isEqualityEqualProp_induct = undefined
