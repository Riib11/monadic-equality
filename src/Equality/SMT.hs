module Equality.SMT where

import qualified Equality
import ProofCombinators
import qualified Relation

-- TODO: build with liquidhaskell develop branch (errors with release branch)

{-
# SMT Equality
-}

-- Measure. Proxy for built-in SMT equality.
{-@
measure eqsmt :: x:a -> y:a -> EqualSMT a -> Bool
@-}

{-@
type EqSMT a X Y = (EqualSMT a)<eqsmt X Y>
@-}

{-@
data EqualSMT :: * -> * where
  SMT ::
    x:a -> y:a ->
    {_:Proof | x = y} ->
    EqSMT a {x} {y}
@-}
data EqualSMT :: * -> * where
  SMT :: a -> a -> Proof -> EqualSMT a

{-@
toEqualSMT :: x:a -> y:a -> {_:Proof | x = y} -> EqSMT a {x} {y}
@-}
toEqualSMT :: a -> a -> Proof -> EqualSMT a
toEqualSMT = SMT

-- TODO: must this be assumed?
{-@
assume fromEqualSMT :: x:a -> y:a -> EqSMT a {x} {y} -> {x = y}
@-}
fromEqualSMT :: a -> a -> EqualSMT a -> Proof
fromEqualSMT _ _ w = toProof w

{-
## Properties
-}

{-@
type IsReflexive a = Relation.IsReflexive<{\x y w -> eqsmt x y w}> EqualSMT a
@-}
type IsReflexive a = Relation.IsReflexive a

{-@
type IsSymmetric a = Relation.IsSymmetric <{\x y w -> eqsmt } a
@-}
type IsSymmetric a = Relation.IsSymmetric a

{-@
type IsTransitive a = Relation.IsTransitive <{\x y w -> eqsmt x y w}> a
@-}
type IsTransitive a = Relation.IsTransitive

{-@
type IsEquality a = Equality.IsEquality <{\x y w -> eqsmt x y w}> a
@-}
type IsEquality a = Equality.IsEquality a

{-
## Instances
-}

-- TODO: temporary notes
{-

A general framework for proving instances of `IsEquality`:

{-@
isReflexive :: IsReflexive a
@-}
isReflexive :: IsReflexive a
isReflexive =
  IsReflexive
    ( \x ->
        let exx = trivial
         in SMT x x exx
    )

{-@
isSymmetric :: IsSymmetric a
@-}
isSymmetric :: IsSymmetric a
isSymmetric =
  IsSymmetric
    ( \x y eSMTxy ->
        let eyx = fromEqualSMT x y eSMTxy
         in SMT y x eyx
    )

{-@
isTransitive :: IsTransitive a
@-}
isTransitive :: IsTransitive a
isTransitive =
  IsTransitive
    ( \x y z eSMTxy eSMTyz ->
        let exz = fromEqualSMT x y eSMTxy &&& fromEqualSMT y z eSMTyz
         in SMT x z exz
    )

{-@
isEquality :: IsEquality a
@-}
isEquality :: IsEquality a
isEquality = IsEquality isReflexive isSymmetric isTransitive

-}

{-
### Bool
-}

-- TODO: implement
{-@
isReflexive_Bool :: IsReflexive Bool
@-}
isReflexive_Bool :: IsReflexive Bool
isReflexive_Bool = undefined

-- TODO: implement
{-@
isSymmetric_Bool :: IsSymmetric Bool
@-}
isSymmetric_Bool :: IsSymmetric Bool
isSymmetric_Bool = undefined

-- TODO: implement
{-@
isTransitive_Bool :: IsTransitive Bool
@-}
isTransitive_Bool :: IsTransitive Bool
isTransitive_Bool = undefined

-- TODO: implement
{-@
isEquality_Bool :: IsEquality Bool
@-}
isEquality_Bool :: IsEquality Bool
isEquality_Bool = undefined
