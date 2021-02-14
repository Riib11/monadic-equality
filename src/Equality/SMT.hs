module Equality.SMT where

import qualified Equality
import ProofCombinators
import Relation

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
type IsReflexiveEqualSMT a = IsReflexive <{\x y w -> eqsmt x y w}> EqualSMT a
@-}
type IsReflexiveEqualSMT a = IsReflexive EqualSMT a

{-@
type IsSymmetricEqualSMT a = IsSymmetric <{\x y w -> eqsmt } a
@-}
type IsSymmetricEqualSMT a = IsSymmetric a

{-@
type IsTransitiveEqualSMT a = IsSymmetric <{\x y w -> eqsmt x y w}> a
@-}
type IsTransitiveEqualSMT a = IsSymmetric a

{-@
type IsEqualityEqualSMT a = Equality.IsEquality <{\x y w -> eqsmt x y w}> a
@-}
type IsEqualityEqualSMT a = Equality.IsEquality a

{-
## Instances
-}

-- TODO: temporary notes
{-

A general framework for proving instances of `IsEqualityEqualSMT`:

{-@
isReflexive :: IsReflexiveEqualSMT a
@-}
isReflexive :: IsReflexiveEqualSMT a
isReflexive =
  IsReflexive
    ( \x ->
        let exx = trivial
         in SMT x x exx
    )

{-@
isSymmetric :: IsSymmetricEqualSMT a
@-}
isSymmetric :: IsSymmetricEqualSMT a
isSymmetric =
  IsSymmetric
    ( \x y eSMTxy ->
        let eyx = fromEqualSMT x y eSMTxy
         in SMT y x eyx
    )

{-@
isTransitive :: IsTransitiveEqualSMT a
@-}
isTransitive :: IsTransitiveEqualSMT a
isTransitive =
  IsTransitive
    ( \x y z eSMTxy eSMTyz ->
        let exz = fromEqualSMT x y eSMTxy &&& fromEqualSMT y z eSMTyz
         in SMT x z exz
    )

{-@
isEquality :: IsEqualityEqualSMT a
@-}
isEquality :: IsEqualityEqualSMT a
isEquality = IsEquality isReflexive isSymmetric isTransitive

-}
