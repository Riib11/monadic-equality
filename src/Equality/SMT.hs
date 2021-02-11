module Equality.SMT where

import qualified Equality
import ProofCombinators
import Relation

{-
# SMT Equality
-}

-- Measure. Proxy for built-in SMT equality.
{-@
measure eqsmt :: x:a -> y:a -> EqualSMT a -> Bool
@-}

-- TODO: is this working? tends to not error when it breaks..
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
isReflexive :: Relation.IsReflexive <{\x y w -> eqsmt x y w}> EqualSMT a
@-}
isReflexive :: Relation.IsReflexive EqualSMT a
isReflexive =
  IsReflexive
    ( \x ->
        let exx = trivial
         in SMT x x exx
    )

{-
TODO: error

**** LIQUID: ERROR :1:1-1:1: Error
  PANIC: Please file an issue at https://github.com/ucsd-progsys/liquid-fixpoint
Unknown func-sort: (Relation.IsSymmetric (Equality.SMT.EqualSMT Int) Int) : Int for apply cast_as_int lq_karg$Equality.SMT.isSymmetric##k_##806
-}
{-@
isSymmetric :: Relation.IsSymmetric <{\x y w -> eqsmt x y w}> EqualSMT a
@-}
isSymmetric :: Relation.IsSymmetric EqualSMT a
isSymmetric =
  IsSymmetric
    ( \x y eSMTxy ->
        let eyx = fromEqualSMT x y eSMTxy
         in SMT y x eyx
    )

{-@
isTransitive :: Relation.IsTransitive <{\x y w -> eqsmt x y w}> EqualSMT a
@-}
isTransitive :: Relation.IsTransitive EqualSMT a
isTransitive =
  IsTransitive
    ( \x y z eSMTxy eSMTyz ->
        let exz = fromEqualSMT x y eSMTxy &&& fromEqualSMT y z eSMTyz
         in SMT x z exz
    )
