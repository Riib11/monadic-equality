module Equality.SMT where

import qualified Equality
import ProofCombinators
import Relation

{-
# SMT Equality
-}

-- Measure. Proxy for built-in SMT equality.
{-@
measure eqsmt :: EqualSMT a -> x:a -> y:a -> Bool
@-}
eqsmt :: EqualSMT a -> a -> a -> Bool
eqsmt _ _ _ = undefined

{-@
type EqSMT a X Y = {w:EqualSMT a | eqsmt w X Y}
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

{-@
assume fromEqualSMT :: x:a -> y:a -> EqSMT a {x} {y} -> {x = y}
@-}
fromEqualSMT :: a -> a -> EqualSMT a -> Proof
fromEqualSMT _ _ w = toProof w

{-
## Properties
-}

{-@
isReflexive :: Relation.IsReflexive <eqsmt> EqualSMT a
@-}
isReflexive :: Relation.IsReflexive EqualSMT a
isReflexive = IsReflexive (\x -> SMT x x trivial)
