module Equality.SMT where

import Equality
import ProofCombinators
import Relation

{-
# SMT Equality
-}

-- Measure. Proxy for built-in SMT equality.
{-@
measure eqSMT :: EqualSMT a -> x:a -> y:a -> Bool
@-}

{-@
type EqSMT a X Y = {w:EqualSMT a | eqSMT w X Y}
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
