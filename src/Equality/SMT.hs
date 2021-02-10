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

-- TODO: error
{-
/Users/henry/Documents/Projects/monadic-quicksort-verification/monadic-equality/src/Equality/SMT.hs:49:16: error:
    • Cannot apply unbound abstract refinement `eqsmt`
    •
   |
49 | isReflexive :: Relation.IsReflexive <eqsmt> EqualSMT a
   |                ^
-}
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

-- must be assumed
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
