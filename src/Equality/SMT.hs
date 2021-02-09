module Equality.SMT where

import Equality
import ProofCombinators
import Relation

{-@
measure eqSMT :: EqualSMT a -> a -> a -> Bool
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
fromEqualSMT :: x:a -> y:a -> {w:EqualSMT a | eqSMT w x y} -> {x = y}
@-}
fromEqualSMT :: a -> a -> EqualSMT a -> Proof
fromEqualSMT _ _ (SMT _ _ e) = e
