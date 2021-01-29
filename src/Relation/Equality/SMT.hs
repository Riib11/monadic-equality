module Relation.Equality.SMT where

import Relation
import Relation.Equality

{-
# SMT Equality

A proxy for Haskell's `Eq` class, used by Liquid Haskell's SMT solver to
represent equalities.
-}

data EqSMT a = EqSMT
  {eqSMT :: (a, a) -> Bool}

eqSMT_Int :: EqSMT Int
eqSMT_Int = EqSMT {eqSMT = \(x, y) -> x == y}

eqSMT_Bool :: EqSMT Bool
eqSMT_Bool = EqSMT {eqSMT = \(x, y) -> x == y}

-- Instances.

{-@ assume isEquality_EqSMT_Bool :: IsEquality EqSMT Bool @-}
isEquality_EqSMT_Bool :: IsEquality EqSMT Bool
isEquality_EqSMT_Bool = undefined

{-@ assume isEquality_EqSMT_Int :: IsEquality EqSMT Int @-}
isEquality_EqSMT_Int :: IsEquality EqSMT Int
isEquality_EqSMT_Int = undefined
