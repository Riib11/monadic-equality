module Relation.Equality.SMT where

import Relation.Equality

{-
# SMT Equality

A proxy for Haskell's `Eq` class, used by Liquid Haskell's SMT solver to
represent equalities.
-}

data SMTEquality a = SMTEquality
  {eqSMT :: a -> a -> Bool}

eqSMT_Int :: SMTEquality Int
eqSMT_Int = SMTEquality {eqSMT = (==)}

eqSMT_Bool :: SMTEquality Bool
eqSMT_Bool = SMTEquality {eqSMT = (==)}

-- Instances.

{-@ assume isSMTEquality_Bool :: IsEquality SMTEquality Bool @-}
isSMTEquality_Bool :: IsEquality SMTEquality Bool
isSMTEquality_Bool = undefined

{-@ assume isSMTEquality_Int :: IsEquality SMTEquality Int @-}
isSMTEquality_Int :: IsEquality SMTEquality Int
isSMTEquality_Int = undefined
