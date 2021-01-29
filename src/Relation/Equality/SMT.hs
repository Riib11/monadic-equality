module Relation.Equality.SMT where

import Relation.Equality

{-
# SMT Equality

A proxy for Haskell's `Eq` class, used by Liquid Haskell's SMT solver to
represent equalities.
-}

data SMTEquality a = SMTEquality
  {eq_smt :: a -> a -> Bool}

-- Instance. SMTEquality Int

-- {-@ assume isSMTEquality_Int :: IsEquality SMTEquality Int @-}
-- isSMTEquality_Int :: IsEquality SMTEquality Int
-- isSMTEquality_Int = undefined

-- -- {-@ assume isRelation :: IsRelation SMTEquality Int @-}
-- -- isRelation :: IsRelation SMTEquality Int
-- -- isRelation = undefined

-- -- {-@ assume isReflexive :: IsReflexive SMTEquality Int @-}
-- -- isReflexive :: IsReflexive SMTEquality Int
-- -- isReflexive = undefined

-- -- {-@ assume isSymmetric :: IsSymmetric SMTEquality Int @-}
-- -- isSymmetric :: IsSymmetric SMTEquality Int
-- -- isSymmetric = undefined

-- -- {-@ assume isTransitive :: IsTransitive SMTEquality Int @-}
-- -- isTransitive :: IsTransitive SMTEquality Int
-- -- isTransitive = undefined

-- -- Instance. SMTEquality Bool
