module Relation.Equality where

import Relation

{-
# Equality

An equality relation is a relation that is reflexive, symmetric, and transitive.
-}

{-@
data IsEquality eq a = IsEquality
  { eq_isRelation :: IsRelation eq a,
    eq_isReflexive :: IsReflexive eq a
  }
@-}
data IsEquality eq a = IsEquality
  { eq_isRelation :: IsRelation eq a,
    eq_isReflexive :: IsReflexive eq a
  }

-- eq_isReflexive :: IsReflexive eq a
-- eq_isReflexive :: a -> Relation eq a

-- a -> Relation eq a

-- {-@
-- data IsEquality eq a = IsEquality
--   { isRelation :: IsRelation eq a,
--     isReflexive :: IsReflexive eq a,
--     isSymmetric :: IsSymmetric eq a,
--     isTransitive :: IsTransitive eq a
--   }
-- @-}
-- data IsEquality eq a = IsEquality
--   { isRelation :: IsRelation eq a,
--     isReflexive :: IsReflexive eq a,
--     isSymmetric :: IsSymmetric eq a,
--     isTransitive :: IsTransitive eq a
--   }
