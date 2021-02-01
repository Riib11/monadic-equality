module Equality where

import Proof
import Relation

{-
# Equality

An equality relation is a relation that is reflexive, symmetric, and transitive.
-}

{-@
data IsEquality a <eq :: a -> a -> Bool> = IsEquality
  { isReflexive :: IsReflexive a <eq>,
    isSymmetric :: IsSymmetric a <eq>,
    isTransitive :: IsTransitive a <eq> }
@-}
data IsEquality a
  = IsEquality
      (IsReflexive a)
      (IsSymmetric a)
      (IsTransitive a)

{-
OLD
-}

-- {-@
-- data Equality a = Equality
--   { eq :: a -> a -> Bool,
--     isReflexive  :: IsReflexive  a {eq},
--     isSymmetric  :: IsSymmetric  a {eq},
--     isTransitive :: IsTransitive a {eq}
--    }
-- @-}
-- data Equality a = Equality
--   { eq :: a -> a -> Bool,
--     isReflexive :: IsReflexive a,
--     isSymmetric :: IsSymmetric a,
--     isTransitive :: IsTransitive a
--   }
