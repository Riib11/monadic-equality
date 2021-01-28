module Equality where

import Relation

{-
Equality
-}

--
{-@
data IsEquality e a = IsEquality
  { eq :: a -> a -> Bool,
    isReflexive :: IsReflexive e a {eq},
    isSymmetric :: IsSymmetric e a {eq},
    isTransitive :: IsTransitive e a {eq}
  }
@-}
data IsEquality e a = IsEquality
  { eq :: a -> a -> Bool,
    isReflexive :: IsReflexive e a,
    isSymmetric :: IsSymmetric e a,
    isTransitive :: IsTransitive e a
  }
