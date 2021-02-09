module Equality where

import Relation

{-@
type Eq e a EQ X Y = Re r a {EQ} {X} {Y}
@-}

{-@
data IsEquality e a <eq :: e a -> a -> a -> Bool> = IsEquality
  { isReflexive :: IsReflexive e a <eq>,
    isSymmetric :: IsSymmetric e a <eq>,
    isTransitive :: IsTransitive e a <eq>
  }
@-}
data IsEquality e a
  = IsEquality
      (IsReflexive e a)
      (IsSymmetric e a)
      (IsTransitive e a)

isReflexive :: IsEquality e a -> IsReflexive e a
isReflexive (IsEquality isReflexive_ _ _) = isReflexive_

isSymmetric :: IsEquality e a -> IsSymmetric e a
isSymmetric (IsEquality _ isSymmetric_ _) = isSymmetric_

isTransitive :: IsEquality e a -> IsTransitive e a
isTransitive (IsEquality _ _ isTransitive_) = isTransitive_
