module Equality.SMT where

import Equality
import ProofCombinators
import Relation

-- TODO: build with liquidhaskell develop branch (errors with release branch)

{-
# SMT Equality
-}

-- Measure. Proxy for built-in SMT equality.
{-@
measure eqsmt :: x:a -> y:a -> EqualSMT a -> Bool
@-}

{-@
type EqSMT a X Y = (EqualSMT a)<eqsmt X Y>
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

-- TODO: must this be assumed?
{-@
assume fromEqualSMT :: x:a -> y:a -> EqSMT a {x} {y} -> {x = y}
@-}
fromEqualSMT :: a -> a -> EqualSMT a -> Proof
fromEqualSMT _ _ w = toProof w

{-
## Instances
-}

{-
### Bool
-}

{-@
isReflexiveEqualSMT_Bool :: IsReflexive <{\x y w -> eqsmt x y w}> EqualSMT Bool
@-}
isReflexiveEqualSMT_Bool :: IsReflexive EqualSMT Bool
isReflexiveEqualSMT_Bool =
  IsReflexive
    ( \x ->
        let e_x_x = trivial
         in SMT x x e_x_x
    )

{-@
assume isSymmetricEqualSMT_Bool :: IsSymmetric <{\x y w -> eqsmt x y w}> EqualSMT Bool
@-}
isSymmetricEqualSMT_Bool :: IsSymmetric EqualSMT Bool
isSymmetricEqualSMT_Bool =
  IsSymmetric
    ( \x y eSMT_x_y ->
        let e_y_x = fromEqualSMT x y eSMT_x_y
         in SMT y x e_y_x
    )

{-@
assume isTransitiveEqualSMT_Bool :: IsTransitive <{\x y w -> eqsmt x y w}> EqualSMT Bool
@-}
isTransitiveEqualSMT_Bool :: IsTransitive EqualSMT Bool
isTransitiveEqualSMT_Bool =
  IsTransitive
    ( \x y z eSMT_x_y eSMT_y_z ->
        let e_x_y = fromEqualSMT x y eSMT_x_y
            e_y_z = fromEqualSMT y z eSMT_y_z
         in SMT x z (e_x_y &&& e_y_z)
    )

{-@
assume isEqualityEqualSMT_Bool :: IsEquality <{\x y w -> eqsmt x y w}> EqualSMT Bool
@-}
isEqualityEqualSMT_Bool :: IsEquality EqualSMT Bool
isEqualityEqualSMT_Bool =
  IsEquality
    isReflexiveEqualSMT_Bool
    isSymmetricEqualSMT_Bool
    isTransitiveEqualSMT_Bool
