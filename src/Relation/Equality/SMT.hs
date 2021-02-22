module Relation.Equality.SMT where

import ProofCombinators
import Relation
import Relation.Equality

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
assume eqsmt_Bool :: x:Bool -> y:Bool -> w:EqualSMT Bool -> {v:Bool | v <=> eqsmt x y w}
@-}
eqsmt_Bool :: Bool -> Bool -> EqualSMT Bool -> Bool
eqsmt_Bool x y w = x == y

{-@
isReflexiveEqualSMT_Bool :: IsReflexive <{\x y w -> eqsmt x y w}> EqualSMT Bool
@-}
isReflexiveEqualSMT_Bool :: IsReflexive EqualSMT Bool
isReflexiveEqualSMT_Bool =
  constructIsReflexive
    ( \x ->
        let e_x_x = trivial
         in SMT x x e_x_x
    )

{-@
assume isSymmetricEqualSMT_Bool :: IsSymmetric <{\x y w -> eqsmt x y w}> EqualSMT Bool
@-}
isSymmetricEqualSMT_Bool :: IsSymmetric EqualSMT Bool
isSymmetricEqualSMT_Bool =
  constructIsSymmetric
    ( \x y eSMT_x_y ->
        let e_y_x = fromEqualSMT x y eSMT_x_y
         in SMT y x e_y_x
    )

{-@
assume isTransitiveEqualSMT_Bool :: IsTransitive <{\x y w -> eqsmt x y w}> EqualSMT Bool
@-}
isTransitiveEqualSMT_Bool :: IsTransitive EqualSMT Bool
isTransitiveEqualSMT_Bool =
  constructIsTransitive
    ( \x y z eSMT_x_y eSMT_y_z ->
        let e_x_y = fromEqualSMT x y eSMT_x_y
            e_y_z = fromEqualSMT y z eSMT_y_z
         in SMT x z (e_x_y &&& e_y_z)
    )

{-
TODO: error

Giving `e_cx_cy` in place of `undefined` below yields this liquid error:

**** LIQUID: ERROR :1:1-1:1: Error
PANIC: Please file an issue at https://github.com/ucsd-progsys/liquid-fixpoint
Unknown func-sort: (Relation.Equality.SMT.EqualSMT Bool) : (Relation.Equality.SMT.EqualSMT Int) for ()
-}

{-@
assume isSubstitutiveEqualSMT_Bool ::
  IsEquality <{\x y w -> eqsmt x y w}> EqualSMT a  ->
  IsSubstitutive <{\x y w -> eqsmt x y w}> EqualSMT Bool a
@-}
isSubstitutiveEqualSMT_Bool :: IsEquality EqualSMT a -> IsSubstitutive EqualSMT Bool a
isSubstitutiveEqualSMT_Bool isEquality =
  constructIsSubstitutive
    ( \x y c eSMT_x_y ->
        let e_x_y = fromEqualSMT x y eSMT_x_y
            e_cx_cy = eSMT_isSubstitutive x y c e_x_y
         in SMT (c x) (c y) undefined
    )

{-@
eSMT_isSubstitutive :: x:a -> y:a -> c:(a -> b) -> {_:Proof | x = y} -> {_:Proof | c x = c y}
@-}
eSMT_isSubstitutive :: a -> a -> (a -> b) -> Proof -> Proof
eSMT_isSubstitutive x y c hyp = hyp

-- {-@
-- assume isEqualityEqualSMT_Bool :: IsEquality <{\x y w -> eqsmt x y w}> EqualSMT Bool
-- @-}
-- isEqualityEqualSMT_Bool :: IsEquality EqualSMT Bool
-- isEqualityEqualSMT_Bool =
--   constructIsEquality
--     isReflexiveEqualSMT_Bool
--     isSymmetricEqualSMT_Bool
--     isTransitiveEqualSMT_Bool
--     isSubstitutiveEqualSMT_Bool
