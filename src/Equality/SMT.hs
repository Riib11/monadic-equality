module Equality.SMT where

import Equality
import Proof
import Relation

-- {-@
-- type EqSMT a X Y = {_:EqualitySMT a | X = Y}
-- @-}

-- {-@ measure eqsmt :: a -> a -> Bool @-}

-- {-@
-- data EqualitySMT :: * -> * where
--   SMT :: x:a -> y:a -> {_:Proof | x = y} -> {_:EqualitySMT a | eqsmt x y}
-- @-}
-- data EqualitySMT :: * -> * where
--   SMT :: a -> a -> Proof -> EqualitySMT a

-- {-@
-- isReflexive_eqsmt :: IsReflexive a <eqsmt>
-- @-}
-- isReflexive_eqsmt = IsReflexive pf
--   where
--     {-@
--     assume pf :: x:a -> {_:Proof | eqsmt x x}
--     @-}
--     pf _ = ()

-- {-@
-- isEqualitySMT :: IsEquality a <eqsmt>
-- @-}
-- isEqualitySMT = IsEquality
