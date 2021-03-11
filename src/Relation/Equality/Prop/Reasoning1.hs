module Relation.Equality.Prop.Reasoning1 where

-- import Language.Haskell.Liquid.ProofCombinators
-- import Relation.Equality.Prop
-- import Prelude hiding (flip, map)

-- {-
-- ## Equational reasoning
-- -}

-- infixl 3 =~

-- infixl 3 ~=~

-- infixl 3 ~**

-- {-@
-- data PC a = PC
--   { pc_x :: a,
--     pc_y :: a,
--     pc_k :: z:a -> {eyz:EqualityProp a | eqprop pc_y z} -> {exz:EqualityProp a | eqprop pc_x z}
--   }
-- @-}
-- data PC a = PC
--   { pc_x :: a,
--     pc_y :: a,
--     pc_k :: a -> EqualityProp a -> EqualityProp a
--   }

-- {-@
-- type PCxy a X Y = {pc:PC a | pc_x pc = X && pc_y pc = Y}
-- @-}

-- {-@
-- (=~) ::
--   Equality a =>
--   x:a ->
--   {y_exy:(a, EqualityProp a) | eqprop x (fst y_exy)} ->
--   PCxy a {x} {fst y_exy}
-- @-}
-- (=~) ::
--   Equality a =>
--   a ->
--   (a, EqualityProp a) ->
--   PC a
-- x =~ y_exy = PC x y (\z eyz -> transitivity x y z exy eyz)
--   where
--     y = fst y_exy
--     exy = snd y_exy

-- {-@
-- (~=~) ::
--   Equality a =>
--   pc:PC a ->
--   {z_eyz:(a, EqualityProp a) | eqprop (pc_y pc) (fst z_eyz)} ->
--   PCxy a {pc_x pc} {fst z_eyz}
-- @-}
-- (~=~) ::
--   Equality a =>
--   PC a ->
--   (a, EqualityProp a) ->
--   PC a
-- pc ~=~ z_eyz = PC x z (\w ezw -> transitivity x z w (kxz z eyz) ezw)
--   where
--     x = pc_x pc
--     y = pc_y pc
--     kxz = pc_k pc
--     z = fst z_eyz
--     eyz = snd z_eyz

-- {-@
-- (~**) ::
--   Equality a =>
--   pc:PC a ->
--   QED ->
--   EqualProp a {pc_x pc} {pc_y pc}
-- @-}
-- (~**) ::
--   Equality a =>
--   PC a ->
--   QED ->
--   EqualityProp a
-- pc ~** QED = kxz y (reflexivity y)
--   where
--     x = pc_x pc
--     y = pc_y pc
--     kxz = pc_k pc
-- pc ~** Admit = undefined

-- {-
-- ### Examples
-- -}

-- {-@
-- ex1 :: Equality a => x:a -> EqualProp a {x} {x}
-- @-}
-- ex1 :: Equality a => a -> EqualityProp a
-- ex1 x =
--   x
--     =~ (x, reflexivity x)
--     ~=~ (x, reflexivity x)
--     ~** QED
