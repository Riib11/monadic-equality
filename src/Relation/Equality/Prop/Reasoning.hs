module Relation.Equality.Prop.Reasoning where

import Function
import Language.Haskell.Liquid.ProofCombinators
import Relation.Equality.Prop

-- {-
-- ## Equational reasoning
-- -}

-- infixl 4 ?~

-- infixl 3 =~

-- infixl 3 ~=~

-- infixl 3 ~**

-- (?~) :: Equality a => a -> EqualityProp a -> (a, EqualityProp a)
-- y ?~ exy = (y, exy)
-- {-# INLINE (?~) #-}

-- {-@
-- (=~) ::
--   Equality a =>
--   x:a ->
--   {y_exy:(a, EqualityProp a) | x = fst y_exy} ->
--   {x_y_kxz:((a, a), z:a -> {_:EqualityProp a | fst y_exy = z} -> {_:EqualityProp a | x = z}) | fst (fst x_y_kxz) = x && snd (fst x_y_kxz) = fst y_exy}
-- @-}
-- (=~) ::
--   Equality a =>
--   a ->
--   (a, EqualityProp a) ->
--   ((a, a), a -> EqualityProp a -> EqualityProp a)
-- x =~ (y, exy) = ((x, y), \z eyz -> transitivity x y z exy eyz)

-- {-@
-- (~=~) ::
--   Equality a =>
--   x_y_kxz:(x_y::(a, a), z:a -> {_:EqualityProp a | snd x_y = z} -> {_:EqualityProp a | fst x_y = z}) ->
--   {z_eyz:(a, EqualityProp a) | snd (fst x_y_kxz) = fst z_eyz} ->
--   {x_z_kxw:((a, a), w:a -> {_:EqualityProp a | fst z_eyz = w} -> {_:EqualityProp a | fst (fst x_y_kxz) = w}) | fst (fst x_z_kxw) = fst (fst x_y_kxz) && snd (fst x_z_kxw) = fst z_eyz}
-- @-}
-- (~=~) ::
--   Equality a =>
--   ((a, a), a -> EqualityProp a -> EqualityProp a) ->
--   (a, EqualityProp a) ->
--   ((a, a), a -> EqualityProp a -> EqualityProp a)
-- ((x, y), kxz) ~=~ (z, eyz) = ((x, z), \w ezw -> transitivity x z w (kxz z eyz) ezw)

-- {-@ assume
-- (~**) ::
--   Equality a =>
--   x_y_kxz:(x_y::(a, a), z:a -> {_:EqualityProp a | snd x_y = z} -> {_:EqualityProp a | fst x_y = z}) ->
--   qed:QED ->
--   {_:EqualityProp a | if (isAdmit qed) then false else fst (fst x_y_kxz) = snd (fst x_y_kxz)}
-- @-}
-- (~**) ::
--   Equality a =>
--   ((a, a), a -> EqualityProp a -> EqualityProp a) ->
--   QED ->
--   EqualityProp a
-- ((x, y), kxz) ~** _ = kxz y (reflexivity y)

-- -- {-@
-- -- ex1_1 :: Equality a => x:a -> {x_y_kxz:((a, a), z:a ->
-- --                                                 EqualProp a {x} {z} -> EqualProp a {x} {z}) | fst (fst x_y_kxz) = x && snd (fst x_y_kxz) = x}
-- -- @-}
-- -- ex1_1 :: Equality a => a -> ((a, a), a -> EqualityProp a -> EqualityProp a)
-- -- ex1_1 x = x =~ (x, reflexivity x)

-- -- {-@
-- -- ex1_2 :: Equality a => x:a -> {x_y_kxz:((a, a), z:a -> EqualProp a {x} {z} -> EqualProp a {x} {z}) | fst (fst x_y_kxz) = x && snd (fst x_y_kxz) = x}
-- -- @-}
-- -- ex1_2 :: Equality a => a -> ((a, a), a -> EqualityProp a -> EqualityProp a)
-- -- ex1_2 x = ((x1', x3), kx1x4)
-- --   where
-- --     ((x1, x2), kx1x3) = x =~ x_exx1
-- --     ((x1', x3), kx1x4) = ((x1, x2), kx1x3) ~=~ x_exx2
-- --     x_exx1 = (x, reflexivity x)
-- --     x_exx2 = (x, reflexivity x)

-- {-
-- `ex1` is SAFE, although needlessly verbose.
-- -}
-- {-@
-- ex1 :: Equality a => x:a -> EqualProp a {x} {x}
-- @-}
-- ex1 :: Equality a => a -> EqualityProp a
-- ex1 x =
--   let ((x1, x2), kx1x3) = x =~ (x, reflexivity x)
--       ((x1', x3), kx1x4) = ((x1, x2), kx1x3) ~=~ (x, reflexivity x)
--    in ((x1', x3), kx1x4) ~** QED

-- {-
-- `ex2` is UNSAFE- but it should typecheck right?!  It is exactly the same
-- as `ex1`, but inlined rather than explicitly naming each of the intermediate
-- results.

-- It produces the following error:
-- ```
-- The inferred type

--   VV : (Relation.Equality.Prop.EqualityProp a)

-- is not a subtype of the required type

--   VV : {VV : (Relation.Equality.Prop.EqualityProp a) | fst ?a = z}
-- ```
-- -}
-- -- {-@
-- -- ex2 :: Equality a => x:a -> EqualProp a {x} {x}
-- -- @-}
-- -- ex2 :: Equality a => a -> EqualityProp a
-- -- ex2 x =
-- --   x
-- --     =~ (x, reflexivity x)
-- --     ~=~ (x, reflexivity x)
-- --     ~** QED

-- {-
-- `ex3` is UNSAFE as well... with its only difference from the SAFE `ex1` being
-- the use of `?~` rather that tuple syntax. Since `?~` is inlined (at the Haskell
-- level) I expected that there wouldn't be refinement problems rising from the
-- fact that `?~` doesn't deal with refinement info (and it couldn't lifted to
-- the refinement level, since its second argument `exy` mentions a refinement-
-- level variable that is not in `~?`'s scope. This sort of pattern works with the
-- liquid-prelude's `?` though... so I was trying to mimic that.)

-- It produces the following error:
-- ```
-- The inferred type
--   VV : {v : (a, (Relation.Equality.Prop.EqualityProp a)) | v == ?~ x (reflexivity x)}

-- is not a subtype of the required type
--   VV : {VV : (a, (Relation.Equality.Prop.EqualityProp a)) | x = fst VV}

-- in the context
--   x : a
--     |
-- 129 |   let ((x1, x2), kx1x3) = x =~ x ?~ reflexivity x
--     |                                ^^^^^^^^^^^^^^^^^^
-- ```
-- -}
-- -- {-@
-- -- ex3 :: Equality a => x:a -> EqualProp a {x} {x}
-- -- @-}
-- -- ex3 :: Equality a => a -> EqualityProp a
-- -- ex3 x =
-- --   let ((x1, x2), kx1x3) = x =~ x ?~ reflexivity x
-- --       ((x1', x3), kx1x4) = ((x1, x2), kx1x3) ~=~ x ?~ reflexivity x
-- --    in ((x1', x3), kx1x4) ~** QED
