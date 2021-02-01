module Function where

import Equality
import Relation

-- {-@
-- type IsCommutative a F
-- @-}

-- {-@
-- type IsCommutative a F = x:a -> y:a ->
--   EqProp a {F x y} {F y x}
-- @-}
-- type IsCommutative a = a -> a -> EqualityProp a

-- {-@
-- type IsAssociative a F = x:a -> y:a -> z:a ->
--   EqProp a {F (F x y) z} {F (F x y) z}
-- @-}
-- type IsAssociative a = a -> a -> a -> EqualityProp a

{-@ reflect compose @-}
compose :: (b -> c) -> (a -> b) -> (a -> c)
compose f g x = f (g x)
