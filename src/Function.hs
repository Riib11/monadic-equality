module Function where

{-@ reflect apply @-}
apply :: (a -> b) -> a -> b
apply f x = f x

{-@ reflect given @-}
given :: a -> (a -> b) -> b
given x f = f x
