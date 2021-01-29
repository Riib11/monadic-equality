module Function where

{-@
type Inverses a b F G =
  ((x:a -> {G (F x) = x}),
   (y:b -> {F (G y) = y}))
@-}
