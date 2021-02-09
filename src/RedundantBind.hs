module RedundantBind where

type Proof = ()

{-@
measure eqWrapped :: a -> a -> Bool
@-}

{-@
type EqW a X Y = {_:EqWrapped a | eqWrapped X Y}
@-}

{-@
data EqWrapped :: * -> * where
  EqWrapped :: x:a -> y:a -> {_:Proof | x = y} -> EqW a {x} {y}
@-}
data EqWrapped :: * -> * where
  EqWrapped :: a -> a -> Proof -> EqWrapped a

-- eq -> eqWrapped
{-@
wrap :: x:a -> y:a -> {_:Proof | x = y} -> EqW a {x} {y}
@-}
wrap :: a -> a -> Proof -> EqWrapped a
wrap = EqWrapped

-- eqWrapped -> eq
{-@ fail unwrap @-}
{-@
unwrap :: x:a -> y:a -> EqW a {x} {y} -> {x = y}
@-}
unwrap :: a -> a -> EqWrapped a -> Proof
unwrap x y ew@(EqWrapped x_ y_ e) = e

-- EqWrapped x_ y_ e :: EqW a {x} {y}
