module Relation where

import Proof

{-@
data IsReflexive a <r :: a -> a -> Bool> =
  IsReflexive (x:a -> {_:Proof | r x x})
@-}
data IsReflexive a = IsReflexive (a -> Proof)

{-@
data IsSymmetric a <r :: a -> a -> Bool> =
  IsSymmetric (x:a -> y:a -> {_:Proof | r x y => r y x})
@-}
data IsSymmetric a = IsSymmetric (a -> a -> Proof)

{-@
data IsTransitive a <r :: a -> a -> Bool> =
  IsTransitive (x:a -> y:a -> z:a -> {_:Proof | (r x y && r y z) => r x z})
@-}
data IsTransitive a = IsTransitive (a -> a -> a -> Proof)

{-
OLD
-}

-- {-@
-- type IsReflexive a R = x:a -> {_:Proof | R x x}
-- @-}
-- type IsReflexive a = a -> Proof

-- {-@
-- type IsSymmetric a R = x:a -> y:a -> {_:Proof | R x y => R y x}
-- @-}
-- type IsSymmetric a = a -> a -> Proof

-- {-@
-- type IsTransitive a R = x:a -> y:a -> z:a -> {_:Proof | R x y && R y z => R x z}
-- @-}
-- type IsTransitive a = a -> a -> a -> Proof

{-
NEW
-}

{-
TMP
-}

-- -- {-@
-- -- data IsReflexive a <r :: a -> a -> Bool> =
-- --   IsReflexive { rx :: a, ry :: a, rp :: {_:Proof | r rx ry} }
-- -- @-}
-- -- data IsReflexive a = IsReflexive a a Proof

-- {-@
-- data PList a <p :: a -> Bool>
--   = PNil
--   | PCons { head :: {_:a | p a}, tail :: PList a <p> }
-- @-}
-- data PList a = PNil | PCons a (PList a)

-- {-@
--   data Map [mllen] k a <l :: root:k -> k -> Bool, r :: root:k -> k -> Bool>
--       = Tip
--       | Bin { mSz    :: Size
--             , mKey   :: k
--             , mValue :: a
--             , mLeft  :: Map <l, r> (k <l mKey>) a
--             , mRight :: Map <l, r> (k <r mKey>) a }
--   @-}

-- {-@ measure mllen @-}
-- mllen :: Map k a -> Int
-- {-@ mllen :: Map k a -> Nat @-}
-- mllen Tip = 0
-- mllen (Bin _ _ _ l r) = 1 + if (mllen l < mllen r) then mllen r else mllen l

-- {-@ measure mlen :: (Map k a) -> Int
--       mlen Tip = 0
--       mlen (Bin s k v l r) = 1 + (mlen l) + (mlen r)
--   @-}

-- {-@ invariant {v:Map k a | (mlen v) >= 0}@-}

-- {-@ type OMap k a = Map <{\root v -> v < root }, {\root v -> v > root}> k a @-}

-- data Map k a
--   = Tip
--   | Bin Size k a (Map k a) (Map k a)

-- type Size = Int

-- -- {-@
-- -- data Related a <r :: a -> a -> Bool> = Related
-- --   { rx :: a,
-- --     ry :: a,
-- --     rxy :: {_:Proof | r rx ry}
-- --   }
-- -- @-}
-- -- data Related a = Related
-- --   { rx :: a,
-- --     ry :: a,
-- --     rxy :: Proof
-- --   }

-- -- {-@
-- -- data IsReflexive a <r :: a -> a -> Bool> =
-- --   IsReflexive { reflexivity :: x:a -> {_:Proof | Related r x x} }
-- -- @-}
-- -- data IsReflexive a = IsReflexive
-- --   {reflexivity :: a -> Proof}

-- -- {-@
-- -- data IsReflexive a <r :: a -> a -> Bool> =
-- --   IsReflexive (x:a -> {_:Proof | r x x})
-- -- @-}
-- -- data IsReflexive a = IsReflexive (a -> Proof)
