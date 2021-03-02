module Example.Monad where

import Function
-- import Language.Haskell.Liquid.Equational
import Language.Haskell.Liquid.ProofCombinators
import Relation.Equality.Prop
import Prelude hiding (Monad)

{-
# Monad
-}

-- {-@
-- data Monad m = Monad
--   { unit :: forall a. a -> m a,
--     bind :: forall a b. m a -> (a -> m b) -> m b,
--     identityLeft ::
--       forall a b.
--       (y:b -> EqualProp b {y} {y}) ->
--       x:a ->
--       k:(a -> m b) ->
--       EqualProp (m b) {bind (unit x) k} {k x},
--     identityRight ::
--       forall a.
--       (x:a -> EqualProp a {x} {x}) ->
--       m:m a ->
--       EqualProp (m a) {bind m unit} {m},
--     associativity ::
--       forall a b c.
--       (x:c -> EqualProp c {x} {x}) ->
--       (x:c -> y:c -> z:c -> EqualProp c {x} {y} -> EqualProp c {y} {z} -> EqualProp c {x} {z}) ->
--       m:m a ->
--       k1:(a -> m b) ->
--       k2:(b -> m c) ->
--       EqualProp (m c) {bind (bind m k1) k2} {bind m (\x:a -> bind (k1 x) k2)}
--   }
-- @-}
-- data Monad m = Monad
--   { unit :: forall a. a -> m a,
--     bind :: forall a b. m a -> (a -> m b) -> m b,
--     identityLeft ::
--       forall a b.
--       (b -> EqualityProp b) ->
--       a ->
--       (a -> m b) ->
--       EqualityProp (m b),
--     identityRight ::
--       forall a.
--       (a -> EqualityProp a) ->
--       m a ->
--       EqualityProp (m a),
--     associativity ::
--       forall a b c.
--       (c -> EqualityProp c) ->
--       (c -> c -> c -> EqualityProp c -> EqualityProp c -> EqualityProp c) ->
--       m a ->
--       (a -> m b) ->
--       (b -> m c) ->
--       EqualityProp (m c)
--   }

-- {-@ reflect kleisli @-}
-- kleisli :: Monad m -> (a -> m b) -> (b -> m c) -> (a -> m c)
-- kleisli mnd k1 k2 x = bind mnd (k1 x) k2

{-
## Reader Monad
-}

type Reader r a = r -> a

-- monadReader :: Monad (Reader r)
-- monadReader =
--   Monad
--     { unit = \a _ -> a,
--       bind = \m k r -> k (m r) r,
--       identityLeft =
--     }

-- type Reader r a = r -> a

-- {-@ reflect pure @-}
-- pure :: a -> Reader r a
-- pure a = \_ -> a

-- {-@ reflect bind @-}
-- bind :: Reader r a -> (a -> Reader r b) -> Reader r b
-- bind m k = \r -> k (m r) r

-- {-@ reflect kleisli @-}
-- kleisli :: (a -> Reader r b) -> (b -> Reader r c) -> (a -> Reader r c)
-- kleisli f g x = bind (f x) g

-- {-@
-- identityLeft ::
--   Reflexivity b =>
--   x:a ->
--   k:(a -> Reader r b) ->
--   EqualProp (Reader r b) {bind (pure x) k} {k x}
-- @-}
-- identityLeft ::
--   Reflexivity b =>
--   a ->
--   (a -> Reader r b) ->
--   EqualityProp (Reader r b)
-- identityLeft x k =
--   Extensionality (bind (pure x) k) (k x) $ \r ->
--     reflexivity (bind (pure x) k r)
--       ? ( bind (pure x) k r
--             =~= k (pure x r) r
--             =~= k x r
--             *** QED
--         )

-- {-@
-- identityRight ::
--   Reflexivity a =>
--   m:Reader r a ->
--   EqualProp (Reader r a) {bind m pure} {m}
-- @-}
-- identityRight ::
--   Reflexivity a =>
--   Reader r a ->
--   EqualityProp (Reader r a)
-- identityRight m =
--   Extensionality (bind m pure) m $ \r ->
--     reflexivity (bind m pure r)
--       ? ( bind m pure r
--             =~= pure (m r) r
--             =~= m r
--             *** QED
--         )

-- {-@
-- associativity ::
--   (Reflexivity c, Transitivity c) =>
--   m:Reader r a ->
--   k1:(a -> Reader r b) ->
--   k2:(b -> Reader r c) ->
--   EqualProp (Reader r c) {bind (bind m k1) k2} {bind m (kleisli k1 k2)}
-- @-}
-- associativity ::
--   (Reflexivity c, Transitivity c) =>
--   Reader r a ->
--   (a -> Reader r b) ->
--   (b -> Reader r c) ->
--   EqualityProp (Reader r c)
-- associativity m k1 k2 =
--   Extensionality (bind (bind m k1) k2) (bind m (kleisli k1 k2)) $ \r ->
--     let el = bind (bind m k1) k2 r
--         eml = k2 (bind m k1 r) r
--         em = bind (k1 (m r)) k2 r
--         emr = kleisli k1 k2 (m r) r
--         er = bind m (kleisli k1 k2) r
--      in (transitivity el em er)
--           ( (transitivity el eml em)
--               (reflexivity el)
--               (reflexivity eml)
--           )
--           ( (transitivity em emr er)
--               (reflexivity em)
--               (reflexivity emr)
--           )

{-
## Utilities
-}

(=~=) :: a -> b -> b
_ =~= y = y
