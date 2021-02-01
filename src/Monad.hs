{-# LANGUAGE ExplicitForAll #-}
{-# LANGUAGE RankNTypes #-}

module Monad where

import Equality
import Function
import Relation
import Prelude hiding (Monad, (>>), (>>=))

-- {-
-- # Monad

-- Monad laws:
-- - bind_correct :: m >>= (lift . f) = map f m
-- - bind_identity :: m >>= lift = m
-- - bind_lift :: lift x >>= k = k x
-- - bind_associative :: (m >>= k1) >>= k2 = m >>= (\x -> k1 x >>= k2)
-- -}
-- {-@
-- data Monad m = Monad
--   { map :: forall a b. (a -> b) -> (m a -> m b),
--     lift :: forall a. a -> m a,
--     bind :: forall a b. m a -> (a -> m b) -> m b,
--     bind_correct :: forall a b. m:m a -> f:(a -> b) ->
--       EqProp (m b) {bind m (compose lift f)} {map f m},
--     bind_identity :: forall a. m:m a ->
--       EqProp (m a) {bind m lift} {m},
--     bind_lift :: forall a b. k:(a -> m b) -> x:a ->
--       EqProp (m b) {bind (lift x) k} {k x},
--     bind_associative :: forall a b c. m:m a -> k1:(a -> m b) -> k2:(b -> m c) ->
--       EqProp (m c) {bind (bind m k1) k2} {bind m (\x:a -> bind (k1 x) k2)}
--   }
-- @-}
-- data Monad m = Monad
--   { map :: forall a b. (a -> b) -> (m a -> m b),
--     lift :: forall a. a -> m a,
--     bind :: forall a b. m a -> (a -> m b) -> m b,
--     bind_correct :: forall a b. m a -> (a -> b) -> EqualityProp (m b),
--     bind_identity :: forall a. m a -> EqualityProp (m a),
--     bind_lift :: forall a b. (a -> m b) -> a -> EqualityProp (m b),
--     bind_associative :: forall a b c. m a -> (a -> m b) -> (b -> m c) -> EqualityProp (m c)
--   }

-- {-@ reflect seq @-}
-- seq :: Monad m -> m a -> m b -> m b
-- seq iMonad m1 m2 = m1 >>= (\_ -> m2)
--   where
--     (>>=) = bind iMonad

-- {-
-- Monad laws:
-- - bind_correct :: m >>= (lift . f)  =  map f m
-- - bind_identity :: m >>= lift  =  m
-- - bind_lift :: lift x >>= k  =  k x
-- - bind_associative :: (m >>= k1) >>= k2  =  m >>= (\x -> k1 x >>= k2)
-- -}

-- -- {-@
-- -- seq_isAssociative :: iMonad:Monad m -> IsAssociative (m a) (seq iMonad)
-- -- @-}
-- -- seq_isAssociative :: Monad m -> IsAssociative (m a)
-- -- seq_isAssociative iMonad m1 m2 m3 = ()

-- -- (m1 >> m2) >> m3
-- -- ===
-- -- (m1 >>= (\_ -> m2)) >>= (\_ -> m3)
-- -- ===
-- -- m1 >>= (\x -> (\_ -> m2) x >>= (\_ -> m3))
-- -- ===
-- -- m1 >>= (\x -> m2 >>= (\_ -> m3))
-- -- ===
-- -- m1 >>= (\_ -> m2 >>= (\_ -> m3))
-- -- ===
-- -- m1 >> (m2 >> m3)
