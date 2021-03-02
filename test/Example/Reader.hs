module Example.Reader where

import Function
-- import Language.Haskell.Liquid.Equational
import Language.Haskell.Liquid.ProofCombinators
import Relation.Equality.Prop

{-
# Reader Monad
-}

{-
## Definitions
-}

type Reader r a = r -> a

{-@ reflect unit @-}
unit :: a -> Reader r a
unit a = \_ -> a

{-@ reflect bind @-}
bind :: Reader r a -> (a -> Reader r b) -> Reader r b
bind m k = \r -> k (m r) r

{-@ reflect kleisli @-}
kleisli :: (a -> Reader r b) -> (b -> Reader r c) -> (a -> Reader r c)
kleisli f g x = bind (f x) g

{-
## Laws
-}

{-@
identityLeft ::
  Reflexive b =>
  x:a ->
  k:(a -> Reader r b) ->
  EqualProp (Reader r b) {bind (unit x) k} {k x}
@-}
identityLeft ::
  Reflexive b =>
  a ->
  (a -> Reader r b) ->
  EqualityProp (Reader r b)
identityLeft x k =
  Extensionality (bind (unit x) k) (k x) $ \r ->
    reflexivity (bind (unit x) k r)
      ? ( bind (unit x) k r
            =~= k (unit x r) r
            =~= k x r
            *** QED
        )

{-@
identityRight ::
  Reflexive a =>
  m:Reader r a ->
  EqualProp (Reader r a) {bind m unit} {m}
@-}
identityRight ::
  Reflexive a =>
  Reader r a ->
  EqualityProp (Reader r a)
identityRight m =
  Extensionality (bind m unit) m $ \r ->
    reflexivity (bind m unit r)
      ? ( bind m unit r
            =~= unit (m r) r
            =~= m r
            *** QED
        )

{-@
associativity ::
  (Reflexive c, Transitive c) =>
  m:Reader r a ->
  k1:(a -> Reader r b) ->
  k2:(b -> Reader r c) ->
  EqualProp (Reader r c) {bind (bind m k1) k2} {bind m (kleisli k1 k2)}
@-}
associativity ::
  (Reflexive c, Transitive c) =>
  Reader r a ->
  (a -> Reader r b) ->
  (b -> Reader r c) ->
  EqualityProp (Reader r c)
associativity m k1 k2 =
  Extensionality (bind (bind m k1) k2) (bind m (kleisli k1 k2)) $ \r ->
    let el = bind (bind m k1) k2 r
        eml = k2 (bind m k1 r) r
        em = bind (k1 (m r)) k2 r
        emr = kleisli k1 k2 (m r) r
        er = bind m (kleisli k1 k2) r
     in (transitivity el em er)
          ( (transitivity el eml em)
              (reflexivity el)
              (reflexivity eml)
          )
          ( (transitivity em emr er)
              (reflexivity em)
              (reflexivity emr)
          )

{-
## Utilities
-}

(=~=) :: a -> b -> b
_ =~= y = y
