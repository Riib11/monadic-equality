module Proof where

{-@ type Proof = () @-}
type Proof = ()

data QED = QED

infixl 2 ***

(***) :: a -> QED -> Proof
_ *** QED = ()

(&&&) :: Proof -> Proof -> Proof
p &&& _ = p

{-@ withProof :: x:a -> Proof -> {y:a | y = x} @-}
withProof :: a -> Proof -> a
x `withProof` _ = x
