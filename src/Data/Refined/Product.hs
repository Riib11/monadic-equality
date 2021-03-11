module Data.Refined.Product where

{-@
type Product a b = (a, b)
@-}
type Product a b = (a, b)

{-@ reflect pi_1_2 @-}
pi_1_2 :: Product a b -> a
pi_1_2 (x, y) = x

{-@ reflect pi_2_2 @-}
pi_2_2 :: Product a b -> b
pi_2_2 (x, y) = y

{-@
type Product3 a b c = (a, b, c)
@-}
type Product3 a b c = (a, b, c)

{-@ reflect pi_1_3 @-}
pi_1_3 :: Product3 a b c -> a
pi_1_3 (x, _, _) = x

{-@ reflect pi_2_3 @-}
pi_2_3 :: Product3 a b c -> b
pi_2_3 (_, y, _) = y

{-@ reflect pi_3_3 @-}
pi_3_3 :: Product3 a b c -> c
pi_3_3 (_, _, z) = z
