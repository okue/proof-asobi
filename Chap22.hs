-- {-@ LIQUID "--no-termination" @-}
module Chap22 where
-- import Language.Haskell.Liquid.ProofCombinators

{-@ type Pos = { v : Int | v > 0 } @-}

{-@
data Sorted a = Nil
              | Cons { hd :: a, tl :: Sorted { v : a | hd <= v } }
@-}
data Sorted a = Nil
              | Cons { hd :: a, tl :: Sorted a }

okSorted = Cons 1 $ Cons 2 $ Cons 3 Nil
-- ngSorted = Cons 4 $ Cons 2 $ Cons 3 Nil

-- sum' Nil = 0
-- sum' (Cons x xs) = x + sum' xs

{-@ type NonZero = { v : Int | v /= 0 } @-}
{-@ ngf :: NonZero -> Int -> Int @-}
ngf :: Int -> Int -> Int
ngf d n
  | d > 0 = n `div` d
  | d < 0 = n `div` (-d)

-- {-@ head' :: { l : [Int] | length l >= 1 } -> Int @-}
-- head' :: [Int] -> Int
-- head' (x:xs) = x

{-@ type Nat = { v : Int | v >= 0 } @-}
{-@ fact :: Nat -> Nat @-}
fact :: Int -> Int
fact 0 = 1
fact n = n * fact (n-1)


-- main :: IO ()
-- main = do
--   print $ sum' okSorted
