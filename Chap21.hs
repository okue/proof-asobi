module Chap21 where

import Language.Haskell.Liquid.ProofCombinators

{-@ type Pos = { v : Int | v > 0 } @-}

{-@ one :: Pos @-}
{-@ one :: { v : Int | v == 1 } @-}
{-@ one :: { v : Int | v <= 2 } @-}
one :: Int
one = 1

{-@ negone :: { v : Int | v < 0 } @-}
negone :: Int
negone = -1

-- {-@ test :: { 1 + 3 == 4 } @-}
-- test :: Proof
-- test = trivial

{-@ safeDiv :: Int -> { d : Int | d /= 0 } -> Int @-}
safeDiv :: Int -> Int -> Int
safeDiv n d = n `div` d

{-@ abs' :: Int -> { v : Int | v >= 0 } @-}
abs' :: Int -> Int
abs' n
  | n >= 0    = n
  | otherwise = - n

{-@ doublePos :: n : Pos -> { v : Int | n < v } @-}
doublePos :: Int -> Int
doublePos n = 2 * n


main :: IO ()
main = do
  print $ safeDiv 3 1
  -- print $ doublePos negone
