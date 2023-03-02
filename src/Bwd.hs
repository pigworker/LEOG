{-# LANGUAGE DeriveTraversable #-}

module Bwd where

data Bwd x = B0 | Bwd x :< x deriving (Show, Eq, Functor, Foldable, Traversable)

(<!) :: Bwd x -> Int -> x
(xz :< x) <! 0 = x
(xz :< x) <! n = xz <! (n - 1)
