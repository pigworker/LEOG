{-# LANGUAGE DeriveTraversable #-}

module Bwd where

data Bwd x = B0 | Bwd x :< x deriving (Show, Eq, Functor, Foldable, Traversable)
