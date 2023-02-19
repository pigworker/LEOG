module Th where

import Bwd

newtype Th = Th Integer deriving (Show, Eq)

instance Monoid Th where
  mempty = Th (-1)
  mappend (Th i) (Th j) = Th (go i j) where
    go th (-1) = th
    go th   0  = 0
    go (-1) ph = ph
    go   0  ph = 0
    go th   ph = case divMod ph 2 of
      (ph, 0) -> 2 * go th ph
      (ph, 1) -> case divMod th 2 of
        (th, b) -> 2 * go th ph + b

instance Semigroup Th where (<>) = mappend

cop :: Th -> Th -> (Th, Th, Th)
cop (Th i) (Th j) = let (a, b, c) = go i j in (Th a, Th b, Th c) where
  go (-1) ph = (-1, -1, ph)
  go 0    ph = (0, ph, -1)
  go th (-1) = (th, -1, -1)
  go th   0  = (-1, th, 0)
  go th   ph = case (divMod th 2, divMod ph 2) of
    ((th, l), (ph, r)) -> let (a, b, c) = go th ph in
      case (l, r) of
        (0, 0) -> (a, 2 * b, c)
        _      -> (2 * a + l, 2 * b + 1, 2 * b + r)

(<?) :: Th -> Bwd x -> Bwd x
Th i <? xz = go i xz where
  go 0 xz    = B0
  go (-1) xz = xz
  go th (xz :< x) = case divMod th 2 of
    (th, 0) -> go th xz
    (th, 1) -> go th xz :< x

class Thins t where
  (-^) :: t -> Th -> t

instance Thins Th where
  th -^ ph = th <> ph

instance Thins b => Thins (a, b) where (a, b) -^ th = (a, b -^ th)
instance Thins x => Thins (Bwd x) where xz -^ th = fmap (-^ th) xz
instance Thins x => Thins [x] where xz -^ th = fmap (-^ th) xz
instance Thins Int where
  i -^ Th th = go i th where
    go i th = case divMod th 2 of
      (th, 0) -> 1 + go i th
      (th, 1) -> if i == 0 then 0 else 1 + go (i - 1) th

wk :: Th
wk = Th (-2)

(-:) :: Th -> Bool -> Th
Th th -: b = Th (2 * th + (if b then 1 else 0))
