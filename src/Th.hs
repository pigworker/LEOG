module Th where

import Bwd

newtype Th = Th Integer deriving (Show, Eq)

io :: Th
io = Th (-1)

no :: Th
no = Th 0

(-:) :: Th -> Bool -> Th
Th th -: b = Th (2 * th + (if b then 1 else 0))

wk :: Th
wk = io -: False   -- a.k.a -2

me :: Th
me = no -: True

thun :: Th -> (Th, Bool)
thun (Th th) = case divMod th 2 of
  (th, r) -> (Th th, r /= 0)

instance Monoid Th where
  mempty = io
  mappend th ph
    | th == io = ph
    | ph == io = th
    | th == no = no
    | ph == no = no
    | otherwise = case thun ph of
      (ph, False) -> mappend th ph -: False
      (ph, True)  -> case thun th of
        (th, b) -> mappend th ph -: b

instance Semigroup Th where (<>) = mappend

combien :: Th -> Int -> Int
combien _  0 = 0
combien th m = case thun th of
  (th, b) -> combien th (m - 1) + (if b then 1 else 0)

cod :: Int -> Th
cod 0 = me
cod n = cod (n - 1) -: False

deb :: Th -> Int -- don't do this to no
deb th = case thun th of
  (th, True)  -> 0
  (th, False) -> deb th + 1

cop ::              Th {-i,m-}           -> Th {-j,m-}
    -> {-least n-} (Th {-i,n-}, Th {-n,m-}, Th {-j,n-})
cop th ph
  | th == io = (io, io, ph)
  | ph == io = (th, io, io)
  | th == no = (no, ph, io)
  | ph == no = (io, th, no)
  | otherwise = case (thun th, thun ph) of
    ((th, False), (ph, False)) -> case cop th ph of
      (th, ps, ph) -> (th, ps -: False, ph)
    ((th, a), (ph, b)) -> case cop th ph of
      (th, ps, ph) -> (th -: a, ps -: True, ph -: b)

relp :: (a, Th) -> (b, Th) -> ((a, Th), Th, (b, Th))
relp (a, th) (b, ph) = case cop th ph of
  (th, ps, ph) -> ((a, th), ps, (b, ph))

class Selects t where
  (<?) :: Th {-n,m-} -> t {-m-} -> t {-n-}

instance Selects (Bwd x) where
  th <? B0 = B0
  th <? (xz :< x) = case thun th of
    (th, b) -> (if b then (:< x) else id) (th <? xz)

class Thins t where
  (-^) :: t -> Th -> t

instance Thins Th where
  th -^ ph = th <> ph

instance Thins b => Thins (a, b) where (a, b) -^ th = (a, b -^ th)
instance Thins x => Thins (Bwd x) where xz -^ th = fmap (-^ th) xz
instance Thins x => Thins [x] where xz -^ th = fmap (-^ th) xz
instance Thins Int where
  i -^ th
    | th == io = i
    | th == no = error "thinning a variable with no"
    | otherwise = case thun th of
      (th, False) -> 1 + (i -^ th)
      (th, True)  -> if i == 0 then 0 else ((i - 1) -^ th) + 1

