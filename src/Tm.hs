{-# LANGUAGE DataKinds, GADTs, KindSignatures, StandaloneDeriving,
    PatternSynonyms, LambdaCase, PatternGuards, TypeFamilies #-}

module Tm where

import Th
import Bwd

-- directions are "checkable" and "synthesizable"
data Dir = Ch | Sy deriving (Show, Eq)

-- terms are free, checkable, codebruijn
type Term = (Tm Ch, Th)
-- computations are free, synthesizable, codebruijn
type Comp = (Tm Sy, Th)

data Tm (d :: Dir) :: * where
  A :: Atom -> Tm Ch {-0-}
  U :: U -> Tm Ch {-0-}
  B :: Sc {-n-} -> Tm Ch {-n-}
  V :: Tm Sy {-1-}
  P :: Pair a c -> (Tm a, Th) {-n-} -> (Tm Ch, Th) {-n-} -> Tm c {-n-}
    -- note that the left and right thinnings must constitute a covering
deriving instance Show (Tm d)

-- atoms are represented numerically
newtype Atom = N Int deriving (Show, Eq)
pattern NIL = N 0
pattern PI  = N 1

-- sorts are prop or type
data U = Prop | Type Int deriving (Show, Eq)

-- scopes are vacuous or otherwise
data Sc {-n-} :: * where
  K :: Tm Ch {-n-} -> Sc {-n-}
  L :: Tm Ch {-n+1-} -> Sc {-n-}
deriving instance Show Sc

-- valid forms of pairing
data Pair (a :: Dir)(c :: Dir) :: * where
  C :: Pair Ch Ch -- canonical form
  R :: Pair Ch Sy -- radical
  E :: Pair Sy Sy -- elimination
  S :: Pair Sy Ch -- syn coerced into chk by eq prf
deriving instance Show (Pair a c)

-- smart constructor for pairing
(%) :: Pair a c -> ((Tm a, Th) {-n-}, (Tm Ch, Th) {-n-}) -> (Tm c, Th) {-n-}
p % (s, t) = case relp s t of
  (s, ps, t) -> (P p s t, ps)

-- smart constructor for binding
bi :: Term {-n+1-} -> Term {-n-}
bi (t, Th th) = case divMod th 2 of
  (th, 0) -> (B (K t), Th th)
  (th, 1) -> (B (L t), Th th)

-- going under a binder
ib :: (Sc, Th) {-n-} -> Term {-n+1-}
ib (K t, th) = (t, th -: False)
ib (L t, th) = (t, th -: True)

-- a context is a backward list of types for vars with *all* in scope
type Cx = Bwd Term

-- if term is a right-nested nil-terminated tuple, make it a list
tup :: Term -> Maybe [Term]
tup (A NIL, _) = pure []
tup (P C s t, ps) = (-^ ps) <$> ((s :) <$> tup t)

list :: [Term] -> Term
list [] = (A NIL, no)
list (x : xs) = C % (x, list xs)

-- top-layer expansion
data XTm (d :: Dir) :: * where
  XA :: Atom -> XTm Ch {-n-}
  XU :: U -> XTm Ch {-n-}
  XB :: Term {-n+1-} -> XTm Ch {-n-}
  XC :: Term {-n-} -> Term {-n-} -> XTm Ch {-n-}
  XS :: Comp {-n-} -> Term {-n-} -> XTm Ch {-n-}
  XV :: Int {-<n-} -> XTm Sy {-n-}
  XE :: Comp {-n-} -> Term {-n-} -> XTm Sy {-n-}
  XR :: Term {-n-} -> Term {-n-} -> XTm Sy {-n-}  
deriving instance Show (XTm d)

xt :: (Tm d, Th) {-n-} -> XTm d
xt (t, th) = case t of
  A a     -> XA a
  U u     -> XU u
  B b     -> XB (ib (b, th))
  P C s t -> XC (s -^ th) (t -^ th)
  P S e q -> XS (e -^ th) (q -^ th)
  V       -> XV (deb th)
  P E e s -> XE (e -^ th) (s -^ th)
  P R t u -> XR (t -^ th) (u -^ th)

va :: Int -> Comp
va i = (V, cod i)
