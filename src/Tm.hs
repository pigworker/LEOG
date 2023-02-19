{-# LANGUAGE DataKinds, GADTs, KindSignatures, StandaloneDeriving,
    PatternSynonyms, LambdaCase #-}

module Tm where

import Th
import Bwd

type Term = (Tm Chk, Th)

newtype Atom = N Int deriving (Show, Eq)
pattern NIL = N 0
pattern PI  = N 1

data Dir = Chk | Syn deriving (Show, Eq)

data Tm (d :: Dir) :: * where
  A :: Atom -> Tm Chk
  U :: Int -> Tm Chk
  B :: Sco -> Tm Chk
  V :: Tm Syn
  P :: (Tm a, Th) -> Pair a b c -> (Tm b, Th) -> Tm c
deriving instance Show (Tm d)

data Sco
  = K (Tm Chk)
  | L (Tm Chk)
  deriving Show

data Pair (a :: Dir)(b :: Dir)(c :: Dir) :: * where
  C :: Pair Chk Chk Chk
  R :: Pair Chk Chk Syn
  E :: Pair Syn Chk Syn
  S :: Pair Syn Chk Chk
deriving instance Show (Pair a b c)

(%) :: Pair a b c -> ((Tm a, Th), (Tm b, Th)) -> (Tm c, Th)
p % ((s, th), (t, ph)) = case cop th ph of
  (th, ps, ph) -> (P (s, th) p (t, ph), ps)

bi :: Term -> Term
bi (t, Th th) = case divMod th 2 of
  (th, 0) -> (B (K t), Th th)
  (th, 1) -> (B (L t), Th th)

ib :: Sco -> Th -> Term
ib (K t) th = (t, th -: False)
ib (L t) th = (t, th -: True)

type Cx = Bwd Term

tup :: Term -> Maybe [Term]
tup (A NIL, _) = pure []
tup (P s C t, ps) = (-^ ps) <$> ((s :) <$> tup t)

ty :: Cx -> Term -> Maybe ()
ty _ (U _, _) = pure ()
ty ga (P e S q, ps) = do
  u <- syn ga (e -^ ps)
  qs ga u q
ty ga t = tup t >>= \case
  [(A PI, _), s, (B t, ph)] -> do
    ty ga s
    ty ((ga :< s) -^ wk) (ib t ph)
  _ -> Nothing

qs :: Cx -> Term -> Term -> Maybe ()
qs ga (U _, _) (A NIL, _) = pure ()
qs _ _ _ = Nothing

syn :: Cx -> (Tm Syn, Th) -> Maybe Term
syn ga (V, th) = case th <? ga of
  _ :< s -> pure s
syn ga (P t R u, ps) = do
  u <- pure (u -^ ps)
  t <- pure (t -^ ps)
  ty ga u
  chk ga u t
  pure t
syn _ _ = Nothing

chk :: Cx -> Term -> Term -> Maybe ()
chk ga _ _ = Nothing
