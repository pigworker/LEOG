{-# LANGUAGE DataKinds, GADTs, KindSignatures, StandaloneDeriving,
    PatternSynonyms, LambdaCase, PatternGuards #-}

module Va where

import Bwd
import Th
import Tm
import Control.Arrow ((***), first, second)

import Debug.Trace
track = const id

eval :: {-m-}Int -> En {-n,m-} -> (Tm d, Th){-n-} -> (Tm d, Th) {-m-}
eval m rh (t, th) = case th ^% rh of
  (rh, th) -> ev (combien th m) rh t -^ th

ev :: {-m-}Int -> En {-n,m-} -> Tm d {-n-} -> (Tm d, Th) {-m-}
ev m rh t
  | track (concat ["ev: ", show m, " ", show rh, " ", show t]) False
  = undefined
ev m E0 (A a)     = (A a, no)
ev m E0 (U u)     = (U u, no)
ev m rh (B (K t)) = first (B . K) (ev m rh t)
ev m rh (B (L t)) = bi (ev (m + 1) (wken rh) t)
ev m rh  V        = case rh{-1,m-} of
  ((E0, _) :& v{-m-}) -> v{-m-}
ev m rh (P p l r) = case (p, eval m rh l, eval m rh r) of
  (C, l, r) -> C % (l, r)
  (R, l, r) -> R % (l, r)
  (E, l, r) -> elim m l r
  (S, l, r) -> ship m l r

elim :: {-m-}Int -> Comp {-m-} -> Term {-m-} -> Comp {-m-}
elim m e s | XR f u <- xt e = case tup u of
  Just [(A PI, _), sS, x] | XB tT <- xt x, XB t <- xt f ->
    eval m (sben m (R % (s, sS))) (R % (t, tT))
  _ -> E % (e, s)
elim _ e s = E % (e, s)

ship :: {-m-}Int -> Comp {-m-} -> Term {-m-} -> Term {-m-}
ship m e q = case (xt e, xt q) of
  (XR t u, XA NIL) -> t
  _ -> S % (e, q)

-- environments
data En
  = E0 {-0,0-}
  | (En, Th){-m,n-} :& Comp{-n-} -- {-m+1,n-}
  deriving Show

sben :: {-m-}Int -> Comp{-m-} -> En {-m+1,m-}
sben m e = (iden m, io) :& e

wken :: En {-n,m-} -> En {-n+1,m+1-}
wken rh = (rh, wk) :& (V, me)

iden :: {-m-}Int -> En {-m,m-}
iden 0 = E0
iden m = wken (iden (m - 1))

(^%) :: Th {-n,m-} -> En {-m,m'-} -> {-exists n'-} (En {-n,n'-}, Th {-n',m'-})
th ^% E0 = (E0, no)
th ^% ((rh, ph0) :& (c, ph1)) = case thun th of
  (th, False) -> case th ^% rh of
    (rh, th) -> (rh, th -^ ph0)
  (th, True)  -> case th ^% rh of
    (rh, th) -> case cop (th -^ ph0) ph1 of
      (ph0, ps, ph1) -> ((rh, ph0) :& (c, ph1), ps)

--

pidty :: Term {-0-}
pidty = list [(A PI, no), (U (Type 0), no), bi $
          list [(A PI, no), (S % (va 0, (A NIL, no))), bi (S % (va 1, (A NIL, no)))
          ]
        ]

pidfu :: Term {-0-}
pidfu = bi (bi (S % (va 0, (A NIL, no))))

ptest :: Comp {-0-}
ptest = E % ( E % ( R % (pidfu, pidty)
                  , pidty
                  )
            , pidfu
            )