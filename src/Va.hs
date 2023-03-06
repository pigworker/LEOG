{-# LANGUAGE DataKinds, GADTs, KindSignatures, StandaloneDeriving,
    PatternSynonyms, LambdaCase, PatternGuards #-}

module Va where

import Bwd
import Th
import Tm
import Control.Arrow ((***), first, second)

import Debug.Trace
track = const id

tyev :: Bwd {-m-} Type{-m-}           -- cx
     -> Type {-m-}                    -- type over cx
     -> Type {-m-}                    -- type, normalised
tyev de (u, th) = chev de (th <? cxen de) (U TYPE, no) u

chev :: Bwd {-m-} Type{-m-}           -- trg cx
     -> Bwd {-n-} (Comp, Type){-m-}   -- src var vals & types over trg cx
     -> Type {-m-}                    -- type over trg cx
     -> Tm Ch {-n-}                   -- src tm
     -> Term{-m-}                     -- trg val
-- if it's an embedded computation, synthesize and ship
chev de ga v (P S (e, th) (q, ph)) = case evsy de (th <? ga) e of
  (e, u) -> case chev de (ph <? ga) (qTy u v) q of
    q -> ship de e u q v
chev de ga _ (U u) = (U u, no)
-- otherwise, it's canonical and should have a canonical type
chev de ga u t = case tyev de u of
  u -> case (xt u, t) of
    (XU _, x)
      | Just ((sS, th), (tT, ph)) <- isPi (xt (x, io)) ->
        case chev de (th <? ga) u sS of
          sS -> case chev ((de :< sS) -^ wk) (ph <? wken ga sS) u tT of
            tT -> pI sS tT
      | Just [(A IRR, _), (pP, th)] <- tup (x, io) ->
        case chev de (th <? ga) (A IRR, no) pP of
          pP -> irr pP
      | A IRR <- t -> (A IRR, no)
    (x, B b) | Just (sS, tT) <- isPi x -> case ib (b, io) of
      (b, th) -> bi (chev ((de :< sS) -^ wk) (th <? wken ga sS) tT b)
    (XA IRR, t)
      | Just [(A QQ, _), (sS, th), (tT, ph)] <- tup (t, io) ->
          list [(A QQ, no), chev de (th <? ga) (U TYPE, no) sS
                          , chev de (ph <? ga) (U TYPE, no) tT]
    _ | Just [(A IRR, _), pP] <- tup u
      , Just [(A QQ, _), _, _] <- tup pP
      , A NIL <- t
      -> (A NIL, no)
    z -> error (show z)

evsy :: Bwd {-m-} Type{-m-}           -- trg cx
     -> Bwd {-n-} (Comp, Type){-m-}
     -> Tm Sy {-n-}
     -> (Comp, Type){-m-} 
evsy de (B0 :< eS) V = eS
evsy de ga (P R (t, th) (u, ph)) = case chev de (ph <? ga) (U TYPE, no) u of
  u -> case chev de (th <? ga) u t of
    t -> (R % (t, u), u)
evsy de ga (P E (e, th) (s, ph)) = case evsy de (th <? ga) e of
  (e, u) -> case tyev de u of
    u -> case xt u of
      x | Just (sS, (tT, ch)) <- isPi x ->
        case chev de (ph <? ga) sS s of
          s -> case cxen de :< (R % (s, sS), sS) of
            ga -> case chev de (ch <? ga) (U TYPE, no) tT of
              tT -> case xt e of
                XR f _ | XB (t, ps) <- xt f -> case chev de (ps <? ga) tT t of
                  t -> (R % (t, tT), tT)
                _ -> (E % (e, s), tT)
evsy de ga e = error (show (ga, e))

ship :: Bwd {-m-} Type{-m-}           -- cx
     -> Comp {-m-} -- what to ship
     -> Type {-m-} -- source type (normal)
     -> Term {-m-} -- path
     -> Type {-m-} -- target type (normal)
     -> Term {-m-} -- result
ship de e u (A NIL, _) v | XR t _ <- xt e = t
ship de e _ q _ = S % (e, q)




wken :: Bwd {-n-} (Comp, Type){-m-}
     -> Type {-m-}
     -> Bwd {-n+1-} (Comp, Type){-m+1-}
wken ga sS = (((-^ wk) *** (-^ wk)) <$> ga) :< ((V, me), sS -^ wk)

cxen :: Bwd {-n-} Type{-m-}              -- cx
     -> Bwd {-n-} (Comp{-n-}, Type{-m-}) -- identity environment on cx
cxen     B0    =                             B0
cxen (ga :< s) = (first (-^ wk) <$> cxen ga) :< ((V, me), s)


--

pidty :: U -> Term {-0-}
pidty u =
  list [(A PI, no), (U u, no), bi $
    list [(A PI, no), (S % (va 0, (A NIL, no))), bi (S % (va 1, (A NIL, no)))
  ] ]
   

pidfu :: Term {-0-}
pidfu = bi (bi (S % (va 0, (A NIL, no))))

ptest :: U -> Comp {-0-}
ptest u =
  E % ( E % ( R % (pidfu, pidty u)
            , pidty (Type 0)
            )
      , pidfu
      )