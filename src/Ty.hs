{-# LANGUAGE LambdaCase, GADTs, PatternGuards, DataKinds #-}

module Ty where

import Control.Monad

import Bwd
import Th
import Tm
import Va

import Debug.Trace
truce = const id

------------------------------------------------------------------------------
-- the monad of knowing the types of the free variables and sometimes barfing
------------------------------------------------------------------------------

-- a context is a snoc-list of types for the variables in scope
-- those types are scoped over the whole context, ready for lookup
type Cx = Bwd Type

newtype TC x = TC {tc :: Cx -> Maybe x}
instance Monad TC where
  return x = TC $ \ _ -> Just x
  TC a >>= k = TC $ \ ga -> a ga >>= \ a -> tc (k a) ga
instance Applicative TC where pure = return; (<*>) = ap
instance Functor TC where fmap = ap . return

-- de Bruijn index range errors are not to be confused with type errors
ixty :: Int -> TC Term
ixty i = TC $ \ ga -> Just (ga <! i)

nmTy :: Type {-ga-} -> TC Type {-ga-}
nmTy tT = TC $ \ ga -> Just (tyev ga tT)

nmTm :: Type {-ga-} -> Term {-ga-} -> TC Term {-ga-}
nmTm tT (t, th) = TC $ \ ga -> Just (chev ga (th <? cxen ga) tT t)

nmCo :: Comp {-ga-} -> TC (Comp, Type) {-ga-}
nmCo (e, th) = TC $ \ ga -> Just (evsy ga (th <? cxen ga) e)

(//) :: Type{-n+1-} -> (Comp, Type){-n-} -> TC Type{-n-}
(tT, th) // s = TC $ \ ga ->
  pure (chev ga (th <? (cxen ga :< s)) (U TYPE, no) tT)

barf :: TC a
barf = TC $ \ _ -> Nothing

must :: Maybe x -> TC x
must (Just x) = pure x
must Nothing  = barf

class Discharge t where
  discharge :: Type {-n-}  -- type of bound variable
            -> t {-n+1-}   -- thing under binding
            -> t {-n-}     -- thing pulled out from under

instance Discharge () where
  discharge _ _ = ()

instance Discharge Term where
  discharge _ = bi

(!-) :: Discharge t => Type {-n-} -> TC t {-n+1-} -> TC t {-n-}
sS !- TC f = TC $ \ ga -> case f ((ga :< sS) -^ wk) of
  Nothing -> Nothing
  Just t -> Just (discharge sS t)

closed :: TC t {-0-} -> Maybe t
closed (TC f) = f B0


------------------------------------------------------------------------------
-- check some types?
------------------------------------------------------------------------------

ty :: Term -> TC ()
ty = ch (U TYPE, no)

ch :: Type -> Term -> TC ()
ch uU t | truce ("ch " ++ show uU ++ " " ++ show t) False = undefined
ch uU t = case xt t of
  XU v -> (xt <$> nmTy uU) >>= \case
    XU w | ltU v w -> pure ()
    _ -> barf
  x | Just (sS, tT) <- isPi x -> do
    uU <- nmTy uU
    case xt uU of
      XU Prop -> do
        ty sS
        sS !- ch uU tT
      XU _ -> do
        ch uU sS
        sS !- ch uU tT
      _ -> barf
  XB t -> (xt <$> nmTy uU) >>= \case
    x | Just (sS, tT) <- isPi x -> sS !- ch tT t
    _ -> barf
  XS e q -> do
    sS <- sy e
    sS <- tg sS q
    cu sS uU
  _ -> barf

sy :: Comp -> TC Type
sy e | truce ("sy " ++ show e) False = undefined
sy e = case xt e of
  XV i -> ixty i
  XR t tT -> do
    ty tT
    ch tT t
    pure tT
  XE e s -> do
    sS <- sy e >>= nmTy
    case xt sS of
      x | Just (sS, tT) <- isPi x -> do
        ch sS s
        tT // ((R % (s, sS)), sS)
      _ -> barf

tg :: Type -> Term -> TC Type
tg sS q | truce ("tg " ++ show sS ++ " " ++ show q) False = undefined
tg sS q = case xt q of
  XA NIL -> pure sS
  _ -> barf

cu :: Type -> Type -> TC ()
cu sS tT | truce ("cu " ++ show sS ++ " " ++ show tT) False = undefined
cu sS tT = do
  sS <- nmTy sS
  tT <- nmTy tT
  case (xt sS, xt tT) of
    (XU v, XU w) | leU v w -> pure ()
    (XC (A PI, _) st0, XC (A PI, _) st1)
      | (Just [sS0, b0], Just [sS1, b1]) <- (tup st0, tup st1)
      , (XB tT0, XB tT1) <- (xt b0, xt b1)
      -> do
        cu sS1 sS0
        sS1 !- cu tT0 tT1
    _ -> uq sS tT

leU :: U -> U -> Bool
leU  Prop     Prop    = True
leU  Prop    (Type i) = 0 < i
leU (Type i) (Type j) = i <= j
leU  _        TYPE    = True
leU  _        _       = False

ltU :: U -> U -> Bool
ltU  Prop    (Type i) = 0 < i
ltU (Type i) (Type j) = i < j
ltU  TYPE     _       = False
ltU  _        TYPE    = True
ltU  _        _       = False

uq :: Type -> Type -> TC ()
uq aA bB | truce ("uq " ++ show aA ++ " " ++ show bB) False = undefined
uq aA bB = do
  aA <- nmTy aA  -- optimize another day
  bB <- nmTy bB
  case (xt aA, xt bB) of
    (XU v, XU w) | v == w -> pure ()
    (a, b) | Just (aS, aT) <- isPi a, Just (bS, bT) <- isPi b -> do
      uq aS bS
      aS !- uq aT bT
    (XS ea qa, XS eb qb) -> do
      sS <- sq ea eb
      aA <- tg sS qa
      bB <- tg sS qb
      uq aA bB
    _ -> barf

sq :: Comp -> Comp -> TC Type
sq ea eb | truce ("sq " ++ show ea ++ " " ++ show eb) False = undefined
sq ea eb = do
  ea <- fst <$> nmCo ea
  eb <- fst <$> nmCo eb
  case (xt ea, xt eb) of
    (XV i, XV j) | i == j -> ixty i
    (XR at aT, XR bt bT) -> do
      uq aT bT
      cq aT at bt
      pure aT
    (XE ea sa, XE eb sb) -> do
      sS <- sq ea eb >>= nmTy
      case xt sS of
        x | Just (sS, tT) <- isPi x -> do
          cq sS sa sb
          tT // (R % (sa, sS), sS)
        _ -> barf
    _ -> barf

cq :: Type -> Term -> Term -> TC ()
cq uU a b = do
  uU <- nmTy uU
  a <- nmTm uU a
  b <- nmTm uU b
  case xt uU of
    XU _ -> uq a b
    x | Just (sS, tT) <- isPi x -> sS !- do
      let test f = E % ((R % (f, uU)) -^ wk, S % ((V, me), (A NIL, no)))
      sq (test a) (test b)
      pure ()
    _ -> case (xt a, xt b) of
      (XS ea (A NIL, _), XS eb (A NIL, _)) -> do
        sq ea eb
        pure ()
      _ -> barf
