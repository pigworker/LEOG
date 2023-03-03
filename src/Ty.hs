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

scop :: TC Int
scop = TC $ (Just . length)

norm :: (Tm d, Th) -> TC (Tm d, Th)
norm t = scop >>= \ m -> pure $ eval m (iden m) t

(//) :: (Tm d, Th){-n+1-} -> Comp{-n-} -> TC (Tm d, Th)
t // s = scop >>= \ m -> pure $ eval m (sben m s) t

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

isPi :: XTm Ch {-n-} -- presumed normalised
     -> Maybe (Term {-n-}, Term {-n+1-})
isPi (XC (A PI, _) st) | Just [sS, b] <- tup st, XB tT <- xt b = Just (sS, tT)
isPi _ = Nothing

ty :: Term -> TC ()
ty t | truce ("type " ++ show t) False = undefined
ty t = case xt t of
  XU _ -> pure ()
  x | Just (sS, tT) <- isPi x -> do
    ty sS
    sS !- ty tT
  XS e q -> do
    sS <- sy e
    sS <- tg sS q >>= norm
    case xt sS of
      XU _ -> pure ()
      _ -> barf
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
    sS <- sy e >>= norm
    case xt sS of
      x | Just (sS, tT) <- isPi x -> do
        ch sS s
        tT // (R % (s, sS))
      _ -> barf

tg :: Type -> Term -> TC Type
tg sS q | truce ("tg " ++ show sS ++ " " ++ show q) False = undefined
tg sS q = case xt q of
  XA NIL -> pure sS
  _ -> barf

ch :: Type -> Term -> TC ()
ch uU t | truce ("ch " ++ show uU ++ " " ++ show t) False = undefined
ch uU t = case xt t of
  XU v -> (xt <$> norm uU) >>= \case
    XU w | ltU v w -> pure ()
    _ -> barf
  x | Just (sS, tT) <- isPi x -> do
    uU <- norm uU
    case xt uU of
      XU Prop -> do
        ty sS
        sS !- ch uU tT
      XU u -> do
        ch uU sS
        sS !- ch uU tT
      _ -> barf
  XB t -> (xt <$> norm uU) >>= \case
    x | Just (sS, tT) <- isPi x -> sS !- ch tT t
    _ -> barf
  XS e q -> do
    sS <- sy e
    sS <- tg sS q
    cu sS uU
  _ -> barf

cu :: Type -> Type -> TC ()
cu sS tT | truce ("cu " ++ show sS ++ " " ++ show tT) False = undefined
cu sS tT = do
  sS <- norm sS
  tT <- norm tT
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
leU  _        _       = False

ltU :: U -> U -> Bool
ltU  Prop    (Type i) = 0 < i
ltU (Type i) (Type j) = i < j
ltU  _        _       = False

uq :: Type -> Type -> TC ()
uq aA bB | truce ("uq " ++ show aA ++ " " ++ show bB) False = undefined
uq aA bB = do
  aA <- norm aA  -- optimize another day
  bB <- norm bB
  case (xt aA, xt bB) of
    (XU v, XU w) | v == w -> pure ()
    (XS ea qa, XS eb qb) -> do
      sS <- sq ea eb
      aA <- tg sS qa
      bB <- tg sS qb
      uq aA bB
    _ -> barf

sq :: Comp -> Comp -> TC Type
sq ea eb | truce ("sq " ++ show ea ++ " " ++ show eb) False = undefined
sq ea eb = do
  ea <- norm ea
  eb <- norm eb
  case (xt ea, xt eb) of
    (XV i, XV j) | i == j -> ixty i
    _ -> barf
