{-# LANGUAGE LambdaCase, GADTs #-}

module Ty where

import Control.Monad

import Bwd
import Th
import Tm
import Va


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

norm :: Term -> TC Term
norm t = TC $ \ ga -> let m = length ga in
  Just $ eval m (iden m) t

barf :: TC a
barf = TC $ \ _ -> Nothing

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
ty t = case xt t of
  XU _ -> pure ()
  XC (A PI, _) st -> case tup st of
    Just [sS, tT] -> case xt tT of
      XB tT -> do
        ty sS
        sS !- ty tT
      _ -> barf
    _ -> barf
  XS e q -> do
    sS <- sy e
    tT <- eq sS q >>= norm
    case xt tT of
      XU _ -> pure ()
      _ -> barf
  _ -> barf

sy :: Comp -> TC Type
sy e = case xt e of
  XV i -> ixty i
  _ -> barf

eq :: Type -> Term -> TC Type
eq sS q = case xt q of
  XA NIL -> pure sS
  _ -> barf


