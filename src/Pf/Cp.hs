-- Classical propositional logic, PHOAS approach, final encoding

{-# LANGUAGE DataKinds, GADTs, KindSignatures, Rank2Types, Safe, TypeOperators #-}

module Pf.Cp where


-- Types

infixl 2 :&&
infixl 1 :||
infixr 0 :=>
data Ty :: * where
  UNIT  ::             Ty
  (:=>) :: Ty -> Ty -> Ty
  (:&&) :: Ty -> Ty -> Ty
  (:||) :: Ty -> Ty -> Ty
  FALSE ::             Ty

infixr 0 :<=>
type a :<=> b = (a :=> b) :&& (b :=> a)

type NOT a = a :=> FALSE

type TRUE = FALSE :=> FALSE


-- Context and truth judgement

-- NOTE: Haskell does not support kind synonyms
-- type Cx = Ty -> *

type IsTrue (a :: Ty) (tc :: Ty -> *) = tc a


-- Terms

infixl 1 .$
class ArrMpTm (tr :: (Ty -> *) -> Ty -> *) where
  var  :: IsTrue a tc                -> tr tc a
  lam' :: (IsTrue a tc -> tr tc b)   -> tr tc (a :=> b)
  (.$) :: tr tc (a :=> b) -> tr tc a -> tr tc b

lam :: ArrMpTm tr => (tr tc a -> tr tc b) -> tr tc (a :=> b)
lam f = lam' $ \x -> f (var x)

class ArrMpTm tr => MpTm (tr :: (Ty -> *) -> Ty -> *) where
  pair'  :: tr tc a         -> tr tc b -> tr tc (a :&& b)
  fst'   :: tr tc (a :&& b)            -> tr tc a
  snd'   :: tr tc (a :&& b)            -> tr tc b
  left   :: tr tc a                    -> tr tc (a :|| b)
  right  :: tr tc b                    -> tr tc (a :|| b)
  case'' :: tr tc (a :|| b) -> (IsTrue a tc -> tr tc c) -> (IsTrue b tc -> tr tc c) -> tr tc c

pair :: MpTm tr => (tr tc a, tr tc b) -> tr tc (a :&& b)
pair (a, b) = pair' a b

case' :: MpTm tr => tr tc (a :|| b) -> (tr tc a -> tr tc c) -> (tr tc b -> tr tc c) -> tr tc c
case' xy f g = case'' xy (\x -> f (var x)) (\y -> g (var y))

class MpTm tr => CpTm (tr :: (Ty -> *) -> Ty -> *) where
  abort' :: (IsTrue (NOT a) tc -> tr tc FALSE) -> tr tc a

abort :: CpTm tr => (tr tc (NOT a) -> tr tc FALSE) -> tr tc a
abort f = abort' $ \na -> f (var na)

type Thm a = CpTm tr => tr tc a
