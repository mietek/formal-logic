-- Minimal implicational modal logic, PHOAS approach, final encoding

{-# LANGUAGE DataKinds, GADTs, KindSignatures, Rank2Types, Safe, TypeOperators #-}

module Pf.BoxMp where

import Lib (Nat (Suc))


-- Types

infixr 0 :=>
data Ty :: * where
  UNIT  ::             Ty
  (:=>) :: Ty -> Ty -> Ty
  BOX   :: Ty       -> Ty


-- Context and truth judgement with modal depth

-- NOTE: Haskell does not support kind synonyms
-- type Cx = Ty -> Nat -> *

type IsTrue (a :: Ty) (d :: Nat) (tc :: Ty -> Nat -> *) = tc a d


-- Terms

infixl 1 ..$
class ArrMpTm (tr :: Nat -> (Ty -> Nat -> *) -> Ty -> *) where
  var  :: IsTrue a d tc                  -> tr d tc a
  lam' :: (IsTrue a d tc -> tr d tc b)   -> tr d tc (a :=> b)
  (..$) :: tr d tc (a :=> b) -> tr d tc a -> tr d tc b

lam :: ArrMpTm tr => (tr d tc a -> tr d tc b) -> tr d tc (a :=> b)
lam f = lam' $ \x -> f (var x)

class ArrMpTm tr => BoxMpTm (tr :: Nat -> (Ty -> Nat -> *) -> Ty -> *) where
  box    :: tr (Suc d) tc a -> tr d tc (BOX a)
  unbox' :: tr d tc (BOX a) -> (IsTrue a gd tc -> tr d tc b) -> tr d tc b

unbox :: BoxMpTm tr => tr d tc (BOX a) -> (tr gd tc a -> tr d tc b) -> tr d tc b
unbox x' f = unbox' x' $ \x -> f (var x)

type Thm a = BoxMpTm tr => tr d tc a


-- Example theorems

rNec :: Thm a -> Thm (BOX a)
rNec x =
  box x

aK :: Thm (BOX (a :=> b) :=> BOX a :=> BOX b)
aK =
  lam $ \f' ->
    lam $ \x' ->
      unbox f' $ \f ->
        unbox x' $ \x -> box (f ..$ x)

aT :: Thm (BOX a :=> a)
aT =
  lam $ \x' ->
    unbox x' $ \x -> x

a4 :: Thm (BOX a :=> BOX (BOX a))
a4 =
  lam $ \x' ->
    unbox x' $ \x -> box (box x)

t1 :: Thm (a :=> BOX (a :=> a))
t1 =
  lam $ \_ -> box (lam $ \y -> y)
