-- Minimal implicational modal logic, PHOAS approach, initial encoding

{-# LANGUAGE DataKinds, GADTs, KindSignatures, Rank2Types, Safe, TypeOperators #-}

module Pi.BoxMp where

import Lib (Nat (Suc))


-- Types

infixr 0 :=>
data Ty :: * where
  UNIT  ::             Ty
  (:=>) :: Ty -> Ty -> Ty
  BOX   :: Ty       -> Ty


-- Context and truth judgement with modal depth

-- NOTE: Haskell does not support kind synonyms
-- type Cx = Ty -> *

type IsTrue (a :: Ty) (d :: Nat) (tc :: Ty -> Nat -> *) = tc a d


-- Terms

infixl 1 ..$
data Tm :: Nat -> (Ty -> Nat -> *) -> Ty -> * where
  Var   :: IsTrue a d tc                  -> Tm d tc a
  Lam   :: (IsTrue a d tc -> Tm d tc b)   -> Tm d tc (a :=> b)
  App   :: Tm d tc (a :=> b) -> Tm d tc a -> Tm d tc b
  Box   :: Tm (Suc d) tc a                -> Tm d tc (BOX a)
  Unbox :: Tm d tc (BOX a)   -> (IsTrue a gd tc -> Tm d tc b) -> Tm d tc b

var :: IsTrue a d tc -> Tm d tc a
var = Var

lam :: (Tm d tc a -> Tm d tc b) -> Tm d tc (a :=> b)
lam f = Lam $ \x -> f (var x)

(..$) :: Tm d tc (a :=> b) -> Tm d tc a -> Tm d tc b
(..$) = App

box :: Tm (Suc d) tc a -> Tm d tc (BOX a)
box = Box

unbox :: Tm d tc (BOX a) -> (Tm gd tc a -> Tm d tc b) -> Tm d tc b
unbox x' f = Unbox x' $ \x -> f (var x)

type Thm a = forall d tc. Tm d tc a


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
