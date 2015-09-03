{-# LANGUAGE DataKinds
           , GADTs
           , KindSignatures
           , NoImplicitPrelude
           , Rank2Types
           , TypeOperators
           #-}

module ImpBoxNm where

import Prelude (($))


infixr 5 :>>

data Proposition :: * where
  (:>>) :: Proposition -> Proposition -> Proposition
  BOX   :: Proposition -> Proposition


data World :: * where
  First :: World
  Next  :: World

data Judgement :: * where
  True :: World -> Proposition -> Judgement

-- kind Context = Judgement -> *


infixl 5 :<<

data Term :: (Judgement -> *) -> World -> Proposition -> * where
  Var   :: cx (True w a)
        -> Term cx w a
  Lam   :: (cx (True w a) -> Term cx w b)
        -> Term cx w (a :>> b)
  (:<<) :: Term cx w (a :>> b) -> Term cx w a
        -> Term cx w b
  Box   :: Term cx (next w) a
        -> Term cx w (BOX a)
  Unbox :: Term cx w (BOX a) -> (cx (True v a) -> Term cx w b)
        -> Term cx w b

newtype Theorem a = T { term :: forall cx. forall w. Term cx w a }


i :: Theorem (a :>> a)
i = T $
  Lam $ \x -> Var x

k :: Theorem (a :>> b :>> a)
k = T $
  Lam $ \x ->
    Lam $ \_ -> Var x

s :: Theorem ((a :>> b :>> c) :>> (a :>> b) :>> a :>> c)
s = T $
  Lam $ \f ->
    Lam $ \g ->
      Lam $ \x -> (Var f :<< Var x) :<< (Var g :<< Var x)


trans :: Theorem (BOX a :>> BOX (BOX a))
trans = T $
  Lam $ \x' ->
    Unbox (Var x') $ \x ->
      Box (Box (Var x))

norm :: Theorem (BOX (a :>> b) :>> BOX a :>> BOX b)
norm = T $
  Lam $ \f' ->
    Lam $ \x' ->
      Unbox (Var f') $ \f ->
        Unbox (Var x') $ \x ->
          Box (Var f :<< Var x)
