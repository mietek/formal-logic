{-# LANGUAGE DataKinds
           , GADTs
           , KindSignatures
           , NoImplicitPrelude
           , Rank2Types
           , TypeOperators
           #-}

module ImpNm where

import Prelude (($))


infixr 5 :>>

data Proposition :: * where
  (:>>) :: Proposition -> Proposition -> Proposition


data Judgement :: * where
  True :: Proposition -> Judgement

-- kind Context = Judgement -> *


infixl 5 :<<

data Term :: (Judgement -> *) -> Proposition -> * where
  Var   :: cx (True a)
        -> Term cx a
  Lam   :: (cx (True a) -> Term cx b)
        -> Term cx (a :>> b)
  (:<<) :: Term cx (a :>> b) -> Term cx a
        -> Term cx b

newtype Theorem a = T { term :: forall cx. Term cx a }


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
