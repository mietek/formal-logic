{-# LANGUAGE DataKinds
           , GADTs
           , KindSignatures
           , TypeOperators
           #-}

module ImpHm where


infixr 5 :>>

data Proposition :: * where
  (:>>) :: Proposition -> Proposition -> Proposition


infixl 5 :<<

data Theorem :: Proposition -> * where
  (:<<) :: Theorem (a :>> b) -> Theorem a
        -> Theorem b
  K     :: Theorem (a :>> b :>> a)
  S     :: Theorem ((a :>> b :>> c) :>> (a :>> b) :>> a :>> c)


i :: Theorem (a :>> a)
i = (S :<< K) :<< K
