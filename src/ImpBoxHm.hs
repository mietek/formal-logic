{-# LANGUAGE DataKinds
           , GADTs
           , KindSignatures
           , TypeOperators
           #-}

module ImpBoxHm where


infixr 5 :>>

data Proposition :: * where
  (:>>) :: Proposition -> Proposition -> Proposition
  BOX   :: Proposition -> Proposition


infixl 5 :<<

data Theorem :: Proposition -> * where
  (:<<) :: Theorem (a :>> b) -> Theorem a
        -> Theorem b
  K     :: Theorem (a :>> b :>> a)
  S     :: Theorem ((a :>> b :>> c) :>> (a :>> b) :>> a :>> c)
  Nec   :: Theorem a
        -> Theorem (BOX a)
  Refl  :: Theorem (BOX a :>> a)
  Trans :: Theorem (BOX a :>> BOX (BOX a))
  Norm  :: Theorem (BOX (a :>> b) :>> (BOX a :>> BOX b))


i :: Theorem (a :>> a)
i = (S :<< K) :<< K
