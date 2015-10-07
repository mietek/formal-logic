{-# LANGUAGE DataKinds, GADTs, KindSignatures, Rank2Types, Safe, TypeFamilies, TypeOperators #-}

module Lib where


-- Natural numbers

data Nat :: * where
  Zero ::        Nat
  Suc  :: Nat -> Nat


infixl 6 :+

type family (m :: Nat) :+ (n :: Nat) :: Nat
type instance Zero  :+ n = n
type instance Suc k :+ n = Suc (k :+ n)
