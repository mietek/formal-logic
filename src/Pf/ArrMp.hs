-- Minimal implicational logic, PHOAS approach, final encoding

{-# LANGUAGE DataKinds, GADTs, KindSignatures, Rank2Types, Safe, TypeOperators #-}

module Pf.ArrMp where


-- Types

infixr 0 :=>
data Ty :: * where
  UNIT  ::             Ty
  (:=>) :: Ty -> Ty -> Ty


-- Context and truth judgement

-- NOTE: Haskell does not support kind synonyms
-- type Cx = Ty -> *

type IsTrue (a :: Ty) (tc :: Ty -> *) = tc a


-- Terms

-- type TmRepr :: (Ty -> *) -> Ty -> *

infixl 1 ..$
class ArrMpTm (tr :: (Ty -> *) -> Ty -> *) where
  var  :: IsTrue a tc                -> tr tc a
  lam' :: (IsTrue a tc -> tr tc b)   -> tr tc (a :=> b)
  (..$) :: tr tc (a :=> b) -> tr tc a -> tr tc b

lam :: ArrMpTm tr => (tr tc a -> tr tc b) -> tr tc (a :=> b)
lam f = lam' $ \x -> f (var x)

type Thm a = ArrMpTm tr => tr tc a


-- Example theorems

aI :: Thm (a :=> a)
aI =
  lam $ \x -> x

aK :: Thm (a :=> b :=> a)
aK =
  lam $ \x ->
    lam $ \_ -> x

aS :: Thm ((a :=> b :=> c) :=> (a :=> b) :=> a :=> c)
aS =
  lam $ \f ->
    lam $ \g ->
      lam $ \x -> f ..$ x ..$ (g ..$ x)

tSKK :: Thm (a :=> a)
tSKK =
  aS ..$ aK ..$ aK
