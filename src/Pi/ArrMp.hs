-- Minimal implicational logic, PHOAS approach, initial encoding

{-# LANGUAGE DataKinds, GADTs, KindSignatures, Rank2Types, Safe, TypeOperators #-}

module Pi.ArrMp where


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

infixl 1 :$
data Tm :: (Ty -> *) -> Ty -> * where
  Var  :: IsTrue a tc                -> Tm tc a
  Lam  :: (IsTrue a tc -> Tm tc b)   -> Tm tc (a :=> b)
  (:$) :: Tm tc (a :=> b) -> Tm tc a -> Tm tc b

var :: IsTrue a tc -> Tm tc a
var = Var

lam :: (Tm tc a -> Tm tc b) -> Tm tc (a :=> b)
lam f = Lam $ \x -> f (var x)

type Thm a = forall tc. Tm tc a


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
      lam $ \x -> f :$ x :$ (g :$ x)

tSKK :: Thm (a :=> a)
tSKK =
  aS :$ aK :$ aK
