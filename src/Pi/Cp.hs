-- Classical propositional logic, PHOAS approach, initial encoding

{-# LANGUAGE DataKinds, GADTs, KindSignatures, Rank2Types, Safe, TypeOperators #-}

module Pi.Cp where


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

infixl 1 :$
data Tm :: (Ty -> *) -> Ty -> * where
  Var    :: IsTrue a tc                -> Tm tc a
  Lam    :: (IsTrue a tc -> Tm tc b)   -> Tm tc (a :=> b)
  (:$)   :: Tm tc (a :=> b) -> Tm tc a -> Tm tc b
  Pair   :: Tm tc a         -> Tm tc b -> Tm tc (a :&& b)
  Fst    :: Tm tc (a :&& b)            -> Tm tc a
  Snd    :: Tm tc (a :&& b)            -> Tm tc b
  Left'  :: Tm tc a                    -> Tm tc (a :|| b)
  Right' :: Tm tc b                    -> Tm tc (a :|| b)
  Match  :: Tm tc (a :|| b) -> (IsTrue a tc -> Tm tc c) -> (IsTrue b tc -> Tm tc c) -> Tm tc c
  Abort  :: (IsTrue (NOT a) tc -> Tm tc FALSE) -> Tm tc a

var :: IsTrue a tc -> Tm tc a
var = Var

lam :: (Tm tc a -> Tm tc b) -> Tm tc (a :=> b)
lam f = Lam $ \x -> f (var x)

pair :: (Tm tc a, Tm tc b) -> Tm tc (a :&& b)
pair (a, b) = Pair a b

fst' :: Tm tc (a :&& b) -> Tm tc a
fst' = Fst

snd' :: Tm tc (a :&& b) -> Tm tc b
snd' = Snd

left :: Tm tc a -> Tm tc (a :|| b)
left = Left'

right :: Tm tc b -> Tm tc (a :|| b)
right = Right'

case' :: Tm tc (a :|| b) -> (Tm tc a -> Tm tc c) -> (Tm tc b -> Tm tc c) -> Tm tc c
case' xy f g = Match xy (\x -> f (var x)) (\y -> g (var y))

abort :: (Tm tc (NOT a) -> Tm tc FALSE) -> Tm tc a
abort f = Abort $ \na -> f (var na)

type Thm a = forall tc. Tm tc a
