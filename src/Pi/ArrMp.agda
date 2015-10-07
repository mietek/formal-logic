-- Minimal implicational logic, PHOAS approach, initial encoding

module Pi.ArrMp where


-- Types

infixr 0 _=>_
data Ty : Set where
  UNIT :             Ty
  _=>_ : Ty -> Ty -> Ty


-- Context and truth judgement

Cx : Set1
Cx = Ty -> Set

isTrue : Ty -> Cx -> Set
isTrue a tc = tc a


-- Terms

module ArrMp where
  infixl 1 _$_
  data Tm (tc : Cx) : Ty -> Set where
    var  : forall {a}   -> isTrue a tc               -> Tm tc a
    lam' : forall {a b} -> (isTrue a tc -> Tm tc b)  -> Tm tc (a => b)
    _$_  : forall {a b} -> Tm tc (a => b) -> Tm tc a -> Tm tc b

  lam'' : forall {tc a b} -> (Tm tc a -> Tm tc b) -> Tm tc (a => b)
  lam'' f = lam' \x -> f (var x)

  syntax lam'' (\a -> b) = lam a => b

  Thm : Ty -> Set1
  Thm a = forall {tc} -> Tm tc a
open ArrMp public


-- Example theorems

aI : forall {a} -> Thm (a => a)
aI =
  lam x => x

aK : forall {a b} -> Thm (a => b => a)
aK =
  lam x =>
    lam _ => x

aS : forall {a b c} -> Thm ((a => b => c) => (a => b) => a => c)
aS =
  lam f =>
    lam g =>
      lam x => f $ x $ (g $ x)

tSKK : forall {a} -> Thm (a => a)
tSKK {a = a} =
  aS {b = a => a} $ aK $ aK
