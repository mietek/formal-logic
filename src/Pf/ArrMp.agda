-- Minimal implicational logic, PHOAS approach, final encoding

module Pf.ArrMp where


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

TmRepr : Set1
TmRepr = Cx -> Ty -> Set

module ArrMp where
  record Tm (tr : TmRepr) : Set1 where
    infixl 1 _$_
    field
      var  : forall {tc a}   -> isTrue a tc               -> tr tc a
      lam' : forall {tc a b} -> (isTrue a tc -> tr tc b)  -> tr tc (a => b)
      _$_  : forall {tc a b} -> tr tc (a => b) -> tr tc a -> tr tc b

    lam'' : forall {tc a b} -> (tr tc a -> tr tc b) -> tr tc (a => b)
    lam'' f = lam' \x -> f (var x)

    syntax lam'' (\a -> b) = lam a => b
  open Tm {{...}} public

  Thm : Ty -> Set1
  Thm a = forall {tr tc} {{_ : Tm tr}} -> tr tc a
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
