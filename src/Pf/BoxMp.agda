-- Minimal implicational modal logic, PHOAS approach, final encoding

module Pf.BoxMp where

open import Lib using (Nat; suc)


-- Types

infixr 0 _=>_
data Ty : Set where
  UNIT :             Ty
  _=>_ : Ty -> Ty -> Ty
  BOX  : Ty       -> Ty


-- Context and truth judgement with modal depth

Cx : Set1
Cx = Ty -> Nat -> Set

isTrue : Ty -> Nat -> Cx -> Set
isTrue a d tc = tc a d


-- Terms

TmRepr : Set1
TmRepr = Nat -> Cx -> Ty -> Set

module ArrMp where
  record Tm (tr : TmRepr) : Set1 where
    infixl 1 _$_
    field
      var  : forall {d tc a}   -> isTrue a d tc                 -> tr d tc a
      lam' : forall {d tc a b} -> (isTrue a d tc -> tr d tc b)  -> tr d tc (a => b)
      _$_  : forall {d tc a b} -> tr d tc (a => b) -> tr d tc a -> tr d tc b

    lam'' : forall {d tc a b} -> (tr d tc a -> tr d tc b) -> tr d tc (a => b)
    lam'' f = lam' \x -> f (var x)

    syntax lam'' (\a -> b) = lam a => b
  open Tm {{...}} public

module BoxMp where
  record Tm (tr : TmRepr) : Set1 where
    field
      box    : forall {d tc a}      -> tr (suc d) tc a          -> tr d tc (BOX a)
      unbox' : forall {d >d tc a b} -> tr d tc (BOX a) -> (isTrue a >d tc -> tr d tc b) -> tr d tc b

      isArrMp : ArrMp.Tm tr
    open ArrMp.Tm isArrMp public

    unbox'' : forall {d >d tc a b} -> tr d tc (BOX a) -> (tr >d tc a -> tr d tc b) -> tr d tc b
    unbox'' x' f = unbox' x' \x -> f (var x)

    syntax unbox'' x' (\x -> y) = unbox x' as x => y
  open Tm {{...}} public

  Thm : Ty -> Set1
  Thm a = forall {tr d tc} {{_ : Tm tr}} -> tr d tc a
open BoxMp public


-- Example theorems

rNec : forall {a} -> Thm a -> Thm (BOX a)
rNec x =
  box x

aK : forall {a b} -> Thm (BOX (a => b) => BOX a => BOX b)
aK =
  lam f' =>
    lam x' =>
      unbox f' as f =>
        unbox x' as x =>
          box (f $ x)

aT : forall {a} -> Thm (BOX a => a)
aT =
  lam x' =>
    unbox x' as x => x

a4 : forall {a} -> Thm (BOX a => BOX (BOX a))
a4 =
  lam x' =>
    unbox x' as x => box (box x)

t1 : forall {a} -> Thm (a => BOX (a => a))
t1 =
  lam _ => box (lam y => y)
