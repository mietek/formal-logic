-- Minimal implicational modal logic, PHOAS approach, initial encoding

module Pi.BoxMp where

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

module BoxMp where
  infixl 1 _$_
  data Tm (d : Nat) (tc : Cx) : Ty -> Set where
    var    : forall {a}      -> isTrue a d tc                 -> Tm d tc a
    lam'   : forall {a b}    -> (isTrue a d tc -> Tm d tc b)  -> Tm d tc (a => b)
    _$_    : forall {a b}    -> Tm d tc (a => b) -> Tm d tc a -> Tm d tc b
    box    : forall {a}      -> Tm (suc d) tc a               -> Tm d tc (BOX a)
    unbox' : forall {>d a b} -> Tm d tc (BOX a)  -> (isTrue a >d tc -> Tm d tc b) -> Tm d tc b

  lam'' : forall {d tc a b} -> (Tm d tc a -> Tm d tc b) -> Tm d tc (a => b)
  lam'' f = lam' \x -> f (var x)

  unbox'' : forall {d >d tc a b} -> Tm d tc (BOX a) -> (Tm >d tc a -> Tm d tc b) -> Tm d tc b
  unbox'' x f = unbox' x \y -> f (var y)

  syntax lam''   (\a -> b)    = lam a => b
  syntax unbox'' x' (\x -> y) = unbox x' as x => y

  Thm : Ty -> Set1
  Thm a = forall {d tc} -> Tm d tc a
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
