-- Minimal implicational logic, vector-based de Bruijn approach, initial encoding

module Vi.ArrMp where

open import Lib using (Nat; suc; _+_; Fin; fin; Vec; _,_; proj; VMem; mem)


-- Types

infixr 0 _=>_
data Ty : Set where
  UNIT :             Ty
  _=>_ : Ty -> Ty -> Ty


-- Context and truth judgement

Cx : Nat -> Set
Cx n = Vec Ty n

isTrue : forall {tn} -> Ty -> Fin tn -> Cx tn -> Set
isTrue a i tc = VMem a i tc


-- Terms

module ArrMp where
  infixr 0 lam=>_
  infixl 1 _$_
  data Tm {tn} (tc : Cx tn) : Ty -> Set where
    var    : forall {a i} -> isTrue a i tc             -> Tm tc a
    lam=>_ : forall {a b} -> Tm (tc , a) b             -> Tm tc (a => b)
    _$_    : forall {a b} -> Tm tc (a => b) -> Tm tc a -> Tm tc b

  v : forall {tn} (k : Nat) {tc : Cx (suc (k + tn))} -> Tm tc (proj tc (fin k))
  v i = var (mem i)

  Thm : Ty -> Set
  Thm a = forall {tn} {tc : Cx tn} -> Tm tc a
open ArrMp public


-- Example theorems

aI : forall {a} -> Thm (a => a)
aI =
  lam=> v 0

aK : forall {a b} -> Thm (a => b => a)
aK =
  lam=>
    lam=> v 1

aS : forall {a b c} -> Thm ((a => b => c) => (a => b) => a => c)
aS =
  lam=>
    lam=>
      lam=> v 2 $ v 0 $ (v 1 $ v 0)

tSKK : forall {a} -> Thm (a => a)
tSKK {a = a} =
  aS {b = a => a} $ aK $ aK
