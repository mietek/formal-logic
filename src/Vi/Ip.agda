-- Intuitionistic propositional logic, vector-based de Bruijn approach, initial encoding

module Vi.Ip where

open import Lib using (Nat; suc; _+_; Fin; fin; Vec; _,_; proj; VMem; mem)


-- Types

infixl 2 _&&_
infixl 1 _||_
infixr 0 _=>_
data Ty : Set where
  UNIT  :             Ty
  _=>_  : Ty -> Ty -> Ty
  _&&_  : Ty -> Ty -> Ty
  _||_  : Ty -> Ty -> Ty
  FALSE :             Ty

infixr 0 _<=>_
_<=>_ : Ty -> Ty -> Ty
a <=> b = (a => b) && (b => a)

NOT : Ty -> Ty
NOT a = a => FALSE

TRUE : Ty
TRUE = FALSE => FALSE


-- Context and truth judgement

Cx : Nat -> Set
Cx n = Vec Ty n

isTrue : forall {tn} -> Ty -> Fin tn -> Cx tn -> Set
isTrue a i tc = VMem a i tc


-- Terms

module Ip where
  infixl 1 _$_
  infixr 0 lam=>_
  data Tm {tn} (tc : Cx tn) : Ty -> Set where
    var    : forall {a i}   -> isTrue a i tc             -> Tm tc a
    lam=>_ : forall {a b}   -> Tm (tc , a) b             -> Tm tc (a => b)
    _$_    : forall {a b}   -> Tm tc (a => b) -> Tm tc a -> Tm tc b
    pair'  : forall {a b}   -> Tm tc a        -> Tm tc b -> Tm tc (a && b)
    fst    : forall {a b}   -> Tm tc (a && b)            -> Tm tc a
    snd    : forall {a b}   -> Tm tc (a && b)            -> Tm tc b
    left   : forall {a b}   -> Tm tc a                   -> Tm tc (a || b)
    right  : forall {a b}   -> Tm tc b                   -> Tm tc (a || b)
    case'  : forall {a b c} -> Tm tc (a || b) -> Tm (tc , a) c -> Tm (tc , b) c -> Tm tc c
    abort  : forall {a}     -> Tm tc FALSE               -> Tm tc a

  syntax pair' x y    = [ x , y ]
  syntax case' xy x y = case xy => x => y

  v : forall {tn} (k : Nat) {tc : Cx (suc (k + tn))} -> Tm tc (proj tc (fin k))
  v i = var (mem i)

  Thm : Ty -> Set
  Thm a = forall {tn} {tc : Cx tn} -> Tm tc a
open Ip public


-- Example theorems

t1 : forall {a b} -> Thm (a => NOT a => b)
t1 =
  lam=>
    lam=> abort (v 0 $ v 1)

t2 : forall {a b} -> Thm (NOT a => a => b)
t2 =
  lam=>
    lam=> abort (v 1 $ v 0)

t3 : forall {a} -> Thm (a => NOT (NOT a))
t3 =
  lam=>
    lam=> v 0 $ v 1

t4 : forall {a} -> Thm (NOT a <=> NOT (NOT (NOT a)))
t4 =
  [ lam=>
      lam=> v 0 $ v 1
  , lam=>
      lam=> v 1 $ (lam=> v 0 $ v 1)
  ]
