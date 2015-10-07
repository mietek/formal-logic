-- Intuitionistic propositional logic, de Bruijn approach, initial encoding

module Bi.Ip where

open import Lib using (List; _,_; LMem; lzero; lsuc)


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

Cx : Set
Cx = List Ty

isTrue : Ty -> Cx -> Set
isTrue a tc = LMem a tc


-- Terms

module Mp where
  infixl 1 _$_
  infixr 0 lam=>_
  data Tm (tc : Cx) : Ty -> Set where
    var    : forall {a}     -> isTrue a tc               -> Tm tc a
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

  v0 : forall {tc a} -> Tm (tc , a) a
  v0 = var lzero

  v1 : forall {tc a b} -> Tm (tc , a , b) a
  v1 = var (lsuc lzero)

  v2 : forall {tc a b c} -> Tm (tc , a , b , c) a
  v2 = var (lsuc (lsuc lzero))

  Thm : Ty -> Set
  Thm a = forall {tc} -> Tm tc a
