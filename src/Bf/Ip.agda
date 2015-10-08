-- Intuitionistic propositional logic, de Bruijn approach, final encoding

module Bf.Ip where

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

TmRepr : Set1
TmRepr = Cx -> Ty -> Set

module ArrMp where
  record Tm (tr : TmRepr) : Set1 where
    infixl 1 _$_
    infixr 0 lam=>_
    field
      var    : forall {tc a}   -> isTrue a tc               -> tr tc a
      lam=>_ : forall {tc a b} -> tr (tc , a) b             -> tr tc (a => b)
      _$_    : forall {tc a b} -> tr tc (a => b) -> tr tc a -> tr tc b

    v0 : forall {tc a} -> tr (tc , a) a
    v0 = var lzero

    v1 : forall {tc a b} -> tr (tc , a , b) a
    v1 = var (lsuc lzero)

    v2 : forall {tc a b c} -> tr (tc , a , b , c) a
    v2 = var (lsuc (lsuc lzero))
  open Tm {{...}} public

module Mp where
  record Tm (tr : TmRepr) : Set1 where
    field
      pair' : forall {tc a b}   -> tr tc a        -> tr tc b -> tr tc (a && b)
      fst   : forall {tc a b}   -> tr tc (a && b)            -> tr tc a
      snd   : forall {tc a b}   -> tr tc (a && b)            -> tr tc b
      left  : forall {tc a b}   -> tr tc a                   -> tr tc (a || b)
      right : forall {tc a b}   -> tr tc b                   -> tr tc (a || b)
      case' : forall {tc a b c} -> tr tc (a || b) -> tr (tc , a) c -> tr (tc , b) c -> tr tc c

      isArrMp : ArrMp.Tm tr
    open ArrMp.Tm isArrMp public

    syntax pair' x y    = [ x , y ]
    syntax case' xy x y = case xy => x => y
  open Tm {{...}} public

module Ip where
  record Tm (tr : TmRepr) : Set1 where
    field
      abort : forall {tc a} -> tr tc FALSE -> tr tc a

      isMp : Mp.Tm tr
    open Mp.Tm isMp public
  open Tm {{...}} public

  Thm : Ty -> Set1
  Thm a = forall {tr tc} {{_ : Tm tr}} -> tr tc a
open Ip public


-- Example theorems

t1 : forall {a b} -> Thm (a => NOT a => b)
t1 =
  lam=>
    lam=> abort (v0 $ v1)

t2 : forall {a b} -> Thm (NOT a => a => b)
t2 =
  lam=>
    lam=> abort (v1 $ v0)

t3 : forall {a} -> Thm (a => NOT (NOT a))
t3 =
  lam=>
    lam=> v0 $ v1

t4 : forall {a} -> Thm (NOT a <=> NOT (NOT (NOT a)))
t4 =
  [ lam=>
      lam=> v0 $ v1
  , lam=>
      lam=> v1 $ (lam=> v0 $ v1)
  ]
