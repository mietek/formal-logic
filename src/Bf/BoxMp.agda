-- Minimal implicational modal logic, de Bruijn approach, final encoding

module Bf.BoxMp where

open import Lib using (List; []; _,_; LMem; lzero; lsuc)


infixr 0 _=>_
data Ty : Set where
  UNIT :             Ty
  _=>_ : Ty -> Ty -> Ty
  BOX  : Ty       -> Ty


-- Context and truth/validity judgements

Cx : Set
Cx = List Ty

isTrue : Ty -> Cx -> Set
isTrue a tc = LMem a tc

isValid : Ty -> Cx -> Set
isValid a vc = LMem a vc


-- Terms

TmRepr : Set1
TmRepr = Cx -> Cx -> Ty -> Set

module ArrMp where
  record Tm (tr : TmRepr) : Set1 where
    infixl 1 _$_
    infixr 0 lam=>_
    field
      var    : forall {vc tc a}   -> isTrue a tc                     -> tr vc tc a
      lam=>_ : forall {vc tc a b} -> tr vc (tc , a) b                -> tr vc tc (a => b)
      _$_    : forall {vc tc a b} -> tr vc tc (a => b) -> tr vc tc a -> tr vc tc b

    v0 : forall {vc tc a} -> tr vc (tc , a) a
    v0 = var lzero

    v1 : forall {vc tc a b} -> tr vc (tc , a , b) a
    v1 = var (lsuc lzero)

    v2 : forall {vc tc a b c} -> tr vc (tc , a , b , c) a
    v2 = var (lsuc (lsuc lzero))
  open Tm {{...}} public

module BoxMp where
  record Tm (tr : TmRepr) : Set1 where
    field
      var#   : forall {vc tc a}   -> isValid a vc                   -> tr vc tc a
      box    : forall {vc tc a}   -> tr vc [] a                     -> tr vc tc (BOX a)
      unbox' : forall {vc tc a b} -> tr vc tc (BOX a) -> tr (vc , a) tc b -> tr vc tc b

      isArrMp : ArrMp.Tm tr
    open ArrMp.Tm isArrMp public

    syntax unbox' x' x = unbox x' as x

    v0# : forall {vc tc a} -> tr (vc , a) tc a
    v0# = var# lzero

    v1# : forall {vc tc a b} -> tr (vc , a , b) tc a
    v1# = var# (lsuc lzero)

    v2# : forall {vc tc a b c} -> tr (vc , a , b , c) tc a
    v2# = var# (lsuc (lsuc lzero))
  open Tm {{...}} public

  Thm : Ty -> Set1
  Thm a = forall {tr vc tc} {{_ : Tm tr}} -> tr vc tc a
open BoxMp public


-- Example theorems

rNec : forall {a} -> Thm a -> Thm (BOX a)
rNec x =
  box x

aK : forall {a b} -> Thm (BOX (a => b) => BOX a => BOX b)
aK =
  lam=>
    lam=>
      (unbox v1 as
        unbox v0 as
          box (v1# $ v0#))

aT : forall {a} -> Thm (BOX a => a)
aT =
  lam=>
    (unbox v0 as v0#)

a4 : forall {a} -> Thm (BOX a => BOX (BOX a))
a4 =
  lam=>
    (unbox v0 as box (box v0#))

t2 : forall {a} -> Thm (a => BOX (a => a))
t2 =
  lam=> box (lam=> v0)
