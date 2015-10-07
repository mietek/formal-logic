-- Minimal implicational modal logic, de Bruijn approach, initial encoding

module Bi.BoxMp where

open import Lib using (List; []; _,_; LMem; lzero; lsuc)


-- Types

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

module BoxMp where
  infixl 1 _$_
  infixr 0 lam=>_
  data Tm (vc tc : Cx) : Ty -> Set where
    var    : forall {a}   -> isTrue a tc                     -> Tm vc tc a
    lam=>_ : forall {a b} -> Tm vc (tc , a) b                -> Tm vc tc (a => b)
    _$_    : forall {a b} -> Tm vc tc (a => b) -> Tm vc tc a -> Tm vc tc b
    var#   : forall {a}   -> isValid a vc                    -> Tm vc tc a
    box    : forall {a}   -> Tm vc [] a                      -> Tm vc tc (BOX a)
    unbox' : forall {a b} -> Tm vc tc (BOX a)  -> Tm (vc , a) tc b -> Tm vc tc b

  syntax unbox' x' x = unbox x' => x

  v0 : forall {vc tc a} -> Tm vc (tc , a) a
  v0 = var lzero

  v1 : forall {vc tc a b} -> Tm vc (tc , a , b) a
  v1 = var (lsuc lzero)

  v2 : forall {vc tc a b c} -> Tm vc (tc , a , b , c) a
  v2 = var (lsuc (lsuc lzero))

  v0# : forall {vc tc a} -> Tm (vc , a) tc a
  v0# = var# lzero

  v1# : forall {vc tc a b} -> Tm (vc , a , b) tc a
  v1# = var# (lsuc lzero)

  v2# : forall {vc tc a b c} -> Tm (vc , a , b , c) tc a
  v2# = var# (lsuc (lsuc lzero))

  Thm : Ty -> Set
  Thm a = forall {vc tc} -> Tm vc tc a
open BoxMp public


-- Example theorems

rNec : forall {a} -> Thm a -> Thm (BOX a)
rNec x =
  box x

aK : forall {a b} -> Thm (BOX (a => b) => BOX a => BOX b)
aK =
  lam=>
    lam=>
      (unbox v1 =>
        unbox v0 =>
          box (v1# $ v0#))

aT : forall {a} -> Thm (BOX a => a)
aT =
  lam=>
    (unbox v0 => v0#)

a4 : forall {a} -> Thm (BOX a => BOX (BOX a))
a4 =
  lam=>
    (unbox v0 => box (box v0#))

t1 : forall {a} -> Thm (a => BOX (a => a))
t1 =
  lam=> box (lam=> v0)
