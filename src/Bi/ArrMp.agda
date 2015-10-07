-- Minimal implicational logic, de Bruijn approach, initial encoding

module Bi.ArrMp where

open import Lib using (List; _,_; LMem; lzero; lsuc)


-- Types

infixr 0 _=>_
data Ty : Set where
  UNIT :             Ty
  _=>_ : Ty -> Ty -> Ty


-- Context and truth judgement

Cx : Set
Cx = List Ty

isTrue : Ty -> Cx -> Set
isTrue a tc = LMem a tc


-- Terms

module ArrMp where
  infixl 1 _$_
  infixr 0 lam=>_
  data Tm (tc : Cx) : Ty -> Set where
    var    : forall {a}   -> isTrue a tc               -> Tm tc a
    lam=>_ : forall {a b} -> Tm (tc , a) b             -> Tm tc (a => b)
    _$_    : forall {a b} -> Tm tc (a => b) -> Tm tc a -> Tm tc b

  v0 : forall {tc a} -> Tm (tc , a) a
  v0 = var lzero

  v1 : forall {tc a b} -> Tm (tc , a , b) a
  v1 = var (lsuc lzero)

  v2 : forall {tc a b c} -> Tm (tc , a , b , c) a
  v2 = var (lsuc (lsuc lzero))

  Thm : Ty -> Set
  Thm a = forall {tc} -> Tm tc a
open ArrMp public


-- Example theorems

aI : forall {a} -> Thm (a => a)
aI =
  lam=> v0

aK : forall {a b} -> Thm (a => b => a)
aK =
  lam=>
    lam=> v1

aS : forall {a b c} -> Thm ((a => b => c) => (a => b) => a => c)
aS =
  lam=>
    lam=>
      lam=> v2 $ v0 $ (v1 $ v0)

tSKK : forall {a} -> Thm (a => a)
tSKK {a = a} =
  aS {b = a => a} $ aK $ aK
