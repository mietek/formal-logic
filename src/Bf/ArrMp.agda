-- Minimal implicational logic, de Bruijn approach, final encoding

module Bf.ArrMp where

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

TmRepr : Set1
TmRepr = Cx -> Ty -> Set

module ArrMp where
  record Tm (tr : TmRepr) : Set1 where
    infixl 1 _$_
    infixr 0 lam=>_
    field
      var    : forall {tc a}   -> isTrue a tc    -> tr tc a
      lam=>_ : forall {tc a b} -> tr (tc , a) b  -> tr tc (a => b)
      _$_    : forall {tc a b} -> tr tc (a => b) -> tr tc a -> tr tc b

    v0 : forall {tc a} -> tr (tc , a) a
    v0 = var lzero

    v1 : forall {tc a b} -> tr (tc , a , b) a
    v1 = var (lsuc lzero)

    v2 : forall {tc a b c} -> tr (tc , a , b , c) a
    v2 = var (lsuc (lsuc lzero))
  open Tm {{...}} public

  Thm : Ty -> Set1
  Thm a = forall {tr tc} {{_ : Tm tr}} -> tr tc a
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
