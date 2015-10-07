-- Minimal implicational modal logic, vector-based de Bruijn approach, initial encoding

module Vi.BoxMp where

open import Lib using (Nat; suc; _+_; Fin; fin; Vec; []; _,_; proj; VMem; mem)


-- Types

infixr 0 _=>_
data Ty : Set where
  UNIT :             Ty
  _=>_ : Ty -> Ty -> Ty
  BOX  : Ty       -> Ty


-- Context and truth/validity judgements

Cx : Nat -> Set
Cx n = Vec Ty n

isTrue : forall {tn} -> Ty -> Fin tn -> Cx tn -> Set
isTrue a i tc = VMem a i tc

isValid : forall {vn} -> Ty -> Fin vn -> Cx vn -> Set
isValid a i vc = VMem a i vc


-- Terms

module BoxMp where
  infixl 1 _$_
  infixr 0 lam=>_
  data Tm {vn tn} (vc : Cx vn) (tc : Cx tn) : Ty -> Set where
    var     : forall {a i} -> isTrue a i tc                   -> Tm vc tc a
    lam=>_  : forall {a b} -> Tm vc (tc , a) b                -> Tm vc tc (a => b)
    _$_     : forall {a b} -> Tm vc tc (a => b) -> Tm vc tc a -> Tm vc tc b
    var#    : forall {a i} -> isValid a i vc                  -> Tm vc tc a
    box     : forall {a}   -> Tm vc [] a                      -> Tm vc tc (BOX a)
    unbox'' : forall {a b} -> Tm vc tc (BOX a)  -> Tm (vc , a) tc b -> Tm vc tc b

  syntax unbox'' x' x = unbox x' => x

  v : forall {vn tn} {vc : Cx vn} (k : Nat) {tc : Cx (suc (k + tn))} -> Tm vc tc (proj tc (fin k))
  v i = var (mem i)

  v# : forall {vn tn} (k : Nat) {vc : Cx (suc (k + vn))} {tc : Cx tn} -> Tm vc tc (proj vc (fin k))
  v# i = var# (mem i)

  Thm : Ty -> Set
  Thm a = forall {vn tn} {vc : Cx vn} {tc : Cx tn} -> Tm vc tc a
open BoxMp public


-- Example theorems

rNec : forall {a} -> Thm a -> Thm (BOX a)
rNec x =
  box x

aK : forall {a b} -> Thm (BOX (a => b) => BOX a => BOX b)
aK =
  lam=>
    lam=>
      (unbox v 1 =>
        unbox v 0 =>
          box (v# 1 $ v# 0))

aT : forall {a} -> Thm (BOX a => a)
aT =
  lam=>
    (unbox v 0 => v# 0)

a4 : forall {a} -> Thm (BOX a => BOX (BOX a))
a4 =
  lam=>
    (unbox v 0 => box (box (v# 0)))

t1 : forall {a} -> Thm (a => BOX (a => a))
t1 =
  lam=> box (lam=> (v 0))
