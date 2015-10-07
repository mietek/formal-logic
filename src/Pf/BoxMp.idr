-- Minimal implicational modal logic, PHOAS approach, final encoding

module Pf.BoxMp

%default total


-- Types

infixr 0 :=>
data Ty : Type where
  UNIT  :             Ty
  (:=>) : Ty -> Ty -> Ty
  BOX   : Ty       -> Ty


-- Context and truth judgement with modal depth

Cx : Type
Cx = Nat -> Ty -> Type

isTrue : Ty -> Nat -> Cx -> Type
isTrue a d tc = tc d a


-- Terms

TmRepr : Type
TmRepr = Nat -> Cx -> Ty -> Type

infixl 1 :$
class ArrMpTm (tr : TmRepr) where
  var  : isTrue a d tc                  -> tr d tc a
  lam' : (isTrue a d tc -> tr d tc b)   -> tr d tc (a :=> b)
  (:$) : tr d tc (a :=> b) -> tr d tc a -> tr d tc b

lam'' : {tr : TmRepr} -> ArrMpTm tr => (tr d tc a -> tr d tc b) -> tr d tc (a :=> b)
lam'' f = lam' $ \x => f (var x)

syntax "lam" {a} ":=>" [b] = lam'' (\a => b)

class ArrMpTm tr => BoxMpTm (tr : TmRepr) where
  box    : tr (succ d) tc a -> tr d tc (BOX a)
  unbox' : tr d tc (BOX a)  -> (isTrue a gd tc -> tr d tc b) -> tr d tc b

unbox'' : {tr : TmRepr} -> BoxMpTm tr => tr d tc (BOX a) -> (tr gd tc a -> tr d tc b) -> tr d tc b
unbox'' x' f = unbox' x' $ \x => f (var x)

syntax "unbox" [a'] as {a} ":=>" [b] = unbox'' a' (\a => b)

Thm : Ty -> Type
Thm a = {tr : TmRepr} -> {d : Nat} -> {tc : Cx} -> BoxMpTm tr => tr d tc a


-- Example theorems

rNec : Thm a -> Thm (BOX a)
rNec x =
  box x

aK : Thm (BOX (a :=> b) :=> BOX a :=> BOX b)
aK =
  lam f' :=>
    lam x' :=>
      unbox f' as f :=>
        unbox x' as x :=> box (f :$ x)

aT : Thm (BOX a :=> a)
aT =
  lam x' :=>
    unbox x' as x :=> x

a4 : Thm (BOX a :=> BOX (BOX a))
a4 =
  lam x' :=>
    unbox x' as x :=> box (box x)

t1 : Thm (a :=> BOX (a :=> a))
t1 =
  lam x :=> box (lam y :=> y)
