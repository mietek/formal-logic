-- Minimal implicational modal logic, PHOAS approach, initial encoding

module Pi.BoxMp

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

infixl 1 :$
data Tm : Nat -> Cx -> Ty -> Type where
  var    : isTrue a d tc                  -> Tm d tc a
  lam'   : (isTrue a d tc -> Tm d tc b)   -> Tm d tc (a :=> b)
  (:$)   : Tm d tc (a :=> b) -> Tm d tc a -> Tm d tc b
  box    : Tm (succ d) tc a               -> Tm d tc (BOX a)
  unbox' : Tm d tc (BOX a)   -> (isTrue a gd tc -> Tm d tc b) -> Tm d tc b

lam'' : (Tm d tc a -> Tm d tc b) -> Tm d tc (a :=> b)
lam'' f = lam' $ \x => f (var x)

unbox'' : Tm d tc (BOX a) -> (Tm gd tc a -> Tm d tc b) -> Tm d tc b
unbox'' x' f = unbox' x' $ \x => f (var x)

syntax "lam"   {a} ":=>" [b]         = lam''   (\a => b)
syntax "unbox" [a'] as {a} ":=>" [b] = unbox'' a' (\a => b)

Thm : Ty -> Type
Thm a = {d : Nat} -> {tc : Cx} -> Tm d tc a


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
