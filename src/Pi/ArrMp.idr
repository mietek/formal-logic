-- Minimal implicational logic, PHOAS approach, initial encoding

module Pi.ArrMp

%default total


-- Types

infixr 0 :=>
data Ty : Type where
  UNIT  :             Ty
  (:=>) : Ty -> Ty -> Ty


-- Context and truth judgement

Cx : Type
Cx = Ty -> Type

isTrue : Ty -> Cx -> Type
isTrue a tc = tc a


-- Terms

infixl 1 :$
data Tm : Cx -> Ty -> Type where
  var  : isTrue a tc                -> Tm tc a
  lam' : (isTrue a tc -> Tm tc b)   -> Tm tc (a :=> b)
  (:$) : Tm tc (a :=> b) -> Tm tc a -> Tm tc b

lam'' : (Tm tc a -> Tm tc b) -> Tm tc (a :=> b)
lam'' f = lam' $ \x => f (var x)

syntax "lam" {a} ":=>" [b] = lam'' (\a => b)

Thm : Ty -> Type
Thm a = {tc : Cx} -> Tm tc a


-- Example theorems

aI : Thm (a :=> a)
aI =
  lam x :=> x

aK : Thm (a :=> b :=> a)
aK =
  lam x :=>
    lam y :=> x

aS : Thm ((a :=> b :=> c) :=> (a :=> b) :=> a :=> c)
aS =
  lam f :=>
    lam g :=>
      lam x :=> f :$ x :$ (g :$ x)

tSKK : Thm (a :=> a)
tSKK {a} =
  aS {b = a :=> a} :$ aK :$ aK
