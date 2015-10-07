-- Minimal implicational logic, PHOAS approach, final encoding

module Pf.ArrMp

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

TmRepr : Type
TmRepr = Cx -> Ty -> Type

infixl 1 :$
class ArrMpTm (tr : TmRepr) where
  var  : isTrue a tc                -> tr tc a
  lam' : (isTrue a tc -> tr tc b)   -> tr tc (a :=> b)
  (:$) : tr tc (a :=> b) -> tr tc a -> tr tc b

lam'' : {tr : TmRepr} -> ArrMpTm tr => (tr tc a -> tr tc b) -> tr tc (a :=> b)
lam'' f = lam' $ \x => f (var x)

syntax "lam" {a} ":=>" [b] = lam'' (\a => b)

Thm : Ty -> Type
Thm a = {tr : TmRepr} -> {tc : Cx} -> ArrMpTm tr => tr tc a


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

-- TODO:
-- ./src/Pf/ArrMp.idr:63:6:When checking right hand side of tSKK:
-- Can't resolve type class ArrMpTm tr
-- tSKK : Thm (a :=> a)
-- tSKK {a} =
--   aS {b = a :=> a} :$ aK :$ aK
