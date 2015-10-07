-- Classical propositional logic, PHOAS approach, final encoding

module Pf.Cp

%default total


-- Types

infixl 2 :&&
infixl 1 :||
infixr 0 :=>
data Ty : Type where
  UNIT  :             Ty
  (:=>) : Ty -> Ty -> Ty
  (:&&) : Ty -> Ty -> Ty
  (:||) : Ty -> Ty -> Ty
  FALSE :             Ty

infixr 0 :<=>
(:<=>) : Ty -> Ty -> Ty
(:<=>) a b = (a :=> b) :&& (b :=> a)

NOT : Ty -> Ty
NOT a = a :=> FALSE

TRUE : Ty
TRUE = FALSE :=> FALSE


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

class ArrMpTm tr => MpTm (tr : TmRepr) where
  pair  : tr tc a         -> tr tc b -> tr tc (a :&& b)
  fst   : tr tc (a :&& b)            -> tr tc a
  snd   : tr tc (a :&& b)            -> tr tc b
  left  : tr tc a                    -> tr tc (a :|| b)
  right : tr tc b                    -> tr tc (a :|| b)
  case' : tr tc (a :|| b) -> (isTrue a tc -> tr tc c) -> (isTrue b tc -> tr tc c) -> tr tc c

case'' : {tr : TmRepr} -> MpTm tr => tr tc (a :|| b) -> (tr tc a -> tr tc c) -> (tr tc b -> tr tc c) -> tr tc c
case'' xy f g = case' xy (\x => f (var x)) (\y => g (var y))

syntax "["    [a]  ","  [b] "]" = pair a b
syntax "case" [ab] "of" {a} ":=>" [c1] or {b} ":=>" [c2] = case'' ab (\a => c1) (\b => c2)

Thm : Ty -> Type
Thm a = {tr : TmRepr} -> {tc : Cx} -> MpTm tr => tr tc a
