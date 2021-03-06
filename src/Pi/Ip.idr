-- Intuitionistic propositional logic, PHOAS approach, initial encoding

module Pi.Ip

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

infixl 1 :$
data Tm : Cx -> Ty -> Type where
  var   : isTrue a tc                -> Tm tc a
  lam'  : (isTrue a tc -> Tm tc b)   -> Tm tc (a :=> b)
  (:$)  : Tm tc (a :=> b) -> Tm tc a -> Tm tc b
  pair  : Tm tc a         -> Tm tc b -> Tm tc (a :&& b)
  fst   : Tm tc (a :&& b)            -> Tm tc a
  snd   : Tm tc (a :&& b)            -> Tm tc b
  left  : Tm tc a                    -> Tm tc (a :|| b)
  right : Tm tc b                    -> Tm tc (a :|| b)
  case' : Tm tc (a :|| b) -> (isTrue a tc -> Tm tc c) -> (isTrue b tc -> Tm tc c) -> Tm tc c
  abort : Tm tc FALSE                -> Tm tc a

lam'' : (Tm tc a -> Tm tc b) -> Tm tc (a :=> b)
lam'' f = lam' $ \x => f (var x)

case'' : Tm tc (a :|| b) -> (Tm tc a -> Tm tc c) -> (Tm tc b -> Tm tc c) -> Tm tc c
case'' xy f g = case' xy (\x => f (var x)) (\y => g (var y))

syntax "lam" {a} ":=>" [b]   = lam'' (\a => b)
syntax "[" [a] "," [b] "]"   = pair a b
syntax "case" [ab] "of" {a} ":=>" [c1] or {b} ":=>" [c2] = case'' ab (\a => c1) (\b => c2)

Thm : Ty -> Type
Thm a = {tc : Cx} -> Tm tc a


-- Example theorems

t1 : Thm (a :=> NOT a :=> b)
t1 =
  lam x :=>
    lam f :=> abort (f :$ x)

t2 : Thm (NOT a :=> a :=> b)
t2 =
  lam f :=>
    lam x :=> abort (f :$ x)

t3 : Thm (a :=> NOT (NOT a))
t3 =
  lam x :=>
    lam f :=> f :$ x

t4 : Thm (NOT a :<=> NOT (NOT (NOT a)))
t4 =
  [ lam f :=>
      lam g :=> g :$ f
  , lam g :=>
      lam x :=> g :$ (lam f :=> f :$ x)
  ]
