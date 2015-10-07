-- Minimal logic, PHOAS approach, initial encoding

module Pi.M

%default total


-- Types

data Indiv : Type where
  TODO : Indiv

Ty : Type

Pred : Type
Pred = Indiv -> Ty

infixl 2 :&&
infixl 1 :||
infixr 0 :=>
data Ty : Type where
  UNIT   :             Ty
  (:=>)  : Ty -> Ty -> Ty
  (:&&)  : Ty -> Ty -> Ty
  (:||)  : Ty -> Ty -> Ty
  FALSE  :             Ty
  FORALL : Pred     -> Ty
  EXISTS : Pred     -> Ty

infixr 0 :<=>
(:<=>) : Ty -> Ty -> Ty
(:<=>) a b = (a :=> b) :&& (b :=> a)

NOT : Ty -> Ty
NOT a = a :=> FALSE

TRUE : Ty
TRUE = FALSE :=> FALSE


-- Context and truth judgement

data El : Type where
  mkTrue  : Ty    -> El
  mkIndiv : Indiv -> El

Cx : Type
Cx = El -> Type

isTrue : Ty -> Cx -> Type
isTrue a tc = tc (mkTrue a)

isIndiv : Indiv -> Cx -> Type
isIndiv x tc = tc (mkIndiv x)


-- Terms

infixl 2 :$$
infixl 1 :$

data Tm : Cx -> Ty -> Type where
  var    : isTrue a tc                           -> Tm tc a
  lam'   : (isTrue a tc -> Tm tc b)              -> Tm tc (a :=> b)
  (:$)   : Tm tc (a :=> b)  -> Tm tc a           -> Tm tc b
  pair   : Tm tc a          -> Tm tc b           -> Tm tc (a :&& b)
  fst    : Tm tc (a :&& b)                       -> Tm tc a
  snd    : Tm tc (a :&& b)                       -> Tm tc b
  left   : Tm tc a                               -> Tm tc (a :|| b)
  right  : Tm tc b                               -> Tm tc (a :|| b)
  case'  : Tm tc (a :|| b)  -> (isTrue a tc -> Tm tc c) -> (isTrue b tc -> Tm tc c) -> Tm tc c
  pi'    : ({x : Indiv} -> isIndiv x tc -> Tm tc (p x)) -> Tm tc (FORALL p)
  (:$$)  : Tm tc (FORALL p) -> isIndiv x tc      -> Tm tc (p x)
  sig    : isIndiv x tc     -> Tm tc (p x)       -> Tm tc (EXISTS p)
  split' : Tm tc (EXISTS p) -> (isTrue (p x) tc -> Tm tc a) -> Tm tc a

lam'' : (Tm tc a -> Tm tc b) -> Tm tc (a :=> b)
lam'' f = lam' $ \x => f (var x)

case'' : Tm tc (a :|| b) -> (Tm tc a -> Tm tc c) -> (Tm tc b -> Tm tc c) -> Tm tc c
case'' xy f g = case' xy (\x => f (var x)) (\y => g (var y))

split'' : Tm tc (EXISTS p) -> (Tm tc (p x) -> Tm tc a) -> Tm tc a
split'' x f = split' x $ \y => f (var y)

syntax "lam"   {a}  ":=>" [b]           = lam'' (\a => b)
syntax "["     [a]  ","   [b] "]"       = pair a b
syntax "case"  [ab] "of"  {a} ":=>" [c1] or {b} ":=>" [c2] = case'' ab (\a => c1) (\b => c2)
syntax "pi"    {x}  ":=>" [y]           = pi' (\x => y)
syntax "["     [x]  ",,"  [y] "]"       = sig x y
syntax "split" [x]  as    {y} ":=>" [z] = split'' x (\y => z)

Thm : Ty -> Type
Thm a = {tc : Cx} -> Tm tc a
