-- Intuitionistic propositional logic, PHOAS approach, initial encoding

module Pi.Ip where


-- Types

infixl 2 _&&_
infixl 1 _||_
infixr 0 _=>_
data Ty : Set where
  UNIT  :             Ty
  _=>_  : Ty -> Ty -> Ty
  _&&_  : Ty -> Ty -> Ty
  _||_  : Ty -> Ty -> Ty
  FALSE :             Ty

infixr 0 _<=>_
_<=>_ : Ty -> Ty -> Ty
a <=> b = (a => b) && (b => a)

NOT : Ty -> Ty
NOT a = a => FALSE

TRUE : Ty
TRUE = FALSE => FALSE


-- Context and truth judgement

Cx : Set1
Cx = Ty -> Set

isTrue : Ty -> Cx -> Set
isTrue a tc = tc a


-- Terms

module Mp where
  infixl 1 _$_
  data Tm (tc : Cx) : Ty -> Set where
    var   : forall {a}     -> isTrue a tc               -> Tm tc a
    lam'  : forall {a b}   -> (isTrue a tc -> Tm tc b)  -> Tm tc (a => b)
    _$_   : forall {a b}   -> Tm tc (a => b) -> Tm tc a -> Tm tc b
    pair' : forall {a b}   -> Tm tc a        -> Tm tc b -> Tm tc (a && b)
    fst   : forall {a b}   -> Tm tc (a && b)            -> Tm tc a
    snd   : forall {a b}   -> Tm tc (a && b)            -> Tm tc b
    left  : forall {a b}   -> Tm tc a                   -> Tm tc (a || b)
    right : forall {a b}   -> Tm tc b                   -> Tm tc (a || b)
    case' : forall {a b c} -> Tm tc (a || b) -> (isTrue a tc -> Tm tc c) -> (isTrue b tc -> Tm tc c) -> Tm tc c
    abort : forall {a}     -> Tm tc FALSE               -> Tm tc a

  lam'' : forall {tc a b} -> (Tm tc a -> Tm tc b) -> Tm tc (a => b)
  lam'' f = lam' \x -> f (var x)

  case'' : forall {tc a b c} -> Tm tc (a || b) -> (Tm tc a -> Tm tc c) -> (Tm tc b -> Tm tc c) -> Tm tc c
  case'' xy f g = case' xy (\x -> f (var x)) (\y -> g (var y))

  syntax lam''  (\a -> b) = lam a => b
  syntax pair'  x y       = [ x , y ]
  syntax case'' xy (\x -> z1) (\y -> z2) = case xy of x => z1 or y => z2

  Thm : Ty -> Set1
  Thm a = forall {tc} -> Tm tc a
