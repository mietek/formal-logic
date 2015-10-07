-- Intuitionistic logic, PHOAS approach, initial encoding

module Pi.I (Indiv : Set) where


-- Types

data Ty : Set

Pred : Set
Pred = Indiv -> Ty

infixl 2 _&&_
infixl 1 _||_
infixr 0 _=>_
data Ty where
  UNIT   :             Ty
  _=>_   : Ty -> Ty -> Ty
  _&&_   : Ty -> Ty -> Ty
  _||_   : Ty -> Ty -> Ty
  FALSE  :             Ty
  FORALL : Pred     -> Ty
  EXISTS : Pred     -> Ty

infixr 0 _<=>_
_<=>_ : Ty -> Ty -> Ty
a <=> b = (a => b) && (b => a)

NOT : Ty -> Ty
NOT a = a => FALSE

TRUE : Ty
TRUE = FALSE => FALSE


-- Context and truth/individual judgement

data El : Set where
  mkTrue  : Ty    -> El
  mkIndiv : Indiv -> El

Cx : Set1
Cx = El -> Set

isTrue : Ty -> Cx -> Set
isTrue a tc = tc (mkTrue a)

isIndiv : Indiv -> Cx -> Set
isIndiv x tc = tc (mkIndiv x)


-- Terms

module I where
  infixl 2 _$$_
  infixl 1 _$_
  data Tm (tc : Cx) : Ty -> Set where
    var    : forall {a}     -> isTrue a tc                      -> Tm tc a
    lam'   : forall {a b}   -> (isTrue a tc -> Tm tc b)         -> Tm tc (a => b)
    _$_    : forall {a b}   -> Tm tc (a => b)   -> Tm tc a      -> Tm tc b
    pair'  : forall {a b}   -> Tm tc a          -> Tm tc b      -> Tm tc (a && b)
    fst    : forall {a b}   -> Tm tc (a && b)                   -> Tm tc a
    snd    : forall {a b}   -> Tm tc (a && b)                   -> Tm tc b
    left   : forall {a b}   -> Tm tc a                          -> Tm tc (a || b)
    right  : forall {a b}   -> Tm tc b                          -> Tm tc (a || b)
    case'  : forall {a b c} -> Tm tc (a || b)   -> (isTrue a tc -> Tm tc c) -> (isTrue b tc -> Tm tc c) -> Tm tc c
    pi'    : forall {p}     -> (forall {x} -> isIndiv x tc -> Tm tc (p x)) -> Tm tc (FORALL p)
    _$$_   : forall {p x}   -> Tm tc (FORALL p) -> isIndiv x tc -> Tm tc (p x)
    sig'   : forall {p x}   -> isIndiv x tc     -> Tm tc (p x)  -> Tm tc (EXISTS p)
    split' : forall {p x a} -> Tm tc (EXISTS p) -> (isTrue (p x) tc -> Tm tc a) -> Tm tc a
    abort  : forall {a}     -> Tm tc FALSE                      -> Tm tc a

  lam'' : forall {tc a b} -> (Tm tc a -> Tm tc b) -> Tm tc (a => b)
  lam'' f = lam' \x -> f (var x)

  case'' : forall {tc a b c} -> Tm tc (a || b) -> (Tm tc a -> Tm tc c) -> (Tm tc b -> Tm tc c) -> Tm tc c
  case'' xy f g = case' xy (\x -> f (var x)) (\y -> g (var y))

  split'' : forall {tc p x a} -> Tm tc (EXISTS p) -> (Tm tc (p x) -> Tm tc a) -> Tm tc a
  split'' x f = split' x \y -> f (var y)

  syntax lam''   (\a -> b)   = lam a => b
  syntax pair'   x y         = [ x , y ]
  syntax case''  xy (\x -> z1) (\y -> z2) = case xy of x => z1 or y => z2
  syntax pi'     (\x -> px)  = pi x => px
  syntax sig'    x px        = [ x ,, px ]
  syntax split'' x (\y -> z) = split x as y => z

  Thm : Ty -> Set1
  Thm a = forall {tc} -> Tm tc a
open I public


-- Example theorems

t214 : forall {p q : Pred} -> Thm (
  FORALL (\x -> p x || NOT (p x)) && FORALL (\x -> p x => EXISTS (\y -> q y)) =>
    FORALL (\x -> EXISTS (\y -> p x => q y)))
t214 =
  lam fg =>
    pi x =>
      case fst fg $$ x
        of px =>
          split snd fg $$ x $ px
            as qy =>
              [ x ,, lam _ => qy ]
        or npx =>
          [ x ,, lam px => abort (npx $ px) ]

l5 : forall {a} -> Thm (a && FALSE <=> FALSE)
l5 =
  [ lam xnt => snd xnt
  , lam nt  => abort nt
  ]

l10 : forall {a} -> Thm (a || FALSE <=> a)
l10 =
  [ lam xnt =>
      case xnt
        of x  => x
        or nt => abort nt
  , lam x => left x
  ]

l20 : forall {a} -> Thm ((FALSE => a) <=> TRUE)
l20 =
  [ lam _ => lam nt => nt
  , lam _ => lam nt => abort nt
  ]
