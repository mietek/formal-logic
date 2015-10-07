-- Minimal propositional logic, PHOAS approach, initial encoding

module Pi.Mp where


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

  lam'' : forall {tc a b} -> (Tm tc a -> Tm tc b) -> Tm tc (a => b)
  lam'' f = lam' \x -> f (var x)

  case'' : forall {tc a b c} -> Tm tc (a || b) -> (Tm tc a -> Tm tc c) -> (Tm tc b -> Tm tc c) -> Tm tc c
  case'' xy f g = case' xy (\x -> f (var x)) (\y -> g (var y))

  syntax lam''  (\a -> b) = lam a => b
  syntax pair'  x y       = [ x , y ]
  syntax case'' xy (\x -> z1) (\y -> z2) = case xy of x => z1 or y => z2

  Thm : Ty -> Set1
  Thm a = forall {tc} -> Tm tc a
open Mp public


-- Example theorems

c1 : forall {a b} -> Thm (a && b <=> b && a)
c1 =
  [ lam xy => [ snd xy , fst xy ]
  , lam yx => [ snd yx , fst yx ]
  ]

c2 : forall {a b} -> Thm (a || b <=> b || a)
c2 =
  [ lam xy =>
      case xy
        of x => right x
        or y => left y
  , lam yx =>
      case yx
        of y => right y
        or x => left x
  ]

i1 : forall {a} -> Thm (a && a <=> a)
i1 =
  [ lam xx => fst xx
  , lam x  => [ x , x ]
  ]

i2 : forall {a} -> Thm (a || a <=> a)
i2 =
  [ lam xx =>
      case xx
        of x => x
        or x => x
  , lam x => left x
  ]

l3 : forall {a} -> Thm ((a => a) <=> TRUE)
l3 =
  [ lam _ => lam nt => nt
  , lam _ => lam x => x
  ]

l1 : forall {a b c} -> Thm (a && (b && c) <=> (a && b) && c)
l1 =
  [ lam xyz =>
      (let yz = snd xyz in
        [ [ fst xyz , fst yz ] , snd yz ])
  , lam xyz =>
      (let xy = fst xyz in
        [ fst xy , [ snd xy , snd xyz ] ])
  ]

l2 : forall {a} -> Thm (a && TRUE <=> a)
l2 =
  [ lam xt => fst xt
  , lam x  => [ x , lam nt => nt ]
  ]

l4 : forall {a b c} -> Thm (a && (b || c) <=> (a && b) || (a && c))
l4 =
  [ lam xyz =>
      (let x = fst xyz in
        case snd xyz
          of y => left  [ x , y ]
          or z => right [ x , z ])
  , lam xyxz =>
      case xyxz
        of xy => [ fst xy , left  (snd xy) ]
        or xz => [ fst xz , right (snd xz) ]
  ]

l6 : forall {a b c} -> Thm (a || (b && c) <=> (a || b) && (a || c))
l6 =
  [ lam xyz =>
      case xyz
        of x  => [ left x , left x ]
        or yz => [ right (fst yz) , right (snd yz) ]
  , lam xyxz =>
      case fst xyxz
        of x => left x
        or y =>
          case snd xyxz
            of x => left x
            or z => right [ y , z ]
  ]

l7 : forall {a} -> Thm (a || TRUE <=> TRUE)
l7 =
  [ lam _ => lam nt => nt
  , lam t => right t
  ]

l9 : forall {a b c} -> Thm (a || (b || c) <=> (a || b) || c)
l9 =
  [ lam xyz =>
      case xyz
        of x  => left (left x)
        or yz =>
          case yz
            of y => left (right y)
            or z => right z
  , lam xyz =>
      case xyz
        of xy =>
          case xy
            of x => left x
            or y => right (left y)
        or z => right (right z)
  ]

l11 : forall {a b c} -> Thm ((a => (b && c)) <=> (a => b) && (a => c))
l11 =
  [ lam xyz =>
      [ lam x => fst (xyz $ x)
      , lam x => snd (xyz $ x)
      ]
  , lam xyxz =>
      lam x => [ fst xyxz $ x , snd xyxz $ x ]
  ]

l12 : forall {a} -> Thm ((a => TRUE) <=> TRUE)
l12 =
  [ lam _ => lam nt => nt
  , lam t => lam _  => t
  ]

l13 : forall {a b c} -> Thm ((a => (b => c)) <=> ((a && b) => c))
l13 =
  [ lam xyz =>
      lam xy => xyz $ fst xy $ snd xy
  , lam xyz =>
      lam x =>
        lam y => xyz $ [ x , y ]
  ]

l16 : forall {a b c} -> Thm (((a && b) => c) <=> (a => (b => c)))
l16 =
  [ lam xyz =>
      lam x =>
        lam y => xyz $ [ x , y ]
  , lam xyz =>
      lam xy => xyz $ fst xy $ snd xy
  ]

l17 : forall {a} -> Thm ((TRUE => a) <=> a)
l17 =
  [ lam tx => tx $ (lam nt => nt)
  , lam x  => lam _ => x
  ]

l19 : forall {a b c} -> Thm (((a || b) => c) <=> (a => c) && (b => c))
l19 =
  [ lam xyz =>
      [ lam x => xyz $ left x
      , lam y => xyz $ right y
      ]
  , lam xzyz =>
      lam xy =>
        case xy
          of x => fst xzyz $ x
          or y => snd xzyz $ y
  ]
