-- Minimal propositional logic, PHOAS approach, initial encoding

module Pi.Mp

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

lam'' : (Tm tc a -> Tm tc b) -> Tm tc (a :=> b)
lam'' f = lam' $ \x => f (var x)

case'' : Tm tc (a :|| b) -> (Tm tc a -> Tm tc c) -> (Tm tc b -> Tm tc c) -> Tm tc c
case'' xy f g = case' xy (\x => f (var x)) (\y => g (var y))

syntax "lam"  {a}  ":=>" [b]     = lam'' (\a => b)
syntax "["    [a]  ","   [b] "]" = pair a b
syntax "case" [ab] "of"  {a} ":=>" [c1] or {b} ":=>" [c2] = case'' ab (\a => c1) (\b => c2)

Thm : Ty -> Type
Thm a = {tc : Cx} -> Tm tc a


-- Example theorems

c1 : Thm (a :&& b :<=> b :&& a)
c1 =
  [ lam xy :=> [ snd xy , fst xy ]
  , lam yx :=> [ snd yx , fst yx ]
  ]

c2 : Thm (a :|| b :<=> b :|| a)
c2 =
  [ lam xy :=>
      case xy
        of x :=> right x
        or y :=> left y
  , lam yx :=>
      case yx
        of y :=> right y
        or x :=> left x
  ]

i1 : Thm (a :&& a :<=> a)
i1 =
  [ lam xx :=> fst xx
  , lam x  :=> [ x , x ]
  ]

i2 : Thm (a :|| a :<=> a)
i2 =
  [ lam xx :=>
      case xx
        of x :=> x
        or x :=> x
  , lam x :=> left x
  ]

l3 : Thm ((a :=> a) :<=> TRUE)
l3 =
  [ lam x :=> lam nt :=> nt
  , lam b :=> lam x  :=> x
  ]

l1 : Thm (a :&& (b :&& c) :<=> (a :&& b) :&& c)
l1 =
  [ lam xyz :=>
      (let yz = snd xyz in
        [ [ fst xyz , fst yz ] , snd yz ])
  , lam xyz :=>
      (let xy = fst xyz in
        [ fst xy , [ snd xy , snd xyz ] ])
  ]

l2 : Thm (a :&& TRUE :<=> a)
l2 =
  [ lam xt :=> fst xt
  , lam x  :=> [ x , lam nt :=> nt ]
  ]

l4 : Thm (a :&& (b :|| c) :<=> (a :&& b) :|| (a :&& c))
l4 =
  [ lam xyz :=>
      (let x = fst xyz in
        case snd xyz
          of y :=> left  [ x , y ]
          or z :=> right [ x , z ])
  , lam xyxz :=>
      case xyxz
        of xy :=> ([ fst xy , left  (snd xy) ])
        or xz :=> [ fst xz , right (snd xz) ]
  ]

l6 : Thm (a :|| (b :&& c) :<=> (a :|| b) :&& (a :|| c))
l6 =
  [ lam xyz :=>
      case xyz
        of x  :=> ([ left x , left x ])
        or yz :=> [ right (fst yz) , right (snd yz) ]
  , lam xyxz :=>
      case fst xyxz
        of x :=> left x
        or y :=>
          case snd xyxz
            of x :=> left x
            or z :=> right [ y , z ]
  ]

l7 : Thm (a :|| TRUE :<=> TRUE)
l7 =
  [ lam xt :=> lam nt :=> nt
  , lam t  :=> right t
  ]

l9 : Thm (a :|| (b :|| c) :<=> (a :|| b) :|| c)
l9 =
  [ lam xyz :=>
      case xyz
        of x  :=> left (left x)
        or yz :=>
          case yz
            of y :=> left (right y)
            or z :=> right z
  , lam xyz :=>
      case xyz
        of xy :=>
          case xy
            of x :=> left x
            or y :=> right (left y)
        or z :=> right (right z)
  ]

l11 : Thm ((a :=> (b :&& c)) :<=> (a :=> b) :&& (a :=> c))
l11 =
  [ lam xyz :=>
      [ lam x :=> fst (xyz :$ x)
      , lam x :=> snd (xyz :$ x)
      ]
  , lam xyxz :=>
      lam x :=> [ fst xyxz :$ x , snd xyxz :$ x ]
  ]

l12 : Thm ((a :=> TRUE) :<=> TRUE)
l12 =
  [ lam f :=> lam nt :=> nt
  , lam t :=> lam f  :=> t
  ]

l13 : Thm ((a :=> (b :=> c)) :<=> ((a :&& b) :=> c))
l13 =
  [ lam xyz :=>
      lam xy :=> xyz :$ fst xy :$ snd xy
  , lam xyz :=>
      lam x :=>
        lam y :=> xyz :$ [ x , y ]
  ]

l16 : Thm (((a :&& b) :=> c) :<=> (a :=> (b :=> c)))
l16 =
  [ lam xyz :=>
      lam x :=>
        lam y :=> xyz :$ [ x , y ]
  , lam xyz :=>
      lam xy :=> xyz :$ fst xy :$ snd xy
  ]

l17 : Thm ((TRUE :=> a) :<=> a)
l17 =
  [ lam tx :=> tx :$ (lam nt :=> nt)
  , lam x  :=> lam tx :=> x
  ]

l19 : Thm (((a :|| b) :=> c) :<=> (a :=> c) :&& (b :=> c))
l19 =
  [ lam xyz :=>
      [ lam x :=> xyz :$ left x
      , lam y :=> xyz :$ right y
      ]
  , lam xzyz :=>
      lam xy :=>
        case xy
          of x :=> fst xzyz :$ x
          or y :=> snd xzyz :$ y
  ]
