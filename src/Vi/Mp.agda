-- Minimal propositional logic, vector-based de Bruijn approach, initial encoding

module Vi.Mp where

open import Lib using (Nat; suc; _+_; Fin; fin; Vec; _,_; proj; VMem; mem)


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

Cx : Nat -> Set
Cx n = Vec Ty n

isTrue : forall {tn} -> Ty -> Fin tn -> Cx tn -> Set
isTrue a i tc = VMem a i tc


-- Terms

module Mp where
  infixl 1 _$_
  infixr 0 lam=>_
  data Tm {tn} (tc : Cx tn) : Ty -> Set where
    var    : forall {a i}   -> isTrue a i tc             -> Tm tc a
    lam=>_ : forall {a b}   -> Tm (tc , a) b             -> Tm tc (a => b)
    _$_    : forall {a b}   -> Tm tc (a => b) -> Tm tc a -> Tm tc b
    pair'  : forall {a b}   -> Tm tc a        -> Tm tc b -> Tm tc (a && b)
    fst    : forall {a b}   -> Tm tc (a && b)            -> Tm tc a
    snd    : forall {a b}   -> Tm tc (a && b)            -> Tm tc b
    left   : forall {a b}   -> Tm tc a                   -> Tm tc (a || b)
    right  : forall {a b}   -> Tm tc b                   -> Tm tc (a || b)
    case'  : forall {a b c} -> Tm tc (a || b) -> Tm (tc , a) c -> Tm (tc , b) c -> Tm tc c

  syntax pair' x y    = [ x , y ]
  syntax case' xy x y = case xy => x => y

  v : forall {tn} (k : Nat) {tc : Cx (suc (k + tn))} -> Tm tc (proj tc (fin k))
  v i = var (mem i)

  Thm : Ty -> Set
  Thm a = forall {tn} {tc : Cx tn} -> Tm tc a
open Mp public


-- Example theorems

c1 : forall {a b} -> Thm (a && b <=> b && a)
c1 =
  [ lam=> [ snd (v 0) , fst (v 0) ]
  , lam=> [ snd (v 0) , fst (v 0) ]
  ]

c2 : forall {a b} -> Thm (a || b <=> b || a)
c2 =
  [ lam=>
      (case v 0
        => right (v 0)
        => left  (v 0))
  , lam=>
      (case v 0
        => right (v 0)
        => left  (v 0))
  ]

i1 : forall {a} -> Thm (a && a <=> a)
i1 =
  [ lam=> fst (v 0)
  , lam=> [ v 0 , v 0 ]
  ]

i2 : forall {a} -> Thm (a || a <=> a)
i2 =
  [ lam=>
      (case v 0
        => v 0
        => v 0)
  , lam=> left (v 0)
  ]

l3 : forall {a} -> Thm ((a => a) <=> TRUE)
l3 =
  [ lam=> lam=> v 0
  , lam=> lam=> v 0
  ]

l1 : forall {a b c} -> Thm (a && (b && c) <=> (a && b) && c)
l1 =
  [ lam=>
      [ [ fst (v 0) , fst (snd (v 0)) ]
      , snd (snd (v 0))
      ]
  , lam=>
      [ fst (fst (v 0))
      , [ snd (fst (v 0)) , snd (v 0) ]
      ]
  ]

l2 : forall {a} -> Thm (a && TRUE <=> a)
l2 =
  [ lam=> fst (v 0)
  , lam=> [ v 0 , lam=> v 0 ]
  ]

l4 : forall {a b c} -> Thm (a && (b || c) <=> (a && b) || (a && c))
l4 =
  [ lam=>
      (case snd (v 0)
        => left  [ fst (v 1) , v 0 ]
        => right [ fst (v 1) , v 0 ])
  , lam=>
      (case v 0
        => [ fst (v 0) , left  (snd (v 0)) ]
        => [ fst (v 0) , right (snd (v 0)) ])
  ]

l6 : forall {a b c} -> Thm (a || (b && c) <=> (a || b) && (a || c))
l6 =
  [ lam=>
      (case v 0
        => [ left  (v 0)       , left  (v 0) ]
        => [ right (fst (v 0)) , right (snd (v 0)) ])
  , lam=>
      (case fst (v 0)
        => left (v 0)
        =>
          case snd (v 1)
            => left  (v 0)
            => right [ v 1 , v 0 ])
  ]

l7 : forall {a} -> Thm (a || TRUE <=> TRUE)
l7 =
  [ lam=> lam=> v 0
  , lam=> right (v 0)
  ]

l9 : forall {a b c} -> Thm (a || (b || c) <=> (a || b) || c)
l9 =
  [ lam=>
      (case v 0
        => left (left (v 0))
        =>
          case v 0
            => left  (right (v 0))
            => right (v 0))
  , lam=>
      (case v 0
        =>
          case v 0
            => left  (v 0)
            => right (left (v 0))
        => right (right (v 0)))
  ]

l11 : forall {a b c} -> Thm ((a => (b && c)) <=> (a => b) && (a => c))
l11 =
  [ lam=>
      [ lam=> fst (v 1 $ v 0)
      , lam=> snd (v 1 $ v 0)
      ]
  , lam=>
      lam=> [ fst (v 1) $ v 0 , snd (v 1) $ v 0 ]
  ]

l12 : forall {a} -> Thm ((a => TRUE) <=> TRUE)
l12 =
  [ lam=> lam=> v 0
  , lam=> lam=> v 1
  ]

l13 : forall {a b c} -> Thm ((a => (b => c)) <=> ((a && b) => c))
l13 =
  [ lam=>
      lam=> v 1 $ fst (v 0) $ snd (v 0)
  , lam=>
      lam=>
        lam=> v 2 $ [ v 1 , v 0 ]
  ]

l16 : forall {a b c} -> Thm (((a && b) => c) <=> (a => (b => c)))
l16 =
  [ lam=>
      lam=>
        lam=> v 2 $ [ v 1 , v 0 ]
  , lam=>
      lam=> v 1 $ fst (v 0) $ snd (v 0)
  ]

l17 : forall {a} -> Thm ((TRUE => a) <=> a)
l17 =
  [ lam=> v 0 $ (lam=> v 0)
  , lam=> lam=> v 1
  ]

l19 : forall {a b c} -> Thm (((a || b) => c) <=> (a => c) && (b => c))
l19 =
  [ lam=>
      [ lam=> v 1 $ left  (v 0)
      , lam=> v 1 $ right (v 0)
      ]
  , lam=>
      lam=>
        (case v 0
          => fst (v 2) $ (v 0)
          => snd (v 2) $ (v 0))
  ]
