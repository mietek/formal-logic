-- Minimal propositional logic, de Bruijn approach, final encoding

module Bf.Mp where

open import Lib using (List; _,_; LMem; lzero; lsuc)


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

Cx : Set
Cx = List Ty

isTrue : Ty -> Cx -> Set
isTrue a tc = LMem a tc


-- Terms

TmRepr : Set1
TmRepr = Cx -> Ty -> Set

module ArrMp where
  record Tm (tr : TmRepr) : Set1 where
    infixl 1 _$_
    infixr 0 lam=>_
    field
      var    : forall {tc a}   -> isTrue a tc               -> tr tc a
      lam=>_ : forall {tc a b} -> tr (tc , a) b             -> tr tc (a => b)
      _$_    : forall {tc a b} -> tr tc (a => b) -> tr tc a -> tr tc b

    v0 : forall {tc a} -> tr (tc , a) a
    v0 = var lzero

    v1 : forall {tc a b} -> tr (tc , a , b) a
    v1 = var (lsuc lzero)

    v2 : forall {tc a b c} -> tr (tc , a , b , c) a
    v2 = var (lsuc (lsuc lzero))
  open Tm {{...}} public

module Mp where
  record Tm (tr : TmRepr) : Set1 where
    field
      pair' : forall {tc a b}   -> tr tc a        -> tr tc b -> tr tc (a && b)
      fst   : forall {tc a b}   -> tr tc (a && b)            -> tr tc a
      snd   : forall {tc a b}   -> tr tc (a && b)            -> tr tc b
      left  : forall {tc a b}   -> tr tc a                   -> tr tc (a || b)
      right : forall {tc a b}   -> tr tc b                   -> tr tc (a || b)
      case' : forall {tc a b c} -> tr tc (a || b) -> tr (tc , a) c -> tr (tc , b) c -> tr tc c

      isArrMp : ArrMp.Tm tr
    open ArrMp.Tm isArrMp public

    syntax pair' x y    = [ x , y ]
    syntax case' xy x y = case xy => x => y
  open Tm {{...}} public

  Thm : Ty -> Set1
  Thm a = forall {tr tc} {{_ : Tm tr}} -> tr tc a
open Mp public


-- Example theorems

c1 : forall {a b} -> Thm (a && b <=> b && a)
c1 =
  [ lam=> [ snd v0 , fst v0 ]
  , lam=> [ snd v0 , fst v0 ]
  ]

c2 : forall {a b} -> Thm (a || b <=> b || a)
c2 =
  [ lam=>
      (case v0
        => right v0
        => left v0)
  , lam=>
      (case v0
        => right v0
        => left v0)
  ]

i1 : forall {a} -> Thm (a && a <=> a)
i1 =
  [ lam=> fst v0
  , lam=> [ v0 , v0 ]
  ]

i2 : forall {a} -> Thm (a || a <=> a)
i2 =
  [ lam=>
      (case v0
        => v0
        => v0)
  , lam=> left v0
  ]

l3 : forall {a} -> Thm ((a => a) <=> TRUE)
l3 =
  [ lam=> lam=> v0
  , lam=> lam=> v0
  ]

l1 : forall {a b c} -> Thm (a && (b && c) <=> (a && b) && c)
l1 =
  [ lam=>
      [ [ fst v0 , fst (snd v0) ]
      , snd (snd v0)
      ]
  , lam=>
      [ fst (fst v0)
      , [ snd (fst v0) , snd v0 ]
      ]
  ]

l2 : forall {a} -> Thm (a && TRUE <=> a)
l2 =
  [ lam=> fst v0
  , lam=> [ v0 , lam=> v0 ]
  ]

l4 : forall {a b c} -> Thm (a && (b || c) <=> (a && b) || (a && c))
l4 =
  [ lam=>
      (case snd v0
        => left  [ fst v1 , v0 ]
        => right [ fst v1 , v0 ])
  , lam=>
      (case v0
        => [ fst v0 , left  (snd v0) ]
        => [ fst v0 , right (snd v0) ])
  ]

l6 : forall {a b c} -> Thm (a || (b && c) <=> (a || b) && (a || c))
l6 =
  [ lam=>
      (case v0
        => [ left v0 , left v0 ]
        => [ right (fst v0) , right (snd v0) ])
  , lam=>
      (case fst v0
        => left v0
        =>
          case snd v1
            => left v0
            => right [ v1 , v0 ])
  ]

l7 : forall {a} -> Thm (a || TRUE <=> TRUE)
l7 =
  [ lam=> lam=> v0
  , lam=> right v0
  ]

l9 : forall {a b c} -> Thm (a || (b || c) <=> (a || b) || c)
l9 =
  [ lam=>
      (case v0
        => left (left v0)
        =>
          case v0
            => left (right v0)
            => right v0)
  , lam=>
      (case v0
        =>
          case v0
            => left v0
            => right (left v0)
        => right (right v0))
  ]

l11 : forall {a b c} -> Thm ((a => (b && c)) <=> (a => b) && (a => c))
l11 =
  [ lam=>
      [ lam=> fst (v1 $ v0)
      , lam=> snd (v1 $ v0)
      ]
  , lam=>
      lam=> [ fst v1 $ v0 , snd v1 $ v0 ]
  ]

l12 : forall {a} -> Thm ((a => TRUE) <=> TRUE)
l12 =
  [ lam=> lam=> v0
  , lam=> lam=> v1
  ]

l13 : forall {a b c} -> Thm ((a => (b => c)) <=> ((a && b) => c))
l13 =
  [ lam=>
      lam=> v1 $ fst v0 $ snd v0
  , lam=>
      lam=>
        lam=> v2 $ [ v1 , v0 ]
  ]

l16 : forall {a b c} -> Thm (((a && b) => c) <=> (a => (b => c)))
l16 =
  [ lam=>
      lam=>
        lam=> v2 $ [ v1 , v0 ]
  , lam=>
      lam=> v1 $ fst v0 $ snd v0
  ]

l17 : forall {a} -> Thm ((TRUE => a) <=> a)
l17 =
  [ lam=> v0 $ (lam=> v0)
  , lam=> lam=> v1
  ]

l19 : forall {a b c} -> Thm (((a || b) => c) <=> (a => c) && (b => c))
l19 =
  [ lam=>
      [ lam=> v1 $ left v0
      , lam=> v1 $ right v0
      ]
  , lam=>
      lam=>
        (case v0
          => fst v2 $ v0
          => snd v2 $ v0)
  ]
