-- Intuitionistic propositional logic, PHOAS approach, final encoding

module Pf.Ip where


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

TmRepr : Set1
TmRepr = Cx -> Ty -> Set

module ArrMp where
  record Tm (tr : TmRepr) : Set1 where
    infixl 1 _$_
    field
      var  : forall {tc a}   -> isTrue a tc               -> tr tc a
      lam' : forall {tc a b} -> (isTrue a tc -> tr tc b)  -> tr tc (a => b)
      _$_  : forall {tc a b} -> tr tc (a => b) -> tr tc a -> tr tc b

    lam'' : forall {tc a b} -> (tr tc a -> tr tc b) -> tr tc (a => b)
    lam'' f = lam' \x -> f (var x)

    syntax lam'' (\a -> b) = lam a => b
  open Tm {{...}} public

module Mp where
  record Tm (tr : TmRepr) : Set1 where
    field
      pair' : forall {tc a b}   -> tr tc a        -> tr tc b -> tr tc (a && b)
      fst   : forall {tc a b}   -> tr tc (a && b)            -> tr tc a
      snd   : forall {tc a b}   -> tr tc (a && b)            -> tr tc b
      left  : forall {tc a b}   -> tr tc a                   -> tr tc (a || b)
      right : forall {tc a b}   -> tr tc b                   -> tr tc (a || b)
      case' : forall {tc a b c} -> tr tc (a || b) -> (isTrue a tc -> tr tc c) -> (isTrue b tc -> tr tc c) -> tr tc c

      isArrMp : ArrMp.Tm tr
    open ArrMp.Tm isArrMp public

    case'' : forall {tc a b c} -> tr tc (a || b) -> (tr tc a -> tr tc c) -> (tr tc b -> tr tc c) -> tr tc c
    case'' xy f g = case' xy (\x -> f (var x)) (\y -> g (var y))

    syntax pair'  x y = [ x , y ]
    syntax case'' xy (\x -> z1) (\y -> z2) = case xy of x => z1 or y => z2
  open Tm {{...}} public

module Ip where
  record Tm (tr : TmRepr) : Set1 where
    field
      abort : forall {tc a} -> tr tc FALSE -> tr tc a

      isMp : Mp.Tm tr
    open Mp.Tm isMp public
  open Tm {{...}} public

  Thm : Ty -> Set1
  Thm a = forall {tr tc} {{_ : Tm tr}} -> tr tc a
open Ip public


-- Example theorems

t1 : forall {a b} -> Thm (a => NOT a => b)
t1 =
  lam x =>
    lam f => abort (f $ x)

t2 : forall {a b} -> Thm (NOT a => a => b)
t2 =
  lam f =>
    lam x => abort (f $ x)

t3 : forall {a} -> Thm (a => NOT (NOT a))
t3 =
  lam x =>
    lam f => f $ x

t4 : forall {a} -> Thm (NOT a <=> NOT (NOT (NOT a)))
t4 =
  [ lam f =>
      lam g => g $ f
  , lam g =>
      lam x => g $ (lam f => f $ x)
  ]
