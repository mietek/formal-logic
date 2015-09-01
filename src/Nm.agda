module Nm where


data Value : Set where
  Unit : Value


infixl 7 _/\_
infixl 6 _\/_
infixr 5 _>>_
infixr 4 _>><<_

data Formula : Set where
  _>>_   : Formula -> Formula -> Formula
  _/\_   : Formula -> Formula -> Formula
  _\/_   : Formula -> Formula -> Formula
  FORALL : (Value -> Formula) -> Formula
  EXISTS : (Value -> Formula) -> Formula
  BOTTOM : Formula

_>><<_ : Formula -> Formula -> Formula
a >><< b = (a >> b) /\ (b >> a)

NOT : Formula -> Formula
NOT a = a >> BOTTOM

TOP : Formula
TOP = BOTTOM >> BOTTOM


data Context : Set where
  value   : Value -> Context
  formula : Formula -> Context


infixl 6 _<<!_
infixl 5 _<<_

syntax lam' (\a -> b)                 = lam a >> b
syntax pair' a b                      = [ a * b ]
syntax case' ab (\a -> c1) (\b -> c2) = case ab of a >> c1 or b >> c2
syntax pi' (\x -> px)                 = pi x !>> px
syntax sig' x px                      = [ x !* px ]
syntax take' t (\px -> a)             = take t as px >> a

data Theorem (cx : Context -> Set) : Formula -> Set where
  hyp    : forall {a}     -> cx (formula a)
                          -> Theorem cx a
  lam'   : forall {a b}   -> (cx (formula a) -> Theorem cx b)
                          -> Theorem cx (a >> b)
  _<<_   : forall {a b}   -> Theorem cx (a >> b) -> Theorem cx a
                          -> Theorem cx b
  pair'  : forall {a b}   -> Theorem cx a -> Theorem cx b
                          -> Theorem cx (a /\ b)
  fst    : forall {a b}   -> Theorem cx (a /\ b)
                          -> Theorem cx a
  snd    : forall {a b}   -> Theorem cx (a /\ b)
                          -> Theorem cx b
  one    : forall {a b}   -> Theorem cx a
                          -> Theorem cx (a \/ b)
  two    : forall {a b}   -> Theorem cx b
                          -> Theorem cx (a \/ b)
  case'  : forall {a b c} -> Theorem cx (a \/ b) -> (cx (formula a) -> Theorem cx c) -> (cx (formula b) -> Theorem cx c)
                          -> Theorem cx c
  pi'    : forall {p}     -> (forall {x} -> cx (value x) -> Theorem cx (p x))
                          -> Theorem cx (FORALL p)
  _<<!_  : forall {p x}   -> Theorem cx (FORALL p) -> cx (value x)
                          -> Theorem cx (p x)
  sig'   : forall {p x}   -> cx (value x) -> Theorem cx (p x)
                          -> Theorem cx (EXISTS p)
  take'  : forall {p x a} -> Theorem cx (EXISTS p) -> (cx (formula (p x)) -> Theorem cx a)
                          -> Theorem cx a


infix 1 ||-_

||-_ : Formula -> Set1
||-_ a = forall {cx} -> Theorem cx a


I : forall {a} -> ||- a >> a
I = lam x >> hyp x

K : forall {a b} -> ||- a >> b >> a
K = lam x >>
      lam y >> hyp x

S : forall {a b c} -> ||- (a >> b >> c) >> (a >> b) >> a >> c
S = lam f >>
      lam g >>
        lam x >> (hyp f << hyp x) << (hyp g << hyp x)
