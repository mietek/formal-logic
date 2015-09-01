module Nc where


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
syntax efq' (\na -> b)                = efq na >> b

infix 1 _|-_

data _|-_ (cx : Context -> Set) : Formula -> Set where
  hyp   : forall {a}     -> cx (formula a)
                         -> cx |- a
  lam'  : forall {a b}   -> (cx (formula a) -> cx |- b)
                         -> cx |- a >> b
  _<<_  : forall {a b}   -> cx |- a >> b -> cx |- a
                         -> cx |- b
  pair' : forall {a b}   -> cx |- a -> cx |- b
                         -> cx |- a /\ b
  fst   : forall {a b}   -> cx |- a /\ b
                         -> cx |- a
  snd   : forall {a b}   -> cx |- a /\ b
                         -> cx |- b
  one   : forall {a b}   -> cx |- a
                         -> cx |- a \/ b
  two   : forall {a b}   -> cx |- b
                         -> cx |- a \/ b
  case' : forall {a b c} -> cx |- a \/ b -> (cx (formula a) -> cx |- c) -> (cx (formula b) -> cx |- c)
                         -> cx |- c
  pi'   : forall {p}     -> (forall {x} -> cx (value x) -> cx |- p x)
                         -> cx |- FORALL p
  _<<!_ : forall {p x}   -> cx |- FORALL p -> cx (value x)
                         -> cx |- p x
  sig'  : forall {p x}   -> cx (value x) -> cx |- p x
                         -> cx |- EXISTS p
  take' : forall {p x a} -> cx |- EXISTS p -> (cx (formula (p x)) -> cx |- a)
                         -> cx |- a
  efq'  : forall {a}     -> (cx (formula (NOT a)) -> cx |- BOTTOM)
                         -> cx |- a


infix 1 ||-_

||-_ : Formula -> Set1
||- a = forall {cx} -> cx |- a


I : forall {a} -> ||- a >> a
I = lam x >> hyp x

K : forall {a b} -> ||- a >> b >> a
K = lam x >>
      lam y >> hyp x

S : forall {a b c} -> ||- (a >> b >> c) >> (a >> b) >> a >> c
S = lam f >>
      lam g >>
        lam x >> (hyp f << hyp x) << (hyp g << hyp x)


Example214 : forall {p} ->
  ||- NOT (FORALL (\x -> NOT (p x))) >> EXISTS p
Example214 =
  lam w >>
    efq u >>
      hyp w << (pi x !>>
                  lam v >>
                    hyp u << [ x !* hyp v ])
