module Ni where


data Individual : Set where
  unit : Individual


infixl 7 _/\_
infixl 6 _\/_
infixr 5 _>>_
infixr 4 _>><<_

data Formula : Set where
  _>>_   : Formula -> Formula -> Formula
  _/\_   : Formula -> Formula -> Formula
  _\/_   : Formula -> Formula -> Formula
  FORALL : (Individual -> Formula) -> Formula
  EXISTS : (Individual -> Formula) -> Formula
  BOTTOM : Formula

_>><<_ : Formula -> Formula -> Formula
a >><< b = (a >> b) /\ (b >> a)

NOT : Formula -> Formula
NOT a = a >> BOTTOM

TOP : Formula
TOP = BOTTOM >> BOTTOM


data Context : Set where
  individual : Individual -> Context
  true       : Formula -> Context


infixl 6 _<<!_
infixl 5 _<<_

syntax lam' (\a -> b)                 = lam a >> b
syntax pair' a b                      = [ a * b ]
syntax case' ab (\a -> c1) (\b -> c2) = case ab of a >> c1 or b >> c2
syntax pi' (\x -> px)                 = pi x !>> px
syntax sig' x px                      = [ x !* px ]
syntax take' t (\px -> a)             = take t as px >> a

infix 1 _|-_

data _|-_ (cx : Context -> Set) : Formula -> Set where
  hyp   : forall {a}     -> cx (true a)
                         -> cx |- a
  lam'  : forall {a b}   -> (cx (true a) -> cx |- b)
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
  case' : forall {a b c} -> cx |- a \/ b -> (cx (true a) -> cx |- c) -> (cx (true b) -> cx |- c)
                         -> cx |- c
  pi'   : forall {p}     -> (forall {x} -> cx (individual x) -> cx |- p x)
                         -> cx |- FORALL p
  _<<!_ : forall {p x}   -> cx |- FORALL p -> cx (individual x)
                         -> cx |- p x
  sig'  : forall {p x}   -> cx (individual x) -> cx |- p x
                         -> cx |- EXISTS p
  take' : forall {p x a} -> cx |- EXISTS p -> (cx (true (p x)) -> cx |- a)
                         -> cx |- a
  efq   : forall {a}     -> cx |- BOTTOM
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


Example214 : forall {p q : Individual -> Formula} ->
  ||- FORALL (\x -> p x \/ NOT (p x)) /\ FORALL (\x -> p x >> EXISTS (\y -> q y)) >>
        FORALL (\x -> EXISTS (\y -> p x >> q y))
Example214 =
  lam u' >>
    pi x !>>
      case fst (hyp u') <<! x
      of u >>
        take snd (hyp u') <<! x << hyp u
        as w >>
          [ x !* lam z >> hyp w ]
      or v >>
        [ x !* lam w' >> efq (hyp v << hyp w') ]
