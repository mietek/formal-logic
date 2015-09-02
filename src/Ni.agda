module Ni where


data Individual : Set where
  unit : Individual


infixl 7 _/\_
infixl 6 _\/_
infixr 5 _>>_
infixr 4 _>><<_

Predicate : Set

data Proposition : Set where
  _>>_   : Proposition -> Proposition -> Proposition
  _/\_   : Proposition -> Proposition -> Proposition
  _\/_   : Proposition -> Proposition -> Proposition
  FORALL : Predicate -> Proposition
  EXISTS : Predicate -> Proposition
  BOTTOM : Proposition

Predicate = Individual -> Proposition

_>><<_ : Proposition -> Proposition -> Proposition
a >><< b = (a >> b) /\ (b >> a)

NOT : Proposition -> Proposition
NOT a = a >> BOTTOM

TOP : Proposition
TOP = BOTTOM >> BOTTOM


infix 1 _|-_
infix 1 ||-_

data Judgement : Set where
  given : Individual -> Judgement
  true  : Proposition -> Judgement

Context : Set1
Context = Judgement -> Set


infixl 6 _<<!_
infixl 5 _<<_

syntax lam' (\a -> b)                 = lam a >> b
syntax pair' a b                      = [ a * b ]
syntax case' ab (\a -> c1) (\b -> c2) = case ab of a >> c1 or b >> c2
syntax pi' (\x -> px)                 = pi x !>> px
syntax sig' x px                      = [ x !* px ]
syntax take' t (\px -> a)             = take t as px >> a

data _|-_ (cx : Context) : Proposition -> Set where
  var   : forall {a}     -> cx (true a)
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
  pi'   : forall {p}     -> (forall {x} -> cx (given x) -> cx |- p x)
                         -> cx |- FORALL p
  _<<!_ : forall {p x}   -> cx |- FORALL p -> cx (given x)
                         -> cx |- p x
  sig'  : forall {p x}   -> cx (given x) -> cx |- p x
                         -> cx |- EXISTS p
  take' : forall {p x a} -> cx |- EXISTS p -> (cx (true (p x)) -> cx |- a)
                         -> cx |- a
  efq   : forall {a}     -> cx |- BOTTOM
                         -> cx |- a

||-_ : Proposition -> Set1
||- a = forall {cx} -> cx |- a


I : forall {a} -> ||- a >> a
I = lam x >> var x

K : forall {a b} -> ||- a >> b >> a
K = lam x >>
      lam y >> var x

S : forall {a b c} -> ||- (a >> b >> c) >> (a >> b) >> a >> c
S = lam f >>
      lam g >>
        lam x >> (var f << var x) << (var g << var x)


Example214 : forall {p q : Predicate} ->
  ||- FORALL (\x -> p x \/ NOT (p x)) /\ FORALL (\x -> p x >> EXISTS (\y -> q y)) >>
        FORALL (\x -> EXISTS (\y -> p x >> q y))
Example214 =
  lam u' >>
    pi x !>>
      case fst (var u') <<! x
      of u >>
        take snd (var u') <<! x << var u
        as w >>
          [ x !* lam z >> var w ]
      or v >>
        [ x !* lam w' >> efq (var v << var w') ]
