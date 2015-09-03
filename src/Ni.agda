module Ni where


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

_>><<_ : Proposition -> Proposition -> Proposition
a >><< b = (a >> b) /\ (b >> a)

NOT : Proposition -> Proposition
NOT a = a >> BOTTOM

TOP : Proposition
TOP = BOTTOM >> BOTTOM


data Individual : Set where
  unit : Individual

Predicate = Individual -> Proposition

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

data Term (cx : Context) : Proposition -> Set where
  var   : forall {a}     -> cx (true a)
                         -> Term cx a
  lam'  : forall {a b}   -> (cx (true a) -> Term cx b)
                         -> Term cx (a >> b)
  _<<_  : forall {a b}   -> Term cx (a >> b) -> Term cx a
                         -> Term cx b
  pair' : forall {a b}   -> Term cx a -> Term cx b
                         -> Term cx (a /\ b)
  fst   : forall {a b}   -> Term cx (a /\ b)
                         -> Term cx a
  snd   : forall {a b}   -> Term cx (a /\ b)
                         -> Term cx b
  one   : forall {a b}   -> Term cx a
                         -> Term cx (a \/ b)
  two   : forall {a b}   -> Term cx b
                         -> Term cx (a \/ b)
  case' : forall {a b c} -> Term cx (a \/ b) -> (cx (true a) -> Term cx c) -> (cx (true b) -> Term cx c)
                         -> Term cx c
  pi'   : forall {p}     -> (forall {x} -> cx (given x) -> Term cx (p x))
                         -> Term cx (FORALL p)
  _<<!_ : forall {p x}   -> Term cx (FORALL p) -> cx (given x)
                         -> Term cx (p x)
  sig'  : forall {p x}   -> cx (given x) -> Term cx (p x)
                         -> Term cx (EXISTS p)
  take' : forall {p x a} -> Term cx (EXISTS p) -> (cx (true (p x)) -> Term cx a)
                         -> Term cx a
  efq   : forall {a}     -> Term cx BOTTOM
                         -> Term cx a

Theorem : Proposition -> Set1
Theorem a = forall {cx} -> Term cx a


i : forall {a} -> Theorem (a >> a)
i = lam x >> var x

k : forall {a b} -> Theorem (a >> b >> a)
k = lam x >>
      lam y >> var x

s : forall {a b c} -> Theorem ((a >> b >> c) >> (a >> b) >> a >> c)
s = lam f >>
      lam g >>
        lam x >> (var f << var x) << (var g << var x)


example214 : forall {p q : Predicate} ->
  Theorem (FORALL (\x -> p x \/ NOT (p x)) /\ FORALL (\x -> p x >> EXISTS (\y -> q y)) >>
    FORALL (\x -> EXISTS (\y -> p x >> q y)))
example214 =
  lam u' >>
    pi x !>>
      case fst (var u') <<! x
      of u >>
        take snd (var u') <<! x << var u
        as w >>
          [ x !* lam z >> var w ]
      or v >>
        [ x !* lam w' >> efq (var v << var w') ]
