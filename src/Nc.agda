module Nc where


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


infix 1 ||-_

data Judgement : Set where
  given : Individual -> Judgement
  true  : Proposition -> Judgement

Context : Set1
Context = Judgement -> Set

data Theorem (cx : Context) : Proposition -> Set

||-_ : Proposition -> Set1
||- a = forall {cx} -> Theorem cx a


infixl 6 _<<!_
infixl 5 _<<_

syntax lam' (\a -> b)                 = lam a >> b
syntax pair' a b                      = [ a * b ]
syntax case' ab (\a -> c1) (\b -> c2) = case ab of a >> c1 or b >> c2
syntax pi' (\x -> px)                 = pi x !>> px
syntax sig' x px                      = [ x !* px ]
syntax take' t (\px -> a)             = take t as px >> a
syntax efq' (\na -> b)                = efq na >> b

data Theorem cx where
  var   : forall {a}     -> cx (true a)
                         -> Theorem cx a
  lam'  : forall {a b}   -> (cx (true a) -> Theorem cx b)
                         -> Theorem cx (a >> b)
  _<<_  : forall {a b}   -> Theorem cx (a >> b) -> Theorem cx a
                         -> Theorem cx b
  pair' : forall {a b}   -> Theorem cx a -> Theorem cx b
                         -> Theorem cx (a /\ b)
  fst   : forall {a b}   -> Theorem cx (a /\ b)
                         -> Theorem cx a
  snd   : forall {a b}   -> Theorem cx (a /\ b)
                         -> Theorem cx b
  one   : forall {a b}   -> Theorem cx a
                         -> Theorem cx (a \/ b)
  two   : forall {a b}   -> Theorem cx b
                         -> Theorem cx (a \/ b)
  case' : forall {a b c} -> Theorem cx (a \/ b) -> (cx (true a) -> Theorem cx c) -> (cx (true b) -> Theorem cx c)
                         -> Theorem cx c
  pi'   : forall {p}     -> (forall {x} -> cx (given x) -> Theorem cx (p x))
                         -> Theorem cx (FORALL p)
  _<<!_ : forall {p x}   -> Theorem cx (FORALL p) -> cx (given x)
                         -> Theorem cx (p x)
  sig'  : forall {p x}   -> cx (given x) -> Theorem cx (p x)
                         -> Theorem cx (EXISTS p)
  take' : forall {p x a} -> Theorem cx (EXISTS p) -> (cx (true (p x)) -> Theorem cx a)
                         -> Theorem cx a
  efq'  : forall {a}     -> (cx (true (NOT a)) -> Theorem cx BOTTOM)
                         -> Theorem cx a


I : forall {a} -> ||- a >> a
I = lam x >> var x

K : forall {a b} -> ||- a >> b >> a
K = lam x >>
      lam y >> var x

S : forall {a b c} -> ||- (a >> b >> c) >> (a >> b) >> a >> c
S = lam f >>
      lam g >>
        lam x >> (var f << var x) << (var g << var x)


Example214 : forall {p} ->
  ||- NOT (FORALL (\x -> NOT (p x))) >> EXISTS p
Example214 =
  lam w >>
    efq u >>
      var w << (pi x !>>
                  lam v >>
                    var u << [ x !* var v ])
