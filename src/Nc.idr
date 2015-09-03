module Nc


infixl 7 /\
infixl 6 \/
infixr 5 >>
infixr 4 >><<

Predicate : Type

data Proposition : Type where
  (>>)   : Proposition -> Proposition -> Proposition
  (/\)   : Proposition -> Proposition -> Proposition
  (\/)   : Proposition -> Proposition -> Proposition
  FORALL : Predicate -> Proposition
  EXISTS : Predicate -> Proposition
  BOTTOM : Proposition

(>><<) : Proposition -> Proposition -> Proposition
a >><< b = (a >> b) /\ (b >> a)

NOT : Proposition -> Proposition
NOT a = a >> BOTTOM

TOP : Proposition
TOP = BOTTOM >> BOTTOM


data Individual : Type where
  unit : Individual

Predicate = Individual -> Proposition

data Judgement : Type where
  given : Individual -> Judgement
  true  : Proposition -> Judgement

Context : Type
Context = Judgement -> Type


infixl 6 <<!
infixl 5 <<

syntax lam {a} ">>" [b]                                = lam' (\a => b)
syntax "[" [a] "*" [b] "]"                             = pair' a b
syntax "case" [ab] "of" {a} ">>" [c1] or {b} ">>" [c2] = case' ab (\a => c1) (\b => c2)
syntax pi {x} "!>>" [px]                               = pi' (\x => px)
syntax "[" [x] "!*" [px] "]"                           = sig' x px
syntax take [t] as {px} ">>" [a]                       = take' t (\px => a)
syntax "efq" {na} ">>" [b]                             = efq' (\na => b)

data Term : Context -> Proposition -> Type where
  var   : cx (true a)
       -> Term cx a
  lam'  : (cx (true a) -> Term cx b)
       -> Term cx (a >> b)
  (<<)  : Term cx (a >> b) -> Term cx a
       -> Term cx b
  pair' : Term cx a -> Term cx b
       -> Term cx (a /\ b)
  fst   : Term cx (a /\ b)
       -> Term cx a
  snd   : Term cx (a /\ b)
       -> Term cx b
  one   : Term cx a
       -> Term cx (a \/ b)
  two   : Term cx b
       -> Term cx (a \/ b)
  case' : Term cx (a \/ b) -> (cx (true a) -> Term cx c) -> (cx (true b) -> Term cx c)
       -> Term cx c
  pi'   : ({x : Individual} -> cx (given x) -> Term cx (p x))
       -> Term cx (FORALL p)
  (<<!) : Term cx (FORALL p) -> cx (given x)
       -> Term cx (p x)
  sig'  : cx (given x) -> Term cx (p x)
       -> Term cx (EXISTS p)
  take' : Term cx (EXISTS p) -> (cx (true (p x)) -> Term cx a)
       -> Term cx a
  efq'  : (cx (true (NOT a)) -> Term cx BOTTOM)
       -> Term cx a

Theorem : Proposition -> Type
Theorem a = {cx : Context} -> Term cx a


i : Theorem (a >> a)
i = lam x >> var x

k : Theorem (a >> b >> a)
k = lam x >>
      lam y >> var x

s : Theorem ((a >> b >> c) >> (a >> b) >> a >> c)
s = lam f >>
      lam g >>
        lam x >> (var f << var x) << (var g << var x)


example214 : {p : Predicate} ->
  Theorem (NOT (FORALL (\x => NOT (p x))) >> EXISTS p)
example214 =
  lam w >>
    efq u >>
      var w << (pi x !>>
                  lam v >>
                    var u << [ x !* var v ])
