module Nc


data Individual : Type where
  unit : Individual


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

Predicate = Individual -> Proposition

(>><<) : Proposition -> Proposition -> Proposition
a >><< b = (a >> b) /\ (b >> a)

NOT : Proposition -> Proposition
NOT a = a >> BOTTOM

TOP : Proposition
TOP = BOTTOM >> BOTTOM


infix  1 |-
prefix 1 ||-

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

data (|-) : Context -> Proposition -> Type where
  var   : cx (true a)
       -> cx |- a
  lam'  : (cx (true a) -> cx |- b)
       -> cx |- a >> b
  (<<)  : cx |- a >> b -> cx |- a
       -> cx |- b
  pair' : cx |- a -> cx |- b
       -> cx |- a /\ b
  fst   : cx |- a /\ b
       -> cx |- a
  snd   : cx |- a /\ b
       -> cx |- b
  one   : cx |- a
       -> cx |- a \/ b
  two   : cx |- b
       -> cx |- a \/ b
  case' : cx |- a \/ b -> (cx (true a) -> cx |- c) -> (cx (true b) -> cx |- c)
       -> cx |- c
  pi'   : ({x : Individual} -> cx (given x) -> cx |- p x)
       -> cx |- FORALL p
  (<<!) : cx |- FORALL p -> cx (given x)
       -> cx |- p x
  sig'  : cx (given x) -> cx |- p x
       -> cx |- EXISTS p
  take' : cx |- EXISTS p -> (cx (true (p x)) -> cx |- a)
       -> cx |- a
  efq'  : (cx (true (NOT a)) -> cx |- BOTTOM)
       -> cx |- a

(||-) : Proposition -> Type
(||-) a = {cx : Context} -> cx |- a


I : ||- a >> a
I = lam x >> var x

K : ||- a >> b >> a
K = lam x >>
      lam y >> var x

S : ||- (a >> b >> c) >> (a >> b) >> a >> c
S = lam f >>
      lam g >>
        lam x >> (var f << var x) << (var g << var x)


Example214 : {p : Predicate} ->
  ||- NOT (FORALL (\x => NOT (p x))) >> EXISTS p
Example214 =
  lam w >>
    efq u >>
      var w << (pi x !>>
                  lam v >>
                    var u << [ x !* var v ])
