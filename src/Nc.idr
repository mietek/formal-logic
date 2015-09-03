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


prefix 1 ||-

data Judgement : Type where
  given : Individual -> Judgement
  true  : Proposition -> Judgement

Context : Type
Context = Judgement -> Type

Theorem : Context -> Proposition -> Type

(||-) : Proposition -> Type
(||-) a = {cx : Context} -> Theorem cx a


infixl 6 <<!
infixl 5 <<

syntax lam {a} ">>" [b]                                = lam' (\a => b)
syntax "[" [a] "*" [b] "]"                             = pair' a b
syntax "case" [ab] "of" {a} ">>" [c1] or {b} ">>" [c2] = case' ab (\a => c1) (\b => c2)
syntax pi {x} "!>>" [px]                               = pi' (\x => px)
syntax "[" [x] "!*" [px] "]"                           = sig' x px
syntax take [t] as {px} ">>" [a]                       = take' t (\px => a)
syntax "efq" {na} ">>" [b]                             = efq' (\na => b)

data Theorem : Context -> Proposition -> Type where
  var   : cx (true a)
       -> Theorem cx a
  lam'  : (cx (true a) -> Theorem cx b)
       -> Theorem cx (a >> b)
  (<<)  : Theorem cx (a >> b) -> Theorem cx a
       -> Theorem cx b
  pair' : Theorem cx a -> Theorem cx b
       -> Theorem cx (a /\ b)
  fst   : Theorem cx (a /\ b)
       -> Theorem cx a
  snd   : Theorem cx (a /\ b)
       -> Theorem cx b
  one   : Theorem cx a
       -> Theorem cx (a \/ b)
  two   : Theorem cx b
       -> Theorem cx (a \/ b)
  case' : Theorem cx (a \/ b) -> (cx (true a) -> Theorem cx c) -> (cx (true b) -> Theorem cx c)
       -> Theorem cx c
  pi'   : ({x : Individual} -> cx (given x) -> Theorem cx (p x))
       -> Theorem cx (FORALL p)
  (<<!) : Theorem cx (FORALL p) -> cx (given x)
       -> Theorem cx (p x)
  sig'  : cx (given x) -> Theorem cx (p x)
       -> Theorem cx (EXISTS p)
  take' : Theorem cx (EXISTS p) -> (cx (true (p x)) -> Theorem cx a)
       -> Theorem cx a
  efq'  : (cx (true (NOT a)) -> Theorem cx BOTTOM)
       -> Theorem cx a


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
