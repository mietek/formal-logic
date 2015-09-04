module Ni


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

data Proof : Context -> Proposition -> Type where
  var   : cx (true a)
       -> Proof cx a
  lam'  : (cx (true a) -> Proof cx b)
       -> Proof cx (a >> b)
  (<<)  : Proof cx (a >> b) -> Proof cx a
       -> Proof cx b
  pair' : Proof cx a -> Proof cx b
       -> Proof cx (a /\ b)
  fst   : Proof cx (a /\ b)
       -> Proof cx a
  snd   : Proof cx (a /\ b)
       -> Proof cx b
  one   : Proof cx a
       -> Proof cx (a \/ b)
  two   : Proof cx b
       -> Proof cx (a \/ b)
  case' : Proof cx (a \/ b) -> (cx (true a) -> Proof cx c) -> (cx (true b) -> Proof cx c)
       -> Proof cx c
  pi'   : ({x : Individual} -> cx (given x) -> Proof cx (p x))
       -> Proof cx (FORALL p)
  (<<!) : Proof cx (FORALL p) -> cx (given x)
       -> Proof cx (p x)
  sig'  : cx (given x) -> Proof cx (p x)
       -> Proof cx (EXISTS p)
  take' : Proof cx (EXISTS p) -> (cx (true (p x)) -> Proof cx a)
       -> Proof cx a
  efq   : Proof cx BOTTOM
       -> Proof cx a

Theorem : Proposition -> Type
Theorem a = {cx : Context} -> Proof cx a


i : Theorem (a >> a)
i = lam x >> var x

k : Theorem (a >> b >> a)
k = lam x >>
      lam y >> var x

s : Theorem ((a >> b >> c) >> (a >> b) >> a >> c)
s = lam f >>
      lam g >>
        lam x >> (var f << var x) << (var g << var x)


example214 : {p, q : Predicate} ->
  Theorem (FORALL (\x => p x \/ NOT (p x)) /\ FORALL (\x => p x >> EXISTS (\y => q y)) >>
    FORALL (\x => EXISTS (\y => p x >> q y)))
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
