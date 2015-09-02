module Ni


data Individual : Type where
  unit : Individual


infixl 7 /\
infixl 6 \/
infixr 5 >>
infixr 4 >><<

data Formula : Type where
  (>>)   : Formula -> Formula -> Formula
  (/\)   : Formula -> Formula -> Formula
  (\/)   : Formula -> Formula -> Formula
  FORALL : (Individual -> Formula) -> Formula
  EXISTS : (Individual -> Formula) -> Formula
  BOTTOM : Formula

(>><<) : Formula -> Formula -> Formula
a >><< b = (a >> b) /\ (b >> a)

NOT : Formula -> Formula
NOT a = a >> BOTTOM

TOP : Formula
TOP = BOTTOM >> BOTTOM


data Context : Type where
  individual : Individual -> Context
  true       : Formula -> Context


infixl 6 <<!
infixl 5 <<

syntax lam {a} ">>" [b]                                = lam' (\a => b)
syntax "[" [a] "*" [b] "]"                             = pair' a b
syntax "case" [ab] "of" {a} ">>" [c1] or {b} ">>" [c2] = case' ab (\a => c1) (\b => c2)
syntax pi {x} "!>>" [px]                               = pi' (\x => px)
syntax "[" [x] "!*" [px] "]"                           = sig' x px
syntax take [t] as {px} ">>" [a]                       = take' t (\px => a)

infix 1 |-

data (|-) : (Context -> Type) -> Formula -> Type where
  hyp   : cx (true a)
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
  pi'   : ({x : Individual} -> cx (individual x) -> cx |- p x)
       -> cx |- FORALL p
  (<<!) : cx |- FORALL p -> cx (individual x)
       -> cx |- p x
  sig'  : cx (individual x) -> cx |- p x
       -> cx |- EXISTS p
  take' : cx |- EXISTS p -> (cx (true (p x)) -> cx |- a)
       -> cx |- a
  efq   : cx |- BOTTOM
       -> cx |- a


prefix 1 ||-

(||-) : Formula -> Type
(||-) a = {cx : Context -> Type} -> cx |- a


I : ||- a >> a
I = lam x >> hyp x

K : ||- a >> b >> a
K = lam x >>
      lam y >> hyp x

S : ||- (a >> b >> c) >> (a >> b) >> a >> c
S = lam f >>
      lam g >>
        lam x >> (hyp f << hyp x) << (hyp g << hyp x)


Example214 : {p, q : Individual -> Formula} ->
  ||- FORALL (\x => p x \/ NOT (p x)) /\ FORALL (\x => p x >> EXISTS (\y => q y)) >>
        FORALL (\x => EXISTS (\y => p x >> q y))
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
