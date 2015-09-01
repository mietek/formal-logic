module Nm


data Value : Type where
  Unit : Value


infixl 7 /\
infixl 6 \/
infixr 5 >>
infixr 4 >><<

data Formula : Type where
  (>>)   : Formula -> Formula -> Formula
  (/\)   : Formula -> Formula -> Formula
  (\/)   : Formula -> Formula -> Formula
  FORALL : (Value -> Formula) -> Formula
  EXISTS : (Value -> Formula) -> Formula
  BOTTOM : Formula

(>><<) : Formula -> Formula -> Formula
a >><< b = (a >> b) /\ (b >> a)

NOT : Formula -> Formula
NOT a = a >> BOTTOM

TOP : Formula
TOP = BOTTOM >> BOTTOM


data Context : Type where
  value   : Value -> Context
  formula : Formula -> Context


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
  hyp   : cx (formula a)
       -> cx |- a
  lam'  : (cx (formula a) -> cx |- b)
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
  case' : cx |- a \/ b -> (cx (formula a) -> cx |- c) -> (cx (formula b) -> cx |- c)
       -> cx |- c
  pi'   : ({x : Value} -> cx (value x) -> cx |- p x)
       -> cx |- FORALL p
  (<<!) : cx |- FORALL p -> cx (value x)
       -> cx |- p x
  sig'  : cx (value x) -> cx |- p x
       -> cx |- EXISTS p
  take' : cx |- EXISTS p -> (cx (formula (p x)) -> cx |- a)
       -> cx |- a


-- NOTE: Issue with scoped implicits:
-- https://github.com/idris-lang/Idris-dev/issues/2565

syntax "||-" [a] = cx |- a

-- prefix 1 ||-
--
-- (||-) : Formula -> Type
-- (||-) a = {cx : Context -> Type} -> cx |- a


I : ||- a >> a
I = lam x >> hyp x

K : ||- a >> b >> a
K = lam x >>
      lam y >> hyp x

S : ||- (a >> b >> c) >> (a >> b) >> a >> c
S = lam f >>
      lam g >>
        lam x >> (hyp f << hyp x) << (hyp g << hyp x)
