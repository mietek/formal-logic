module Nc


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
syntax "efq" {na} ">>" [b]                             = efq' (\na => b)

data Theorem : (Context -> Type) -> Formula -> Type where
  hyp    : cx (formula a)
        -> Theorem cx a
  lam'   : (cx (formula a) -> Theorem cx b)
        -> Theorem cx (a >> b)
  (<<)   : Theorem cx (a >> b) -> Theorem cx a
        -> Theorem cx b
  pair'  : Theorem cx a -> Theorem cx b
        -> Theorem cx (a /\ b)
  fst    : Theorem cx (a /\ b)
        -> Theorem cx a
  snd    : Theorem cx (a /\ b)
        -> Theorem cx b
  one    : Theorem cx a
        -> Theorem cx (a \/ b)
  two    : Theorem cx b
        -> Theorem cx (a \/ b)
  case'  : Theorem cx (a \/ b) -> (cx (formula a) -> Theorem cx c) -> (cx (formula b) -> Theorem cx c)
        -> Theorem cx c
  pi'    : ({x : Value} -> cx (value x) -> Theorem cx (p x))
        -> Theorem cx (FORALL p)
  (<<!)  : Theorem cx (FORALL p) -> cx (value x)
        -> Theorem cx (p x)
  sig'   : cx (value x) -> Theorem cx (p x)
        -> Theorem cx (EXISTS p)
  take'  : Theorem cx (EXISTS p) -> (cx (formula (p x)) -> Theorem cx a)
        -> Theorem cx a
  efq'   : (cx (formula (NOT a)) -> Theorem cx BOTTOM)
        -> Theorem cx a


-- NOTE: Issue with scoped implicits:
-- https://github.com/idris-lang/Idris-dev/issues/2565

syntax "||-" [a] = Theorem cx a

-- prefix 1 ||-
--
-- (||-) : Formula -> Type
-- (||-) a = {cx : Context -> Type} -> Theorem cx a


I : ||- a >> a
I = lam x >> hyp x

K : ||- a >> b >> a
K = lam x >>
      lam y >> hyp x

S : ||- (a >> b >> c) >> (a >> b) >> a >> c
S = lam f >>
      lam g >>
        lam x >> (hyp f << hyp x) << (hyp g << hyp x)


Example214 : {p : Value -> Formula} ->
  ||- NOT (FORALL (\x => NOT (p x))) >> EXISTS p
Example214 =
  lam w >>
    efq u >>
      hyp w << (pi x !>>
                  lam v >>
                    hyp u << [ x !* hyp v ])
