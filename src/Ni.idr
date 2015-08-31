module Ni


data Value : Type where
  Unit : Value


infixl 7 /\
infixl 6 \/
infixr 5 |>
infixr 4 |><|

data Formula : Type where
  (|>)   : Formula -> Formula -> Formula
  (/\)   : Formula -> Formula -> Formula
  (\/)   : Formula -> Formula -> Formula
  FORALL : (Value -> Formula) -> Formula
  EXISTS : (Value -> Formula) -> Formula
  BOTTOM : Formula

(|><|) : Formula -> Formula -> Formula
a |><| b = (a |> b) /\ (b |> a)

NOT : Formula -> Formula
NOT a = a |> BOTTOM

TOP : Formula
TOP = BOTTOM |> BOTTOM


infixl 6 <<!
infixl 5 <<

syntax lam {a} ">>" [b]                                = lam' (\a => b)
syntax "[" [a] "*" [b] "]"                             = pair' a b
syntax "case" [ab] "of" {a} ">>" [c1] or {b} ">>" [c2] = case' ab (\a => c1) (\b => c2)
syntax pi {x} "!>>" [px]                               = pi' (\x => px)
syntax "[" [x] "!*" [px] "]"                           = sig' x px
syntax take [t] as {px} ">>" [a]                       = take' t (\px => a)

data Theorem : (Value -> Type) -> (Formula -> Type) -> Formula -> Type where
  hyp    : hs a
        -> Theorem vs hs a
  lam'   : (hs a -> Theorem vs hs b)
        -> Theorem vs hs (a |> b)
  (<<)   : Theorem vs hs (a |> b) -> Theorem vs hs a
        -> Theorem vs hs b
  pair'  : Theorem vs hs a -> Theorem vs hs b
        -> Theorem vs hs (a /\ b)
  fst    : Theorem vs hs (a /\ b)
        -> Theorem vs hs a
  snd    : Theorem vs hs (a /\ b)
        -> Theorem vs hs b
  one    : Theorem vs hs a
        -> Theorem vs hs (a \/ b)
  two    : Theorem vs hs b
        -> Theorem vs hs (a \/ b)
  case'  : Theorem vs hs (a \/ b) -> (hs a -> Theorem vs hs c) -> (hs b -> Theorem vs hs c)
        -> Theorem vs hs c
  pi'    : ({x : Value} -> vs x -> Theorem vs hs (p x))
        -> Theorem vs hs (FORALL p)
  (<<!)  : Theorem vs hs (FORALL p) -> vs x
        -> Theorem vs hs (p x)
  sig'   : vs x -> Theorem vs hs (p x)
        -> Theorem vs hs (EXISTS p)
  take'  : Theorem vs hs (EXISTS p) -> (hs (p x) -> Theorem vs hs a)
        -> Theorem vs hs a
  efq    : Theorem vs hs BOTTOM
        -> Theorem vs hs a


I : Theorem vs hs (a |> a)
I = lam x >> hyp x

K : Theorem vs hs (a |> b |> a)
K = lam x >>
      lam y >> hyp x

S : Theorem vs hs ((a |> b |> c) |> (a |> b) |> a |> c)
S = lam f >>
      lam g >>
        lam x >> (hyp f << hyp x) << (hyp g << hyp x)


Example214 : {p, q : Value -> Formula} -> Theorem vs hs
  (FORALL (\x => p x \/ NOT (p x)) /\ FORALL (\x => p x |> EXISTS (\y => q y)) |>
    FORALL (\x => EXISTS (\y => p x |> q y)))
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
