module Ni where


data Value : Set where
  Unit : Value


infixl 7 _/\_
infixl 6 _\/_
infixr 5 _|>_
infixr 4 _|><|_

data Formula : Set where
  _|>_   : Formula -> Formula -> Formula
  _/\_   : Formula -> Formula -> Formula
  _\/_   : Formula -> Formula -> Formula
  FORALL : (Value -> Formula) -> Formula
  EXISTS : (Value -> Formula) -> Formula
  BOTTOM : Formula

_|><|_ : Formula -> Formula -> Formula
a |><| b = (a |> b) /\ (b |> a)

NOT : Formula -> Formula
NOT a = a |> BOTTOM

TOP : Formula
TOP = BOTTOM |> BOTTOM


infixl 6 _<<!_
infixl 5 _<<_

syntax lam' (\a -> b)                 = lam a >> b
syntax pair' a b                      = [ a * b ]
syntax case' ab (\a -> c1) (\b -> c2) = case ab of a >> c1 or b >> c2
syntax pi' (\x -> px)                 = pi x !>> px
syntax sig' x px                      = [ x !* px ]
syntax take' t (\px -> a)             = take t as px >> a

data Theorem (vs : Value -> Set) (hs : Formula -> Set) : Formula -> Set where
  hyp    : forall {a}     -> hs a
                          -> Theorem vs hs a
  lam'   : forall {a b}   -> (hs a -> Theorem vs hs b)
                          -> Theorem vs hs (a |> b)
  _<<_   : forall {a b}   -> Theorem vs hs (a |> b) -> Theorem vs hs a
                          -> Theorem vs hs b
  pair'  : forall {a b}   -> Theorem vs hs a -> Theorem vs hs b
                          -> Theorem vs hs (a /\ b)
  fst    : forall {a b}   -> Theorem vs hs (a /\ b)
                          -> Theorem vs hs a
  snd    : forall {a b}   -> Theorem vs hs (a /\ b)
                          -> Theorem vs hs b
  one    : forall {a b}   -> Theorem vs hs a
                          -> Theorem vs hs (a \/ b)
  two    : forall {a b}   -> Theorem vs hs b
                          -> Theorem vs hs (a \/ b)
  case'  : forall {a b c} -> Theorem vs hs (a \/ b) -> (hs a -> Theorem vs hs c) -> (hs b -> Theorem vs hs c)
                          -> Theorem vs hs c
  pi'    : forall {p}     -> (forall {x} -> vs x -> Theorem vs hs (p x))
                          -> Theorem vs hs (FORALL p)
  _<<!_  : forall {p x}   -> Theorem vs hs (FORALL p) -> vs x
                          -> Theorem vs hs (p x)
  sig'   : forall {p x}   -> vs x -> Theorem vs hs (p x)
                          -> Theorem vs hs (EXISTS p)
  take'  : forall {p x a} -> Theorem vs hs (EXISTS p) -> (hs (p x) -> Theorem vs hs a)
                          -> Theorem vs hs a
  efq    : forall {a}     -> Theorem vs hs BOTTOM
                          -> Theorem vs hs a


I : forall {vs hs a} -> Theorem vs hs (a |> a)
I = lam x >> hyp x

K : forall {vs hs a b} -> Theorem vs hs (a |> b |> a)
K = lam x >>
      lam y >> hyp x

S : forall {vs hs a b c} -> Theorem vs hs ((a |> b |> c) |> (a |> b) |> a |> c)
S = lam f >>
      lam g >>
        lam x >> (hyp f << hyp x) << (hyp g << hyp x)


Example214 : forall {vs hs} -> {p q : Value -> Formula} -> Theorem vs hs
  (FORALL (\x -> p x \/ NOT (p x)) /\ FORALL (\x -> p x |> EXISTS (\y -> q y)) |>
    FORALL (\x -> EXISTS (\y -> p x |> q y)))
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
