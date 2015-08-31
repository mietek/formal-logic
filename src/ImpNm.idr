module ImpNm


infixr 5 >>

data Formula : Type where
  (>>) : Formula -> Formula -> Formula


infixl 5 <<

syntax "lam" {a} ">>" [b] = lam' (\a => b)

data Theorem : (Formula -> Type) -> Formula -> Type where
  hyp  : hs a
      -> Theorem hs a
  lam' : (hs a -> Theorem hs b)
      -> Theorem hs (a >> b)
  (<<) : Theorem hs (a >> b) -> Theorem hs a
      -> Theorem hs b


-- NOTE: Issue with scoped implicits:
-- https://github.com/idris-lang/Idris-dev/issues/2565

syntax "Theorem1" [a] = Theorem hs a

-- Theorem1 : Formula -> Type
-- Theorem1 a = {hs : Formula -> Type} -> Theorem hs a


I : Theorem1 (a >> a)
I = lam x >> hyp x

K : Theorem1 (a >> b >> a)
K = lam x >>
      lam y >> hyp x

S : Theorem1 ((a >> b >> c) >> (a >> b) >> a >> c)
S = lam f >>
      lam g >>
        lam x >> (hyp f << hyp x) << (hyp g << hyp x)
