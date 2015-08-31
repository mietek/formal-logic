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


I : Theorem hs (a >> a)
I = lam x >> hyp x

K : Theorem hs (a >> b >> a)
K = lam x >>
      lam y >> hyp x

S : Theorem hs ((a >> b >> c) >> (a >> b) >> a >> c)
S = lam f >>
      lam g >>
        lam x >> (hyp f << hyp x) << (hyp g << hyp x)
