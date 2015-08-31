module ImpHm


infixr 5 >>

data Formula : Type where
  (>>) : Formula -> Formula -> Formula


infixl 5 <<

data Theorem : Formula -> Type where
  (<<) : Theorem (a >> b) -> Theorem a
      -> Theorem b
  K    : Theorem (a >> b >> a)
  S    : Theorem ((a >> b >> c) >> (a >> b) >> a >> c)


I : Theorem (a >> a)
I {a} = (S {b = a >> a} << K) << K
