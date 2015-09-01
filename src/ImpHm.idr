module ImpHm


infixr 5 >>

data Formula : Type where
  (>>) : Formula -> Formula -> Formula


infixl 5 <<

prefix 1 ||-

data (||-) : Formula -> Type where
  (<<) : ||- a >> b -> ||- a
      -> ||- b
  K    : ||- a >> b >> a
  S    : ||- (a >> b >> c) >> (a >> b) >> a >> c


I : ||- a >> a
I {a} = (S {b = a >> a} << K) << K
