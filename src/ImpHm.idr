module ImpHm


infixr 5 >>

data Proposition : Type where
  (>>) : Proposition -> Proposition -> Proposition


prefix 1 ||-


infixl 5 <<

data (||-) : Proposition -> Type where
  (<<) : ||- a >> b -> ||- a
      -> ||- b
  K    : ||- a >> b >> a
  S    : ||- (a >> b >> c) >> (a >> b) >> a >> c


I : ||- a >> a
I {a} = (S {b = a >> a} << K) << K
