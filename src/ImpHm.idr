module ImpHm


infixr 5 >>

data Proposition : Type where
  (>>) : Proposition -> Proposition -> Proposition


infixl 5 <<

data Theorem : Proposition -> Type where
  (<<) : Theorem (a >> b) -> Theorem a
      -> Theorem b
  K    : Theorem (a >> b >> a)
  S    : Theorem ((a >> b >> c) >> (a >> b) >> a >> c)


i : Theorem (a >> a)
i {a} = (S {b = a >> a} << K) << K
