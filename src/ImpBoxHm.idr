module ImpBoxHm


infixr 5 >>

data Proposition : Type where
  (>>) : Proposition -> Proposition -> Proposition
  BOX  : Proposition -> Proposition


infixl 5 <<

data Theorem : Proposition -> Type where
  (<<)  : Theorem (a >> b) -> Theorem a
       -> Theorem b
  K     : Theorem (a >> b >> a)
  S     : Theorem ((a >> b >> c) >> (a >> b) >> a >> c)
  nec   : Theorem a
       -> Theorem (BOX a)
  refl  : Theorem (BOX a >> a)
  trans : Theorem (BOX a >> BOX (BOX a))
  norm  : Theorem (BOX (a >> b) >> (BOX a >> BOX b))


i : Theorem (a >> a)
i {a} = (S {b = a >> a} << K) << K
