module ImpHm


infixr 5 >>


data Formula : Type where
  (>>) : Formula -> Formula -> Formula


data Theorem : Formula -> Type where
  Emp : Theorem (a >> b) -> Theorem a
     -> Theorem b
  K   : Theorem (a >> b >> a)
  S   : Theorem ((a >> b >> c) >> (a >> b) >> a >> c)


I : Theorem (a >> a)
I {a} = Emp (Emp (S {b = a >> a}) K) K
