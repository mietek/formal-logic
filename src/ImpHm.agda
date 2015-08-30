module ImpHm where


infixr 5 _>>_


data Value : Set where
  Unit : Value


data Formula : Set where
  _>>_ : Formula -> Formula -> Formula


data Theorem : Formula -> Set where
  Emp : forall {a b}   -> Theorem (a >> b) -> Theorem a
                       -> Theorem b
  K   : forall {a b}   -> Theorem (a >> b >> a)
  S   : forall {a b c} -> Theorem ((a >> b >> c) >> (a >> b) >> a >> c)


I : forall {a} -> Theorem (a >> a)
I {a = a} = Emp (Emp (S {b = a >> a}) K) K

I' : forall {a} -> Theorem (a >> a)
I' = Emp (Emp f K) K
  where
    f : forall {a} -> Theorem ((a >> (a >> a) >> a) >> (a >> a >> a) >> a >> a)
    f = S
