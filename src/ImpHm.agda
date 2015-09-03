module ImpHm where


infixr 5 _>>_

data Proposition : Set where
  _>>_ : Proposition -> Proposition -> Proposition


infixl 5 _<<_

data Theorem : Proposition -> Set where
  _<<_ : forall {a b}   -> Theorem (a >> b) -> Theorem a
                        -> Theorem b
  K    : forall {a b}   -> Theorem (a >> b >> a)
  S    : forall {a b c} -> Theorem ((a >> b >> c) >> (a >> b) >> a >> c)


i : forall {a} -> Theorem (a >> a)
i {a = a} = (S {b = a >> a} << K) << K
