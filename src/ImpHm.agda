module ImpHm where


infixr 5 _>>_

data Proposition : Set where
  _>>_ : Proposition -> Proposition -> Proposition


infix 1 ||-_


infixl 5 _<<_

data ||-_ : Proposition -> Set where
  _<<_ : forall {a b}   -> ||- a >> b -> ||- a
                        -> ||- b
  K    : forall {a b}   -> ||- a >> b >> a
  S    : forall {a b c} -> ||- (a >> b >> c) >> (a >> b) >> a >> c


I : forall {a} -> ||- a >> a
I {a = a} = (S {b = a >> a} << K) << K
