module ImpHm where


infixr 5 _>>_

data Formula : Set where
  _>>_ : Formula -> Formula -> Formula


infixl 5 _<<_

infix 1 ||-_

data ||-_ : Formula -> Set where
  _<<_ : forall {a b}   -> ||- a >> b -> ||- a
                        -> ||- b
  K    : forall {a b}   -> ||- a >> b >> a
  S    : forall {a b c} -> ||- (a >> b >> c) >> (a >> b) >> a >> c


I : forall {a} -> ||- a >> a
I {a = a} = (S {b = a >> a} << K) << K
