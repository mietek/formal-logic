module ImpBoxHm where


infixr 5 _>>_

data Proposition : Set where
  _>>_ : Proposition -> Proposition -> Proposition
  BOX  : Proposition -> Proposition


infixl 5 _<<_

data Theorem : Proposition -> Set where
  _<<_  : forall {a b}   -> Theorem (a >> b) -> Theorem a
                         -> Theorem b
  K     : forall {a b}   -> Theorem (a >> b >> a)
  S     : forall {a b c} -> Theorem ((a >> b >> c) >> (a >> b) >> a >> c)
  nec   : forall {a}     -> Theorem a
                         -> Theorem (BOX a)
  refl  : forall {a}     -> Theorem (BOX a >> a)
  trans : forall {a}     -> Theorem (BOX a >> BOX (BOX a))
  norm  : forall {a b}   -> Theorem (BOX (a >> b) >> (BOX a >> BOX b))


i : forall {a} -> Theorem (a >> a)
i {a = a} = (S {b = a >> a} << K) << K
