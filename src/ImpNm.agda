module ImpNm where


infixr 5 _>>_


data Formula : Set where
  _>>_ : Formula -> Formula -> Formula


data Theorem (hs : Formula -> Set) : Formula -> Set where
  Hyp : forall {a}   -> hs a
                     -> Theorem hs a
  Imp : forall {a b} -> (hs a -> Theorem hs b)
                     -> Theorem hs (a >> b)
  Emp : forall {a b} -> Theorem hs (a >> b) -> Theorem hs a
                     -> Theorem hs b


I : forall {hs a} -> Theorem hs (a >> a)
I = Imp \x -> Hyp x

K : forall {hs a b} -> Theorem hs (a >> b >> a)
K = Imp \x ->
      Imp \y -> Hyp x

S : forall {hs a b c} -> Theorem hs ((a >> b >> c) >> (a >> b) >> a >> c)
S = Imp \f ->
      Imp \g ->
        Imp \x -> Emp (Emp (Hyp f) (Hyp x))
                      (Emp (Hyp g) (Hyp x))
