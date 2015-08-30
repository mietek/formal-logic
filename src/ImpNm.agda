module ImpNm where


infixr 5 _>>_


data Value : Set where
  Unit : Value


data Formula : Set where
  _>>_ : Formula -> Formula -> Formula


data Theorem (vs : Value -> Set) (hs : Formula -> Set) : Formula -> Set where
  Hyp : forall {a}   -> hs a
                     -> Theorem vs hs a
  Imp : forall {a b} -> (hs a -> Theorem vs hs b)
                     -> Theorem vs hs (a >> b)
  Emp : forall {a b} -> Theorem vs hs (a >> b) -> Theorem vs hs a
                     -> Theorem vs hs b


I : forall {vs hs a} -> Theorem vs hs (a >> a)
I = Imp \x -> Hyp x

K : forall {vs hs a b} -> Theorem vs hs (a >> b >> a)
K = Imp \x ->
      Imp \y -> Hyp x

S : forall {vs hs a b c} -> Theorem vs hs ((a >> b >> c) >> (a >> b) >> a >> c)
S = Imp \f ->
      Imp \g ->
        Imp \x -> Emp (Emp (Hyp f) (Hyp x))
                      (Emp (Hyp g) (Hyp x))
