module ImpNm


infixr 5 >>


data Formula : Type where
  (>>) : Formula -> Formula -> Formula


data Theorem : (Formula -> Type) -> Formula -> Type where
  Hyp : hs a
     -> Theorem hs a
  Imp : (hs a -> Theorem hs b)
     -> Theorem hs (a >> b)
  Emp : Theorem hs (a >> b) -> Theorem hs a
     -> Theorem hs b


I : Theorem hs (a >> a)
I = Imp $ \x => Hyp x

K : Theorem hs (a >> b >> a)
K = Imp $ \x =>
      Imp $ \y => Hyp x

S : Theorem hs ((a >> b >> c) >> (a >> b) >> a >> c)
S = Imp $ \f =>
      Imp $ \g =>
        Imp $ \x => Emp (Emp (Hyp f) (Hyp x))
                        (Emp (Hyp g) (Hyp x))
