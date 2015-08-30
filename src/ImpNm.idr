module ImpNm


infixr 5 >>


data Value : Type where
  Unit : Value


data Formula : Type where
  (>>) : Formula -> Formula -> Formula


data Theorem : (Value -> Type) -> (Formula -> Type) -> Formula -> Type where
  Hyp : hs a
     -> Theorem vs hs a
  Imp : (hs a -> Theorem vs hs b)
     -> Theorem vs hs (a >> b)
  Emp : Theorem vs hs (a >> b) -> Theorem vs hs a
     -> Theorem vs hs b


I : Theorem vs hs (a >> a)
I = Imp $ \x => Hyp x

K : Theorem vs hs (a >> b >> a)
K = Imp $ \x =>
      Imp $ \y => Hyp x

S : Theorem vs hs ((a >> b >> c) >> (a >> b) >> a >> c)
S = Imp $ \f =>
      Imp $ \g =>
        Imp $ \x => Emp (Emp (Hyp f) (Hyp x))
                        (Emp (Hyp g) (Hyp x))
