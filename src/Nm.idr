module Nm


infixl 7 &&
infixl 6 ||
infixr 5 >>
infixr 4 >><<


data Value : Type where
  Unit : Value


data Formula : Type where
  (>>)   : Formula -> Formula -> Formula
  (&&)   : Formula -> Formula -> Formula
  (||)   : Formula -> Formula -> Formula
  FORALL : (Value -> Formula) -> Formula
  EXISTS : (Value -> Formula) -> Formula
  FALSE  : Formula

(>><<) : Formula -> Formula -> Formula
a >><< b = (a >> b) && (b >> a)

NOT : Formula -> Formula
NOT a = a >> FALSE

TRUE : Formula
TRUE = FALSE >> FALSE


data Theorem : (Value -> Type) -> (Formula -> Type) -> Formula -> Type where
  Hyp    : hs a
        -> Theorem vs hs a
  Imp    : (hs a -> Theorem vs hs b)
        -> Theorem vs hs (a >> b)
  Emp    : Theorem vs hs (a >> b) -> Theorem vs hs a
        -> Theorem vs hs b
  And    : Theorem vs hs a -> Theorem vs hs b
        -> Theorem vs hs (a && b)
  Lend   : Theorem vs hs (a && b)
        -> Theorem vs hs a
  Rend   : Theorem vs hs (a && b)
        -> Theorem vs hs b
  Lor    : Theorem vs hs a
        -> Theorem vs hs (a || b)
  Ror    : Theorem vs hs b
        -> Theorem vs hs (a || b)
  Er     : Theorem vs hs (a || b) -> (hs a -> Theorem vs hs c) -> (hs b -> Theorem vs hs c)
        -> Theorem vs hs c
  Forall : ({x : Value} -> vs x -> Theorem vs hs (p x))
        -> Theorem vs hs (FORALL p)
  Fae    : Theorem vs hs (FORALL p) -> vs x
        -> Theorem vs hs (p x)
  Exists : Theorem vs hs (p x) -> vs x
        -> Theorem vs hs (EXISTS p)
  Ee     : Theorem vs hs (EXISTS p) -> (hs (p x) -> Theorem vs hs a)
        -> Theorem vs hs a


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
