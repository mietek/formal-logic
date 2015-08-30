module Nc where


infixl 7 _&&_
infixl 6 _||_
infixr 5 _>>_
infixr 4 _>><<_


data Value : Set where
  Unit : Value


data Formula : Set where
  _>>_   : Formula -> Formula -> Formula
  _&&_   : Formula -> Formula -> Formula
  _||_   : Formula -> Formula -> Formula
  FORALL : (Value -> Formula) -> Formula
  EXISTS : (Value -> Formula) -> Formula
  FALSE  : Formula

_>><<_ : Formula -> Formula -> Formula
a >><< b = (a >> b) && (b >> a)

NOT : Formula -> Formula
NOT a = a >> FALSE

TRUE : Formula
TRUE = FALSE >> FALSE


data Theorem (vs : Value -> Set) (hs : Formula -> Set) : Formula -> Set where
  Hyp    : forall {a}     -> hs a
                          -> Theorem vs hs a
  Imp    : forall {a b}   -> (hs a -> Theorem vs hs b)
                          -> Theorem vs hs (a >> b)
  Emp    : forall {a b}   -> Theorem vs hs (a >> b) -> Theorem vs hs a
                          -> Theorem vs hs b
  And    : forall {a b}   -> Theorem vs hs a -> Theorem vs hs b
                          -> Theorem vs hs (a && b)
  Lend   : forall {a b}   -> Theorem vs hs (a && b)
                          -> Theorem vs hs a
  Rend   : forall {a b}   -> Theorem vs hs (a && b)
                          -> Theorem vs hs b
  Lor    : forall {a b}   -> Theorem vs hs a
                          -> Theorem vs hs (a || b)
  Ror    : forall {a b}   -> Theorem vs hs b
                          -> Theorem vs hs (a || b)
  Er     : forall {a b c} -> Theorem vs hs (a || b) -> (hs a -> Theorem vs hs c) -> (hs b -> Theorem vs hs c)
                          -> Theorem vs hs c
  Forall : forall {p}     -> (forall {x} -> vs x -> Theorem vs hs (p x))
                          -> Theorem vs hs (FORALL p)
  Fae    : forall {p x}   -> Theorem vs hs (FORALL p) -> vs x
                          -> Theorem vs hs (p x)
  Exists : forall {p x}   -> Theorem vs hs (p x) -> vs x
                          -> Theorem vs hs (EXISTS p)
  Ee     : forall {p x a} -> Theorem vs hs (EXISTS p) -> (hs (p x) -> Theorem vs hs a)
                          -> Theorem vs hs a
  False  : forall {a}     -> (hs (NOT a) -> Theorem vs hs FALSE)
                          -> Theorem vs hs a


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


example214c : forall {vs hs p} -> Theorem vs hs (NOT (FORALL \x -> NOT (p x)) >> EXISTS p)
example214c =
  Imp \w ->
    False \u ->
      Emp (Hyp w)
          (Forall \x ->
            Imp \v ->
              Emp (Hyp u) (Exists (Hyp v) x))