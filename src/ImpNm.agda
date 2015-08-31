module ImpNm where


infixr 5 _>>_

data Formula : Set where
  _>>_ : Formula -> Formula -> Formula


infixl 5 _<<_

syntax lam' (\a -> b) = lam a >> b

data Theorem (hs : Formula -> Set) : Formula -> Set where
  hyp  : forall {a}   -> hs a
                      -> Theorem hs a
  lam' : forall {a b} -> (hs a -> Theorem hs b)
                      -> Theorem hs (a >> b)
  _<<_ : forall {a b} -> Theorem hs (a >> b) -> Theorem hs a
                      -> Theorem hs b


I : forall {hs a} -> Theorem hs (a >> a)
I = lam x >> hyp x

K : forall {hs a b} -> Theorem hs (a >> b >> a)
K = lam x >>
      lam y >> hyp x

S : forall {hs a b c} -> Theorem hs ((a >> b >> c) >> (a >> b) >> a >> c)
S = lam f >>
      lam g >>
        lam x >> (hyp f << hyp x) << (hyp g << hyp x)
