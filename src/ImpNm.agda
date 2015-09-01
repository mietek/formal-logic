module ImpNm where


infixr 5 _>>_

data Formula : Set where
  _>>_ : Formula -> Formula -> Formula


infixl 5 _<<_

syntax lam' (\a -> b) = lam a >> b

infix 1 _|-_

data _|-_ (cx : Formula -> Set) : Formula -> Set where
  hyp  : forall {a}   -> cx a
                      -> cx |- a
  lam' : forall {a b} -> (cx a -> cx |- b)
                      -> cx |- a >> b
  _<<_ : forall {a b} -> cx |- a >> b -> cx |- a
                      -> cx |- b


infix 1 ||-_

||-_ : Formula -> Set1
||- a = forall {cx} -> cx |- a


I : forall {a} -> ||- a >> a
I = lam x >> hyp x

K : forall {a b} -> ||- a >> b >> a
K = lam x >>
      lam y >> hyp x

S : forall {a b c} -> ||- (a >> b >> c) >> (a >> b) >> a >> c
S = lam f >>
      lam g >>
        lam x >> (hyp f << hyp x) << (hyp g << hyp x)
