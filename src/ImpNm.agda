module ImpNm where


infixr 5 _>>_

data Proposition : Set where
  _>>_ : Proposition -> Proposition -> Proposition


infix 1 _|-_
infix 1 ||-_


infixl 5 _<<_

syntax lam' (\a -> b) = lam a >> b

data _|-_ (cx : Proposition -> Set) : Proposition -> Set where
  var  : forall {a}   -> cx a
                      -> cx |- a
  lam' : forall {a b} -> (cx a -> cx |- b)
                      -> cx |- a >> b
  _<<_ : forall {a b} -> cx |- a >> b -> cx |- a
                      -> cx |- b

||-_ : Proposition -> Set1
||- a = forall {cx} -> cx |- a


I : forall {a} -> ||- a >> a
I = lam x >> var x

K : forall {a b} -> ||- a >> b >> a
K = lam x >>
      lam y >> var x

S : forall {a b c} -> ||- (a >> b >> c) >> (a >> b) >> a >> c
S = lam f >>
      lam g >>
        lam x >> (var f << var x) << (var g << var x)
