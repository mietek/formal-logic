module ImpNm where


infixr 5 _>>_

data Proposition : Set where
  _>>_ : Proposition -> Proposition -> Proposition


data Judgement : Set where
  true : Proposition -> Judgement

Context : Set1
Context = Judgement -> Set


infixl 5 _<<_

syntax lam' (\a -> b) = lam a >> b

data Term (cx : Context) : Proposition -> Set where
  var  : forall {a}   -> cx (true a)
                      -> Term cx a
  lam' : forall {a b} -> (cx (true a) -> Term cx b)
                      -> Term cx (a >> b)
  _<<_ : forall {a b} -> Term cx (a >> b) -> Term cx a
                      -> Term cx b

Theorem : Proposition -> Set1
Theorem a = forall {cx} -> Term cx a


i : forall {a} -> Theorem (a >> a)
i = lam x >> var x

k : forall {a b} -> Theorem (a >> b >> a)
k = lam x >>
      lam y >> var x

s : forall {a b c} -> Theorem ((a >> b >> c) >> (a >> b) >> a >> c)
s = lam f >>
      lam g >>
        lam x >> (var f << var x) << (var g << var x)
