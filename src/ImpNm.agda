module ImpNm where


infixr 5 _>>_

data Proposition : Set where
  _>>_ : Proposition -> Proposition -> Proposition


infix 1 ||-_

data Judgement : Set where
  true : Proposition -> Judgement

Context : Set1
Context = Judgement -> Set

data Theorem (cx : Context) : Proposition -> Set

||-_ : Proposition -> Set1
||- a = forall {cx} -> Theorem cx a


infixl 5 _<<_

syntax lam' (\a -> b) = lam a >> b

data Theorem cx where
  var  : forall {a}   -> cx (true a)
                      -> Theorem cx a
  lam' : forall {a b} -> (cx (true a) -> Theorem cx b)
                      -> Theorem cx (a >> b)
  _<<_ : forall {a b} -> Theorem cx (a >> b) -> Theorem cx a
                      -> Theorem cx b


I : forall {a} -> ||- a >> a
I = lam x >> var x

K : forall {a b} -> ||- a >> b >> a
K = lam x >>
      lam y >> var x

S : forall {a b c} -> ||- (a >> b >> c) >> (a >> b) >> a >> c
S = lam f >>
      lam g >>
        lam x >> (var f << var x) << (var g << var x)
