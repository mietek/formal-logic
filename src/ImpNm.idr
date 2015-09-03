module ImpNm


infixr 5 >>

data Proposition : Type where
  (>>) : Proposition -> Proposition -> Proposition


prefix 1 ||-

data Judgement : Type where
  true : Proposition -> Judgement

Context : Type
Context = Judgement -> Type

Theorem : Context -> Proposition -> Type

(||-) : Proposition -> Type
(||-) a = {cx : Context} -> Theorem cx a


infixl 5 <<

syntax "lam" {a} ">>" [b] = lam' (\a => b)

data Theorem : Context -> Proposition -> Type where
  var  : cx (true a)
      -> Theorem cx a
  lam' : (cx (true a) -> Theorem cx b)
      -> Theorem cx (a >> b)
  (<<) : Theorem cx (a >> b) -> Theorem cx a
      -> Theorem cx b


I : ||- a >> a
I = lam x >> var x

K : ||- a >> b >> a
K = lam x >>
      lam y >> var x

S : ||- (a >> b >> c) >> (a >> b) >> a >> c
S = lam f >>
      lam g >>
        lam x >> (var f << var x) << (var g << var x)
