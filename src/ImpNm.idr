module ImpNm


infixr 5 >>

data Proposition : Type where
  (>>) : Proposition -> Proposition -> Proposition


data Judgement : Type where
  true : Proposition -> Judgement

Context : Type
Context = Judgement -> Type


infixl 5 <<

syntax "lam" {a} ">>" [b] = lam' (\a => b)

data Proof : Context -> Proposition -> Type where
  var  : cx (true a)
      -> Proof cx a
  lam' : (cx (true a) -> Proof cx b)
      -> Proof cx (a >> b)
  (<<) : Proof cx (a >> b) -> Proof cx a
      -> Proof cx b

Theorem : Proposition -> Type
Theorem a = {cx : Context} -> Proof cx a


i : Theorem (a >> a)
i = lam x >> var x

k : Theorem (a >> b >> a)
k = lam x >>
      lam y >> var x

s : Theorem ((a >> b >> c) >> (a >> b) >> a >> c)
s = lam f >>
      lam g >>
        lam x >> (var f << var x) << (var g << var x)
