module ImpNm


infixr 5 >>

data Proposition : Type where
  (>>) : Proposition -> Proposition -> Proposition


infix  1 |-
prefix 1 ||-


infixl 5 <<

syntax "lam" {a} ">>" [b] = lam' (\a => b)

data (|-) : (Proposition -> Type) -> Proposition -> Type where
  var  : cx a
      -> cx |- a
  lam' : (cx a -> cx |- b)
      -> cx |- a >> b
  (<<) : cx |- a >> b -> cx |- a
      -> cx |- b

(||-) : Proposition -> Type
(||-) a = {cx : Proposition -> Type} -> cx |- a


I : ||- a >> a
I = lam x >> var x

K : ||- a >> b >> a
K = lam x >>
      lam y >> var x

S : ||- (a >> b >> c) >> (a >> b) >> a >> c
S = lam f >>
      lam g >>
        lam x >> (var f << var x) << (var g << var x)
