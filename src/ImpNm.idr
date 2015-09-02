module ImpNm


infixr 5 >>

data Formula : Type where
  (>>) : Formula -> Formula -> Formula


infixl 5 <<

syntax "lam" {a} ">>" [b] = lam' (\a => b)

infix 1 |-

data (|-) : (Formula -> Type) -> Formula -> Type where
  hyp  : cx a
      -> cx |- a
  lam' : (cx a -> cx |- b)
      -> cx |- a >> b
  (<<) : cx |- a >> b -> cx |- a
      -> cx |- b


prefix 1 ||-

(||-) : Formula -> Type
(||-) a = {cx : Formula -> Type} -> cx |- a


I : ||- a >> a
I = lam x >> hyp x

K : ||- a >> b >> a
K = lam x >>
      lam y >> hyp x

S : ||- (a >> b >> c) >> (a >> b) >> a >> c
S = lam f >>
      lam g >>
        lam x >> (hyp f << hyp x) << (hyp g << hyp x)
