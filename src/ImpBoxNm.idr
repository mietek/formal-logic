module ImpBoxNm


infixr 5 >>

data Proposition : Type where
  (>>) : Proposition -> Proposition -> Proposition
  BOX  : Proposition -> Proposition


data World : Type where
  first : World
  next  : World -> World

data Judgement : Type where
  true : World -> Proposition -> Judgement

Context : Type
Context = Judgement -> Type


infixl 5 <<

syntax lam {a} ">>" [b]           = lam' (\a => b)
syntax unbox [a'] as {a} ">>" [b] = unbox' a' (\a => b)

data Term : Context -> World -> Proposition -> Type where
  var    : cx (true w a)
        -> Term cx w a
  lam'   : (cx (true w a) -> Term cx w b)
        -> Term cx w (a >> b)
  (<<)   : Term cx w (a >> b) -> Term cx w a
        -> Term cx w b
  box    : Term cx (next w) a
        -> Term cx w (BOX a)
  unbox' : Term cx w (BOX a) -> (cx (true v a) -> Term cx w b)
        -> Term cx w b

Theorem : Proposition -> Type
Theorem a = {cx : Context} -> {w : World} -> Term cx w a


i : Theorem (a >> a)
i = lam x >> var x

k : Theorem (a >> b >> a)
k = lam x >>
      lam y >> var x

s : Theorem ((a >> b >> c) >> (a >> b) >> a >> c)
s = lam f >>
      lam g >>
        lam x >> (var f << var x) << (var g << var x)


trans : Theorem (BOX a >> BOX (BOX a))
trans =
  lam x' >>
    unbox var x' as x >>
      box (box (var x))

norm : Theorem (BOX (a >> b) >> BOX a >> BOX b)
norm =
  lam f' >>
    lam x' >>
      unbox var f' as f >>
        unbox var x' as x >>
          box (var f << var x)
