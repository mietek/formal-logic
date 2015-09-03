module ImpBoxNm where


infixr 5 _>>_

data Proposition : Set where
  _>>_ : Proposition -> Proposition -> Proposition
  BOX  : Proposition -> Proposition


data World : Set where
  first : World
  next  : World -> World

data Judgement : Set where
  true : World -> Proposition -> Judgement

Context : Set1
Context = Judgement -> Set


infixl 5 _<<_

syntax lam' (\a -> b)      = lam a >> b
syntax unbox' a' (\a -> b) = unbox a' as a >> b

data Term (cx : Context) (w : World) : Proposition -> Set where
  var    : forall {a}     -> cx (true w a)
                          -> Term cx w a
  lam'   : forall {a b}   -> (cx (true w a) -> Term cx w b)
                          -> Term cx w (a >> b)
  _<<_   : forall {a b}   -> Term cx w (a >> b) -> Term cx w a
                          -> Term cx w b
  box    : forall {a}     -> Term cx (next w) a
                          -> Term cx w (BOX a)
  unbox' : forall {v a b} -> Term cx w (BOX a) -> (cx (true v a) -> Term cx w b)
                          -> Term cx w b

Theorem : Proposition -> Set1
Theorem a = forall {cx w} -> Term cx w a


i : forall {a} -> Theorem (a >> a)
i = lam x >> var x

k : forall {a b} -> Theorem (a >> b >> a)
k = lam x >>
      lam y >> var x

s : forall {a b c} -> Theorem ((a >> b >> c) >> (a >> b) >> a >> c)
s = lam f >>
      lam g >>
        lam x >> (var f << var x) << (var g << var x)


trans : forall {a} -> Theorem (BOX a >> BOX (BOX a))
trans =
  lam x' >>
    unbox var x' as x >>
      box (box (var x))

norm : forall {a b} -> Theorem (BOX (a >> b) >> BOX a >> BOX b)
norm =
  lam f' >>
    lam x' >>
      unbox var f' as f >>
        unbox var x' as x >>
          box (var f << var x)
