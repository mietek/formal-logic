module Lib where


-- Natural numbers

data Nat : Set where
  zero :        Nat
  suc  : Nat -> Nat

{-# BUILTIN NATURAL Nat #-}

_+_ : Nat -> Nat -> Nat
zero  + n  = n
suc k + n = suc (k + n)


-- Finite sets

data Fin : Nat -> Set where
  fzero : forall {n} ->          Fin (suc n)
  fsuc  : forall {n} -> Fin n -> Fin (suc n)

fin : forall {n} (k : Nat) -> Fin (suc (k + n))
fin zero    = fzero
fin (suc i) = fsuc (fin i)


-- Lists

infixl 0 _,_

data List (X : Set) : Set where
  []  :                List X
  _,_ : List X -> X -> List X


-- List membership

data LMem {X : Set} (a : X) : List X -> Set where
  lzero : forall {l}               -> LMem a (l , a)
  lsuc  : forall {l b} -> LMem a l -> LMem a (l , b)


-- Vectors

data Vec (X : Set) : Nat -> Set where
  []  :                               Vec X zero
  _,_ : forall {n} -> Vec X n -> X -> Vec X (suc n)

proj : forall {X n} -> Vec X n -> Fin n -> X
proj []      ()
proj (_ , a) fzero    = a
proj (v , _) (fsuc i) = proj v i


-- Vector membership

data VMem {X : Set} (a : X) : forall {n} -> Fin n -> Vec X n -> Set where
  mzero : forall {n}     {v : Vec X n}               -> VMem a fzero    (v , a)
  msuc  : forall {n i b} {v : Vec X n} -> VMem a i v -> VMem a (fsuc i) (v , b)

fmem : forall {X n} -> (i : Fin n) -> {v : Vec X n} -> VMem (proj v i) i v
fmem {_} {zero}  ()
fmem {_} {suc n} fzero    {_ , a} = mzero
fmem {_} {suc n} (fsuc i) {v , _} = msuc (fmem i)

mem : forall {X n} -> (k : Nat) -> {v : Vec X (suc (k + n))} -> VMem (proj v (fin k)) (fin k) v
mem i = fmem (fin i)
