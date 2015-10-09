-- Minimal propositional logic, PHOAS approach, final encoding

{-# LANGUAGE DataKinds, GADTs, KindSignatures, Rank2Types, Safe, TypeOperators #-}

module Pf.Mp where


-- Types

infixl 2 :&&
infixl 1 :||
infixr 0 :=>
data Ty :: * where
  UNIT  ::             Ty
  (:=>) :: Ty -> Ty -> Ty
  (:&&) :: Ty -> Ty -> Ty
  (:||) :: Ty -> Ty -> Ty
  FALSE ::             Ty

infixr 0 :<=>
type a :<=> b = (a :=> b) :&& (b :=> a)

type NOT a = a :=> FALSE

type TRUE = FALSE :=> FALSE


-- Context and truth judgement

-- NOTE: Haskell does not support kind synonyms
-- type Cx = Ty -> *

type IsTrue (a :: Ty) (tc :: Ty -> *) = tc a


-- Terms

infixl 1 .$
class ArrMpTm (tr :: (Ty -> *) -> Ty -> *) where
  var  :: IsTrue a tc                -> tr tc a
  lam' :: (IsTrue a tc -> tr tc b)   -> tr tc (a :=> b)
  (.$) :: tr tc (a :=> b) -> tr tc a -> tr tc b

lam :: ArrMpTm tr => (tr tc a -> tr tc b) -> tr tc (a :=> b)
lam f = lam' $ \x -> f (var x)

class ArrMpTm tr => MpTm (tr :: (Ty -> *) -> Ty -> *) where
  pair'  :: tr tc a         -> tr tc b -> tr tc (a :&& b)
  fst'   :: tr tc (a :&& b)            -> tr tc a
  snd'   :: tr tc (a :&& b)            -> tr tc b
  left   :: tr tc a                    -> tr tc (a :|| b)
  right  :: tr tc b                    -> tr tc (a :|| b)
  case'' :: tr tc (a :|| b) -> (IsTrue a tc -> tr tc c) -> (IsTrue b tc -> tr tc c) -> tr tc c

pair :: MpTm tr => (tr tc a, tr tc b) -> tr tc (a :&& b)
pair (a, b) = pair' a b

case' :: MpTm tr => tr tc (a :|| b) -> (tr tc a -> tr tc c) -> (tr tc b -> tr tc c) -> tr tc c
case' xy f g = case'' xy (\x -> f (var x)) (\y -> g (var y))

type Thm a = MpTm tr => tr tc a


-- Example theorems

c1 :: Thm (a :&& b :<=> b :&& a)
c1 =
  pair
    ( lam $ \xy -> pair ( snd' xy , fst' xy )
    , lam $ \yx -> pair ( snd' yx , fst' yx )
    )

c2 :: Thm (a :|| b :<=> b :|| a)
c2 =
  pair
    ( lam $ \xy ->
        case' xy
          (\x -> right x)
          (\y -> left y)
    , lam $ \yx ->
        case' yx
          (\y -> right y)
          (\x -> left x)
    )

i1 :: Thm (a :&& a :<=> a)
i1 =
  pair
    ( lam $ \xx -> fst' xx
    , lam $ \x  -> pair ( x , x )
    )

i2 :: Thm (a :|| a :<=> a)
i2 =
  pair
    ( lam $ \xx ->
        case' xx
          (\x -> x)
          (\x -> x)
    , lam $ \x -> left x
    )

l3 :: Thm ((a :=> a) :<=> TRUE)
l3 =
  pair
    ( lam $ \_ -> lam $ \nt -> nt
    , lam $ \_ -> lam $ \x -> x
    )

l1 :: Thm (a :&& (b :&& c) :<=> (a :&& b) :&& c)
l1 =
  pair
    ( lam $ \xyz ->
        let yz = snd' xyz in
          pair
            ( pair ( fst' xyz , fst' yz )
            , snd' yz
            )
    , lam $ \xyz ->
        let xy = fst' xyz in
          pair
            ( fst' xy
            , pair ( snd' xy , snd' xyz )
            ))

l2 :: Thm (a :&& TRUE :<=> a)
l2 =
  pair
    ( lam $ \xt -> fst' xt
    , lam $ \x  -> pair ( x , lam $ \nt -> nt )
    )

l4 :: Thm (a :&& (b :|| c) :<=> (a :&& b) :|| (a :&& c))
l4 =
  pair
    ( lam $ \xyz ->
        let x = fst' xyz in
          case' (snd' xyz)
            (\y -> left  (pair ( x , y )))
            (\z -> right (pair ( x , z )))
    , lam $ \xyxz ->
        case' xyxz
          (\xy -> pair ( fst' xy , left  (snd' xy) ))
          (\xz -> pair ( fst' xz , right (snd' xz) ))
    )

l6 :: Thm (a :|| (b :&& c) :<=> (a :|| b) :&& (a :|| c))
l6 =
  pair
    ( lam $ \xyz ->
        case' xyz
          (\x  -> pair ( left x , left x ))
          (\yz -> pair ( right (fst' yz) , right (snd' yz) ))
    , lam $ \xyxz ->
        case' (fst' xyxz)
          (\x -> left x)
          (\y ->
            case' (snd' xyxz)
              (\x -> left x)
              (\z -> right (pair ( y , z ))))
    )

l7 :: Thm (a :|| TRUE :<=> TRUE)
l7 =
  pair
    ( lam $ \_ -> lam $ \nt -> nt
    , lam $ \t -> right t
    )

l9 :: Thm (a :|| (b :|| c) :<=> (a :|| b) :|| c)
l9 =
  pair
    ( lam $ \xyz ->
        case' xyz
          (\x  -> left (left x))
          (\yz ->
            case' yz
              (\y -> left (right y))
              (\z -> right z))
    , lam $ \xyz ->
        case' xyz
          (\xy ->
            case' xy
              (\x -> left x)
              (\y -> right (left y)))
          (\z -> right (right z))
    )

l11 :: Thm ((a :=> (b :&& c)) :<=> (a :=> b) :&& (a :=> c))
l11 =
  pair
    ( lam $ \xyz ->
        pair
          ( lam $ \x -> fst' (xyz .$ x)
          , lam $ \x -> snd' (xyz .$ x)
          )
    , lam $ \xyxz ->
        lam $ \x -> pair ( fst' xyxz .$ x , snd' xyxz .$ x )
    )

l12 :: Thm ((a :=> TRUE) :<=> TRUE)
l12 =
  pair
    ( lam $ \_ -> lam $ \nt -> nt
    , lam $ \t -> lam $ \_  -> t
    )

l13 :: Thm ((a :=> (b :=> c)) :<=> ((a :&& b) :=> c))
l13 =
  pair
    ( lam $ \xyz ->
        lam $ \xy -> xyz .$ fst' xy .$ snd' xy
    , lam $ \xyz ->
        lam $ \x ->
          lam $ \y -> xyz .$ pair ( x , y )
    )

l16 :: Thm (((a :&& b) :=> c) :<=> (a :=> (b :=> c)))
l16 =
  pair
    ( lam $ \xyz ->
        lam $ \x ->
          lam $ \y -> xyz .$ pair ( x , y )
    , lam $ \xyz ->
        lam $ \xy -> xyz .$ fst' xy .$ snd' xy
    )

l17 :: Thm ((TRUE :=> a) :<=> a)
l17 =
  pair
    ( lam $ \tx -> tx .$ (lam $ \nt -> nt)
    , lam $ \x  -> lam $ \_ -> x
    )

l19 :: Thm (((a :|| b) :=> c) :<=> (a :=> c) :&& (b :=> c))
l19 =
  pair
    ( lam $ \xyz ->
        pair
          ( lam $ \x -> xyz .$ left x
          , lam $ \y -> xyz .$ right y
          )
    , lam $ \xzyz ->
        lam $ \xy ->
          case' xy
            (\x -> fst' xzyz .$ x)
            (\y -> snd' xzyz .$ y)
    )
