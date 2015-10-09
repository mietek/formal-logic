-- Minimal propositional logic, PHOAS approach, initial encoding

{-# LANGUAGE DataKinds, GADTs, KindSignatures, Rank2Types, Safe, TypeOperators #-}

module Pi.Mp where


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

infixl 1 :$
data Tm :: (Ty -> *) -> Ty -> * where
  Var    :: IsTrue a tc                -> Tm tc a
  Lam    :: (IsTrue a tc -> Tm tc b)   -> Tm tc (a :=> b)
  (:$)   :: Tm tc (a :=> b) -> Tm tc a -> Tm tc b
  Pair   :: Tm tc a         -> Tm tc b -> Tm tc (a :&& b)
  Fst    :: Tm tc (a :&& b)            -> Tm tc a
  Snd    :: Tm tc (a :&& b)            -> Tm tc b
  Left'  :: Tm tc a                    -> Tm tc (a :|| b)
  Right' :: Tm tc b                    -> Tm tc (a :|| b)
  Match  :: Tm tc (a :|| b) -> (IsTrue a tc -> Tm tc c) -> (IsTrue b tc -> Tm tc c) -> Tm tc c

var :: IsTrue a tc -> Tm tc a
var = Var

lam :: (Tm tc a -> Tm tc b) -> Tm tc (a :=> b)
lam f = Lam $ \x -> f (var x)

pair :: (Tm tc a, Tm tc b) -> Tm tc (a :&& b)
pair (a, b) = Pair a b

fst' :: Tm tc (a :&& b) -> Tm tc a
fst' = Fst

snd' :: Tm tc (a :&& b) -> Tm tc b
snd' = Snd

left :: Tm tc a -> Tm tc (a :|| b)
left = Left'

right :: Tm tc b -> Tm tc (a :|| b)
right = Right'

case' :: Tm tc (a :|| b) -> (Tm tc a -> Tm tc c) -> (Tm tc b -> Tm tc c) -> Tm tc c
case' xy f g = Match xy (\x -> f (var x)) (\y -> g (var y))

type Thm a = forall tc. Tm tc a


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
          ( lam $ \x -> fst' (xyz :$ x)
          , lam $ \x -> snd' (xyz :$ x)
          )
    , lam $ \xyxz ->
        lam $ \x -> pair ( fst' xyxz :$ x , snd' xyxz :$ x )
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
        lam $ \xy -> xyz :$ fst' xy :$ snd' xy
    , lam $ \xyz ->
        lam $ \x ->
          lam $ \y -> xyz :$ pair ( x , y )
    )

l16 :: Thm (((a :&& b) :=> c) :<=> (a :=> (b :=> c)))
l16 =
  pair
    ( lam $ \xyz ->
        lam $ \x ->
          lam $ \y -> xyz :$ pair ( x , y )
    , lam $ \xyz ->
        lam $ \xy -> xyz :$ fst' xy :$ snd' xy
    )

l17 :: Thm ((TRUE :=> a) :<=> a)
l17 =
  pair
    ( lam $ \tx -> tx :$ (lam $ \nt -> nt)
    , lam $ \x  -> lam $ \_ -> x
    )

l19 :: Thm (((a :|| b) :=> c) :<=> (a :=> c) :&& (b :=> c))
l19 =
  pair
    ( lam $ \xyz ->
        pair
          ( lam $ \x -> xyz :$ left x
          , lam $ \y -> xyz :$ right y
          )
    , lam $ \xzyz ->
        lam $ \xy ->
          case' xy
            (\x -> fst' xzyz :$ x)
            (\y -> snd' xzyz :$ y)
    )
