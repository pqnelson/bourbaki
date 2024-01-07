{-# LINE 41 "bourbaki.lhs" #-}
import Data.Set
import Prelude hiding (and)
{-# LINE 49 "bourbaki.lhs" #-}
type Letter = String
{-# LINE 84 "bourbaki.lhs" #-}
data Term = TTau Integer Letter Relation
          | TBox Integer Letter
          | TVar Letter
          | TSubst Term Letter Term
          | TPair Term Term
          deriving (Show, Eq)
{-# LINE 119 "bourbaki.lhs" #-}
data Relation = ROr Relation Relation
              | RNot Relation
              | RSubst Term Letter Relation
              | REq Term Term
              | RIn Term Term
              deriving (Show, Eq)

and            :: Relation -> Relation -> Relation
and      a  b  = RNot (ROr (RNot a) (RNot b))

implies        :: Relation -> Relation -> Relation
implies  a  b  = ROr (RNot a) b

iff            :: Relation -> Relation -> Relation
iff      a  b  =  and (implies a b) (implies b a)
{-# LINE 145 "bourbaki.lhs" #-}
class Subst a where
  subst :: Letter -> Term -> a -> a
{-# LINE 166 "bourbaki.lhs" #-}
instance Subst Term where
  subst y t t' = case t' of
    (TVar x)  ->  if x==y
                  then t
                  else t'
    (TSubst b x a)  ->  if x==y
                        then (TSubst b x a)
                        else (TSubst (subst y t b) x (subst y t a))
    _  ->  t'
{-# LINE 190 "bourbaki.lhs" #-}
instance Subst Relation where
  subst y t (ROr a b)  =  ROr (subst y t a) (subst y t b)
  subst y t (RNot a)   =  RNot (subst y t a)
  subst y t (RSubst b x r)  =  if y==x then (RSubst b x r)
                               else RSubst (subst y t b) x (subst y t r)
  subst y t (REq a b)  =  REq (subst y t a) (subst y t b)
  subst y t (RIn a b)  =  RIn (subst y t a) (subst y t b)
{-# LINE 203 "bourbaki.lhs" #-}
class Simplifier a where
  simp :: a -> a
{-# LINE 211 "bourbaki.lhs" #-}
instance Simplifier Relation where
  simp (ROr a b)  =  let  a'  =  simp a
                          b'  =  simp b
                     in  if (simp (RNot a')) == b'
                         then (REq (TVar "_") (TVar "_"))
                         else ROr a' b'
  simp (RNot (RNot a))  =  simp a
  simp (RNot a)   =  RNot (simp a)
  simp (RSubst t x r)   =  subst x t r
  simp (REq a b)  =  REq (simp a) (simp b)
  simp (RIn a b)  =  RIn (simp a) (simp b)
{-# LINE 227 "bourbaki.lhs" #-}
instance Simplifier Term where
  simp (TTau m x r)    =  TTau m x (simp r)
  simp (TBox m x)      =  TBox m x
  simp (TVar x)        =  TVar x
  simp (TSubst t x b)  =  subst x t b
  simp (TPair a b)     =  TPair (simp a) (simp b)
{-# LINE 244 "bourbaki.lhs" #-}
class Shift a where
  shift :: a -> a
{-# LINE 252 "bourbaki.lhs" #-}
instance Shift Term where
  shift (TTau m x r)   =  TTau (m+1) x r
  shift (TBox m x)     =  TBox (m+1) x
  shift (TVar x)       =  TVar x
  shift (TSubst b x a) =  TSubst (shift b) x (shift a)
  shift (TPair a b)    =  TPair (shift a) (shift b)
{-# LINE 263 "bourbaki.lhs" #-}
instance Shift Relation where
  shift (ROr a b) = ROr (shift a) (shift b)
  shift (RNot a) = RNot (shift a)
  shift (RSubst a x r) = RSubst (shift a) x (shift r)
  shift (REq a b) = REq (shift a) (shift b)
  shift (RIn a b) = RIn (shift a) (shift b)
{-# LINE 276 "bourbaki.lhs" #-}
tau      ::  Letter -> Relation -> Term
tau x r  =   TTau 0 x $ subst x (TBox 0 x) (shift r)
{-# LINE 298 "bourbaki.lhs" #-}
exists        ::  Letter -> Relation -> Relation
exists  x  r  =   simp $ subst (tau x r) x r

forall        ::  Letter -> Relation -> Relation
forall  x  r  =   simp $ RNot (exists x (RNot r))
{-# LINE 312 "bourbaki.lhs" #-}
class Vars a where
  vars :: a -> Set Letter
{-# LINE 319 "bourbaki.lhs" #-}
instance Vars Term where
  vars (TTau _ x r)    =  Data.Set.union (Data.Set.singleton x) (vars r)
  vars (TBox _ x)      =  (Data.Set.singleton x)
  vars (TVar x)        =  Data.Set.singleton x
  vars (TSubst b x a)  =  Data.Set.delete x (Data.Set.union (vars a) (vars b))
  vars (TPair a b)     =  Data.Set.union (vars a) (vars b)
{-# LINE 331 "bourbaki.lhs" #-}
instance Vars Relation where
  vars (ROr a b)       =  Data.Set.union (vars a) (vars b)
  vars (RNot a)        =  vars a
  vars (RSubst a x r)  =  Data.Set.delete x (Data.Set.union (vars a) (vars r))
  vars (REq a b)       =  Data.Set.union (vars a) (vars b)
  vars (RIn a b)       =  Data.Set.union (vars a) (vars b)
{-# LINE 345 "bourbaki.lhs" #-}
freshVar :: Letter -> Int -> Set Letter -> Letter
freshVar x m vs  =  if (x++(show m)) `Data.Set.member` vs
                    then freshVar x (m+1) vs
                    else x++(show m)
{-# LINE 356 "bourbaki.lhs" #-}
fresh :: Vars a => Letter -> a -> Letter
fresh x fm  =  let vs = vars fm
               in  if x `elem` vs
                   then freshVar x 0 vs
                   else x
{-# LINE 369 "bourbaki.lhs" #-}
class Occur a where
  occur :: Letter -> a -> Integer
{-# LINE 388 "bourbaki.lhs" #-}
instance Occur Term where
  occur x (TTau _ y r)    =  if x==y then 0 else (occur x r)
  occur x (TBox _ _)      =  0
  occur x (TVar y)        =  if x==y then 1 else 0
  occur x (TSubst b y a)  =  if x==y
                             then (occur x b)*(occur x a)
                             else (occur x b)*(occur y a)+(occur x a)
  occur x (TPair a b)     =  (occur x a) + (occur x b)
{-# LINE 402 "bourbaki.lhs" #-}
instance Occur Relation where
  occur x (ROr a b)       =  (occur x a) + (occur x b)
  occur x (RNot a)        =  occur x a
  occur x (RSubst a y r)  =  if x==y
                             then (occur x a)*(occur x r)
                             else (occur x a)*(occur y r) + (occur x r)
  occur x (REq a b)       =  (occur x a) + (occur x b)
  occur x (RIn a b)       =  (occur x a) + (occur x b)
{-# LINE 418 "bourbaki.lhs" #-}
class Len a where
  len :: a -> Integer
{-# LINE 435 "bourbaki.lhs" #-}
instance Len Term where
  len (TTau _ _ r)    =  1 + len r
  len (TBox _ _)      =  1
  len (TVar _)        =  1
  len (TSubst b x a)  =  ((len b) - 1)*(occur x a) + (len a)
  len (TPair a b)     =  1 + (len a) + (len b)
{-# LINE 452 "bourbaki.lhs" #-}
instance Len Relation where
  len (ROr a b)       =  1 + len a + len b
  len (RNot a)        =  1 + len a
  len (RSubst a y r)  =  ((len a) - 1)*(occur y r) + (len r)
  len (REq a b)       =  1 + len a + len b
  len (RIn a b)       =  1 + len a + len b
{-# LINE 473 "bourbaki.lhs" #-}
ens  ::  Letter -> Relation -> Term
ens x r  =  let y = fresh "y" r
            in tau 0 y (forall x (iff (RIn (TVar x) (TVar y)) r))
{-# LINE 483 "bourbaki.lhs" #-}
--  The set with two elements, a.k.a., the unordered pair.
pair      ::  Term -> Term -> Term
pair x y  =   let z = fresh "z" (REq x y)
              in ens z (ROr (REq x (TVar z)) (REq y (TVar z)))
{-# LINE 499 "bourbaki.lhs" #-}
ssingleton    ::  Term -> Term
ssingleton x  =   let z = fresh "z" x
                  in ens z (REq x (TVar z))
{-# LINE 508 "bourbaki.lhs" #-}
--  use orderedPair = TPair for debugging purposes
orderedPair    ::  Term -> Term -> Term
orderedPair    x  y     =  pair (ssingleton x) (pair x y)

orderedTriple  ::  Term -> Term -> Term -> Term
orderedTriple  x  y  z  =  orderedPair (orderedPair x y) z
{-# LINE 523 "bourbaki.lhs" #-}
cartesianProduct :: Term -> Term -> Term
cartesianProduct x y = ens "z"  (exists "x'"
                                  (exists "y'"
                                    (and  (REq  (TVar "z") (orderedPair (TVar "x'") (TVar "y'")))
                                          (and  (RIn (TVar "x'") x)
                                                (RIn (TVar "y'") y)))))
{-# LINE 539 "bourbaki.lhs" #-}
subset :: Term -> Term -> Relation
subset u v = forall "s" (implies (RIn (TVar "s") u) (RIn (TVar "s") v))
{-# LINE 548 "bourbaki.lhs" #-}
emptySet :: Term
emptySet = tau 0 "X" (forall "y" (RNot (RIn (TVar "y") (TVar "X"))))
{-# LINE 584 "bourbaki.lhs" #-}
termA :: Term -> Letter -> Letter -> Letter -> Relation
termA x u upperU z = REq (TVar u) (orderedTriple (TVar upperU) x (TVar z))

termB :: Term -> Letter -> Letter -> Relation
termB x upperU z = subset (TVar upperU) (cartesianProduct x (TVar z))

termC :: Term -> Letter -> Relation
termC x upperU = forall "x" (implies  (RIn (TVar "x") x)
                                      (exists "y" (RIn  (orderedPair (TVar "x") (TVar "y"))
                                                        (TVar upperU))))

termD :: Letter -> Relation
termD upperU = forall "x"
  (forall "y" (forall "z"
                (implies  (and  (RIn (orderedPair (TVar "x") (TVar "y")) (TVar upperU))
                                (RIn (orderedPair (TVar "x") (TVar "z")) (TVar upperU)))
                          (REq (TVar "y") (TVar "z")))))

termE :: Letter -> Letter -> Relation
termE upperU z = forall "y" (implies
                              (RIn (TVar "y") (TVar z))
                              (exists "x" (RIn  (orderedPair (TVar "x") (TVar "y"))
                                                (TVar upperU))))

card :: Term -> Term
card x = tau 0 "Z" (exists "u" (exists "U" (and  (termA x "u" "U" "Z")
                                                 (and  (termB x "U" "Z")
                                                       (and  (termC x "U")
                                                             (and  (termD "U")
                                                                   (termE "U" "Z")))))))
{-# LINE 617 "bourbaki.lhs" #-}
one :: Term
one = card (ssingleton emptySet)

two :: Term
two = card (pair emptySet (ssingleton emptySet))
{-# LINE 637 "bourbaki.lhs" #-}
val :: Term -> Term -> Term
val x graph = tau "y" (RIn (orderedPair x (TVar "y")) graph)
{-# LINE 659 "bourbaki.lhs" #-}
setSum :: Term -> Term -> Term
setSum idx family = ens "x"  (exists "i"
                               (and  (RIn (TVar "i") idx)
                                     (RIn (TVar "x") (val (TVar "i") family))))
{-# LINE 671 "bourbaki.lhs" #-}
cardSum :: Term -> Term -> Term
cardSum a b = setSum two (cartesianProduct two (pair a b))
{-# LINE 676 "bourbaki.lhs" #-}
onePlusOneIsTwo :: Relation
onePlusOneIsTwo = REq two (cardSum one one)
{-# LINE 683 "bourbaki.lhs" #-}
pairOfOnes :: Term
pairOfOnes = pair one one

productTwoOnes :: Term
productTwoOnes = cartesianProduct two pairOfOnes
{-# LINE 696 "bourbaki.lhs" #-}
main = do
  putStrLn ("The size of {x, y} = " ++ (show (len (pair (TVar "x") (TVar "y")))))
  putStrLn ("Size of (x, y) = " ++ (show (len (orderedPair (TVar "x") (TVar "y")))))
  putStrLn ("Size of the Empty Set = " ++ (show (len emptySet)))
  putStrLn ("Size of $X\\times Y$ = " ++ (show (len (cartesianProduct (TVar "X") (TVar "Y")))))
  putStrLn ("Size of       1   = " ++ (show (len one)))
  putStrLn ("Size of `{1,1}`   = " ++ (show (len pairOfOnes)))
  putStrLn ("Size of `2*{1,1}` = " ++ (show (len productTwoOnes)))
  putStrLn ("Size of '1+1=2' = " ++ (show (len onePlusOneIsTwo)))
  putStrLn ("Size of 1*      = " ++ (show (len (simp one))))
  putStrLn ("Size of A = " ++ (show (len (termA (ssingleton emptySet) "u" "U" "Z"))))
  putStrLn ("Size of B = " ++ (show (len (termB (ssingleton emptySet) "U" "Z"))))
  putStrLn ("Size of C = " ++ (show (len (termC (ssingleton emptySet) "U"))))
  putStrLn ("Size of D = " ++ (show (len (termD "U"))))
  putStrLn ("Size of E = " ++ (show (len (termE "U" "Z"))))
