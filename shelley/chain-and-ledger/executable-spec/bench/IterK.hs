{-# OPTIONS_GHC -Wno-unused-imports #-}
{-# OPTIONS_GHC -Wno-unused-matches #-}

{-# LANGUAGE FlexibleContexts, FlexibleInstances, FunctionalDependencies  #-}
{-# LANGUAGE GADTs, MultiParamTypeClasses #-}
{-# LANGUAGE TypeOperators, DataKinds,  KindSignatures #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE BangPatterns #-}


-- Iteration with Continuations

module IterK where

import Debug.Trace
-- import Data.Array
import Data.List(sort,nub)
import qualified Data.Map.Strict as Map
import Data.Map.Internal(Map(..),link)
import Data.Map.Internal.Debug(showTree)

import qualified Data.Set as Set

-- ==================================================================
-- One type that can be iterated over (in order) and hence collected
-- Of course the iteration is trivial as there are only 0 or 1 pairs.

data Pair k v where
  Pair :: k -> v -> Pair k v
  Fail :: Pair k v
  One :: k -> Pair k ()

newtype Sett k v = Sett (Set.Set k)

chars::String
chars = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdeghijklmnopqrstuvwxyz0123456789"

nchars :: Int
nchars = length chars

-- ==========================================================================
-- Data.Map.Strict is another example, let's build a few things to test with

m1 :: Map.Map Int Char
m1 = Map.fromList [ (n,chars !! n) | n <- [0..length chars -1]]

m2 :: Map.Map Int Char
m2 = Map.fromList [ (57+n,chars !! n) | n <- [0..length chars -1]]

mN :: Int -> Int -> Map.Map Int Char
mN start size  = Map.fromList [ (n,chars !! (n `mod` nchars)) | n <- [start..start+size]]

-- | Some really big Maps, with very small overlap.

m5,m6 :: Map.Map Int Char
m5 = mN 1 10000000
m6 = mN 9999995 10000000

-- =========================================================================
-- Sample continuation monad to study. We don't actually use this monad, but
-- we put it here since it is the simplest continuation monad, and studying
-- it, helped me define the Collect monad.

newtype Cont ans x = Cont { runCont :: ((x -> ans) -> ans) } -- ans is the final result type of the whole computation

instance Functor (Cont ans) where
  fmap f (Cont k2) = Cont (\k1 -> k2 (k1 . f))

instance Applicative (Cont ans) where
  pure x = Cont (\ ret -> ret x)
  f <*> x = do { g <- f; y <- x; pure(g y)}

instance Monad (Cont r) where
    return a       = Cont $ \k -> k a                       -- i.e. return a = \k -> k a
    (Cont c) >>= f = Cont $ \k -> c (\a -> runCont (f a) k) -- i.e. c >>= f = \k -> c (\a -> f a k)

-- ========================================================================
-- Now we want to make the following, more complicated continuation a Monad
-- Here the answer type is completely abstract.

newtype Collect tuple = Collect (forall ans . ans -> (tuple -> ans -> ans) -> ans)

unCollect :: Collect tuple -> ans -> (tuple -> ans -> ans) -> ans
unCollect (Collect x) = x

instance Functor Collect where
  fmap f (Collect g) = Collect (\ x c -> g x (\ t a -> c (f t) a))
-- Playing type tetris find this term    ^----------------------^
-- given
-- f:: t -> s
-- g:: a -> (t -> a -> a) -> a
-- x:: a
-- c:: s -> a -> a

instance Applicative Collect where
  pure x = Collect (\ ans c -> c x ans)
  f <*> x = do { g <- f; y <- x; pure(g y)}

instance Monad Collect where
  (Collect g) >>= f = Collect(\ x c -> g x (\ t a -> unCollect (f t) a c))
-- Playing type tetris find this term  ^--------------------------------^                                   ----------------------------------
-- given
-- g:: a -> (t -> a -> a) -> a
-- f:: t -> (Collect s)
-- x:: a
-- c:: (s -> a -> a)



-- | A (Collect t) is completely abstract over how 't's are beging collected.
-- We can make this abstraction concrete by using fixAction.

fixAction :: Collect tuple -> ans -> (tuple -> ans -> ans) -> ans
fixAction = unCollect

mapify :: Ord a => Collect (a,b) -> Map.Map a b
mapify m = fixAction m Map.empty (\ (a,b) ans -> Map.insert a b ans)

-- | Here are two ways to add a new t to what is being collected.

add:: t -> Collect t
add t = Collect(\ a f -> f t a)

push:: t -> Collect t -> Collect t
push t (Collect g) = Collect(\ a f -> g (f t a) f)

-- | Conditional collecting

when:: Bool -> Collect ()
when True = Collect(\ ans f -> f () ans)
when False = Collect(\ ans f -> ans)

-- | Even though a (Collect t) is a function, if we can (Show t), we can pick an action
-- that collects all the shown t, and turn them into a big multi-line string.

instance Show t => Show (Collect t) where
    show c2 = unlines(fixAction c2 [] (\ t ans -> show t : ans))

-- ======================================================================================
-- A binary type constructor can act as an iterator, collecting the pairs in the type,
-- if it supports the following operations: `nxt` and `lub`
-- If it iterates over items in increasing order, and can skip over many items
-- using `lub` in sub-linear time, it can make things really fast. Many collections
-- support lub: Balanced binary trees, Arrays (using binary search), Tries, etc.

class Iter f a b where
  nxt:: f a b -> Collect (a,b,f a b)
  lub :: Ord a => a -> f a b -> Collect (a,b,f a b)
  (∈) :: Ord a => a -> f a b -> Collect ()

instance Iter Pair a b where
  nxt (Pair k v) = Collect(\ ans f -> f (k,v,Fail) ans)
  nxt (One k) = Collect(\ ans f ->  f (k,(),Fail) ans)
  nxt Fail = Collect(\ ans f -> ans)
  lub key (Pair k v) = Collect(\ ans f -> if k<=key then f (k,v,Fail) ans else ans)
  lub key (One k) = Collect(\ ans f -> if k<=key then f(k,(),Fail) ans else ans)
  lub key Fail = Collect(\ ans f -> ans)
  x ∈ (Pair k v) = when (x==k)
  x ∈ (One k) = when (x==k)
  x ∈ Fail = when False

instance Iter Sett a () where
  x ∈ (Sett m) =  when (Set.member x m)
  nxt (Sett m) = Collect (\ ans f -> if Set.null m then ans else let (k,nextm) = Set.deleteFindMin m in f (k,(),Sett nextm) ans)
  lub key (Sett m) =
      Collect (\ ans f -> if Set.null m
                             then ans
                             else case Set.splitMember key m of   -- NOTE in Log time, we skip over all those tuples in _left
                                     (_left,True,right) -> f (key,(),Sett right) ans
                                     (_left,False,right) -> if Set.null right
                                                        then ans
                                                        else let (k,nextm) = Set.deleteFindMin right in f (k,(),Sett  nextm) ans)

instance Iter Map.Map a b where
  x ∈ m =  when (Map.member x m)
  nxt m = Collect (\ ans f ->
     case Map.minViewWithKey m of
        Nothing -> ans
        Just((k,v),nextm) -> f (k,v,nextm) ans)
  lub key m = Collect (\ ans f ->
     -- mygo key m ans (\ v nextm -> f (key,v,nextm) ans) (\ nextm -> let ((k,v),m3) = Map.deleteFindMin nextm in f (k,v,m3) ans))
     case Map.splitLookup key m of                  -- NOTE in Log time, we skip over all those tuples in _left
       (_left,Just v,right) -> f (key,v,right) ans
       (_left,Nothing,Tip) -> ans
       (_left,Nothing,right) -> f (k,v,m3) ans
           where ((k,v),m3) = Map.deleteFindMin right)


-- ==================================================================
-- Now we make an iterator that collects triples, on the intersection
-- of the domain of the two Iter types 'f' and 'g'. An answer of (k,b,c) means that
-- (k,b) is in m::f k a, and (k,c) is in n::g k c. All the other possible triples
-- are skipped over.  This is an instance of a thing called a "Generic Join"
-- See https://arxiv.org/pdf/1310.3314.pdf  or  http://personales.dcc.uchile.cl/~pbarcelo/ngo.pdf
-- The number of tuples it touches is proportional to the size of the output (modulo log factors).
-- It's cost is unrelated to the size of its inputs (modulo log factors)

(⨝) ::  (Ord k,Iter f k b,Iter g k c) =>  f k b -> g k c -> Collect (k,b,c)
(⨝) = domEq

domEq:: (Ord k,Iter f k b,Iter g k c) =>  f k b -> g k c -> Collect (k,b,c)
domEq m n = do
    triplem <- nxt m
    triplen <- nxt n
    let loop (mt@(k1,b,nextm)) (nt@(k2,c,nextn)) =
          case compare k1 k2 of
            EQ -> push (k1,b,c) (domEq nextm nextn)
            LT -> do { mt' <- lub k2 nextm; loop mt' nt }
            GT -> do { nt' <- lub k1 nextn; loop mt nt' }
    loop triplem triplen

-- This version is really slow as it visits every tuple in both Types.

domEqSlow:: (Ord k,Iter f k b,Iter g k c) =>  f k b -> g k c -> Collect (k,b,c)
domEqSlow m n = do
    triplem <- nxt m
    triplen <- nxt n
    let loop (mt@(k1,b,nextm)) (nt@(k2,c,nextn)) =
          case compare k1 k2 of
            EQ -> push (k1,b,c) (domEqSlow nextm nextn)
            LT -> do { mt' <- nxt nextm; loop mt' nt }
            GT -> do { nt' <- nxt nextn; loop mt nt' }
    loop triplem triplen

-- ===========================================================================================
{-  Compare the run times and the memory allocation difference between domEq and domEqSlow
    where m5 and m6 have 10,000,000 pairs, and an intersection size of 7

*IterK> domEq m5 m6
(10000001,'b','b')
(10000000,'a','a')
(9999999,'Z','Z')
(9999998,'Y','Y')
(9999997,'X','X')
(9999996,'W','W')
(9999995,'V','V')

(0.01 secs, 250,160 bytes)

*IterK> domEqSlow m5 m6
(10000001,'b','b')
(10000000,'a','a')
(9999999,'Z','Z')
(9999998,'Y','Y')
(9999997,'X','X')
(9999996,'W','W')
(9999995,'V','V')

(10.67 secs, 18,391,871,488 bytes)
-}

-- ==============================================================================================
-- Consider one of transactions that needs to compute the following.
-- ((dom stkcreds) ◁ delegs) ▷ (dom stpools)
-- We could express this in datalog as follows
-- ans(x,y) <- skcreds(x,z) and delegs(x,y) and stpools(y,w)
-- Or if collections: stkcreds, delegs, and stpools were lists of pairs as a comprehension
-- [ (x,y) | (x,z) <- skcreds, (x',y) <- delegs, x==x', (y',w) <- stpools, y=y' ]
-- This runs in time and space proportional to: size(dom skcreds) + size(dom delegs) + size(dom stpools) (perhaps even worse)
-- Or if  stkcreds, delegs, and stpools were Data.Map, we could use the Collection monad.
-- Even better, this will run in time and space proportional to: size((dom skcreds) ∩ (dom delegs))
-- See the example with timing above.

foo skcreds delegs stpools = mapify $
  do (x,z,y) <- skcreds ⨝ delegs
     y ∈ stpools
     add (x,y)

-- Even better,  stkcreds, delegs, and stpools can be any binary type construtors in the Iter class.

foo :: (Iter s a b2, Iter d a b1, Iter p b1 b3, Ord a, Ord b1) =>
       s a b2 ->
       d a b1 ->
       p b1 b3 ->
       Map a b1

-- =====================================================================================
-- Note that the `nxt` instance for Data.Map call Map.splitLookup and Map.deleteFindMin
-- Can we rewrite these as operations in the Collect monad (i.e. using continuations)?
-- If we can, this will drastically cut down on allocating memory (we hope).


data StrictTriple a b c = StrictTriple !a !b !c

splitLookup :: Ord k => k -> Map k a -> (Map k a,Maybe a,Map k a)
splitLookup k0 m = case go k0 m of
     StrictTriple l mv r -> (l, mv, r)
  where
    go :: Ord k => k -> Map k a -> StrictTriple (Map k a) (Maybe a) (Map k a)
    go !k t =
      case t of
        Tip            -> StrictTriple Tip Nothing Tip
        Bin _ kx x l r -> case compare k kx of
          LT -> let StrictTriple lt z gt = go k l
                    !gt' = link kx x gt r
                in StrictTriple lt z gt'
          GT -> let StrictTriple lt z gt = go k r
                    !lt' = link kx x l lt
                in StrictTriple lt' z gt
          EQ -> StrictTriple l (Just x) r
{-# INLINABLE splitLookup #-}

mygo :: Ord k => k -> Map k a -> ans -> (a -> Map k a -> ans) -> (Map k a -> ans) -> ans
mygo !k t c1 c2 c3 =
   case t of
      Tip -> c3 Tip
      Bin _ kx x l r -> case compare k kx of
        EQ -> c2 x r
        -- LT -> mygo k l c1 (\ z gt -> let !gt' = link kx x gt r in c2 z gt') (\ gt -> let !gt' = link kx x gt r in c3 gt')
        LT -> mygo k l c1 (\ z gt -> c2 z (link kx x gt r)) (\ gt -> c3 (link kx x gt r))
        GT -> mygo k r c1 c2 c3


{- So experiment seems to show DO NOT USE MYGO

Not using mygo
benchmarking ITER/ITER A
time                 10.77 ns   (9.985 ns .. 12.45 ns)
                     0.893 R²   (0.778 R² .. 0.999 R²)
mean                 10.47 ns   (9.982 ns .. 11.95 ns)
std dev              2.955 ns   (200.9 ps .. 6.221 ns)
variance introduced by outliers: 99% (severely inflated)

USING mygo (with lets in continuattion)
benchmarking ITER/ITER A
time                 13.01 ns   (12.03 ns .. 14.18 ns)
                     0.961 R²   (0.941 R² .. 0.983 R²)
mean                 13.10 ns   (12.30 ns .. 13.95 ns)
std dev              2.923 ns   (2.461 ns .. 3.560 ns)
variance introduced by outliers: 99% (severely inflated)

benchmarking ITER/MYGO NO LET
time                 13.11 ns   (12.20 ns .. 14.43 ns)
                     0.947 R²   (0.894 R² .. 0.982 R²)
mean                 13.33 ns   (12.39 ns .. 14.41 ns)
std dev              3.494 ns   (2.549 ns .. 4.986 ns)
variance introduced by outliers: 99% (severely inflated)

-}
