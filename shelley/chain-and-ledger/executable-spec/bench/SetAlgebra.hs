{-# OPTIONS_GHC -Wno-unused-matches #-}


{-# LANGUAGE GADTs, MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances, FunctionalDependencies  #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DeriveGeneric           #-}
{-# LANGUAGE BangPatterns #-}


module SetAlgebra where

import Prelude hiding(lookup)

import qualified Data.Map.Strict as Map
import Data.Map.Strict(Map)
import Data.Map.Internal(Map(..),link2)

import qualified Data.Set as Set

import Data.List(sortBy)
import qualified Data.List as List

import Collect


-- ==================================================================================================
-- In order to build typed Exp (which are a typed deep embedding) of Set operations, we need to know
-- what kind of basic types of Maps and Sets can be embedded. Every Basic type has a few operations
-- ===================================================================================================

class Iter f => Basic f where
  addpair:: (Ord k) => k -> v -> f k v -> f k v
  addpair k v f = addkv (k,v) f (\ a b -> a)
  addkv :: Ord k => (k,v) -> f k v -> (v -> v -> v) -> f k v
  removekey:: (Ord k) => k -> f k v -> f k v
  emptyc:: Ord k => f k v
  emptyc = error ("emptyc only works on some types.")

-- ========== Basic List ==============

instance Basic List where
   addpair k v (List xs) = List(insert xs) where
       insert [] = [(k,v)]
       insert ((key,u):ys) = if k==key then ((k,v):ys) else (k,u):(insert ys)
   addkv (k,v) (List xs) comb = List(insert xs) where
       insert [] = [(k,v)]
       insert ((key,u):ys) = if k==key then ((k,comb u v):ys) else (k,u):(insert ys)
   removekey k (List xs) = List(remove xs) where
       remove [] = []
       remove ((key,u):ys) = if key==k then ys else (k,u):(remove ys)
   emptyc = (List [])

-- ================ Basic Single ===============
-- The Single type encode 0 or 1 pairs. Iteration is trivial. Succeeds only once.

data Single k v where
  Single :: k -> v -> Single k v
  Fail :: Single k v
  SetSingle :: k -> Single k ()

firstwins :: Bool
firstwins = False

instance Basic Single where
  addkv (k,v) set comb =
     if firstwins     -- Since we can only store one key, we have to choose who wins
        then case set of
               (Single a b) -> if k==a then Single a (comb v b) else (Single a b)
               (SetSingle a) -> SetSingle a
               Fail ->  Single k v
        else case set of
               (Single a b) -> if k==a then Single a (comb v b) else (Single k v)
               (SetSingle a) -> SetSingle k
               Fail ->  Single k v

  removekey key (Single a b) = if key==a then Fail else (Single a b)
  removekey key (SetSingle a) = if key==a then Fail else (SetSingle a)
  removekey key Fail = Fail
  emptyc = Fail

-- ============== Basic Map =========================

instance Basic Map.Map where
  addpair = Map.insertWith (\x _y -> x)
  addkv (k,v) m comb = Map.insertWith comb  k v m
  removekey k m = Map.delete k m
  emptyc = Map.empty

-- =================== Basic BiMap =====================
-- For Bijections we define (BiMap v k v).  Reasons we can't use (Data.Bimap k v)
-- 1) We need to enforce that the second argument `v` is in the Ord class, when making it an Iter instance.
-- 2) The constructor MkBimap is not exported, so we can't roll our own operations necessary to get good asymptotic performance
-- 3) Missing operation 'restrictkeys' and 'withoutkeys' make performant versions of operations  ◁ ⋪ ▷ ⋫ hard.
-- 4) Missing operation 'union', make performant versions of ∪ and ⨃ hard.


data BiMap v a b where MkBiMap:: (v ~ b) => !(Map.Map a b) -> !(Map.Map b a) -> BiMap v a b
                                --  ^   the 1st and 3rd parameter must be the same:   ^   ^

instance Ord v => Basic (BiMap v) where
  addpair k y (MkBiMap m1 m2) = MkBiMap (Map.insertWith (\x _y -> x) k y m1)  (Map.insertWith (\x _y -> x) y k m2)
  addkv (k,v) (MkBiMap f b) comb =
     case Map.lookup k f of
       Nothing -> MkBiMap (Map.insert k v f) (Map.insert v k b)
       Just v2 -> MkBiMap (Map.insert k v3 f) (Map.insert v3 k (Map.delete v2 b))
          where v3 = comb v v2
  removekey k (m@(MkBiMap m1 m2)) =  -- equality constraint (a ~ v) from (BiMap a k v) into scope.
     case Map.lookup k m1 of
        Just v -> MkBiMap (Map.delete k m1) (Map.delete v m2)
        Nothing -> m
  emptyc = error ("emptyc cannot be defined for BiMap, use the variable: biMapEmpty :: BiMap v k v")

biMapEmpty :: BiMap v k v
biMapEmpty = MkBiMap Map.empty Map.empty

biMapFromList:: (Ord k,Ord v) => [(k,v)] -> BiMap v k v
biMapFromList xs = foldr (\ (k,v) ans -> addpair k v ans) biMapEmpty xs

-- This synonym makes (BiMap v k v) appear as an ordinary Binary type contructor: (Bimap k v)
type Bimap k v = BiMap v k v

-- This operation is very fast (Log n) on BiMap, but extremely slow on other collections.
removeval:: (Ord k, Ord v) => v -> BiMap v k v -> BiMap v k v
removeval v (m@(MkBiMap m1 m2)) =
     case Map.lookup v m2 of
        Just k -> MkBiMap (Map.delete k m1) (Map.delete v m2)
        Nothing -> m

-- ================= Basic Set =====================

data Sett k v where Sett :: (Set.Set k) -> Sett k ()

instance Basic Sett where
  addpair key unit (Sett m) = Sett(Set.insert key m)
  addkv (k,unit) (Sett m) comb = Sett(Set.insert k m)  -- We can ignore comb since there is only one function at type: () -> () -> ()
  removekey k (Sett m) = Sett(Set.delete k m)
  emptyc = error ("Sett Set.empty has type (Sett k ()) and it needs type (Sett k v)")


-- ================= The Iter class =================================================
-- The Set algebra include types that encode finite maps of some type. They
-- have a finite domain, and for each domain element they pair a single range
-- element. We are interested in those finite maps that can iterate their
-- pairs in ascending domain order. The operations are: `nxt` and `lub` .
-- lub can skip over many items in sub-linear time, it can make things really fast.
-- Many finite maps can support a support lub operation. Some examples:
-- Balanced binary trees, Arrays (using binary search), Tries, etc.
-- There are basic and compound Iter instances. Compound types include components
-- with types that have Iter instances.
-- ===================================================================================

class Iter f where
  nxt:: f a b -> Collect (a,b,f a b)
  lub :: Ord k => k -> f k b -> Collect (k,b,f k b)

  -- The next few methods can all be defined via nxt and lub, but for base types
  -- there are often much more efficent means, so the default definitions should be
  -- overwritten. For compound types with Guards, these are often the only way to define them.

  hasNxt :: f a b -> Maybe(a,b,f a b)
  hasNxt f = hasElem (nxt f)
  hasLub :: Ord k => k -> f k b -> Maybe(k,b,f k b)
  hasLub a f = hasElem (lub a f)
  haskey:: Ord key => key -> f key b -> Bool
  haskey k x = case hasLub k x of { Nothing -> False; Just (key,_,_) -> k==key}
  isnull:: f k v -> Bool
  isnull f = isempty(nxt f)
  lookup:: Ord key => key -> f key rng -> Maybe rng
  lookup k x = case hasLub k x of { Nothing -> Nothing; Just (key,v,_) -> if k==key then Just v else Nothing}
  element :: (Ord k) => k -> f k v -> Collect ()
  element k f = when (haskey k f)


-- ============ Iter List =========
data List k v where  List :: Ord k => [(k,v)]  -> List k v

instance Iter List where
   nxt (List []) = none
   nxt (List ((k,v):xs)) = one(k,v,List xs)
   lub k (List xs) = case dropWhile (\ (key,v) -> key < k) xs of
                       [] -> none
                       ((key,v):ys) -> one (key,v,List ys)
   isnull (List xs) = null xs
   lookup k (List xs) = List.lookup k xs


-- =============== Iter Single ==================

instance Iter Single where
  nxt (Single k v) = Collect(\ ans f -> f (k,v,Fail) ans)
  nxt (SetSingle k) = Collect(\ ans f ->  f (k,(),Fail) ans)
  nxt Fail = Collect(\ ans f -> ans)
  lub key (Single k v) = Collect(\ ans f -> if k<=key then f (k,v,Fail) ans else ans)
  lub key (SetSingle k) = Collect(\ ans f -> if k<=key then f(k,(),Fail) ans else ans)
  lub key Fail = Collect(\ ans f -> ans)
  haskey k (SetSingle a) = k==a
  haskey k (Single a b) = k==a
  haskey k Fail = False
  isnull Fail = True
  isnull _ = False
  lookup k (SetSingle a) = if k==a then Just() else Nothing
  lookup k (Single a b) = if k==a then Just b else Nothing
  lookup k Fail = Nothing

instance (Show k,Show v) => Show (Single k v) where
  show (Single k v) = "(Single "++show k ++ " "++show v++")"
  show (SetSingle k) = "(SetSingle "++show k++")"
  show Fail = "Fail"

-- ============= Iter Sett ===============

instance Iter Sett where
  nxt (Sett m) = Collect (\ ans f -> if Set.null m then ans else let (k,nextm) = Set.deleteFindMin m in f (k,(),Sett nextm) ans)
  lub key (Sett m) =
      Collect (\ ans f -> if Set.null m
                             then ans
                             else case Set.splitMember key m of   -- NOTE in Log time, we skip over all those tuples in _left
                                     (_left,True,right) -> f (key,(),Sett right) ans
                                     (_left,False,right) -> if Set.null right
                                                        then ans
                                                        else let (k,nextm) = Set.deleteFindMin right in f (k,(),Sett  nextm) ans)
  haskey key (Sett m) = Set.member key m
  isnull (Sett x) = Set.null x
  lookup k (Sett m) = if Set.member k m then Just() else Nothing


-- ================== Iter Map ===============

instance Iter Map.Map where
  nxt m = Collect (\ ans f ->
     case Map.minViewWithKey m of
        Nothing -> ans
        Just((k,v),nextm) -> f (k,v,nextm) ans)
  lub key m = Collect (\ ans f ->
     case Map.splitLookup key m of                  -- NOTE in Log time, we skip over all those tuples in _left
       (_left,Just v,right) -> f (key,v,right) ans
       (_left,Nothing,Tip) -> ans
       (_left,Nothing,right) -> f (k,v,m3) ans
           where ((k,v),m3) = Map.deleteFindMin right)
  haskey x m = case Map.lookup x m of Just _ -> True; Nothing -> False
  isnull = Map.null
  lookup = Map.lookup


-- ===========================================================
-- Some times we need to write our own version of functions
-- over  Map.Map that do not appear in the library
-- A version of Map.withoutKeys where both parts are Map.Map
-- ============================================================

noKeys :: Ord k => Map k a -> Map k b -> Map k a
noKeys Tip _ = Tip
noKeys m Tip = m
noKeys m (Bin _ k _ ls rs) = case Map.split k m of
  (lm, rm) -> link2 lm' rm'     -- We know `k` is not in either `lm` or `rm`
     where !lm' = noKeys lm ls
           !rm' = noKeys rm rs
{-# INLINABLE noKeys #-}


-- ============== Iter BiMap ====================

instance Ord v => Iter (BiMap v) where
  nxt (MkBiMap left right) = Collect (\ ans f ->
     case Map.minViewWithKey left of
        Nothing -> ans
        Just((k,v),nextm) -> f (k,v,MkBiMap nextm right) ans)
  lub key (MkBiMap forward backward) = Collect (\ ans f ->
     case Map.splitLookup key forward of           -- NOTE in Log time, we skip over all those tuples in _left
       (_left,Just v,right) -> f (key,v,MkBiMap right backward) ans
       (_left,Nothing,Tip) -> ans
       (_left,Nothing,right) -> f (k,v,MkBiMap m3 backward) ans
           where ((k,v),m3) = Map.deleteFindMin right )
  isnull (MkBiMap f g) = isnull f
  lookup x (MkBiMap left right) = Map.lookup x left
  haskey k (MkBiMap left right) = haskey k left


-- ===============================================================================================
-- BaseRep witnesses Basic types. I.e. those that instances of both Basic and Iter.
-- It is used in constructors 'Base' and 'BaseD' and functions 'materialize' and 'fromList'
-- ===============================================================================================

data BaseRep f k v where
   MapR::    Basic Map.Map => BaseRep Map.Map k v
   SetR::    Basic Sett    => BaseRep Sett k ()
   ListR::   Basic List    => BaseRep List k v
   SingleR:: Basic Single  => BaseRep Single k v
   BiMapR::  (Basic (BiMap v),Ord v) => BaseRep (BiMap v) k v


-- ==========================================================================
-- The most basic operation of iteration, where (Iter f) is to use the 'nxt'
-- operator on (f k v) to create a (Collect k v). The two possible
-- ways to produce their elements are in LIFO or FIFO order.
-- ===========================================================================

lifo :: Iter f => f k v -> Collect (k,v)
lifo x = do { (k,v,x2) <- nxt x; front (k,v) (lifo x2) }

fifo :: Iter f => f k v -> Collect (k,v)
fifo x = do { (k,v,x2) <- nxt x; rear (fifo x2) (k,v)}


-- ================================================================================================
-- | The self typed Exp GADT, that encodes the shape of Set expressions. A deep embedding.
-- Exp is a typed Symbolic representation of queries we may ask. It allows us to introspect a query
-- The strategy is to
-- 1) Define Exp so all queries can be represented.
-- 2) Define smart constructors that "parse" the surface syntax, and build a typed Exp
-- 3) Write an evaluate function. eval:: Exp t -> t
-- 4) "eval" can introspect the code and apply efficient domain and type specific translations
-- 5) Use the (Iter f) class to evaluate some Exp that can benefit from its efficient nature.
-- ===============================================================================================

data Exp t where
   Base:: (Ord k,Basic f) => BaseRep f k v -> f k v -> Exp (f k v)  -- Note the use of BaseRep to witness what Base type.
   Dom:: Ord k => Exp (f k v) -> Exp (Sett k ())
   Rng:: (Ord k,Ord v) => Exp (f k v) -> Exp (Sett v ())
   DRestrict:: (Ord k,Iter g) => Exp (g k ()) -> Exp (f k v) -> Exp (f k v)
   DExclude::  (Ord k,Iter g) => Exp (g k ()) -> Exp (f k v) -> Exp (f k v)
   RRestrict:: (Ord k,Iter g,Ord v) => Exp (f k v) -> Exp (g v ()) -> Exp (f k v)
   RExclude:: (Ord k,Iter g,Ord v) => Exp (f k v) -> Exp (g v ()) -> Exp (f k v)
   Elem :: (Ord k,Iter g,Show k) => k -> Exp(g k ()) -> Exp Bool
   NotElem ::(Ord k,Iter g, Show k) => k -> Exp(g k ()) -> Exp Bool
   UnionLeft:: Ord k => Exp (f k v) -> Exp (g k v) -> Exp(f k v)
   UnionPlus:: (Ord k,Num n) => Exp (f k n) -> Exp (f k n) -> Exp(f k n)
   UnionRight:: Ord k => Exp (f k v) -> Exp (f k v) -> Exp(f k v)
   Singleton:: (Show k,Ord k,Show v) => k -> v -> Exp(Single k v)
   SetSingleton:: (Show k,Ord k) => k -> Exp(Single k ())


-- =================================================================
-- | Basic types are those that can be embedded into Exp.
-- The Base class, encodes how to lift a Basic type into an Exp.
-- The function 'toExp' will build a typed Exp for that Basic type.
-- This will be really usefull in the smart constructors.
-- ==================================================================

class Base s t | s -> t where
  toExp :: s -> Exp t

-- | The simplest Base type is one that is already an Exp

instance Base (Exp t) t where
  toExp x = x

instance (Ord k) => Base (Map k v) (Map k v) where
  toExp x = Base MapR x

instance (Ord k) => Base (Set.Set k) (Sett k ()) where
  toExp x = Base SetR (Sett x)

instance  (Ord k) => Base [(k,v)] (List k v) where
  toExp l = Base ListR (List (sortBy (\ x y -> compare (fst x) (fst y)) l))

instance (Ord k) => Base (Single k v) (Single k v) where
  toExp x = Base SingleR x

instance (Ord k,Ord v) => Base (Bimap k v) (Bimap k v) where
  toExp x = Base BiMapR x


-- ==========================================================================================
-- Smart constructors build typed Exp with real values at the leaves (the Base constuctor)

dom :: (Ord k,Base s (f k v)) => s -> Exp (Sett k ())
dom x = Dom (toExp x)

range:: (Ord k,Ord v) => Base s (f k v) => s -> Exp (Sett v ())
range x = Rng(toExp x)

(◁),(<|),drestrict ::  (Ord k,Iter g, Base s1 (g k ()), Base s2 (f k v)) => s1 -> s2 -> Exp (f k v)
(◁) x y = DRestrict (toExp x) (toExp y)
drestrict = (◁)
(<|) = drestrict

(⋪),dexclude :: (Ord k,Iter g, Base s1 (g k ()), Base s2 (f k v)) => s1 -> s2 -> Exp (f k v)
(⋪) x y = DExclude (toExp x) (toExp y)
dexclude = (⋪)

(▷),(|>),rrestrict :: (Ord k,Iter g, Ord v, Base s1 (f k v), Base s2 (g v ())) => s1 -> s2 -> Exp (f k v)
(▷) x y = RRestrict (toExp x) (toExp y)
rrestrict = (▷)
(|>) = (▷)

(⋫),rexclude :: (Ord k,Iter g, Ord v, Base s1 (f k v), Base s2 (g v ())) => s1 -> s2 -> Exp (f k v)
(⋫) x y = RExclude (toExp x) (toExp y)
rexclude = (⋫)

(∈) :: (Show k, Ord k,Iter g,Base s (g k ())) => k -> s -> Exp Bool
(∈) x y = Elem x (toExp y)

(∉),notelem :: (Show k, Ord k,Iter g, Base s (g k ())) => k -> s -> Exp Bool
(∉) x y = NotElem x (toExp y)
notelem = (∉)

(∪),unionleft :: (Ord k,Base s1 (f k v), Base s2 (g k v)) => s1 -> s2 -> Exp (f k v)
(∪) x y = UnionLeft (toExp x) (toExp y)
unionleft = (∪)

(⨃),unionright :: (Ord k,Base s1 (f k v), Base s2 (f k v)) => s1 -> s2 -> Exp (f k v)
(⨃) x y = UnionRight (toExp x) (toExp y)
unionright = (⨃)

(∪+),unionplus :: (Ord k,Num n, Base s1 (f k n), Base s2 (f k n)) => s1 -> s2 -> Exp (f k n)
(∪+) x y = UnionPlus (toExp x) (toExp y)
unionplus = (∪+)

singleton :: (Ord k, Show k,Show v) => k -> v -> Exp (Single k v)
singleton k v = Singleton k v

setSingleton :: (Show k, Ord k) => k -> Exp (Single k ())
setSingleton k = SetSingleton k


-- =======================================================================================
-- | Symbolc functions are data, that can be pattern matched over. They
-- 1) Represent a wide class of binary functions that are used in translating the SetAlgebra
-- 2) Turned into a String so they can be printed
-- 3) Turned into the function they represent.
-- 4) Composed into bigger functions
-- 5) Symbolically symplified
-- ========================================================================================

data SymFun x y ans where
  XX:: SymFun a b a                                                -- (\ x y -> x)
  YY:: SymFun a b b                                                -- (\ x y -> y)
  Fst:: SymFun a (b,c) b                                           -- (\ x (a,b) -> a)
  Snd:: SymFun a (b,c) c                                           -- (\ x (a,b) -> b)
  Equate :: Eq a => SymFun a a Bool                                -- (\ x y -> x==y)
  Plus :: Num a => SymFun a a a                                    -- (\ x y -> x==y)
  Const:: Show a => a -> SymFun x y a                              -- (\ x y -> ())
  RngFst:: SymFun x (a,b) a                                        -- (\ x y -> fst y)
  RngSnd:: SymFun x (a,b) b                                        -- (\ x y -> snd y)
  Negate:: SymFun k v Bool -> SymFun k v Bool                      -- (\ x y -> not(f x y))
  RngElem:: (Ord rng,Iter f) => f rng v ->  SymFun dom rng Bool    -- (\ x y -> haskey y frngv)  -- x is ignored and frngv is supplied
  DomElem:: (Ord dom,Iter f) => f dom v -> SymFun dom rng Bool     -- (\ x y -> haskey x fdomv)  -- y is ignored and fdomv is supplied
  Comp :: SymFun k b c -> SymFun k a b -> SymFun k a c             -- (Comp f g) = \ x y -> fm x (gm x y)
  CompSndL:: SymFun k (a,b) c -> SymFun k d a -> SymFun k (d,b) c  -- (ComSndL f g) = \ x (a,b) -> mf x (mg x a,b)
  CompSndR:: SymFun k (a,b) c -> SymFun k d b -> SymFun k (a,d) c  -- (comSndR f g) = \ x (a,b) -> mf x (a,mg x b)
  CompCurryR :: SymFun k (a,b) d ->
                SymFun a c b ->
                SymFun k (a,c) d                                    -- (compCurry f g) = \ x (a,b) -> f x(a,g a b)
  Cat :: SymFun String String String
  Len :: Foldable t => SymFun a (t b) Int
  Lift:: String -> (a -> b -> c) -> SymFun a b c


splitString :: [Char] -> ([Char], [Char])
splitString y = ("(fst "++y++")","(snd "++y++")")

showSFP :: SymFun a (b,c) d -> String -> (String,String) -> String
showSFP Fst k (x,y) = x
showSFP Snd k (x,y) = y
showSFP RngFst k (x,y) = x
showSFP RngSnd k (x,y) = y
showSFP (CompSndL f g) k (x,y) = showSFP f k (showSF g k x,y)
showSFP (CompSndR f g) k (x,y) = showSFP f k (x,showSF g k y)
showSFP XX k (x,y) = k
showSFP YY k (x,y) = "("++x++","++y++")"
showSFP (CompCurryR f g) k (x,y) = showSFP f k (x,showSF g x y)
showSFP other k (x,y) = error ("SFP unreachable: "++show other)

showSF :: SymFun a b c -> String -> String -> String
showSF XX x y = x
showSF YY x y = y
showSF Fst x y = showSFP Fst x (splitString y)
showSF Snd x y = showSFP Fst x (splitString y)
showSF Equate x y = "("++x++" == "++y++")"
showSF Plus x y = "("++x++" + "++y++")"
showSF (Const c) x y = "'"++show c
showSF RngFst x y = showSFP RngFst x (splitString y)
showSF RngSnd x y = showSFP RngSnd x (splitString y)
showSF (Negate f) x y = "(not "++(showSF f x y)++")"
showSF (DomElem dset) x y = "(haskey "++x++" ?)"
showSF (RngElem dset) x y = "(haskey "++y++" ?)"
showSF (Comp f g) x y = showSF f x (showSF g x y)
showSF Cat x y = "("++x++" ++ "++y++")"
showSF Len x y = "(len "++y++")"
showSF (Lift nm f) x y = "("++nm++" "++x++" "++y++")"
showSF (CompSndL f g) x y = showSFP (CompSndL f g) x (splitString y)
showSF (CompSndR f g) x y = showSFP (CompSndR f g) x (splitString y)
showSF (CompCurryR f g) x y = showSFP (CompCurryR f g) x (splitString y)


mean:: SymFun a b c -> (a -> b -> c)
mean XX = \ x y -> x
mean YY = \ x y -> y
mean Fst = \ x (a,b) -> a
mean Snd = \ x (a,b) -> b
mean Equate = (==)
mean Plus = (+)
mean (Const c) = \ x y -> c
mean RngFst = \ x (u,v) -> u
mean RngSnd = \ x (u,v) -> v
mean (RngElem dset) = \ x y -> haskey y dset
mean (DomElem dset) = \ x y -> haskey x dset
mean (Negate f) = \ x y -> not(fm x y)
  where !fm = mean f
mean (Comp f g) = \ x y -> fm x (gm x y)
  where !fm = mean f
        !gm = mean g
mean Cat = \ x y -> x ++ "-" ++ y
mean Len = \ x y -> length y
mean (Lift nm f) = f
mean (CompSndL f g) = \ x (a,b) -> mf x (mg x a,b)
   where !mf = mean f
         !mg = mean g
mean (CompSndR f g) = \ x (a,b) -> mf x (a,mg x b)
   where !mf = mean f
         !mg = mean g
mean (CompCurryR f g) =  \ x (a,b) -> mf x(a,mg a b)
   where !mf = mean f
         !mg = mean g


-- ======= Operations for building and using Symbolic functions  =======

data Fun x where
   Fun:: (SymFun x y ans) -> (x -> y -> ans) -> Fun (x -> y -> ans)

fun :: SymFun x y ans -> Fun (x -> y -> ans)
fun s = Fun s (mean s)

apply :: Fun (a -> b -> c) -> a -> b -> c
apply (Fun s f) = f

-- ====================== Showing things ===============================

instance Show (Fun x) where
   show (Fun s f) = show s


instance Show (SymFun a b c) where
   show x = "(\\ x y -> "++(showSF x "x" "y")++")"


instance Show (BaseRep f k v) where
  show MapR = "Map"
  show SetR = "Set"
  show ListR = "List"
  show SingleR = "Single"
  show BiMapR = "BiMap"

instance Show (Exp t) where
  show (Base rep x) = show rep++"?"
  show (Dom x) = "(dom "++show x++")"
  show (Rng x) = "(rng "++show x++")"
  show (DRestrict x y) = "("++show x++" ◁ "++show y++")"
  show (DExclude x y) = "("++show x++" ⋪ "++show y++")"
  show (RRestrict x y) = "("++show x++" ▷ "++show y++")"
  show (RExclude x y) = "("++show x++" ⋫ "++show y++")"
  show (Elem k x) = "("++show k++" ∈ "++show x++")"
  show (NotElem k x) = "("++show k++" ∉ "++show x++")"
  show (UnionLeft x y) = "("++show x++" ∪ "++show y++")"
  show (UnionPlus x y) = "("++show x++" ∪+ "++show y++")"
  show (UnionRight x y) = "("++show x++" ⨃ "++show y++")"
  show (Singleton x y) = "(singleton "++show x++" "++show y++")"
  show (SetSingleton x) = "(Set.Singleton "++show x++")"
