{-# OPTIONS_GHC -Wno-unused-imports #-}
{-# OPTIONS_GHC -Wno-unused-matches #-}
{-# OPTIONS_GHC -Wno-orphans #-}

{-# LANGUAGE GADTs, MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances, FunctionalDependencies  #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DeriveGeneric           #-}


module SetAlgebra where

import Prelude hiding(lookup)
import qualified Data.Map.Strict as Map
import Data.Map.Strict(Map)
import qualified Data.Set as Set
import Data.List(sortBy)
import Collect

-- ===============================================================================================
-- Witnesses of what Haskell types can appear in the Set Algebra

data BaseRep f k v where
   MapR:: BaseRep Map.Map k v
   SetR:: BaseRep Sett k ()
   ListR:: BaseRep List k v
   SingleR:: BaseRep Single k v
   BiMapR:: Ord v => BaseRep (BiMap v) k v
   AndR:: BaseRep f k u -> BaseRep g k v -> BaseRep And k (u,v)
   ChainR:: BaseRep f k v -> BaseRep g v w -> Fun(k -> (v,w) -> u) -> BaseRep Chain k u
   AndPR:: BaseRep f k u -> BaseRep g k v -> Fun(k -> (u,v) -> w) -> BaseRep AndP k w
   DiffR:: BaseRep f k u -> BaseRep g k v -> BaseRep Diff k u
   OrR:: BaseRep f k v -> BaseRep g k v -> Fun(v -> v -> v) -> BaseRep Or k v
   ProjectR:: BaseRep f k v -> Fun (k -> v -> u) -> BaseRep Project k u
   GuardR:: BaseRep f k v -> Fun(k -> v -> Bool) -> BaseRep Guard k v


-- =================================================================
-- The Set algebra include types that encode finite maps of some type. They
-- have a finite domain, and for each domain element they pair a single range
-- element. We are interested in those finite maps that can iterate their
-- pairs in ascending domain order. The operations are: `nxt` and `lub` .
-- lub can skip over many items in sub-linear time, it can make things really fast.
-- Many finite maps can support a support lub operation. Some examples:
-- Balanced binary trees, Arrays (using binary search), Tries, etc.
-- There are basic and compound Iter instances. Compound types include components
-- with types that have Iter instances.

class Iter f where
  nxt:: f a b -> Collect (a,b,f a b)
  lub :: Ord k => k -> f k b -> Collect (k,b,f k b)
  repOf :: f a b -> BaseRep f a b

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

  addpair:: (Ord k) => k -> v -> f k v -> f k v
  addpair k v f = addkv (k,v) f (\ a b -> a)
  addkv :: Ord k => (k,v) -> f k v -> (v -> v -> v) -> f k v
  removekey:: (Ord k) => k -> f k v -> f k v
  emptyc:: Ord k => f k v
  emptyc = error ("emptyc only works on some types.")

-- =========================================================================
-- The most basic operation of iteration, where (Iter f) is to use the 'nxt'
-- operator on (f k v) to create a collection (Collect k v). The two possible
-- ways to produce their elements are in LIFO or FIFO order.

lifo :: Iter f => f k v -> Collect (k,v)
lifo x = do { (k,v,x2) <- nxt x; front (k,v) (lifo x2) }

fifo :: Iter f => f k v -> Collect (k,v)
fifo x = do { (k,v,x2) <- nxt x; rear (fifo x2) (k,v)}


-- =================================================================
-- Primitive types (f k v) that we will make instances of (Iter f')
-- Also a few we just import: Data.Map.Strict.Map and Data.Set.Set
-- ==================================================================

-- The Single type that can be iterated over (in order) and hence collected
-- Of course the iteration is trivial as there are only 0 or 1 pairs.

data Single k v where
  Single :: k -> v -> Single k v
  Fail :: Single k v
  SetSingle :: k -> Single k ()

instance (Show k,Show v) => Show (Single k v) where
  show (Single k v) = "(Single "++show k ++ " "++show v++")"
  show (SetSingle k) = "(SetSingle "++show k++")"
  show Fail = "Fail"

-- Data.Set where we fix the value to be ()

data Sett k v where Sett :: (Set.Set k) -> Sett k ()

-- Lists of pairs with (1) the sorted assumption, and (2) there is only one v for each k.

data List k v where
   List :: Ord k => [(k,v)]  -> List k v


-- For Bijections we define (BiMap v k v).  Reasons we can't use (Data.Bimap k v)
-- 1) We need to enforce that the second argument `v` is in the Ord class, when making it an Iter instance.
-- 2) The constructor MkBimap is not exported, so we can't roll our own operations necessary to get good asymptotic performance
-- 3) Missing operation 'restrictkeys' and 'withoutkeys' make performant versions of operations  ◁ ⋪ ▷ ⋫ hard.
-- 4) Missing operation 'union', make performant versions of ∪ and ⨃ hard.

data BiMap v a b where MkBiMap:: (v ~ b) => !(Map.Map a b) -> !(Map.Map b a) -> BiMap v a b
                                --  ^   the 1st and 3rd parameter must be the same:   ^   ^

biMapEmpty :: BiMap v k v
biMapEmpty = MkBiMap Map.empty Map.empty

biMapFromList:: (Ord k,Ord v) => [(k,v)] -> BiMap v k v
biMapFromList xs = foldr (\ (k,v) ans -> biMapAddpair k v ans) biMapEmpty xs

-- This synonym makes (BiMap v k v) appear as an ordinary Binary type contractor: (Bimap k v)
type Bimap k v = BiMap v k v

biMapAddpair :: (Ord v, Ord k) => k -> v -> BiMap v k v -> BiMap v k v
biMapAddpair k y (MkBiMap m1 m2) = MkBiMap (Map.insertWith (\x _y -> x) k y m1)  (Map.insertWith (\x _y -> x) y k m2)

biMapRemovekey :: (Ord k, Ord v) => k -> BiMap v k v -> BiMap v k v
biMapRemovekey k (m@(MkBiMap m1 m2)) =
     case Map.lookup k m1 of
        Just v -> MkBiMap (Map.delete k m1) (Map.delete v m2)
        Nothing -> m

-- This operation is very fast (Log n) on BiMap, but extremely slow on other collections.
removeval:: (Ord k, Ord v) => v -> BiMap v k v -> BiMap v k v
removeval v (m@(MkBiMap m1 m2)) =
     case Map.lookup v m2 of
        Just k -> MkBiMap (Map.delete k m1) (Map.delete v m2)
        Nothing -> m


-- ================== Compound data definitions ======================
-- Compound types we will make instances of Iter
-- ===================================================================

data Project k v where
   Project :: (Ord k,Iter f) => f k v -> Fun (k -> v -> u) -> Project k u

data And k t where
     And :: (Ord k,Iter f, Iter g) => f k v1 -> g k v2 -> And k (v1,v2)

data Chain k t where
    Chain:: (Ord k,Iter f,Ord v,Iter g) => f k v -> g v w -> Fun(k -> (v,w) -> u) -> Chain k u

data Or k t where
     Or :: (Ord k,Iter f, Iter g) => f k v -> g k v -> Fun(v -> v -> v) -> Or k v

data Guard k v where
   Guard:: (Ord k,Iter f) => f k v -> Fun (k -> v -> Bool) -> Guard k v

data Diff k v where
   Diff :: (Ord k,Iter f,Iter g) => f k v -> g k u -> Diff k v

data AndP k v where
   AndP:: (Ord k,Iter f,Iter g) => f k v -> g k u -> Fun(k -> (v,u) -> w) -> AndP k w


-- ================================================================================================
-- | The self typed Exp GADT, that encodes the shape of Set expressions. A deep embedding.

data Exp t where
   Base:: (Ord k,Iter f) => BaseRep f k v -> f k v -> Exp (f k v)
   Dom:: Exp (f k v) -> Exp (Sett k ())
   Rng:: Ord v => Exp (f k v) -> Exp (Sett v ())
   DRestrict:: Iter g => Exp (g k ()) -> Exp (f k v) -> Exp (f k v)
   DExclude::  Iter g => Exp (g k ()) -> Exp (f k v) -> Exp (f k v)
   RRestrict:: (Iter g,Ord v) => Exp (f k v) -> Exp (g v ()) -> Exp (f k v)
   RExclude:: (Iter g,Ord v) => Exp (f k v) -> Exp (g v ()) -> Exp (f k v)
   Elem :: (Iter g,Show k) => k -> Exp(g k ()) -> Exp Bool
   NotElem ::(Iter g, Show k) => k -> Exp(g k ()) -> Exp Bool
   UnionLeft:: Exp (f k v) -> Exp (g k v) -> Exp(f k v)
   UnionPlus:: Num n => Exp (f k n) -> Exp (f k n) -> Exp(f k n)
   UnionRight:: Exp (f k v) -> Exp (f k v) -> Exp(f k v)
   Singleton:: (Show k,Ord k,Show v) => k -> v -> Exp(Single k v)
   SetSingleton:: (Show k,Ord k) => k -> Exp(Single k ())


-- =================================================================
-- | Basic type are those that can be embedded into Exp.
-- The function 'toExp' will build a typed Exp for that Basic type.
-- This will be really usefull in the smart constructors.

class Basic s t | s -> t where
  toExp :: s -> Exp t

-- | The simplest Basic type is one that is already an Exp

instance Basic (Exp t) t where
  toExp x = x

instance (Iter Map,Ord k) => Basic (Map k v) (Map k v) where
  toExp x = Base MapR x

instance (Iter Sett,Ord k) => Basic (Set.Set k) (Sett k ()) where
  toExp x = Base SetR (Sett x)

instance  (Iter List,Ord k) => Basic [(k,v)] (List k v) where
  toExp l = Base ListR (List (sortBy (\ x y -> compare (fst x) (fst y)) l))

instance (Iter Single, Ord k) => Basic (Single k v) (Single k v) where
  toExp x = Base SingleR x

instance (Iter (BiMap v), Ord k,Ord v) => Basic (Bimap k v) (Bimap k v) where
  toExp x = Base BiMapR x


-- ==========================================================================================
-- Smart constructors build typed Exp with real values at the leaves (the Basic constuctor)

dom :: Basic s (f k v) => s -> Exp (Sett k ())
dom x = Dom (toExp x)

range:: Ord v => Basic s (f k v) => s -> Exp (Sett v ())
range x = Rng(toExp x)

(◁),(<|),drestrict ::  (Iter g, Basic s1 (g k ()), Basic s2 (f k v)) => s1 -> s2 -> Exp (f k v)
(◁) x y = DRestrict (toExp x) (toExp y)
drestrict = (◁)
(<|) = drestrict

(⋪),dexclude :: (Iter g, Basic s1 (g k ()), Basic s2 (f k v)) => s1 -> s2 -> Exp (f k v)
(⋪) x y = DExclude (toExp x) (toExp y)
dexclude = (⋪)

(▷),(|>),rrestrict :: (Iter g, Ord v, Basic s1 (f k v), Basic s2 (g v ())) => s1 -> s2 -> Exp (f k v)
(▷) x y = RRestrict (toExp x) (toExp y)
rrestrict = (▷)
(|>) = (▷)

(⋫),rexclude :: (Iter g, Ord v, Basic s1 (f k v), Basic s2 (g v ())) => s1 -> s2 -> Exp (f k v)
(⋫) x y = RExclude (toExp x) (toExp y)
rexclude = (⋫)

(∈) :: (Show k, Iter g,Basic s (g k ())) => k -> s -> Exp Bool
(∈) x y = Elem x (toExp y)

(∉),notelem :: (Show k, Iter g, Basic s (g k ())) => k -> s -> Exp Bool
(∉) x y = NotElem x (toExp y)
notelem = (∉)

(∪),unionleft :: (Basic s1 (f k v), Basic s2 (g k v)) => s1 -> s2 -> Exp (f k v)
(∪) x y = UnionLeft (toExp x) (toExp y)
unionleft = (∪)

(⨃),unionright :: (Basic s1 (f k v), Basic s2 (f k v)) => s1 -> s2 -> Exp (f k v)
(⨃) x y = UnionRight (toExp x) (toExp y)
unionright = (⨃)

(∪+),unionplus :: (Num n, Basic s1 (f k n), Basic s2 (f k n)) => s1 -> s2 -> Exp (f k n)
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
  where fm = mean f
mean (Comp f g) = \ x y -> fm x (gm x y)
  where fm = mean f
        gm = mean g
mean Cat = \ x y -> x ++ "-" ++ y
mean Len = \ x y -> length y
mean (Lift nm f) = f
mean (CompSndL f g) = \ x (a,b) -> mf x (mg x a,b)
   where mf = mean f
         mg = mean g
mean (CompSndR f g) = \ x (a,b) -> mf x (a,mg x b)
   where mf = mean f
         mg = mean g
mean (CompCurryR f g) =  \ x (a,b) -> mf x(a,mg a b)
   where mf = mean f
         mg = mean g


-- ============================== ReWrites =========================

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
  show (AndR x y) = "(And "++show x++" "++show y++")"
  show (AndPR x y p) = "(AndP "++show x++" "++show y++" "++show p++")"
  show (ChainR x y p) = "(Chain "++show x++" "++show y++" "++show p++")"
  show (OrR x y p) =  "(Or "++show x++" "++show y++" "++show p++")"
  show (DiffR x y) = "(Diff "++show x++" "++show y++")"
  show (ProjectR x p) = "(Project "++show x++" "++show p++")"
  show (GuardR x p) = "(Guard "++show x++" "++show p++")"


shape :: Iter f => f k v -> String
shape x = show(repOf x)

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
