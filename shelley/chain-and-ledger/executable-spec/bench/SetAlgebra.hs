{-# OPTIONS_GHC -Wno-unused-imports #-}
{-# OPTIONS_GHC -Wno-unused-matches #-}
{-# OPTIONS_GHC -Wno-orphans #-}

{-# LANGUAGE GADTs, MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances, FunctionalDependencies  #-}
{-# LANGUAGE TypeFamilies #-}


module SetAlgebra where

import Prelude hiding(lookup)
import Shelley.Spec.Ledger.Core(Bimap(..),bimapFromList, bimapEmpty)
import qualified Data.Map.Strict as Map
import Data.Map.Strict(Map)
import qualified Data.Set as Set
import Collect

-- ===============================================================================================
-- Witnesses of what Haskell types can appear in the Set Algebra

data BaseRep f k v where
   MapR:: BaseRep Map.Map k v
   SetR:: BaseRep Sett k ()
   SingleR:: BaseRep Single k v
   BimapR:: BaseRep Bimap k v
   AndR:: BaseRep f k u -> BaseRep g k v -> BaseRep And k (u,v)
   AndPR:: BaseRep f k u -> BaseRep g k v -> (u -> v -> w) -> BaseRep (AndP f g) k w
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
-- Their are basic and compound Iter instances. Compound types include components
-- with types that have Iter instances.

class Iter f where
  nxt:: f a b -> Collect (a,b,f a b)
  lub :: Ord a => a -> f a b -> Collect (a,b,f a b)

  haskey:: Ord key => key -> f key b -> Bool
  haskey k x = case lookup k x of {Just _ -> True; Nothing -> False}
  isnull:: f k v -> Bool
  repOf :: f a b -> BaseRep f a b

  lookup:: Ord key => key -> f key rng -> Maybe rng
  addpair:: (Ord k) => k -> v -> f k v -> f k v
  removekey:: (Ord k) => k -> f k v -> f k v
  element :: (Ord k) => k -> f k v -> Collect ()
  element k f = when (haskey k f)

class Iter f => HasNull f where
   nullary:: f k v -> Bool

-- =================================================================
-- Primitive types that we will make instances of Iter
-- ==================================================================

-- One type that can be iterated over (in order) and hence collected
-- Of course the iteration is trivial as there are only 0 or 1 pairs.

data Single k v where
  Single :: k -> v -> Single k v
  Fail :: Single k v
  SetSingle :: k -> Single k ()

data Sett k v where Sett :: (Set.Set k) -> Sett k ()

-- ================== Compound data definitions ======================
-- Compound types we will make instances of Iter
-- ===================================================================

data Project k v where
   Project :: (Ord k,Iter f) => f k v -> Fun (k -> v -> u) -> Project k u

data And k t where
     And :: (Ord k,Iter f, Iter g) => f k v1 -> g k v2 -> And k (v1,v2)

data Or k t where
     Or :: (Ord k,Iter f, Iter g) => f k v -> g k v -> Fun(v -> v -> v) -> Or k v

data Guard k v where
   Guard:: (Ord k,Iter f) => f k v -> Fun (k -> v -> Bool) -> Guard k v

data Diff k v where
   Diff :: (Ord k,Iter f,Iter g) => f k v -> g k u -> Diff k v

data AndP f g k v where
   AndP:: (Ord k,Iter f,Iter g) => f k v -> g k u -> (v -> u -> w) -> AndP f g k w

-- ================================================================================================
-- | The self typed Exp GADT, that encodes the shape of Set expressions. A deep embedding.

data Exp t where
   Base:: (Ord k,Ord v,Iter f) => BaseRep f k v -> f k v -> Exp (f k v)
   Dom:: Exp (f k v) -> Exp (Sett k ())
   Rng:: Ord v => Exp (f k v) -> Exp (Sett v ())
   DRestrict:: Exp (Sett k ()) -> Exp (f k v) -> Exp (f k v)
   DExclude::  Exp (Sett k ()) -> Exp (f k v) -> Exp (f k v)
   RRestrict:: Ord v => Exp (f k v) -> Exp (Sett v ()) -> Exp (f k v)
   RExclude:: Ord v => Exp (f k v) -> Exp (Sett v ()) -> Exp (f k v)
   Elem :: Show k => k -> Exp(Sett k ()) -> Exp Bool
   NotElem :: Show k => k -> Exp(Sett k ()) -> Exp Bool
   UnionLeft:: Exp (f k v) -> Exp (g k v) -> Exp(f k v)
   UnionPlus:: Num n => Exp (f k n) -> Exp (f k n) -> Exp(f k n)
   UnionRight:: Exp (f k v) -> Exp (f k v) -> Exp(f k v)
   Singleton:: (Show k,Ord k,Ord v,Show v) => k -> v -> Exp(Single k v)
   SetSingleton:: (Show k,Ord k) => k -> Exp(Sett k ())


-- =================================================================
-- | Basic type are those that can be embedded into Exp.
-- The function 'toExp' will build a typed Exp for that Basic type.
-- This will be really usefull in the smart constructors.

class Basic s t | s -> t where
  toExp :: s -> Exp t

-- | The simplest Basic type is one that is already an Exp

instance Basic (Exp t) t where
  toExp x = x

instance (Iter Map,Ord k,Ord v) => Basic (Map k v) (Map k v) where
  toExp x = Base MapR x

instance (Iter Sett,Ord k) => Basic (Sett k ()) (Sett k ()) where
  toExp x = Base SetR x

instance (Iter Single, Ord k,Ord v) => Basic (Single k v) (Single k v) where
  toExp x = Base SingleR x

instance (Iter Bimap, Ord k,Ord v) => Basic (Bimap k v) (Bimap k v) where
  toExp x = Base BimapR x


-- ==========================================================================================
-- Smart constructors build typed Exp with real values at the leaves (the Basic constuctor)

dom :: Basic s (f k v) => s -> Exp (Sett k ())
dom x = Dom (toExp x)

range:: Ord v => Basic s (f k v) => s -> Exp (Sett v ())
range x = Rng(toExp x)

(◁),(<|),drestrict :: (Basic s1 (Sett k ()), Basic s2 (f k v)) => s1 -> s2 -> Exp (f k v)
(◁) x y = DRestrict (toExp x) (toExp y)
drestrict = (◁)
(<|) = drestrict

(⋪),dexclude :: (Basic s1 (Sett k ()), Basic s2 (f k v)) =>  s1 -> s2 -> Exp (f k v)
(⋪) x y = DExclude (toExp x) (toExp y)
dexclude = (⋪)

(▷),(|>),rrestrict :: (Ord v,Basic s1 (f k v), Basic s2 (Sett v ())) => s1 -> s2 -> Exp (f k v)
(▷) x y = RRestrict (toExp x) (toExp y)
rrestrict = (▷)
(|>) = (▷)

(⋫),rexclude :: (Ord v,Basic s1 (f k v), Basic s2 (Sett v ())) => s1 -> s2 -> Exp (f k v)
(⋫) x y = RExclude (toExp x) (toExp y)
rexclude = (⋫)

(∈) :: (Show k, Basic s (Sett k ())) => k -> s -> Exp Bool
(∈) x y = Elem x (toExp y)

(∉),notelem :: (Show k, Basic s (Sett k ())) => k -> s -> Exp Bool
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

singleton :: (Ord k, Show k, Ord v,Show v) => k -> v -> Exp (Single k v)
singleton k v = Singleton k v

setSingleton :: (Show k, Ord k) => k -> Exp (Sett k ())
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
  XX:: SymFun a b a                                              -- (\ x y -> x)
  YY:: SymFun a b b                                              -- (\ x y -> y)
  Equate :: Eq a => SymFun a a Bool                              -- (\ x y -> x==y)
  Plus :: Num a => SymFun a a a                                  -- (\ x y -> x==y)
  Const:: Show a => a -> SymFun x y a                            -- (\ x y -> ())
  RngFst:: SymFun x (a,b) a                                      -- (\ x y -> fst y)
  RngSnd:: SymFun x (a,b) b                                      -- (\ x y -> snd y)
  Negate:: SymFun k v Bool -> SymFun k v Bool                    -- (\ x y -> not(f x y))
  RngElem:: (Ord rng,Iter f) => f rng v ->  SymFun dom rng Bool  -- (\ x y -> haskey y frngv)  -- x is ignored and frngv is supplied
  DomElem:: (Ord dom,Iter f) => f dom v -> SymFun dom rng Bool   -- (\ x y -> haskey x fdomv)  -- y is ignored and fdomv is supplied
  Comp :: SymFun k b c -> SymFun k a b -> SymFun k a c


showSF :: SymFun a b c -> String -> String -> String
showSF XX x y = x
showSF YY x y = y
showSF Equate x y = "("++x++" == "++y++")"
showSF Plus x y = "("++x++" + "++y++")"
showSF (Const c) x y = show c
showSF RngFst x y = "(fst "++y++")"
showSF RngSnd x y = "(snd "++y++")"
showSF (Negate f) x y = "(not "++(showSF f x y)++")"
showSF (DomElem dset) x y = "(haskey "++x++" ?)"
showSF (RngElem dset) x y = "(haskey "++y++" ?)"
showSF (Comp f g) x y = showSF f x (showSF g x y)

mean:: SymFun a b c -> (a -> b -> c)
mean XX = \ x y -> x
mean YY = \ x y -> y
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
  show SingleR = "Single"
  show BimapR = "Bimap"
  show (AndR x y) = "(And "++show x++" "++show y++")"
  show (AndPR x y p) = "(AndP "++show x++" "++show y++")"
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
