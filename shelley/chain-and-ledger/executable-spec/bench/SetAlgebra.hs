{-# OPTIONS_GHC -Wno-unused-imports #-}
{-# OPTIONS_GHC -Wno-unused-matches #-}
{-# OPTIONS_GHC -Wno-orphans #-}

{-# LANGUAGE GADTs, MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances, FunctionalDependencies  #-}


module SetAlgebra where

import Shelley.Spec.Ledger.Core(Bimap(..),bimapFromList, bimapEmpty)
import qualified Data.Map.Strict as Map
import Data.Map.Strict(Map)
import qualified Data.Set as Set
import Collect

-- ===============================================================================================
-- Witnesses of what Haskell types can appear in the Set Algebra

data BaseRep f k v where
   Map:: BaseRep Map.Map k v
   Set:: BaseRep Sett k ()
   Pair:: BaseRep Pair k v
   Bimap:: BaseRep Bimap k v
   Project:: BaseRep Project k v
   And2:: BaseRep And2 k (v1,v2)
   Or2:: BaseRep Or2 k [v]
   Guard:: BaseRep Guard k v

data Project k v where
   Projectx :: (Ord k,Iter f) => f k v -> (k -> v -> u) -> Project k u

data And2 k t where
     And2x :: (Ord k,Iter f, Iter g) => f k v1 -> g k v2 -> And2 k (v1,v2)

data Or2 k t where
     Or2x :: (Ord k, Iter f, Iter g) => f k v -> g k v -> Or2 k [v]


data Guard k v where
   Guardx:: (Ord k,Iter f) => f k v -> (k -> v -> Bool) -> Guard k v

data Pair k v where
  Two :: k -> v -> Pair k v
  Fail :: Pair k v
  One :: k -> Pair k ()

data Sett k v where Sett :: (Set.Set k) -> Sett k ()

-- ==============================================================
-- A binary type constructor can act as an iterator, collecting the pairs in the type,
-- if it supports the following operations: `nxt` and `lub`
-- If it iterates over items in increasing order, and can skip over many items
-- using `lub` in sub-linear time, it can make things really fast. Many collections
-- support lub: Balanced binary trees, Arrays (using binary search), Tries, etc.

class Iter f where
  nxt:: f a b -> Collect (a,b,f a b)
  lub :: Ord a => a -> f a b -> Collect (a,b,f a b)
  element :: Ord a => a -> f a b -> Collect ()
  haskey:: Ord key => key -> f key b -> Bool
  addpair:: (Ord k) => k -> v -> f k v -> f k v
  empty:: f k v -> Bool
  removekey:: (Ord k) => k -> f k v -> f k v
  --removekey k f = error ("Default remove key raises error")

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
   Singleton:: (Show k,Ord k,Ord v,Show v) => k -> v -> Exp(Pair k v)
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
  toExp x = Base Map x

instance (Iter Sett,Ord k) => Basic (Sett k ()) (Sett k ()) where
  toExp x = Base Set x

instance (Iter Pair,Ord k,Ord v) => Basic (Pair k v) (Pair k v) where
  toExp x = Base Pair x

instance (Iter Bimap,Ord k,Ord v) => Basic (Bimap k v) (Bimap k v) where
  toExp x = Base Bimap x


-- ==========================================================================================
-- Smart constructors build typed Exp with real values at the leaves (the Basic constuctor)

dom :: Basic s (f k v) => s -> Exp (Sett k ())
dom x = Dom (toExp x)

rng:: Ord v => Basic s (f k v) => s -> Exp (Sett v ())
rng x = Rng(toExp x)

(◁),drestrict :: (Basic s1 (Sett k ()), Basic s2 (f k v)) => s1 -> s2 -> Exp (f k v)
(◁) x y = DRestrict (toExp x) (toExp y)
drestrict = (◁)

(⋪),dexclude :: (Basic s1 (Sett k ()), Basic s2 (f k v)) =>  s1 -> s2 -> Exp (f k v)
(⋪) x y = DExclude (toExp x) (toExp y)
dexclude = (⋪)

(▷),rrestrict :: (Ord v,Basic s1 (f k v), Basic s2 (Sett v ())) => s1 -> s2 -> Exp (f k v)
(▷) x y = RRestrict (toExp x) (toExp y)
rrestrict = (▷)

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

singleton :: (Ord k, Show k, Ord v,Show v) => k -> v -> Exp (Pair k v)
singleton k v = Singleton k v

setSingleton :: (Show k, Ord k) => k -> Exp (Sett k ())
setSingleton k = SetSingleton k


-- =======================================================================================

instance Show (BaseRep f k v) where
  show Map = "Map"
  show Set = "Set"
  show Pair = "Pair"
  show Bimap = "Bimap"
  show And2 = "And2"
  show Or2 = "Or2"
  show Project = "Project"
  show Guard = "Guard"

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
