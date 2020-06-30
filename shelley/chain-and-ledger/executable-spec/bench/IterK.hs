{-# OPTIONS_GHC -Wno-unused-imports #-}
{-# OPTIONS_GHC -Wno-unused-matches #-}
{-# OPTIONS_GHC -Wno-orphans #-}

{-# LANGUAGE FlexibleContexts, FlexibleInstances, FunctionalDependencies  #-}
{-# LANGUAGE GADTs, MultiParamTypeClasses #-}
{-# LANGUAGE TypeOperators, DataKinds,  KindSignatures #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE TypeFamilies, TypeFamilyDependencies  #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- Iteration with Continuations

module IterK where

import Prelude hiding (lookup)
-- import Debug.Trace

import qualified Data.List as List

import Data.Map.Strict(Map)
import qualified Data.Map.Strict as Map
import Data.Map.Internal(Map(..),link,link2)
import Data.Map.Internal.Debug(showTree)

import Data.Set(Set)
import qualified Data.Set as Set

import Data.Char(ord)

import Collect
import SetAlgebra(Iter(..),
                  And(..),Or(..),Project(..),Guard(..),Diff(..),Single(..),Sett(..),AndP(..),List(..),
                  Exp(..),BaseRep(..),
                  dom, range, singleton, setSingleton, (◁), (⋪), (▷), (⋫), (∪), (⨃), (∈), (∉),(|>),(<|),
                  element,shape, lifo, fifo,
                  SymFun(..), Fun, fun, SymFun, apply,
                  BiMap(..), Bimap, biMapAddpair, biMapRemovekey, biMapFromList, biMapEmpty, removeval
                 )

import Test.HUnit


-- =====================================================================================
-- Instances for the Basic types
-- =====================================================================================

-- ====================== Basic List =========================

-- List defined in SetAlgebra.hs
-- data List k v where List :: Ord k => [(k,v)]  -> List k v

instance Iter List where
   nxt (List []) = none
   nxt (List ((k,v):xs)) = one(k,v,List xs)
   lub k (List xs) = case dropWhile (\ (key,v) -> key < k) xs of
                       [] -> none
                       ((key,v):ys) -> one (key,v,List ys)
   repOf (List _) = ListR
   isnull (List xs) = null xs
   lookup k (List xs) = List.lookup k xs
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


-- =================== Basic Single =================

-- Single defined in SetAlgebra.hs
-- data Single k v where { Single :: k -> v -> Single k v; Fail :: Single k v; SetSingle :: k -> Single k () }

firstwins :: Bool
firstwins = False


instance Iter Single where
  nxt (Single k v) = Collect(\ ans f -> f (k,v,Fail) ans)
  nxt (SetSingle k) = Collect(\ ans f ->  f (k,(),Fail) ans)
  nxt Fail = Collect(\ ans f -> ans)
  lub key (Single k v) = Collect(\ ans f -> if k<=key then f (k,v,Fail) ans else ans)
  lub key (SetSingle k) = Collect(\ ans f -> if k<=key then f(k,(),Fail) ans else ans)
  lub key Fail = Collect(\ ans f -> ans)
  repOf x = SingleR
  haskey k (SetSingle a) = k==a
  haskey k (Single a b) = k==a
  haskey k Fail = False
  isnull Fail = True
  isnull _ = False
  lookup k (SetSingle a) = if k==a then Just() else Nothing
  lookup k (Single a b) = if k==a then Just b else Nothing
  lookup k Fail = Nothing

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

-- ============= Basic Sett ===============

-- Sett defined in SetAlgebra.hs
-- data Sett k v where Sett :: (Set.Set k) -> Sett k ()

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
  repOf (Sett x) = SetR
  haskey key (Sett m) = Set.member key m
  isnull (Sett x) = Set.null x
  lookup k (Sett m) = if Set.member k m then Just() else Nothing

  addpair key unit (Sett m) = Sett(Set.insert key m)
  addkv (k,unit) (Sett m) comb = Sett(Set.insert k m)  -- We can ignore comb since there is only one function at type: () -> () -> ()
  removekey k (Sett m) = Sett(Set.delete k m)
  emptyc = error ("Sett Set.empty has type (Sett k ()) and it needs type (Sett k v)")

-- ================== Basic Map ===============

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
  repOf x = MapR
  haskey x m = case Map.lookup x m of Just _ -> True; Nothing -> False
  isnull = Map.null
  lookup = Map.lookup

  addpair = Map.insertWith (\x _y -> x)
  addkv (k,v) m comb = Map.insertWith comb  k v m
  removekey k m = Map.delete k m
  emptyc = Map.empty

-- ============== Basic BiMap ====================

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
  repOf (MkBiMap _ _) = BiMapR
  isnull (MkBiMap f g) = isnull f
  lookup x (MkBiMap left right) = Map.lookup x left
  haskey k (MkBiMap left right) = haskey k left

  addpair k v (b@(MkBiMap _ _)) = biMapAddpair k v b  -- We need to use the pattern match on MkBiMap to bring the type
  addkv (k,v) (MkBiMap f b) comb =
     case Map.lookup k f of
       Nothing -> MkBiMap (Map.insert k v f) (Map.insert v k b)
       Just v2 -> MkBiMap (Map.insert k v3 f) (Map.insert v3 k (Map.delete v2 b))
          where v3 = comb v v2

  removekey k (b@(MkBiMap _ _)) = biMapRemovekey k b  -- equality constraint (a ~ v) from (BiMap a k v) into scope.
  emptyc = error ("biMapEmpty has type BiMap v k v, and it needs (BiMap a k v)")


-- =============================================================================================
-- Now we look at instances for Compound type that combine simple iterators. Such a compound
-- instances will call the Iter methods of its constituent types to build its compound methods.
-- =============================================================================================

-- ================= Compound And ================

andLoop ::
  (Ord key, Iter f1, Iter f2) =>
  (key, b1, f1 key b1) ->
  (key, b2, f2 key b2) ->
  Collect (key, (b1, b2), And key (b1,b2))

andLoop (ftrip@(k1,v1,f1)) (gtrip@(k2,v2,g2)) =
   case compare k1 k2 of
      EQ -> one (k1,(v1,v2), And f1 g2)
      LT -> do { ftrip' <- lub k2 f1; andLoop ftrip' gtrip  }
      GT -> do { gtrip' <- lub k1 g2; andLoop ftrip gtrip' }

instance Iter And where
   nxt (And f g) = do { triple1 <- nxt f; triple2 <- nxt g; andLoop triple1 triple2 }
   lub  key (And f g) = do { triple1 <- lub key f; triple2 <- lub key g; andLoop triple1 triple2 }
   repOf (And f g) = AndR (repOf f) (repOf g)
   haskey k (And f g) = haskey k f && haskey k g
   isnull (And f g) = isnull f  ||  isnull g

   addpair k v (And f g) = And (addpair k (fst v) f) (addpair k (snd v) g)
   addkv (k,v) (And f g) comb = error("Can't addkv to And")
   removekey k (And f g) = And (removekey k f) g

-- ================ Compound AndP with Projection ===========================

andLoop2 ::
  (Ord key,Iter f1, Iter f2) =>
  (key, b1, f1 key b1) ->
  (key, b2, f2 key b2) ->
  Fun(b1 -> b2 -> b3) ->
  Collect (key, b3, AndP key b3)

andLoop2 (ftrip@(k1,v1,f1)) (gtrip@(k2,v2,g2)) p =
   case compare k1 k2 of
      EQ -> one (k1,(apply p v1 v2), AndP f1 g2 p)
      LT -> do { ftrip' <- lub k2 f1; andLoop2 ftrip' gtrip p }
      GT -> do { gtrip' <- lub k1 g2; andLoop2 ftrip gtrip' p }

instance Iter AndP where
   nxt (AndP f g p) = do { triple1 <- nxt f; triple2 <- nxt g; andLoop2 triple1 triple2 p }
   lub  key (AndP f g p) = do { triple1 <- lub key f; triple2 <- lub key g; andLoop2 triple1 triple2 p}

   haskey k (AndP f g p) = haskey k f && haskey k g
   isnull (AndP f g p) = isnull f || isnull g

   repOf (AndP f g p) = AndPR (repOf f) (repOf g) p

   lookup k (x@(AndP f g p)) = do { v1 <- lookup k f; v2 <- lookup k g; Just(apply p v1 v2)} -- In the Maybe Monad
   addpair k v (x@(AndP f g p)) = error("Can't addpair to the view (AndP f g p).")
   addkv (k,v) (x@(AndP f g p)) comb = error("Can't addkc to the view (AndP f g p).")
   removekey k (AndP f g p) = AndP (removekey k f) g p


-- ================= Compound Or =====================

-- A type synonym for the type of 'nxt' and a partially applied 'lub key'.
-- We will use this pattern, of passing the next `advancer` as a parameter, quite often.

type NxtOrLub k = (forall h b . Iter h => h k b -> Collect(k,b,h k b))

orAction ::
   (Iter f, Iter g, Ord k) =>
   NxtOrLub k ->
   f k v -> g k v -> Fun (v -> v -> v) ->
   Collect (k, v, Or k v)

orAction next f g comb =
   case (hasNxt f, hasNxt g) of   -- We have to be careful, because if only one has a nxt, there is still an answer
      (Nothing,Nothing) -> none
      (Just(k1,v1,f1),Nothing) -> one (k1,v1,Or f1 g comb)
      (Nothing,Just(k1,v1,g1)) -> one (k1,v1,Or f g1 comb)
      (Just(k1,v1,f1),Just(k2,v2,g2)) ->
        case compare k1 k2 of
           EQ -> one (k1,apply comb v1 v2,Or f1 g2 comb)
           LT -> one (k1,v1,Or f1 g comb)
           GT -> one (k2,v2,Or f g2 comb)

instance Iter Or where
   nxt (Or f g comb) = orAction nxt f g comb
   lub key (Or f g comb) = orAction (lub key) f g comb
   repOf (Or f g comb) = OrR (repOf f) (repOf g) comb
   isnull (Or f g comb) = isnull f && isnull g

   addpair k x (Or f g comb) = Or (addpair k x f) g comb
   addkv (k,x) (Or f g comb) comb2 = Or (addkv (k,x) f comb2) g comb
   removekey k (Or f g comb) = Or (removekey k f) (removekey k g) comb


-- =============== Compound Guard =================

guardAction ::
   (Iter f, Ord k) =>
   NxtOrLub k ->
   Fun (k -> v -> Bool) ->
   f k v ->
   Collect (k, v, Guard k v)

guardAction next p f = do { triple <- next f; loop triple }
   where loop (k,v,f') = if (apply p k v) then one (k,v,Guard f' p) else do { triple <- nxt f'; loop triple}

instance Iter Guard where
   nxt (Guard f p) = guardAction nxt p f
   lub key (Guard f p) = guardAction (lub key) p f
   repOf (Guard f p) = GuardR (repOf f) p

   addpair k v (old@(Guard f p)) = if (apply p k v) then Guard (addpair k v f) p else old
   addkv (k,v) (old@(Guard f p)) comb = if (apply p k v) then Guard (addkv (k,v) f comb) p else old
   removekey key (Guard f p) = Guard (removekey key f) p



-- ================= Compound Project ===================

projAction ::
   (Iter f, Ord k) =>
   (forall h b . Iter h => h k b -> Collect(k,b,h k b)) ->
   Fun (k -> v -> u) ->
   f k v ->
   Collect (k, u, Project k u)

projAction next p f = do { (k,v,f') <- next f; one (k,apply p k v,Project f' p) }

instance Iter Project where
   nxt (Project f p) = projAction nxt p f
   lub key (Project f p) = projAction (lub key) p f
   repOf (Project f p) = ProjectR (repOf f) p
   haskey key (Project f p) = haskey key f
   isnull (Project f p) = isnull f

   addpair k v (Project f p) = error ("can't addpair a (key,value) pair to a projection view.")
   addkv (k,v) (Project f p) comb = error ("can't addkc a (key,value) pair to a projection view.")
   removekey key (Project f p) = Project (removekey key f) p

-- ================ Compound Diff ======================

diffAction::
   (Iter f, Iter g, Ord k) =>
   (k,u,f k u) ->
   g k v ->
   Collect (k,u,Diff k u)

diffAction (t1@(k1,u1,f1)) g =
   case hasLub k1 g of
      Nothing -> one (k1,u1,Diff f1 g)  -- g has nothing to subtract
      Just (t2@(k2,u2,g2)) -> case compare k1 k2 of
          EQ -> do { tup <- nxt f1; diffAction tup g2 }
          LT -> one (k1,u1,Diff f1 g)
          GT -> one (k1,u1,Diff f1 g)   -- the hasLub guarantees k1 <= k2, so this case is dead code

instance Iter Diff where
   nxt (Diff f g) = do { trip <- nxt f; diffAction trip g }
   lub key (Diff f g) = do { trip <- lub key f; diffAction trip g}
   repOf (Diff f g) = DiffR (repOf f) (repOf g)
   haskey key (Diff f g) = haskey key f && (not (haskey key g))

   addpair k v (Diff f g) = Diff (addpair k v f) (removekey k g)
   addkv (k,v) (Diff f g) comb = Diff (addkv (k,v) f comb) (removekey k g)
   removekey key (Diff f g) = Diff (removekey key f) g




-- ==================================================================
-- Now we make an iterator that collects triples, on the intersection
-- of the domain of the two Iter types 'f' and 'g'. An answer of (k,b,c) means that
-- (k,b) is in m::f k a, and (k,c) is in n::g k c. All the other possible triples
-- are skipped over.  This is an instance of a thing called a "Generic Join"
-- See https://arxiv.org/pdf/1310.3314.pdf  or  http://personales.dcc.uchile.cl/~pbarcelo/ngo.pdf
-- The number of tuples it touches is proportional to the size of the output (modulo log factors).
-- It's cost is unrelated to the size of its inputs (modulo log factors)

(⨝) ::  (Ord k,Iter f,Iter g) =>  f k b -> g k c -> Collect (k,b,c)
(⨝) = domEq

domEq:: (Ord k,Iter f,Iter g) =>  f k b -> g k c -> Collect (k,b,c)
domEq m n = do
    triplem <- nxt m
    triplen <- nxt n
    let loop (mt@(k1,b,nextm)) (nt@(k2,c,nextn)) =
          case compare k1 k2 of
            EQ -> front (k1,b,c) (domEq nextm nextn)
            LT -> do { mt' <- lub k2 nextm; loop mt' nt }
            GT -> do { nt' <- lub k1 nextn; loop mt nt' }
    loop triplem triplen

-- This version is really slow as it visits every tuple in both Types.

domEqSlow:: (Ord k,Iter f, Iter g) =>  f k b -> g k c -> Collect (k,b,c)
domEqSlow m n = do
    triplem <- nxt m
    triplen <- nxt n
    let loop (mt@(k1,b,nextm)) (nt@(k2,c,nextn)) =
          case compare k1 k2 of
            EQ -> front (k1,b,c) (domEqSlow nextm nextn)
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

foo skcreds delegs stpools = materialize MapR $
  do (x,z,y) <- skcreds ⨝ delegs
     y `element` stpools
     one (x,y)

-- Even better,  stkcreds, delegs, and stpools can be any binary type construtors in the Iter class.

foo :: (Iter s, Iter d, Iter p, Ord a, Ord b1) =>
       s a b2 ->
       d a b1 ->
       p b1 b3 ->
       Map a b1


example :: Exp (Map Int Char)
example = ((dom stkcred) ◁ deleg) ▷ (dom stpool)

stkcred :: Map Int [Char]
deleg :: Map Int Char
stpool :: Map Char Int

stkcred = Map.fromList[(5,"a"),(6,"q"),(12,"r")]
deleg = Map.fromList [ (n,chars !! n) | n <- [1..10]]
stpool = Map.fromList [('A',99),('C',12),('F',42),('R',33),('Z',99)]

instance Show (Code k v) where
  show (Data x) = shape x

-- =====================================================================================
-- Some times we need to write our own version of functions over Map.Map that
-- do not appear in the library

-- A version of withoutKeys where both parts are Map.Map

noKeys :: Ord k => Map k a -> Map k b -> Map k a
noKeys Tip _ = Tip
noKeys m Tip = m
noKeys m (Bin _ k _ ls rs) = case Map.split k m of
  (lm, rm) -> link2 lm' rm'     -- We know `k` is not in either `lm` or `rm`
     where !lm' = noKeys lm ls
           !rm' = noKeys rm rs
{-# INLINABLE noKeys #-}

-- ===============================================================================================
-- Exp is a typed Symbol representation of queries we may ask. It allows us to introspect a query
-- The strategy is to
-- 1) Define Exp so all queries can be represented.
-- 2) Define smart constructors that "parse" the surface syntax, and build a typed Exp
-- 3) Write an evaluate function. eval:: Exp t -> t
-- 4) "eval" can introspect the code and apply efficient domain and type specific translations
-- 5) Use the (Iter f) class to evaluate some Exp that can benefit from its efficient nature.


-- ============================================================================================
-- | In order to build typed Exp, we need to know what Basic types of Maps and Sets are supported.


-- | Given a BaseRep we can materialize a (Collect k v) which has no intrinsic type.

materialize :: (Ord k,Ord v) => BaseRep f k v -> Collect (k,v) -> f k v
materialize MapR x = runCollect x Map.empty (\ (k,v) ans -> Map.insert k v ans)
materialize SetR x = Sett (runCollect x Set.empty (\ (k,_) ans -> Set.insert k ans))
materialize BiMapR x = runCollect x  biMapEmpty (\ (k,v) ans -> addpair k v ans)
materialize SingleR x = runCollect x Fail (\ (k,v) _ignore -> Single k v)
materialize other x = error ("Can't materialize compound (Iter f) type: "++show other++". Choose some other BaseRep.")


-- ===============================================================================================
-- The eval function. Here are some sample of optimizations we incorporate
--  x  ∈ (dom y)            haskey
--  x  ∉ (dom y)            not . haskey
-- x ∪ (singleton y)        addpair
-- (Set.singleton x) ⋪ y    removekey
-- x ⋫ (Set.singleton y)    easy on Bimap  remove val
-- (dom x) ⊆ (dom y)
-- ===============================================================================================

data Code k v where
  Data:: (Ord k,Iter f) => f k v -> Code k v
--   Act:: (Ord k) => Collect (k,v) -> Code k v

compile:: Exp (f k v) -> Code k v
compile (Base rep relation) = Data relation

compile (Dom (Base SetR rel)) = Data rel
compile (Dom (Singleton k v)) = Data (Sett (Set.singleton k))
compile (Dom (SetSingleton k)) = Data (Sett (Set.singleton k))
compile (Dom x) = case compile x of
  Data xcode -> Data (Project xcode (fun (Const ())))

compile (Rng (Base SetR rel)) = Data (Sett (Set.singleton ()))
compile (Rng (Singleton k v)) = Data (Sett (Set.singleton v))
compile (Rng (SetSingleton k)) = Data (Sett (Set.singleton ()))
compile (Rng x) =
   case compile x of  -- This is going to be expensive, last gasp fallback build an index
      Data xcode -> Data(materialize MapR (do { (_,y) <- lifo xcode; one(y,()) }))

compile (DRestrict set rel) = case (compile set, compile rel) of
   (Data setd, Data reld) -> Data (Project (And setd reld) (fun RngSnd))

compile (DExclude set rel) = case (compile set,compile rel) of
   (Data setd, Data reld) -> Data (Diff reld setd)

compile (RRestrict rel set) = case (compile rel,compile set) of
   (Data reld, Data setd) -> Data (Guard reld (fun (RngElem setd)))

compile (RExclude rel set) = case (compile rel,compile set) of
   (Data reld, Data setd) -> Data (Guard reld (fun (Negate(RngElem setd))))

compile (UnionLeft rel1 rel2) =  case (compile rel1,compile rel2) of
   (Data d1, Data d2) -> Data (Or d1 d2 (fun YY))

compile (UnionRight rel1 rel2) =  case (compile rel1,compile rel2) of
   (Data d1, Data d2) -> Data (Or d1 d2 (fun XX))

compile (UnionPlus rel1 rel2) =  case (compile rel1,compile rel2) of
   (Data d1, Data d2) -> Data (Or d1 d2 (fun Plus))

compile other = error "No compile yet"


eval:: Exp t -> t
eval (Base rep relation) = relation

eval (Dom (Base SetR rel)) = rel
eval (Dom (Singleton k v)) = Sett (Set.singleton k)
eval (Dom (SetSingleton k)) = Sett (Set.singleton k)

eval (Rng (Base SetR rel)) = Sett (Set.singleton ())
eval (Rng (Singleton k v)) = Sett (Set.singleton v)
eval (Rng (SetSingleton k)) = Sett (Set.singleton ())


eval (DRestrict (Base SetR x1) (Base rep x2)) = materialize rep $ do { (x,y,z) <- x1 `domEq` x2; one (x,z) }
eval (DRestrict (Dom (Base _ x1)) (Base rep x2)) = materialize rep $ do { (x,y,z) <- x1 `domEq` x2; one (x,z) }
eval (DRestrict (SetSingleton k) (Base rep x2)) = materialize rep $  do { (x,y,z) <- (SetSingle k) `domEq` x2; one (x,z) }
eval (DRestrict (Dom (Singleton k _)) (Base rep x2)) = materialize rep $  do { (x,y,z) <- (SetSingle k) `domEq` x2; one (x,z) }
eval (DRestrict (Rng (Singleton _ v)) (Base rep x2)) = materialize rep $  do { (x,y,z) <- (SetSingle v) `domEq` x2; one (x,z) }

eval (DExclude (SetSingleton n) (Base MapR m)) = Map.withoutKeys m (Set.singleton n)
eval (DExclude (Dom (Singleton n v)) (Base MapR m)) = Map.withoutKeys m (Set.singleton n)
eval (DExclude (Rng (Singleton n v)) (Base MapR m)) = Map.withoutKeys m (Set.singleton v)
eval (DExclude (Base SetR (Sett x1)) (Base MapR x2)) =  Map.withoutKeys x2 x1
eval (DExclude (Dom (Base MapR x1)) (Base MapR x2)) = noKeys x2 x1
eval (DExclude (SetSingleton k) (Base BiMapR x)) = removekey k x
eval (DExclude (Dom (Singleton k _)) (Base BiMapR x)) = removekey k x
eval (DExclude (Rng (Singleton _ v)) (Base BiMapR x)) = removekey v x

eval (RExclude (Base BiMapR x) (SetSingleton k)) = removeval k x
eval (RExclude (Base BiMapR x) (Dom (Singleton k v))) = removeval k x
eval (RExclude (Base BiMapR x) (Rng (Singleton k v))) = removeval v x
eval (RExclude (Base rep lhs) y) =
   materialize rep $ do { (a,b) <- lifo lhs; (c,_) <- lifo rhs; when (not(b==c)); one (a,b)} where rhs = eval y

eval (RRestrict (DRestrict (Dom (Base r1 stkcreds)) (Base r2 delegs)) (Dom (Base r3 stpools))) =
   materialize r2 $ do { (x,z,y) <- stkcreds `domEq` delegs; y `element` stpools; one (x,y)}
eval (RRestrict (Base rep lhs) y) =
   materialize rep $ do { (a,b) <- lifo lhs; (c,_) <- lifo rhs; when ((b==c)); one (a,b)} where rhs = eval y

eval (Elem k (Dom (Base rep x))) = haskey k x
eval (Elem k (Base rep rel)) = haskey k rel
eval (Elem k (Dom (Singleton key v))) = k==key
eval (Elem k (Rng (Singleton _ key))) = k==key
eval (Elem k (SetSingleton key)) = k==key

eval (NotElem k (Dom (Base rep x))) = not $ haskey k x
eval (NotElem k (Base rep rel)) = not $ haskey k rel
eval (NotElem k (Dom (Singleton key v))) = not $ k==key
eval (NotElem k (Rng (Singleton _ key))) = not $ k==key
eval (NotElem k (SetSingleton key)) = not $ k==key

eval (UnionLeft (Base rep x) (Singleton k v)) = addpair k v x
eval (UnionRight (Base rep x) (Singleton k v)) = addpair k v x   --TODO MIght not have the right parity
eval (UnionPlus (Base MapR x) (Base MapR y)) = Map.unionWith (+) x y

eval (Singleton k v) = Single k v
eval (SetSingleton k) = Sett (Set.singleton k)

eval other = error ("Can't eval: "++show other ++" yet.")


-- =========================================================
-- Some examples of Exp and tests
-- let's build a few things to test with


-- ======== Build any (Iter f) from a list. =======

addp :: Ord k => Iter f => (k,v) -> f k v -> f k v
addp (k,v) xs = addpair k v xs

fromList:: (Ord v,Ord k) => BaseRep f k v -> [(k,v)] -> f k v
fromList MapR xs = foldr addp Map.empty xs
fromList ListR xs = List xs
fromList SetR xs = foldr addp (Sett (Set.empty)) xs
fromList BiMapR xs = biMapFromList xs
fromList SingleR xs = foldr addp Fail xs
fromList other xs = error ("No fromList for compound iterators")

-- =============== Build a few maps ===================

chars::String
chars = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdeghijklmnopqrstuvwxyz0123456789"

nchars :: Int
nchars = length chars

m0 :: Map.Map Int Char
m0 = Map.fromList [(1,'a'),(2,'z'),(4,'g')]

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

b0::Bimap Int Char
b0 = biMapFromList [(1,'a'),(2,'z'),(4,'g')]

-- ============ Some small Maps to And, Or, Diff, Guard, Project with =========

l1,l2 :: [(Int,String)]
l1 = [(1,"a"),(4,"d"),(5,"e"),(10,"j"),(12,"l"),(21,"v"),(26,"z")]
l2 = [(3,"c"),(4,"d"),(5,"e"),(6,"f"),(10,"j"),(11,"k"),(21,"v")]

l3 :: [(Int,Int)]
l3 = [(4,12),(9,13),(12,44),(55,22)]
evens :: Sett Int ()
evens = fromList SetR [(n,()) | n <- [2,4,6,8,10,12,14,16,18,20,22,24,26]]

-- =================== Some sample (Exp t) =============================

ex1 :: Exp Bool
ex1 = 5 ∈ (dom m1)

ex2 :: Exp Bool
ex2 = 70 ∈ (dom m1)

ex3 :: Exp (Map Int Char)
ex3 = m0 ∪ (singleton 3 'b')

ex4,ex5,ex6 :: Exp(Map Int Char)
ex4 = (setSingleton 2) ⋪ m0
ex5 = dom(singleton 2 'z') ⋪ m0
ex6 = range(singleton 'z' 2) ⋪ m0

ex7::Exp Bool
ex7 = 70 ∉ (dom m1)

-- ===================== test that eval works ======================

evalTest :: (Show t,Eq t) => String -> Exp t -> t -> Test
evalTest nm expr ans = TestCase (assertEqual (show expr++" where Map? = "++nm) (eval expr) ans)

eval_tests :: Test
eval_tests = TestList
          [ evalTest "m1"  (5 ∈ (dom m1))                True
          , evalTest "m1"  (70 ∈ (dom m1))               False
          , evalTest "m0"  (m0 ∪ (singleton 3 'b'))      (Map.fromList [(1,'a'),(2,'z'),(3,'b'),(4,'g')])
          , evalTest "m0"  ((setSingleton 2) ⋪ m0)       (Map.fromList [(1,'a'),(4,'g')])
          , evalTest "m0"  (dom(singleton 2 'z') ⋪ m0)   (Map.fromList [(1,'a'),(4,'g')])
          , evalTest "m0"  (range(singleton 'z' 2) ⋪ m0) (Map.fromList [(1,'a'),(4,'g')])
          , evalTest "m0"  (70 ∉ (dom m1))                True
          ]


-- ========================== test that various Compound iterators work ================

testcase :: (Eq k, Eq v, Show k, Show v, Iter f) => String -> f k v -> [(k, v)] -> Test
testcase nm col ans = TestCase (assertEqual nm (runCollect (fifo col) [] (:)) ans)


-- Tests where we vary how we represent l1 and l2 (the f in (Iter f) )
-- and see that we always get the same answer no matter how we store the data of l1 and l2

testAnd1,testAnd2,testOr,testDiff1,testDiff2 :: Iter g => String -> BaseRep g Int String -> Test

testAnd1 nm rep = testcase nm (And (fromList rep l1) (fromList rep l2))
                              [(4,("d","d")),(5,("e","e")),(10,("j","j")),(21,("v","v"))]

testAnd2 nm rep = TestCase (assertEqual nm (runCollect (lifo (And (fromList rep l1) (fromList rep l2))) [] (:))
                                           (reverse  [(4,("d","d")),(5,("e","e")),(10,("j","j")),(21,("v","v"))]))

testOr nm rep = testcase nm (Or (fromList rep l1) (fromList rep l2) (fun Cat))
                            [(1,"a"),(3,"c"),(4,"d-d"),(5,"e-e"),(6,"f"),(10,"j-j"),(11,"k"),(12,"l"),(21,"v-v"),(26,"z")]

testDiff1 nm rep = testcase nm (Diff (fromList rep l1) (fromList rep l2))
                               [(1,"a"),(12,"l"),(26,"z")]

testDiff2 nm rep = testcase nm (Diff (fromList rep l2) (fromList rep l1)) [(3,"c"),(6,"f"),(11,"k")]

-- ==========================================================================
-- tests where we vary both the data, and how it is represented.

testGuard :: (Show b, Iter f, Ord b) => String -> BaseRep f Int b -> [(Int, b)] -> Test
testGuard nm rep f = testcase nm (Guard (fromList rep f) (fun (DomElem evens)))
                                 (filter (even . fst) f)

testProj :: (Show k, Ord k, Iter f) => String -> BaseRep f k [Char] -> [(k, [Char])] -> Test
testProj nm rep f = testcase nm (Project (fromList rep f) (fun (Lift "ord" (\ x y -> ord (y!!0)))))
                                [ (k,ord(v!!0)) | (k,v) <- f ]

-- =============================================================================
-- tests where we AndP l1 and l3, and use different type of data for l1 from l3
-- We use the second projection in AndP, that is the value will come from l3

testAndP :: (Iter f, Iter g) => String -> BaseRep f Int String -> BaseRep g Int Int -> Test
testAndP nm rep1 rep2 =  testcase nm (AndP (fromList rep1 l1) (fromList rep2 l3) (fun YY))
                                     [(4,12),(12,44)]

iter_tests :: Test
iter_tests = TestList
  [ testAnd1 "(And l1 l2) as List, fifo"  ListR
  , testAnd1 "(And l1 l2) as Map, fifo"   MapR
  , testAnd1 "(And l1 l2) as BiMap, fifo" BiMapR
  , testAnd2 "(And l1 l2) as List, lifo"  ListR
  , testAnd2 "(And l1 l2) as Map, lifo"   MapR
  , testAnd2 "(And l1 l2) as BiMap, lifo" BiMapR

  , testOr "(Or l1 l2) as List" ListR
  , testOr "(Or l1 l2) as Map" MapR
  , testOr "(Or l1 l2) as BiMap" BiMapR

  , testDiff1 "(Diff l1 l2) as List" ListR    -- (Diff is not symmetric)
  , testDiff2 "(Diff l2 l1) as List" ListR
  , testDiff1 "(Diff l1 l2) as Map" MapR
  , testDiff2 "(Diff l2 l1) as Map" MapR
  , testDiff1 "(Diff l1 l2) as BiMap" BiMapR
  , testDiff2 "(Diff l2 l1) as BiMap" BiMapR

  , testGuard "(Guard l1 even) as List" ListR l1
  , testGuard "(Guard l1 even) as Map" MapR l1
  , testGuard "(Guard l1 even) as BiMap" BiMapR l1
  , testGuard "(Guard l2 even) as List" ListR l2
  , testGuard "(Guard l2 even) as Map" MapR l2
  , testGuard "(Guard l2 even) as BiMap" BiMapR l2

  , testProj "(Proj l1 ord) as List" ListR l1
  , testProj "(Proj l1 ord) as Map" MapR l1
  , testProj "(Proj l1 ord) as BiMap" BiMapR l1
  , testProj "(Proj l2 ord) as List" ListR l2
  , testProj "(Proj l2 ord) as Map" MapR l2
  , testProj "(Proj l2 ord) as BiMap" BiMapR l2

  ,testAndP "(AndP l1:List l3:Map ord)" ListR MapR
  ,testAndP "(AndP l1:Map l3:List ord)" MapR ListR
  ,testAndP "(AndP l1:Map l3:List Map)" MapR MapR
  ,testAndP "(AndP l1:BiMap l3:List Map)" BiMapR MapR
  ]

alltests :: Test
alltests = TestList [ eval_tests, iter_tests ]
