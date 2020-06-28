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
import Debug.Trace
-- import Data.Array
import Data.List(sort,nub)

import Data.Map.Strict(Map)
import qualified Data.Map.Strict as Map
import Data.Map.Internal(Map(..),link,link2)
import Data.Map.Internal.Debug(showTree)

import Data.Maybe(fromJust,catMaybes)

import Shelley.Spec.Ledger.Core(Bimap(..),bimapFromList, bimapEmpty)
import qualified Shelley.Spec.Ledger.Core as Core
import qualified Control.Monad as CM
import qualified Control.Applicative as AP

import qualified Data.Set as Set
import Data.Set(Set)

import Collect
import SetAlgebra(Iter(..),
                  And(..),Or(..),Project(..),Guard(..),Diff(..),Single(..),Sett(..),AndP(..),
                  Exp(..),BaseRep(..),
                  dom, range, singleton, setSingleton, (◁), (⋪), (▷), (⋫), (∪), (⨃), (∈), (∉),(|>),(<|),
                  element,shape,
                  SymFun(..), Fun, fun, SymFun, apply
                 )
-- ================================ EXPERIMENT ====================================
-- And with projection


andLoop2 ::
  (Ord key,Iter f1, Iter f2) =>
  (key, b1, f1 key b1) ->
  (key, b2, f2 key b2) ->
  (b1 -> b2 -> b3) ->
  Collect (key, b3, AndP f1 f2 key b3)

andLoop2 (ftrip@(k1,v1,f1)) (gtrip@(k2,v2,g2)) p =
   case compare k1 k2 of
      EQ -> one (k1,(p v1 v2), AndP f1 g2 p)
      LT -> do { ftrip' <- lub k2 f1; andLoop2 ftrip' gtrip p }
      GT -> do { gtrip' <- lub k1 g2; andLoop2 ftrip gtrip' p }

instance Iter (AndP f g) where
   nxt (AndP f g p) = do { triple1 <- nxt f; triple2 <- nxt g; andLoop2 triple1 triple2 p }
   lub  key (AndP f g p) = do { triple1 <- lub key f; triple2 <- lub key g; andLoop2 triple1 triple2 p}

   haskey k (AndP f g p) = haskey k f && haskey k g
   isnull (AndP f g p) = isnull f || isnull g

   repOf (AndP f g p) = AndPR (repOf f) (repOf g) p

   lookup k (x@(AndP f g p)) = do { v1 <- lookup k f; v2 <- lookup k g; Just(p v1 v2)} -- In the Maybe Monad
   addpair k v (x@(AndP f g p)) = error("Can't addpair to the view (AndP f g p).")
   removekey k (AndP f g p) = AndP (removekey k f) g p


-- ==========================================================================
--  let's build a few things to test with

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
b0 = bimapFromList [(1,'a'),(2,'z'),(4,'g')]


-- =================================================================
-- The most basic operation of a Collect computation, is to create a
-- collection from the 'nxt' operator. The two collections possible
-- produce their elements in LIFO or FIFO order.

lifo :: Iter f => f k v -> Collect (k,v)
lifo x = do { (k,v,x2) <- nxt x; front (k,v) (lifo x2) }

fifo :: Iter f => f k v -> Collect (k,v)
fifo x = do { (k,v,x2) <- nxt x; rear (fifo x2) (k,v)}

-- =====================================================================================
-- Instances for the Basic types
-- =====================================================================================


-- =================== Basic Single =================

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
  repOf x = SingleR

  lookup k (SetSingle a) = if k==a then Just() else Nothing
  lookup k (Single a b) = if k==a then Just b else Nothing
  lookup k Fail = Nothing
  addpair k v (Single a b) = if k==a then Single a v else Fail
  addpair k v (SetSingle a) = if k==a then Single a v else Fail
  addpair k v Fail = Single k v
  removekey key (Single a b) = if key==a then Fail else (Single a b)
  removekey key (SetSingle a) = if key==a then Fail else (SetSingle a)
  removekey key Fail = Fail

-- ============= Basic Sett ===============

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
  repOf (Sett x) = SetR

  addpair key unit (Sett m) = Sett(Set.insert key m)
  lookup k (Sett m) = if Set.member k m then Just() else Nothing
  removekey k (Sett m) = Sett(Set.delete k m)

-- ================== Basic Map ===============

instance Iter Map.Map where
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
  haskey x m = case Map.lookup x m of Just _ -> True; Nothing -> False
  isnull = Map.null
  repOf x = MapR

  lookup = Map.lookup
  addpair = Map.insertWith (\x _y -> x)
  removekey k m = Map.delete k m

-- ============== Basic Bimap ====================
leftpart:: Bimap k v -> Map.Map k v
leftpart(MkBimap left right) = left

rightpart:: Bimap k v -> Map.Map v k
rightpart(MkBimap left right) = right

instance Iter Bimap where
  nxt m = Collect (\ ans f ->
     case Map.minViewWithKey (leftpart m) of
        Nothing -> ans
        Just((k,v),nextm) -> f (k,v,MkBimap nextm (rightpart m)) ans)
  lub key m = Collect (\ ans f ->
     case Map.splitLookup key (leftpart m) of           -- NOTE in Log time, we skip over all those tuples in _left
       (_left,Just v,right) -> f (key,v,MkBimap right (rightpart m)) ans
       (_left,Nothing,Tip) -> ans
       (_left,Nothing,right) -> f (k,v,MkBimap m3 (rightpart m)) ans
           where ((k,v),m3) = Map.deleteFindMin right )
  haskey x (MkBimap left right) = case Map.lookup x left of { Just _ -> True; Nothing -> False }
  isnull (MkBimap f g) = isnull f
  repOf x = BimapR


  lookup x (MkBimap left right) = Map.lookup x left
  addpair = undefined -- Core.addpair
  removekey key m = error("removekey for Bimap requires (Ord val) as well as (Ord key)")

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
   haskey k (And f g) = haskey k f && haskey k g
   isnull (And f g) = isnull f  ||  isnull g
   repOf (And f g) = AndR (repOf f) (repOf g)

   lookup k (x@(And f g)) = if haskey k x then Just(fromJust(lookup k f), fromJust(lookup k g)) else Nothing
   addpair k v (And f g) = And (addpair k (fst v) f) (addpair k (snd v) g)
   removekey k (And f g) = And (removekey k f) g

-- ================= Compound Or =====================

-- A type synonym for the type of 'nxt' and a partially applied 'lub key'.
-- We will use this pattern, of passing the next `advancer` as a parameter, quite often.

type NxtOrLub k = (forall h b . Iter h => h k b -> Collect(k,b,h k b))

orAction ::
   (Iter f, Iter g, Ord k) =>
   NxtOrLub k ->
   f k v -> g k v -> Fun (v -> v -> v) ->
   Collect (k, v, Or k v)

orAction next f g comb | isnull g = do { (k1,v1,h1) <- next f; one (k1,v1,Or h1 g comb)}
orAction next f g comb | isnull f = do { (k1,v1,h1) <- next g; one (k1,v1,Or f h1 comb)}
orAction next f g comb =
   do (ftrip@(k1,v1,f1)) <- next f
      (gtrip@(k2,v2,g2)) <- next g
      case compare k1 k2 of
         EQ -> one (k1,apply comb v1 v2,Or f1 g2 comb)
         LT -> one (k1,v1,Or f1 g comb)
         GT -> one (k2,v2,Or f g2 comb)

instance Iter Or where
   nxt (Or f g comb) = orAction nxt f g comb
   lub key (Or f g comb) = orAction (lub key) f g comb
   haskey k (Or f g comb) = haskey k f ||  haskey k g
   isnull (Or f g comb) = isnull f &&  isnull g
   repOf (Or f g comb) = OrR (repOf f) (repOf g) comb

   lookup k (Or f g comb) =
       case (lookup k f,lookup k g) of
          (Just x,Just y) -> Just(apply comb x y)
          (Just x,Nothing) -> Just x
          (Nothing,Just y) -> Just y
          (Nothing,Nothing) -> Nothing
   addpair k x (Or f g comb) = Or (addpair k x f) g comb
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
   -- haskey relies on lookup
   isnull (Guard f p) = error ("Can't tell if a guard is null")
   repOf (Guard f p) = GuardR (repOf f) p

   lookup key (Guard f p) = case lookup key f of { Just v -> if apply p key v then Just v else Nothing; Nothing -> Nothing}
   addpair k v (old@(Guard f p)) = if (apply p k v) then Guard (addpair k v f) p else old
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
   haskey key (Project f p) = haskey key f
   isnull (Project f p) = isnull f
   repOf (Project f p) = ProjectR (repOf f) p

   lookup key (Project f p) = case lookup key f of { Just v -> Just(apply p key v); Nothing -> Nothing }
   addpair k v (Project f p) = error ("can't add a (key,value) pair to a projection view.")
   removekey key (Project f p) = Project (removekey key f) p

-- ================ Compound Diff ======================

diffAction::
   (Iter f, Iter g, Ord k) =>
   (k,u,f k u) ->
   g k v ->
   Collect (k,u,Diff k u)

diffAction (k1,u1,f1) g | isnull g = one (k1,u1,Diff f1 g)
diffAction (t1@(k1,u1,f1)) g = do
   (t2@(k2,u2,g2)) <- lub k1 g
   case compare k1 k2 of
      EQ -> do { tup <- nxt f1; diffAction tup g2 }
      LT -> one (k1,u1,Diff f1 g)
      GT -> one (k1,u1,Diff f1 g)

instance Iter Diff where
   nxt (Diff f g) = do { trip <- nxt f; diffAction trip g }
   lub key (Diff f g) = do { trip <- lub key f; diffAction trip g}
   haskey key (Diff f g) = haskey key f && (not (haskey key g))
   isnull (Diff f g) = error("Can't tell if a Diff is null.")
   repOf (Diff f g) = DiffR (repOf f) (repOf g)

   lookup key (x@(Diff f _)) = if haskey key x then lookup key f else Nothing
   addpair k v (Diff f g) = Diff (addpair k v f) (removekey k g)
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
materialize BimapR x = runCollect x  bimapEmpty (\ (k,v) ans -> Core.addpair k v ans)
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

eval (DExclude (Base SetR (Sett x1)) (Base MapR x2)) =  Map.withoutKeys x2 x1
eval (DExclude (Dom (Base MapR x1)) (Base MapR x2)) = noKeys x2 x1
eval (DExclude (SetSingleton k) (Base BimapR x)) = Core.removekey k x
eval (DExclude (Dom (Singleton k _)) (Base BimapR x)) = Core.removekey k x
eval (DExclude (Rng (Singleton _ v)) (Base BimapR x)) = Core.removekey v x

eval (RExclude (Base BimapR x) (SetSingleton k)) = Core.removeval k x
eval (RExclude (Base BimapR x) (Dom (Singleton k v))) = Core.removeval k x
eval (RExclude (Base BimapR x) (Rng (Singleton k v))) = Core.removeval v x
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

eval other = error ("Can't eval: "++show other++" yet.")


-- =========================================================
-- Some examples of Exp and tests

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

tests :: [Bool]
tests = [ eval ex1==True
        , eval ex2==False
        , eval ex3 == Map.fromList [(1,'a'),(2,'z'),(3,'b'),(4,'g')]
        , eval ex4 == Map.fromList [(1,'a'),(4,'g')]
        , eval ex5 == Map.fromList [(1,'a'),(4,'g')]
        , eval ex6 == Map.fromList [(1,'a'),(4,'g')]
        , eval ex7 == True
        ]


-- ==================================================================
-- Show instances
