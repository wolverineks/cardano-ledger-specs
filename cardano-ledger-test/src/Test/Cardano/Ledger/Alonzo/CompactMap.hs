{-# OPTIONS_GHC -Wno-orphans #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE UnboxedTuples #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE OverloadedStrings #-}

module  Test.Cardano.Ledger.Alonzo.CompactMap where

import Cardano.Binary
  ( ToCBOR(..),
    FromCBOR(..),
    serialize',
    Encoding,
    unsafeDeserialize',
  )


import Test.Shelley.Spec.Ledger.Serialisation.Generators ()
import Test.Tasty.QuickCheck (Arbitrary (..), Gen, generate,vector)
import Shelley.Spec.Ledger.Tx (TxId(..),TxIn(..), TxOut)

import Cardano.Prelude (HeapWords(..))
import Shelley.Spec.Ledger.TxBody(TxOut(..))
import Shelley.Spec.Ledger.CompactAddr(CompactAddr(..))

import Cardano.Ledger.Crypto (StandardCrypto)
import Cardano.Ledger.Alonzo (AlonzoEra)
import Cardano.Ledger.Shelley (ShelleyEra)
import Cardano.Ledger.SafeHash(extractHash)
import Cardano.Crypto.Hash.Class(Hash(..))
import qualified Data.ByteString.Short as Short

import Test.Shelley.Spec.Ledger.PackedBytes(PackedBytes(..),packBytes)
import GHC.Word(Word64(..),Word32(..))
import GHC.Base (Int(I#))

-- https://downloads.haskell.org/~ghc/8.10.4/docs/html/libraries/base-4.14.1.0/GHC-Exts.html#v:indexWord32Array-35-
import GHC.Exts
  ( (+#), (*#), Int#,

    indexWord8ArrayAsWord64#,
    readWord8ArrayAsWord64#,
    writeWord8ArrayAsWord64#,
    indexWord64OffAddr#,
    readWord64OffAddr#,
    writeWord64OffAddr#,

    indexWord8ArrayAsWord32#,    
    readWord8ArrayAsWord32#,
    writeWord8ArrayAsWord32#,
    indexWord32OffAddr#,
    readWord32OffAddr#,
    writeWord32OffAddr#,
{-
    indexWord8ArrayAsWord16#,    
    readWord8ArrayAsWord16#,
    writeWord8ArrayAsWord16#,
    indexWord16OffAddr#,
    readWord16OffAddr#,
    writeWord16OffAddr#,
-}    
  )
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.CompactMap
import Data.Messages
import qualified Data.Array as A
import Data.ByteString (ByteString)
import Data.Text(Text,pack)


import Test.Cardano.Ledger.ShelleyMA.Serialisation.Generators() -- Arbitrary instance Value
import Cardano.Ledger.Mary.Value(Value(..)) -- HeapWords instance CompactValue
import Cardano.Ledger.Compactible (Compactible (..))
import qualified Cardano.Ledger.DescribeEras as E(Witness(..))
import Cardano.Ledger.Era(Era,Crypto)
import qualified Cardano.Ledger.Core as Core(Value)
import Test.QuickCheck.Gen(frequency,vectorOf)
import Cardano.Ledger.Coin (Coin (..))
import Cardano.Ledger.Val(Val(..))


import Data.Primitive.Types(Prim(..), defaultSetByteArray#, defaultSetOffAddr# )
import Data.Primitive.PrimArray -- (PrimArray,primArrayFromList)
import Control.Monad.Primitive
import Data.List(sort,sortBy)
import Control.Monad.ST(runST,ST)
import Data.Foldable(foldl')
import qualified Data.Array.MArray as MutA
import Data.Array.ST(STArray)


import Debug.Trace
-- import Test.Tasty
-- import Cardano.Binary.Deserialize(unsafeDeserialize)
-- import Shelley.Spec.Ledger.UTxO(UTxO(..))
-- import Test.Shelley.Spec.Ledger.ConcreteCryptoTypes (C,C_Crypto)
-- import qualified Data.ByteString as BS
-- import Data.ByteString.Conversion.From(FromByteString(parser),runParser)
-- import qualified Data.Vector.Generic as VGen
-- import qualified Data.Vector.Unboxed as VUnbox
-- import Data.Primitive.ByteArray


withSTArray :: Int -> (forall s. STArray s Int a -> ST s x) -> (A.Array Int a,x)
withSTArray size process = runST $ do
   marr <- MutA.newArray_ (0,size - 1)
   x <- process marr
   arr <- MutA.freeze marr
   pure(arr,x)

withPrimArray :: Prim a => Int -> (forall s. MutablePrimArray s a -> ST s x) -> (PrimArray a,x)
withPrimArray size process = runST $ do
   marr <- newPrimArray size
   x <- process marr
   arr <- unsafeFreezePrimArray marr
   pure(arr,x)

withBoth ::
   Prim a =>
   Int ->
   Int ->
   (forall s. MutablePrimArray s a -> STArray s Int b -> ST s ()) ->
   (PrimArray a, A.Array Int b)
withBoth primsize normsize process = runST $ do
   arr1 <- newPrimArray primsize
   arr2 <- MutA.newArray_ (0,normsize - 1)
   process arr1 arr2
   arr3 <- unsafeFreezePrimArray arr1
   arr4 <- MutA.freeze arr2
   pure(arr3,arr4)

-- ==============================

arraySize arr = (hi-lo) +1 where (lo,hi) = A.bounds arr

readFromGroup :: forall v. FromCBOR v => Int -> A.Array Int ByteString -> Int -> v
readFromGroup groupsize arr i =  (vals !! (i `mod` groupsize))
  where vals :: [ v ]
        vals = unsafeDeserialize' (index arr (i `div` groupsize))


-- | If the 'group' is full, serialise it, and then write it to 'mvalues' a index 'jv'
--   Aways return the next index and the next group. Most times the group grows
--   but the index says the same. The index grows only when the group becomes full.
resetNewGroup:: (Show v,ToCBOR v) => Int -> v -> STArray s Int ByteString -> Int -> [v] -> ST s (Int,[v])
resetNewGroup groupsize v mvalues jv group  = do
   if length group == groupsize - 1
      then trace ("Serialize "++show newgroup++" "++show jv) $
           do { MutA.writeArray mvalues jv (serialize' newgroup); pure(jv+1,[]) }
      else pure(jv, v : group)
   where newgroup = (reverse (v : group))


-- | Every 'groupsize' entries into the 'keys' array, we advance one entry into the 'values' array.
--   A 'group' is a deserialized entry from the 'values' array, for groupsize 'keys' entries.
--   So when we advance the index into the 'keys' array, and its group moves to next entry in the
--   'values' array, we need to fetch that group and deserialize it.
--   Note this can only happen when we advance the index into the 'keys' array.
resetOldGroup :: FromCBOR v => Int -> A.Array Int ByteString -> Int -> Int -> [v] -> (Int,[v])
resetOldGroup groupsize values ik iv oldgroup  = trace ("RESET OLD GROUP(ik,iv,groupsize)="++show(ik,iv,groupsize)) $
   if ((ik `mod` groupsize) == 0)
      then (iv+1,nextgroup)
      else (iv,oldgroup) 
   where nextgroup = trace ("DESERIALIZE RESET OLD GROUP") $ unsafeDeserialize' (index values (iv+1))

flush :: forall a v. (ToCBOR v,FromCBOR v,Show v,Ord a, Prim a,Show a) =>
         Int ->
         PrimArray a ->
         A.Array Int ByteString ->
         [(a,Message v)] ->
         (Message v -> v -> Message v) ->
         (PrimArray a,A.Array Int ByteString)
flush groupsize keys values list combine = trace ("NEWSIZES "++show(newsize,normsize)) $
                                           withBoth newsize normsize process where
   keysize = sizeofPrimArray keys
   valsize = arraySize values
   newsize = keysize + foldl' (accumSize keys) 0 (map fst list)
   normsize = if newsize `mod` groupsize == 0
                 then newsize `div` groupsize
                 else (newsize `div` groupsize) + 1
   sortedlist = sortBy (\ x y -> compare (fst x) (fst y)) list
   -- group0 :: [v]
   -- group0 =  unsafeDeserialize' (index values 0)
   
   process :: forall s. MutablePrimArray s a -> STArray s Int ByteString -> ST s ()
   process mkeys mvalues = loop 0 0 0 0 sortedlist [] 
     where pushFromList :: Int -> Int -> Int -> Int -> (a,Message v) -> [(a,Message v)] -> [v] -> ST s ()
           pushFromList ik iv jk jv (k,Delete) vs newgroup =
              loop ik iv jk jv vs newgroup -- Skip over because its is deleted
           pushFromList ik -- index into keys
                        iv -- index into values
                        jk -- index into mkeys
                        jv -- index into mvalues
                        (k,Edit v)
                        vs
                        newgroup = do
              writePrimArray mkeys jk k
              (jv',newgroup') <- resetNewGroup groupsize v mvalues jv newgroup
              loop ik iv (jk+1) jv' vs newgroup'
           pushFromArray ik iv jk jv (k,v) vs newgroup = do
              writePrimArray mkeys jk k
              (jv',newgroup') <- resetNewGroup groupsize v mvalues jv newgroup
              -- let (iv',oldgroup') = resetOldGroup groupsize values (ik+1) iv oldgroup
              loop (ik+1) iv (jk+1) jv' vs newgroup'              
           loop :: Int -> Int -> Int -> Int -> [(a,Message v)] -> [v] -> ST s ()
           loop ik iv jk jv xs newgroup =
             trace ("\n  "++show (ik,iv,jk,jv,xs,newgroup)) $
               case (ik < keysize, iv < valsize, jk < newsize, xs) of
                  (True,True,True,pairs) -> 
                    let k2 = indexPrimArray keys ik
                        v2 = readFromGroup groupsize values ik
                    in trace ("ARRAY PAIRS "++show(k2,v2)) $
                       case pairs of
                        [] -> pushFromArray ik iv jk jv (k2,v2) [] newgroup
                        ((k,v):ys) ->
                           case compare k k2 of
                             EQ -> pushFromList ik iv jk jv (k,v) ys newgroup
                             LT -> pushFromList ik iv jk jv (k,combine v v2) ys newgroup
                             GT -> pushFromArray ik iv jk jv (k2,v2) xs newgroup
                  (False,_,True,((k,v):xs)) -> pushFromList ik iv jk jv (k,v) xs newgroup
              -- This case should only happen when we have run out of things to process
              -- (ik >= keysize), so there is nothing left to copy from 'arr'
              -- or xs is null , so there is nothing left to copy from 'list'
              -- or jk >= newsize, so mkeys is already full
                  other -> pure ()


testflush :: Par2 Int Text -> Par2 Int Text     
testflush (Par2 groupsize keys values delta) = Par2 groupsize ks vs Map.empty
   where (ks,vs) = flush groupsize keys values (Map.toList delta) (\ new old -> new <> (Edit old))


m2 :: Map.Map Int Text
m2 = Map.fromList [(1::Int,pack "a"),(2,pack "b"),(9,pack "d"),(5,pack "c")]

p2 = insert2 10 "e" (insert2 12 "f" (toPar2 3 m2))

instance ToCBOR v => ToCBOR (Message v) where
  toCBOR (Edit v) = toCBOR v

instance FromCBOR v => FromCBOR (Message v) where
  fromCBOR = Edit <$> fromCBOR

-- =========================================

accumSize :: (Ord k, Indexable arr k, Num p) => arr k -> p -> k -> p
accumSize arr ans key  =
  case binsearch 0 (isize arr - 1) key arr of { Just _ -> ans ; _ -> ans+1 }


-- | Merge 'list' (of type [a]) into 'arr' (a sorted (PrimArray a)) creating a new (PrimArray a)
--   The 'arr' should be sorted, and then the result will be sorted.
mergePrimArray :: forall a. (Ord a, Prim a) => PrimArray a -> [a] -> PrimArray a
mergePrimArray arr list = arr2 where
   (arr2,_) = withPrimArray newsize process
   oldsize = sizeofPrimArray arr
   newsize = oldsize + foldl' (accumSize arr) 0 list
   sortedlist = sort list
   process :: forall s. MutablePrimArray s a -> ST s ()
   process mutarr = do
       let loop i next xs = 
            case (i < oldsize, next < newsize, xs) of
              (True,True,(x:xs)) ->
                do let y = indexPrimArray arr i
                   case compare x y of
                     EQ -> do writePrimArray mutarr next x
                              loop (i+1) (next+1) xs
                     LT -> do writePrimArray mutarr next x
                              loop i (next+1) xs
                     GT -> do writePrimArray mutarr next y
                              loop (i+1) (next+1) (x:xs)
              (True,True,[]) ->
                copyPrimArray mutarr next arr i (oldsize - i)
              (False,True,(x:xs)) ->
                do writePrimArray mutarr next x
                   loop i (next+1) xs
              -- This case should only happen when we have run out of things to process
              -- (i >= oldsize), so there is nothing left to copy from 'arr'
              -- or xs is null , so there is nothing left to copy from 'list'
              other -> pure ()
       loop 0 0 sortedlist
   
t21 = primArrayFromList [3,6,9,12::Int]

test :: [Int] -> PrimArray Int
test xs = mergePrimArray t21 xs
  

-- ==========================================

-- ==========================================
data TT = TT Word64 Word64 Word64 Word32 Word32 deriving (Eq,Ord,Show)


txInToTT :: TxIn StandardCrypto -> TT
txInToTT txin =
 let TxInCompact (TxId safe) w5 = txin
     UnsafeHash bytes = extractHash safe 
 in case (packBytes bytes) :: PackedBytes 28 of
       PackedBytes28 w1 w2 w3 w4 -> TT w1 w2 w3 w4 (fromIntegral w5)
       _ -> error ("BAD TxIn")  


-- | Offsets (in Bytes) of the arguments (TT w1 w2 w3 w4 w5)
w1offset, w2offset, w3offset, w4offset, w5offset :: Int
w1offset = 0
w2offset = 8
w3offset = 16
w4offset = 24
w5offset = 28

instance Prim TT where
  sizeOf# _ = (3# *# sizeOf# (undefined ::Word64) +#  2# *# sizeOf#  (undefined ::Word32))
  alignment# x = sizeOf# x -- Pack as tight as possible.
  indexByteArray# arr# i# = 
    let i2# = i# *# sizeOf# (undefined :: TT)
    in TT (W64# (indexWord8ArrayAsWord64# arr# (i2# +# unInt w1offset)))
          (W64# (indexWord8ArrayAsWord64# arr# (i2# +# unInt w2offset)))
          (W64# (indexWord8ArrayAsWord64# arr# (i2# +# unInt w3offset)))
          (W32# (indexWord8ArrayAsWord32# arr# (i2# +# unInt w4offset)))
          (W32# (indexWord8ArrayAsWord32# arr# (i2# +# unInt w5offset)))      

  readByteArray# arr# i# =
    \s0 -> case readWord8ArrayAsWord64# arr# (i2# +# unInt w1offset) s0 of
       (# s1, w1 #) -> case readWord8ArrayAsWord64# arr#  (i2# +# unInt w2offset) s1 of
          (# s2, w2 #) -> case readWord8ArrayAsWord64# arr#  (i2# +# unInt w3offset) s2 of
             (# s3, w3 #) -> case readWord8ArrayAsWord32# arr#  (i2# +# unInt w4offset) s3 of
                (# s4, w4 #) -> case readWord8ArrayAsWord32# arr#  (i2# +# unInt w5offset) s4 of
                   (# s5, w5 #) -> (# s5, TT (W64# w1) (W64# w2) (W64# w3) (W32# w4) (W32# w5) #)
   where i2# = i# *# sizeOf# (undefined :: TT)

  writeByteArray# arr# i# (TT (W64# w1) (W64# w2) (W64# w3) (W32# w4) (W32# w5)) =
      \s0 -> case writeWord8ArrayAsWord64# arr# (i2# +# unInt w1offset) w1 s0 of
          s1 -> case writeWord8ArrayAsWord64# arr#  (i2# +# unInt w2offset) w2 s1 of
             s2 -> case writeWord8ArrayAsWord64# arr# (i2# +# unInt w3offset) w3 s2 of
                s3 -> case writeWord8ArrayAsWord32# arr#  (i2# +# unInt w4offset) w4 s3 of
                   s4 -> case writeWord8ArrayAsWord32# arr#  (i2# +# unInt w5offset) w5 s4 of
                      s5 -> s5
   where i2# =  i# *# sizeOf# (undefined :: TT)

  setByteArray# arr n m a state = defaultSetByteArray# arr n m a state
  
  indexOffAddr# arr# i# =
    let i2# = i# *# sizeOf# (undefined :: TT)
    in TT (W64# (indexWord64OffAddr# arr# (i2# +# unInt w1offset)))
          (W64# (indexWord64OffAddr# arr# (i2# +# unInt w2offset)))
          (W64# (indexWord64OffAddr# arr# (i2# +# unInt w3offset)))
          (W32# (indexWord32OffAddr# arr# (i2# +# unInt w4offset)))
          (W32# (indexWord32OffAddr# arr# (i2# +# unInt w5offset)))      


  readOffAddr# arr# i# =
       \s0 -> case readWord64OffAddr#  arr# (i2# +# unInt w1offset) s0 of
        (# s1, w1 #) -> case readWord64OffAddr#  arr#  (i2# +# unInt w2offset) s1 of
          (# s2, w2 #) -> case readWord64OffAddr#  arr#  (i2# +# unInt w3offset) s2 of
            (# s3, w3 #) -> case readWord32OffAddr#  arr#  (i2# +# unInt w4offset) s3 of
              (# s4, w4 #) -> case readWord32OffAddr#  arr#  (i2# +# unInt w5offset) s4 of
                 (# s5, w5 #) -> (# s5, TT (W64# w1) (W64# w2) (W64# w3) (W32# w4) (W32# w5) #)
    where i2# =  i# *# sizeOf# (undefined :: TT)

  writeOffAddr# arr# i# (TT (W64# w1) (W64# w2) (W64# w3) (W32# w4) (W32# w5)) =
      \s0 -> case writeWord64OffAddr# arr# (i2# +# unInt w1offset) w1 s0 of
          s1 -> case writeWord64OffAddr# arr#  (i2# +# unInt w2offset) w2 s1 of
             s2 -> case writeWord64OffAddr# arr# (i2# +# unInt w3offset) w3 s2 of
                s3 -> case writeWord32OffAddr# arr#  (i2# +# unInt w4offset) w4 s3 of
                   s4 -> case writeWord32OffAddr# arr# (i2# +# unInt w5offset) w5 s4 of
                      s5 -> s5
   where i2# =  i# *# sizeOf# (undefined :: TT)
   
  setOffAddr# = defaultSetOffAddr# 

unInt :: Int -> Int#
unInt (I# x) = x
tt :: TT
tt = TT 1 2 3 4 6


pa :: PrimArray TT
pa = primArrayFromList [TT 1 2 3 4 99, TT 8 7 6 5 21, TT 1 1 1 1 4]


-- ===========================================
data ParVector k v where
   ParVector:: (Prim k) => (PrimArray k) -> (A.Array Int v) -> ParVector k v

instance (Show k, Show v, Prim k) => Show (ParVector k v) where
  show (ParVector ks vs) = show ks ++"\n"++show vs


toPar :: Prim k => Map.Map k v -> ParVector k v
toPar m = ParVector keys values
  where pairs = Map.toAscList m
        keys = primArrayFromList (map fst pairs)
        values = A.listArray (0,isize keys - 1) (map snd pairs)

m1 :: Map.Map Int Char
m1 = Map.fromList [(1::Int,'a'),(2,'b'),(9,'c'),(5,'d')]



look :: Ord k => k -> ParVector k v -> Maybe v
look k (ParVector keys values) =
   case search k keys of
      Just i -> Just $ index values i
      Nothing -> Nothing 

-- ==================================================
{-
*Test.Shelley.Spec.Ledger.CompactMap> main
Size 49250 entries 49250
Normal  1576000 words
Compact 648388 words
Percent 41.141370558375634
Parallel HW PARVECTOR 295502  679045
974550 words
Percent 61.836928934010146
-}



instance HeapWords TT where
  heapWords (TT _ _ _ _ _) = 4

instance (HeapWords k, HeapWords v) => HeapWords (ParVector k v) where
  heapWords (ParVector k v) =  (3 + hwk + hwv)
      where hwk = heapWords k
            hwv = heapWords v 


-- ==================================================

type Alonzo = -- ShelleyEra StandardCrypto
              AlonzoEra StandardCrypto

percent :: Integral n => n -> n -> String
percent new old = show(round((fromIntegral new / fromIntegral old)*100 :: Double))++"%"


hasTokens :: E.Witness era -> TxOut era -> Bool
hasTokens E.Alonzo (TxOutCompact _ x) = case fromCompact x of (Value _ m) -> not (Map.null m)
hasTokens E.Mary (TxOutCompact _ x) = case fromCompact x of (Value _ m) -> not (Map.null m)
hasTokens _ _ = False

tokenSize :: E.Witness era -> Int -> TxOut era -> Int
tokenSize E.Shelley ans x = ans
tokenSize E.Allegra ans x = ans
tokenSize E.Mary ans (TxOutCompact _ x) =
  case fromCompact x of
    (Value _ m) -> if Map.null m then ans else heapWords x + ans - 1
tokenSize E.Alonzo ans (TxOutCompact _ x) =
  case fromCompact x of
    (Value _ m) -> if Map.null m then ans else heapWords x + ans - 1

serialTxOut:: E.Witness era -> TxOut era -> ByteString
serialTxOut E.Shelley (txout@(TxOutCompact _ _)) = serialize' txout
serialTxOut E.Allegra (txout@(TxOutCompact _ _)) = serialize' txout
serialTxOut E.Mary (txout@(TxOutCompact _ _)) = serialize' txout
serialTxOut E.Alonzo (txout@(TxOutCompact _ _)) = serialize' txout

 

genTxOut :: E.Witness era -> Int -> Gen (TxOut era)
genTxOut E.Alonzo percent =
   TxOut <$> arbitrary
         <*> frequency [(percent,arbitrary),((100 - percent), inject <$> arbitrary)]
genTxOut E.Mary percent =
   TxOut <$> arbitrary
         <*> frequency [(percent,arbitrary),((100 - percent), inject <$> arbitrary)]
genTxOut E.Shelley percent =
   TxOut <$> arbitrary
         <*> frequency [(percent,arbitrary),((100 - percent), inject <$> arbitrary)]
genTxOut E.Allegra percent =
   TxOut <$> arbitrary
         <*> frequency [(percent,arbitrary),((100 - percent), inject <$> arbitrary)]        



main :: forall era.
  ( Era era,
    ToCBOR (Core.Value era),
    HeapWords (CompactForm (Core.Value era))
  ) => E.Witness era -> IO ()
main wit = do
  pairs <- generate (vectorOf 100000 ((,) <$> arbitrary <*> genTxOut wit 1))
  let m = Map.fromList pairs
      withnewkeys = Map.mapKeys txInToTT m
      m2 = Map.map (serialTxOut wit) $ withnewkeys
      pm = toPar m2
      pm2 = toPar2 30 withnewkeys
      keys = Set.fromList $ map fst (take 100 pairs)
      norm = (heapWords m)
      compact = (heapWords(initMap m keys))
      par = (heapWords pm)
      par2 = (heapWords pm2)
      tokens = Map.foldl' (\ ans txout -> if hasTokens wit txout then ans+1 else ans) (0::Int) m
      totaltokenwords = Map.foldl' (tokenSize wit) 0 m
      
  putStrLn (unlines [show wit++" Era."
                    ,"Size "++show(Map.size m)++" entries "++show(Map.size m2)
                    ,"Number of entries with Tokens = "++show tokens++"  "++ percent tokens (Map.size m) ++
                       " of entries have tokens,  total words from tokens "++show  totaltokenwords
                    ,"Normal  "++show norm++" words"
                    ,"Compact "++show compact++" words"
                    ,"Percent " ++ percent compact norm
                    ,"Parallel "++show par++" words"
                    ,"Percent " ++percent par norm
                    ,"Parallel2 "++show par2++" words"
                    ,"Percent " ++percent par2 norm
                    ])


aa :: IO (Short.ShortByteString, [Word64],Int)
aa = do txin <- generate (arbitrary :: Gen (TxIn  StandardCrypto))
        let TxInCompact (TxId safe) _ = txin
            UnsafeHash bytes = extractHash safe 
        case (packBytes bytes) :: PackedBytes 32 of
          PackedBytes32 w1 w2 w3 w4 -> pure (bytes,[w1,w2,w3,w4],Short.length bytes)
          _ -> putStrLn ("BAD ") >> pure( bytes,[],Short.length bytes)

bb :: IO (Int, Int)
bb = do txouts <- generate (vector 10 :: Gen [(TxOut Alonzo)])
        putStrLn (show(toCBOR txouts))
        putStrLn ""
        putStrLn (unlines (map (show . toCBOR) txouts))
        pure (heapWords (serialize' txouts), foldr (\ x ans -> heapWords (serialize' x) + ans) 0 txouts)

cc :: IO Encoding
cc = do txouts <- generate (vector 4 :: Gen [(TxOut Alonzo)])
        pure(toCBOR txouts)
 
dd =  -- Average 12 Tokens per Value
   do l <- generate (vector 100 :: Gen [TxOut Alonzo])
      let baz :: TxOut Alonzo -> Int
          baz (TxOut _ (Value _ mm)) = Map.size mm
      pure(fmap baz l)

-- =======================================

foo :: TxOut era -> Short.ShortByteString
foo (TxOutCompact (UnsafeCompactAddr bytes1) _) = bytes1

-- =========================================

ex2, ex3, ex4 :: Par2 Int Text
ex2 = toPar2 5 (Map.fromList [(i,pack(show i)) | i <- [0::Int ..21]])
ex3 = delete2 5 ex2
ex4 = insert2 12 (pack "99") ex3

instance Exp Text where
  plus x y = x <> y

