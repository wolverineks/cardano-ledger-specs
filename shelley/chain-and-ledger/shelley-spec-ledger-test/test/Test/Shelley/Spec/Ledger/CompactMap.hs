{-# OPTIONS_GHC -Wno-orphans #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE UnboxedTuples #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts  #-}

module Test.Shelley.Spec.Ledger.CompactMap where

import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.CompactMap
import Test.Shelley.Spec.Ledger.Serialisation.Generators ()
-- import Test.Tasty
import Test.Tasty.QuickCheck (Arbitrary (..), Gen, generate,vector)
import Shelley.Spec.Ledger.Tx (TxId(..),TxIn(..), TxOut)
-- import Shelley.Spec.Ledger.UTxO(UTxO(..))
-- import Test.Shelley.Spec.Ledger.ConcreteCryptoTypes (C,C_Crypto)
-- import Cardano.Ledger.Era(Crypto)
import Cardano.Prelude (HeapWords(..))
import Shelley.Spec.Ledger.TxBody(TxOut(..))
import Shelley.Spec.Ledger.CompactAddr(CompactAddr(..))

import Cardano.Ledger.Crypto (StandardCrypto)
import Cardano.Ledger.Shelley (ShelleyEra)
import Cardano.Ledger.SafeHash(extractHash)
import Cardano.Crypto.Hash.Class(Hash(..))
import qualified Data.ByteString.Short as Short
-- import qualified Data.ByteString as BS
-- import Data.ByteString.Conversion.From(FromByteString(parser),runParser)

import Test.Shelley.Spec.Ledger.PackedBytes(PackedBytes(..),packBytes)

import qualified Data.Vector.Generic as VGen
import qualified Data.Vector.Unboxed as VUnbox

import GHC.Word(Word64(..),Word32(..),Word16(..))
import GHC.Base (Int(I#))
import Data.Primitive.Types(Prim(..), defaultSetByteArray#, defaultSetOffAddr# )
-- https://downloads.haskell.org/~ghc/8.10.4/docs/html/libraries/base-4.14.1.0/GHC-Exts.html#v:indexWord32Array-35-
import GHC.Exts
  ( (+#), (*#), State#, Int#,

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

    indexWord8ArrayAsWord16#,    
    readWord8ArrayAsWord16#,
    writeWord8ArrayAsWord16#,
    indexWord16OffAddr#,
    readWord16OffAddr#,
    writeWord16OffAddr#,
  )

import Data.Primitive.ByteArray
import Data.Primitive.PrimArray(PrimArray,primArrayFromList,indexPrimArray,sizeofPrimArray)
import qualified Data.Primitive.PrimArray as PA

import Debug.Trace
import Data.Primitive.PrimArray(PrimArray)
import qualified Data.Array as A

-- ==========================================

instance (Prim a, HeapWords a) => HeapWords(PrimArray a) where
  heapWords arr = 2 + (sizeofPrimArray arr * heapWords (indexPrimArray arr 0))

-- ==========================================
data TT = TT Word64 Word64 Word64 Word32 Word64 deriving (Eq,Ord,Show)

instance HeapWords TT where
  heapWords (TT _ _ _ _ _) = 6

txInToTT :: TxIn StandardCrypto -> TT
txInToTT txin =
 let TxInCompact (TxId safe) w5 = txin
     UnsafeHash bytes = extractHash safe 
 in case (packBytes bytes) :: PackedBytes 28 of
       PackedBytes28 w1 w2 w3 w4 -> TT w1 w2 w2 w4 w5
       _ -> error ("BAD TxIn")  


-- | Offsets (in Bytes) of the arguments (TT w1 w2 w3 w4 w5)
w1offset, w2offset, w3offset, w4offset, w5offset :: Int
w1offset = 0
w2offset = 8
w3offset = 16
w4offset = 24
w5offset = 31

instance Prim TT where
  sizeOf# _ = (4# *# sizeOf# (undefined ::Word64) +#  sizeOf#  (undefined ::Word32))
  alignment# x = sizeOf# x -- Pack as tight as possible.
  indexByteArray# arr# i# = 
    let i2# = i# *# sizeOf# (undefined :: TT)
    in TT (W64# (indexWord8ArrayAsWord64# arr# (i2# +# unInt w1offset)))
          (W64# (indexWord8ArrayAsWord64# arr# (i2# +# unInt w2offset)))
          (W64# (indexWord8ArrayAsWord64# arr# (i2# +# unInt w3offset)))
          (W32# (indexWord8ArrayAsWord32# arr# (i2# +# unInt w4offset)))
          (W64# (indexWord8ArrayAsWord64# arr# (i2# +# unInt w5offset)))      

  readByteArray# arr# i# =
    \s0 -> case readWord8ArrayAsWord64# arr# (i2# +# unInt w1offset) s0 of
       (# s1, w1 #) -> case readWord8ArrayAsWord64# arr#  (i2# +# unInt w2offset) s1 of
          (# s2, w2 #) -> case readWord8ArrayAsWord64# arr#  (i2# +# unInt w3offset) s2 of
             (# s3, w3 #) -> case readWord8ArrayAsWord32# arr#  (i2# +# unInt w4offset) s3 of
                (# s4, w4 #) -> case readWord8ArrayAsWord64# arr#  (i2# +# unInt w5offset) s4 of
                   (# s5, w5 #) -> (# s5, TT (W64# w1) (W64# w2) (W64# w3) (W32# w4) (W64# w5) #)
   where i2# = i# *# sizeOf# (undefined :: TT)

  writeByteArray# arr# i# (TT (W64# w1) (W64# w2) (W64# w3) (W32# w4) (W64# w5)) =
      \s0 -> case writeWord8ArrayAsWord64# arr# (i2# +# unInt w1offset) w1 s0 of
          s1 -> case writeWord8ArrayAsWord64# arr#  (i2# +# unInt w2offset) w2 s1 of
             s2 -> case writeWord8ArrayAsWord64# arr# (i2# +# unInt w3offset) w3 s2 of
                s3 -> case writeWord8ArrayAsWord32# arr#  (i2# +# unInt w4offset) w4 s3 of
                   s4 -> case writeWord8ArrayAsWord64# arr#  (i2# +# unInt w5offset) w5 s4 of
                      s5 -> s5
   where i2# =  i# *# sizeOf# (undefined :: TT)

  setByteArray# arr n m a state = defaultSetByteArray# arr n m a state
  
  indexOffAddr# arr# i# =
    let i2# = i# *# sizeOf# (undefined :: TT)
    in TT (W64# (indexWord64OffAddr# arr# (i2# +# unInt w1offset)))
          (W64# (indexWord64OffAddr# arr# (i2# +# unInt w2offset)))
          (W64# (indexWord64OffAddr# arr# (i2# +# unInt w3offset)))
          (W32# (indexWord32OffAddr# arr# (i2# +# unInt w4offset)))
          (W64# (indexWord64OffAddr# arr# (i2# +# unInt w5offset)))      


  readOffAddr# arr# i# =
       \s0 -> case readWord64OffAddr#  arr# (i2# +# unInt w1offset) s0 of
        (# s1, w1 #) -> case readWord64OffAddr#  arr#  (i2# +# unInt w2offset) s1 of
          (# s2, w2 #) -> case readWord64OffAddr#  arr#  (i2# +# unInt w3offset) s2 of
            (# s3, w3 #) -> case readWord32OffAddr#  arr#  (i2# +# unInt w4offset) s3 of
              (# s4, w4 #) -> case readWord64OffAddr#  arr#  (i2# +# unInt w5offset) s2 of
                 (# s5, w5 #) -> (# s5, TT (W64# w1) (W64# w2) (W64# w3) (W32# w4) (W64# w5) #)
    where i2# =  i# *# sizeOf# (undefined :: TT)

  writeOffAddr# arr# i# (TT (W64# w1) (W64# w2) (W64# w3) (W32# w4) (W64# w5)) =
      \s0 -> case writeWord64OffAddr# arr# (i2# +# unInt w1offset) w1 s0 of
          s1 -> case writeWord64OffAddr# arr#  (i2# +# unInt w2offset) w2 s1 of
             s2 -> case writeWord64OffAddr# arr# (i2# +# unInt w3offset) w3 s2 of
                s3 -> case writeWord32OffAddr# arr#  (i2# +# unInt w4offset) w4 s3 of
                   s4 -> case writeWord64OffAddr# arr# (i2# +# unInt w5offset) w5 s4 of
                      s5 -> s5
   where i2# =  i# *# sizeOf# (undefined :: TT)
   
  setOffAddr# = defaultSetOffAddr# 

unInt :: Int -> Int#
unInt (I# x) = x
tt :: TT
tt = TT 1 2 3 4 6


pa :: PrimArray TT
pa = primArrayFromList [TT 1 2 3 4 99, TT 8 7 6 5 21, TT 1 1 1 1 4]

-- ===============================================

class Indexable t a where
   index:: t a -> Int -> a
   isize :: t a -> Int

binsearch:: (Ord k, Indexable arr k) => Int -> Int -> k -> arr k -> Maybe Int
binsearch lo hi _k _v | lo > hi = Nothing
binsearch lo hi k v | lo==hi = if index v lo == k then Just lo else Nothing
binsearch lo _hi k v | index v lo == k = Just lo
binsearch _lo hi k v | index v hi == k = Just hi
binsearch lo hi _k _v | lo+1== hi = Nothing
binsearch lo hi k v = (if index v mid > k then binsearch lo mid k v else binsearch mid hi k v)
   where mid = lo + (div (hi-lo) 2)

search :: (Ord k, Indexable arr k) => k -> arr k -> Maybe Int
search key v = binsearch 0 (isize v - 1) key v


-- vv c = search c (VUnbox.fromList "bcdwxy")

alub :: (Ord t1, Indexable t2 t1) => (Int, Int) -> t2 t1 -> t1 -> Maybe (Int, t1)
alub (lo,hi) arr target
  | lo > hi = Nothing
  | target <= index arr lo = Just(lo,index arr lo)
  | lo==hi = Nothing
  | lo+1 == hi && index arr lo < target && target <= index arr hi = Just(hi,index arr hi)
  | True = if target <= index arr mid then (alub (lo,mid) arr target) else (alub (mid,hi) arr target)
      where mid = lo + (div (hi-lo) 2)
      
instance Prim a => Indexable PrimArray a where
  index = indexPrimArray
  isize = sizeofPrimArray

instance Indexable (A.Array Int) a where
  index = (A.!)
  isize arr = (hi - lo) + 1 where (lo,hi) = A.bounds arr


-- ===========================================
data ParVector k v where
   ParVector:: (Prim k) => (PrimArray k) -> (A.Array Int v) -> ParVector k v

instance (HeapWords k, HeapWords v) => HeapWords (ParVector k v) where
  heapWords (ParVector k v) = trace ("HW PARVECTOR "++show hwk ++"  "++show hwv) (3 + hwk + hwv)
      where hwk = heapWords k
            hwv = heapWords v
instance (HeapWords v) => HeapWords (A.Array Int v) where
  heapWords arr = foldl accum (3 + (trace (" -- Array Size = "++show n) n)) arr
     where accum ans v = ans + heapWords v
           n = isize arr
           
instance (Show k, Show v, Prim k) => Show (ParVector k v) where
  show (ParVector ks vs) = show ks ++"\n"++show vs


toPar m = ParVector keys values
  where pairs = Map.toAscList m
        keys = primArrayFromList (map fst pairs)
        values = A.listArray (0,isize keys - 1) (map snd pairs)

m1 = Map.fromList [(1::Int,'a'),(2,'b'),(9,'c'),(5,'d')]


look :: Ord k => k -> ParVector k v -> Maybe v
look k (ParVector keys values) =
   case search k keys of
      Just i -> Just $ index values i
      Nothing -> Nothing 



-- ==================================================

type Shelley = ShelleyEra StandardCrypto


main :: IO ()
main = do
  pairs <- generate (vector 100000 :: Gen [(TxIn StandardCrypto,TxOut Shelley)])
  let m = Map.fromList pairs
      m2 = Map.mapKeys txInToTT m
      pm = toPar m2
      keys = Set.fromList $ map fst (take 100 pairs)
      norm = (heapWords m)
      compact = (heapWords(initMap m keys))
      par = (heapWords pm)
      
  putStrLn (unlines ["Size "++show(Map.size m)++" entries "++show(Map.size m2)
                    ,"Normal  "++show norm++" words"
                    ,"Compact "++show compact++" words"
                    ,"Percent " ++show((fromIntegral compact / fromIntegral norm)*100 :: Double)
                    ,"Parallel "++show par++" words"
                    ,"Percent " ++show((fromIntegral par / fromIntegral norm)*100 :: Double)
                    ])


aa :: IO (Short.ShortByteString, [Word64],Int)
aa = do txin <- generate (arbitrary :: Gen (TxIn  StandardCrypto))
        let TxInCompact (TxId safe) _ = txin
            UnsafeHash bytes = extractHash safe 
        case (packBytes bytes) :: PackedBytes 32 of
          PackedBytes32 w1 w2 w3 w4 -> pure (bytes,[w1,w2,w3,w4],Short.length bytes)
          _ -> putStrLn ("BAD ") >> pure( bytes,[],Short.length bytes)
        

-- =======================================

