{-# OPTIONS_GHC -Wno-orphans #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE UnboxedTuples #-}

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
    indexWord8ArrayAsWord16#,
    indexWord8ArrayAsWord64#,
    readWord8ArrayAsWord64#,
    readWord8ArrayAsWord16#,
    writeWord8ArrayAsWord64#,
    writeWord8ArrayAsWord16#,
    indexWord64OffAddr#,
    indexWord16OffAddr#,
    readWord64OffAddr#,
    readWord16OffAddr#,
    writeWord64OffAddr#,
    writeWord16OffAddr#,
  )

import Data.Primitive.ByteArray
import Data.Primitive.PrimArray(PrimArray,primArrayFromList)

import Debug.Trace
import Data.Primitive.PrimArray(PrimArray)

-- ==========================================
data TT = TT Word64 Word64 Word64 Word16 deriving Show

-- | Offsets (in Bytes) of the arguments (TT w1 w2 w3 w4)
w1offset, w2offset, w3offset, w4offset :: Int
w1offset = 0
w2offset = 8
w3offset = 16
w4offset = 24

instance Prim TT where
  sizeOf# (TT w1 w2 w3 w4) = (sizeOf# w1 +#  sizeOf# w2  +# sizeOf# w3 +#  sizeOf# w4)
  alignment# x = sizeOf# x -- Pack as tight as possible.
  indexByteArray# arr# i# = 
    let i2# = i# *# 26#
    in TT (W64# (indexWord8ArrayAsWord64# arr# (i2# +# unInt w1offset)))
          (W64# (indexWord8ArrayAsWord64# arr# (i2# +# unInt w2offset)))
          (W64# (indexWord8ArrayAsWord64# arr# (i2# +# unInt w3offset)))
          (W16# (indexWord8ArrayAsWord16# arr# (i2# +# unInt w4offset)))      

  readByteArray# arr# i# =
    \s0 -> case readWord8ArrayAsWord64# arr# (i2# +# unInt w1offset) s0 of
       (# s1, w1 #) -> case readWord8ArrayAsWord64# arr#  (i2# +# unInt w2offset) s1 of
          (# s2, w2 #) -> case readWord8ArrayAsWord64# arr#  (i2# +# unInt w3offset) s2 of
             (# s3, w3 #) -> case readWord8ArrayAsWord16# arr#  (i2# +# unInt w3offset) s3 of
                (# s4, w4 #) -> (# s4, TT (W64# w1) (W64# w2) (W64# w3) (W16# w4) #)
   where i2# =  26# *# i#

  writeByteArray# arr# i# (TT (W64# w1) (W64# w2) (W64# w3) (W16# w4)) =
      \s0 -> case writeWord8ArrayAsWord64# arr# (i2# +# unInt w1offset) w1 s0 of
          s1 -> case writeWord8ArrayAsWord64# arr#  (i2# +# unInt w2offset) w2 s1 of
             s2 -> case writeWord8ArrayAsWord64# arr# (i2# +# unInt w3offset) w3 s2 of
                s3 -> case writeWord8ArrayAsWord16# arr#  (i2# +# unInt w3offset) w4 s3 of
                   s4 -> s4
   where i2# =  26# *# i#

  setByteArray# arr n m a state = defaultSetByteArray# arr n m a state
  
  indexOffAddr# arr# i# =
    let i2# = i# *# 26#
    in TT (W64# (indexWord64OffAddr# arr# (i2# +# unInt w1offset)))
          (W64# (indexWord64OffAddr# arr# (i2# +# unInt w2offset)))
          (W64# (indexWord64OffAddr# arr# (i2# +# unInt w3offset)))
          (W16# (indexWord16OffAddr# arr# (i2# +# unInt w4offset)))      

  readOffAddr# arr# i# =
       \s0 -> case readWord64OffAddr#  arr# (i2# +# unInt w1offset) s0 of
        (# s1, w1 #) -> case readWord64OffAddr#  arr#  (i2# +# unInt w2offset) s1 of
          (# s2, w2 #) -> case readWord64OffAddr#  arr#  (i2# +# unInt w3offset) s2 of
            (# s3, w3 #) -> case readWord16OffAddr#  arr#  (i2# +# unInt w3offset) s3 of
              (# s4, w4 #) -> (# s4, TT (W64# w1) (W64# w2) (W64# w3) (W16# w4) #)
    where i2# =  26# *# i#

  writeOffAddr# arr# i# (TT (W64# w1) (W64# w2) (W64# w3) (W16# w4)) =
      \s0 -> case writeWord64OffAddr# arr# (i2# +# unInt w1offset) w1 s0 of
          s1 -> case writeWord64OffAddr# arr#  (i2# +# unInt w2offset) w2 s1 of
             s2 -> case writeWord64OffAddr# arr# (i2# +# unInt w3offset) w3 s2 of
                s3 -> case writeWord16OffAddr# arr#  (i2# +# unInt w3offset) w4 s3 of
                   s4 -> s4
   where i2# =  26# *# i#
   
  setOffAddr# = defaultSetOffAddr# 

unInt (I# x) = x
tt :: TT
tt = TT 1 2 3 4


pa = primArrayFromList [TT 1 2 3 4, TT 8 7 6 5]

-- ===========================================
data ParVector k v where
   ParVector:: (VGen.Vector vec v, Prim i) =>  (i-> k) -> (k -> i) -> (VUnbox.Vector i) -> (vec v) -> ParVector k v

binsearch:: (Ord k, VUnbox.Unbox k) => Int -> Int -> k -> VUnbox.Vector k -> Maybe Int
binsearch lo hi k v | lo > hi = Nothing
binsearch lo hi k v | lo==hi = if  (VUnbox.!) v lo == k then Just lo else Nothing
binsearch lo hi k v | (VUnbox.!) v lo == k = Just lo
binsearch lo hi k v | (VUnbox.!) v hi == k = Just hi
binsearch lo hi k v | lo+1== hi = Nothing
binsearch lo hi k v = trace ("XXX "++show(lo,mid,hi)) (if (VUnbox.!) v mid > k then binsearch lo mid k v else binsearch mid hi k v)
   where mid = lo + (div (hi-lo) 2)

search :: (Ord k, VUnbox.Unbox k) => k -> VUnbox.Vector k -> Maybe Int
search key v = binsearch 0 (VUnbox.length v - 1) key v


vv c = search c (VUnbox.fromList "bcdwxy")

alub :: (Ord t, VUnbox.Unbox t) => (Int, Int) -> VUnbox.Vector t -> t -> Maybe (Int, t)
alub (first,last) arr target
  | first > last = Nothing
  | target <= arr VUnbox.! first = Just(first,arr VUnbox.! first)
  | first==last = Nothing
  | first+1 == last && arr VUnbox.! first < target && target <= arr VUnbox.! last = Just(last,arr  VUnbox.! last)
  | True = if target <= arr VUnbox.! mid then (alub (first,mid) arr target) else (alub (mid,last) arr target)
      where mid = first + (div (last-first) 2)
      

look :: Ord k => k -> ParVector k v -> Maybe v
look k (ParVector toK fromK keys values) = undefined



-- ==================================================

type Shelley = ShelleyEra StandardCrypto

instance Memory (TxIn StandardCrypto) where
  memory x = heapWords x

instance Memory (TxOut Shelley) where
  memory x = heapWords x

main :: IO ()
main = do
  pairs <- generate (vector 100000 :: Gen [(TxIn StandardCrypto,TxOut Shelley)])
  let m = Map.fromList pairs
      keys = Set.fromList $ map fst (take 100 pairs)
      norm = (heapWords m)
      compact = (memory(initMap m keys))
  putStrLn (unlines ["Size "++show(Map.size m)++" entries"
                    ,"Normal  "++show norm++" words"
                    ,"Compact "++show compact++" words"
                    ,"Percent " ++show((fromIntegral compact / fromIntegral norm)*100 :: Double)
                    ])


aa :: IO (Short.ShortByteString, [Word64],Int)
aa = do txin <- generate (arbitrary :: Gen (TxIn  StandardCrypto))
        let TxInCompact (TxId safe) _ = txin
            UnsafeHash bytes = extractHash safe 
        case (packBytes bytes) :: PackedBytes 32 of
          PackedBytes32 w1 w2 w3 w4 -> pure (bytes,[w1,w2,w3,w4],Short.length bytes)
          _ -> putStrLn ("BAD ") >> pure( bytes,[],Short.length bytes)
        
