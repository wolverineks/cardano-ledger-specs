{-# OPTIONS_GHC -Wno-orphans #-}
-- {-# OPTIONS_GHC -Wno-unused-imports #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE UnboxedTuples #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Test.Shelley.Spec.Ledger.CompactMap where

import Cardano.Binary
  ( ToCBOR(..),
    serialize',
    Encoding,
  )


import Test.Shelley.Spec.Ledger.Serialisation.Generators ()
import Test.Tasty.QuickCheck (Arbitrary (..), Gen, generate,vector)
import Shelley.Spec.Ledger.Tx (TxId(..),TxIn(..), TxOut)

import Cardano.Prelude (HeapWords(..))
import Shelley.Spec.Ledger.TxBody(TxOut(..))
import Shelley.Spec.Ledger.CompactAddr(CompactAddr(..))

import Cardano.Ledger.Crypto (StandardCrypto)
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

import Data.Primitive.Types(Prim(..), defaultSetByteArray#, defaultSetOffAddr# )
import Data.Primitive.PrimArray(PrimArray,primArrayFromList)

-- import Debug.Trace
-- import Test.Tasty
-- import Cardano.Binary.Deserialize(unsafeDeserialize)
-- import Shelley.Spec.Ledger.UTxO(UTxO(..))
-- import Test.Shelley.Spec.Ledger.ConcreteCryptoTypes (C,C_Crypto)
-- import Cardano.Ledger.Era(Crypto)
-- import qualified Data.ByteString as BS
-- import Data.ByteString.Conversion.From(FromByteString(parser),runParser)
-- import qualified Data.Vector.Generic as VGen
-- import qualified Data.Vector.Unboxed as VUnbox
-- import Data.Primitive.ByteArray


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

type Shelley = ShelleyEra StandardCrypto


main :: IO ()
main = do
  pairs <- generate (vector 100000 :: Gen [(TxIn StandardCrypto,TxOut Shelley)])
  let m = Map.fromList pairs
      withnewkeys = Map.mapKeys txInToTT m
      m2 = Map.map serialTxOut $ withnewkeys
      pm = toPar m2
      pm2 = toPar2 30 withnewkeys
      keys = Set.fromList $ map fst (take 100 pairs)
      norm = (heapWords m)
      compact = (heapWords(initMap m keys))
      par = (heapWords pm)
      par2 = (heapWords pm2)
      
  putStrLn (unlines ["Size "++show(Map.size m)++" entries "++show(Map.size m2)
                    ,"Normal  "++show norm++" words"
                    ,"Compact "++show compact++" words"
                    ,"Percent " ++show((fromIntegral compact / fromIntegral norm)*100 :: Double)
                    ,"Parallel "++show par++" words"
                    ,"Percent " ++show((fromIntegral par / fromIntegral norm)*100 :: Double)
                    ,"Parallel2 "++show par2++" words"
                    ,"Percent " ++show((fromIntegral par2 / fromIntegral norm)*100 :: Double)
                    ])


aa :: IO (Short.ShortByteString, [Word64],Int)
aa = do txin <- generate (arbitrary :: Gen (TxIn  StandardCrypto))
        let TxInCompact (TxId safe) _ = txin
            UnsafeHash bytes = extractHash safe 
        case (packBytes bytes) :: PackedBytes 32 of
          PackedBytes32 w1 w2 w3 w4 -> pure (bytes,[w1,w2,w3,w4],Short.length bytes)
          _ -> putStrLn ("BAD ") >> pure( bytes,[],Short.length bytes)

bb :: IO (Int, Int)
bb = do txouts <- generate (vector 10 :: Gen [(TxOut Shelley)])
        putStrLn (show(toCBOR txouts))
        putStrLn ""
        putStrLn (unlines (map (show . toCBOR) txouts))
        pure (heapWords (serialize' txouts), foldr (\ x ans -> heapWords (serialize' x) + ans) 0 txouts)

cc :: IO Encoding
cc = do txouts <- generate (vector 4 :: Gen [(TxOut Shelley)])
        pure(toCBOR txouts)

-- =======================================


serialTxOut:: TxOut Shelley -> ByteString
serialTxOut (TxOutCompact a b) = serialize' (a,b)

foo :: TxOut era -> Short.ShortByteString
foo (TxOutCompact (UnsafeCompactAddr bytes1) _) = bytes1

-- =========================================

ex2, ex3, ex4 :: Par2 Int Text
ex2 = toPar2 5 (Map.fromList [(i,pack(show i)) | i <- [0::Int ..21]])
ex3 = delete2 5 ex2
ex4 = insert2 12 (pack "99") ex3

instance Exp Text where
  plus x y = x <> y