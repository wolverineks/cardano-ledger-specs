module Shrinkers where

import           Cardano.Ledger.Shelley.Crypto

import           Data.Foldable (toList)
import           Data.Map (Map)
import qualified Data.Map as M
import           Data.Sequence (Seq)
import qualified Data.Sequence as Seq
import           Data.Set (Set)
import qualified Data.Set as S
import           Lens.Micro ((^.))
import           Test.QuickCheck (shrinkIntegral, shrinkList)

import           Coin
import           Slot
import           Tx
import           TxData
import           Updates

shrinkTx
  :: Crypto crypto
  => Tx crypto
  -> [Tx crypto]
shrinkTx tx =
  Tx <$> shrinkTxBody (tx ^. body)
     <*> shrinkSet shrinkWitVKey (tx ^. witnessVKeySet)
     <*> shrinkMap shrinkScriptHash shrinkMultiSig (tx ^. witnessMSigMap)

shrinkTxBody :: TxBody crypto -> [TxBody crypto]
shrinkTxBody txBody =
  TxBody <$> shrinkSet shrinkTxIn (txBody ^. inputs)
         <*> shrinkList shrinkTxOut (txBody ^. outputs)
         <*> shrinkSeq shrinkDCert (txBody ^. certs)
         <*> shrinkWdrl (txBody ^. wdrls)
         <*> shrinkCoin (txBody ^. txfee)
         <*> shrinkSlot (txBody ^. ttl)
         <*> shrinkUpdate (txBody ^. txUpdate)

shrinkTxIn :: TxIn crypto -> [TxIn crypto]
shrinkTxIn = const []

shrinkTxOut :: TxOut crypto -> [TxOut crypto]
shrinkTxOut (TxOut addr coin) =
  TxOut addr <$> shrinkCoin coin

shrinkCoin :: Coin -> [Coin]
shrinkCoin (Coin x) = Coin <$> shrinkIntegral x

shrinkDCert :: DCert crypto -> [DCert crypto]
shrinkDCert = const []

shrinkWdrl :: Wdrl crypto -> [Wdrl crypto]
shrinkWdrl = shrinkMap shrinkRewardAcnt shrinkCoin

shrinkRewardAcnt :: RewardAcnt crypto -> [RewardAcnt crypto]
shrinkRewardAcnt = const []

shrinkSlot :: Slot -> [Slot]
shrinkSlot (Slot x) = Slot <$> shrinkIntegral x

shrinkUpdate :: Update crypto -> [Update crypto]
shrinkUpdate = const []

shrinkWitVKey :: WitVKey crypto -> [WitVKey crypto]
shrinkWitVKey = const []

shrinkScriptHash :: ScriptHash crypto -> [ScriptHash crypto]
shrinkScriptHash = const []

shrinkMultiSig :: MultiSig crypto -> [MultiSig crypto]
shrinkMultiSig = const []

shrinkSet :: Ord a => (a -> [a]) -> Set a -> [Set a]
shrinkSet f = (S.fromList <$>) . shrinkList f . toList

-- TODO can this be made more efficient?
shrinkSeq :: (a -> [a]) -> Seq a -> [Seq a]
shrinkSeq f = (Seq.fromList <$>) . shrinkList f . toList

shrinkMap
  :: Ord k
  => (k -> [k])
  -> (v -> [v])
  -> Map k v
  -> [Map k v]
shrinkMap shrinkK shrinkV
  = (M.fromList <$>) . shrinkList shrinkPair . M.toList
 where
  shrinkPair (x, y) =
    [ (x', y) | x' <- shrinkK x ]
    ++ [ (x, y') | y' <- shrinkV y ]
