{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}

module Test.Cardano.Ledger.ModelChain.Script where

import qualified Cardano.Ledger.Alonzo.Scripts as Alonzo
import qualified Cardano.Ledger.Crypto as C
import Cardano.Ledger.Keys
import Cardano.Ledger.ShelleyMA.Timelocks
import Cardano.Slotting.Slot hiding (at)
import Control.DeepSeq
import Data.Coerce (Coercible, coerce)
import Data.Kind (Type)
import qualified Data.Sequence.Strict as StrictSeq
import qualified GHC.Exts as GHC
import GHC.Generics
import Numeric.Natural (Natural)
import Test.Cardano.Ledger.ModelChain.FeatureSet

data ModelAddress (k :: TyScriptFeature) = ModelAddress
  { _modelAddres_pmt :: ModelCredential 'Payment k,
    _modelAddres_stk :: ModelCredential 'Staking k
  }
  deriving (Generic)

deriving instance Eq (ModelAddress k)

deriving instance Ord (ModelAddress k)

deriving instance Show (ModelAddress k)

instance GHC.IsString (ModelAddress k) where
  fromString s = ModelAddress (GHC.fromString s) (GHC.fromString s)

instance NFData (ModelAddress k)

-- | Polykinded HasKeyRole
class HasKeyRole' (a :: KeyRole -> k -> Type) where
  -- | General coercion of key roles.
  --
  --   The presence of this function is mostly to help the user realise where they
  --   are converting key roles.
  coerceKeyRole' ::
    a r x ->
    a r' x
  default coerceKeyRole' ::
    Coercible (a r x) (a r' x) =>
    a r x ->
    a r' x
  coerceKeyRole' = coerce

data ModelCredential (r :: KeyRole) (k :: TyScriptFeature) where
  ModelKeyHashObj :: String -> ModelCredential r k
  ModelScriptHashObj :: ModelPlutusScript -> ModelCredential r ('TyScriptFeature x 'True)

deriving instance Eq (ModelCredential r k)

deriving instance Ord (ModelCredential r k)

deriving instance Show (ModelCredential r k)

instance GHC.IsString (ModelCredential r k) where
  fromString = ModelKeyHashObj

instance HasKeyRole' ModelCredential

instance NFData (ModelCredential r k) where
  rnf = \case
    ModelKeyHashObj x -> rnf x
    ModelScriptHashObj x -> rnf x

liftModelAddress ::
  ModelAddress ('TyScriptFeature 'False 'False) ->
  ModelAddress a
liftModelAddress (ModelAddress a b) = ModelAddress (liftModelCredential a) (liftModelCredential b)

liftModelCredential ::
  ModelCredential r ('TyScriptFeature 'False 'False) ->
  ModelCredential r a
liftModelCredential (ModelKeyHashObj a) = ModelKeyHashObj a

liftModelAddress' ::
  ModelAddress a ->
  ModelAddress ('TyScriptFeature 'True 'True)
liftModelAddress' (ModelAddress a b) = ModelAddress (liftModelCredential' a) (liftModelCredential' b)

liftModelCredential' ::
  ModelCredential r a ->
  ModelCredential r ('TyScriptFeature 'True 'True)
liftModelCredential' (ModelKeyHashObj a) = ModelKeyHashObj a
liftModelCredential' (ModelScriptHashObj a) = ModelScriptHashObj a

data ModelScript (k :: TyScriptFeature) where
  ModelScript_Timelock :: ModelTimelock -> ModelScript ('TyScriptFeature 'True x)
  ModelScript_PlutusV1 :: ModelPlutusScript -> ModelScript ('TyScriptFeature x 'True)

instance NFData (ModelScript k) where
  rnf = \case
    ModelScript_Timelock a -> rnf a
    ModelScript_PlutusV1 a -> rnf a

deriving instance Eq (ModelScript k)

deriving instance Ord (ModelScript k)

deriving instance Show (ModelScript k)

data ModelPlutusScript
  = ModelPlutusScript_AlwaysSucceeds Natural
  | ModelPlutusScript_AlwaysFails Natural
  deriving (Eq, Ord, Show, Generic)

instance NFData ModelPlutusScript

modelScriptNeededSigs :: ModelTimelock -> [ModelCredential 'Witness ('TyScriptFeature 'False 'False)]
modelScriptNeededSigs = go
  where
    go = \case
      ModelTimelock_Signature ma -> [ma]
      ModelTimelock_AllOf xs -> go =<< xs
      ModelTimelock_AnyOf xs -> go =<< take 1 xs
      ModelTimelock_MOfN n xs -> go =<< take n xs
      ModelTimelock_TimeStart _ -> []
      ModelTimelock_TimeExpire _ -> []

-- modelScriptNeededSigs (ModelScript_PlutusV1 {}) = []
-- TODO: start/expire are somewhat irritating since absolute slot numbers aren't
-- visible in the model; it should probably be refactored to use epochs + slot
-- in epoch
data ModelTimelock
  = ModelTimelock_Signature (ModelCredential 'Witness ('TyScriptFeature 'False 'False))
  | ModelTimelock_AllOf [ModelTimelock]
  | ModelTimelock_AnyOf [ModelTimelock]
  | ModelTimelock_MOfN Int [ModelTimelock] -- Note that the Int may be negative in which case (MOfN -2 [..]) is always True
  | ModelTimelock_TimeStart SlotNo -- The start time
  | ModelTimelock_TimeExpire SlotNo -- The time it expires
  deriving (Eq, Ord, Show, Generic)

instance NFData ModelTimelock

elaborateModelTimelock ::
  forall crypto m.
  (C.Crypto crypto, Applicative m) =>
  (ModelCredential 'Witness ('TyScriptFeature 'False 'False) -> m (KeyHash 'Witness crypto)) ->
  ModelTimelock ->
  m (Timelock crypto)
elaborateModelTimelock f = go
  where
    go :: ModelTimelock -> m (Timelock crypto)
    go = \case
      ModelTimelock_Signature maddr -> RequireSignature <$> f maddr
      ModelTimelock_AllOf xs -> RequireAllOf . StrictSeq.fromList <$> traverse go xs
      ModelTimelock_AnyOf xs -> RequireAnyOf . StrictSeq.fromList <$> traverse go xs
      ModelTimelock_MOfN m xs -> RequireMOf m . StrictSeq.fromList <$> traverse go xs
      ModelTimelock_TimeStart slotNo -> pure $ RequireTimeStart slotNo
      ModelTimelock_TimeExpire slotNo -> pure $ RequireTimeExpire slotNo

elaborateModelScript ::
  ModelPlutusScript ->
  Alonzo.Script era
elaborateModelScript = \case
  ModelPlutusScript_AlwaysSucceeds n -> Alonzo.alwaysSucceeds n
  ModelPlutusScript_AlwaysFails n -> Alonzo.alwaysFails n
