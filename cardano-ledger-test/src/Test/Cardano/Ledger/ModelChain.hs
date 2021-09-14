{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE EmptyDataDeriving #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Test.Cardano.Ledger.ModelChain where

import Cardano.Ledger.Alonzo.Scripts (ExUnits (..))
import Cardano.Ledger.Alonzo.Tx (IsValid (..))
import Cardano.Ledger.BaseTypes
import Cardano.Ledger.Coin
import qualified Cardano.Ledger.Crypto as C
import Cardano.Ledger.Keys (KeyRole (..))
import Cardano.Ledger.Mary.Value (AssetName, PolicyID (..))
import qualified Cardano.Ledger.Mary.Value
import qualified Cardano.Ledger.Val as Val
import Cardano.Slotting.Slot hiding (at)
import Control.Applicative
import Control.Arrow ((&&&))
import Control.DeepSeq
import Control.Lens
import Control.Monad
import qualified Control.Monad.State.Strict as State
import Data.Bifunctor (first)
import Data.Bool (bool)
import Data.Foldable (fold)
import Data.Group
import Data.Kind (Type)
import qualified Data.List as List
import qualified Data.Map as Map
import qualified Data.Map.Merge.Strict as Map
import Data.Maybe (mapMaybe)
import Data.Proxy
import Data.Semigroup (Sum (..))
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Traversable
import qualified GHC.Exts as GHC
import GHC.Generics (Generic)
import qualified PlutusTx
import Quiet (Quiet (..))
import Shelley.Spec.Ledger.STS.EraMapping ()
import Test.Cardano.Ledger.ModelChain.Address
import Test.Cardano.Ledger.ModelChain.FeatureSet
import Test.Cardano.Ledger.ModelChain.Script
import Test.Cardano.Ledger.ModelChain.Value

class Val.Val val => ValueFromList val crypto | val -> crypto where
  valueFromList :: Integer -> [(PolicyID crypto, AssetName, Integer)] -> val

  insert :: (Integer -> Integer -> Integer) -> PolicyID crypto -> AssetName -> Integer -> val -> val

  gettriples :: val -> (Integer, [(PolicyID crypto, AssetName, Integer)])

instance C.Crypto crypto => ValueFromList (Cardano.Ledger.Mary.Value.Value crypto) crypto where
  valueFromList = Cardano.Ledger.Mary.Value.valueFromList

  insert = Cardano.Ledger.Mary.Value.insert

  gettriples (Cardano.Ledger.Mary.Value.Value c m1) = (c, triples)
    where
      triples =
        [ (policyId, aname, amount)
          | (policyId, m2) <- Map.toList m1,
            (aname, amount) <- Map.toList m2
        ]

-- TODO: this is a bit overconstrained, we probably want a more constraints
-- based approach using ValueFromList
type family ElaborateValueType (valF :: TyValueExpected) crypto :: Type where
  ElaborateValueType 'ExpectAdaOnly _ = Coin
  ElaborateValueType 'ExpectAnyOutput crypto = Cardano.Ledger.Mary.Value.Value crypto

instance RequiredFeatures ModelTxOut where
  filterFeatures tag@(FeatureTag v _) (ModelTxOut addr qty dat) =
    hasKnownValueFeature v $
      ModelTxOut
        <$> filterModelAddress tag addr
        <*> (filterFeatures tag =<< filterModelValue qty)
        <*> (filterSupportsPlutus tag dat)

filterModelValueVars ::
  forall a b c d.
  (KnownRequiredFeatures c, KnownValueFeature d) =>
  ModelValueVars a b ->
  Maybe (ModelValueVars c d)
filterModelValueVars (ModelValue_Reward x) = ModelValue_Reward <$> filterModelCredential (reifyRequiredFeatures (Proxy @c)) x
filterModelValueVars (ModelValue_MA ys) = do
  Refl <- reifyExpectAnyOutput (reifyValueFeature (Proxy @d))
  Refl <- reifyExpectAnyOutput (reifyValueFeature (Proxy @(ValueFeature c)))

  ModelValue_MA <$> _1 filterModelScript ys

filterModelScript ::
  forall b a.
  KnownScriptFeature b =>
  ModelScript a ->
  Maybe (ModelScript b)
filterModelScript = \case
  ModelScript_Timelock t -> case reifyScriptFeature (Proxy @b) of
    ScriptFeatureTag_None -> Nothing
    ScriptFeatureTag_Simple -> Just $ ModelScript_Timelock t
    ScriptFeatureTag_PlutusV1 -> Just $ ModelScript_Timelock t
  ModelScript_PlutusV1 t -> case reifyScriptFeature (Proxy @b) of
    ScriptFeatureTag_None -> Nothing
    ScriptFeatureTag_Simple -> Nothing
    ScriptFeatureTag_PlutusV1 -> Just $ ModelScript_PlutusV1 t

-- change the "expected return type" of a ModelValue
filterModelValue ::
  forall a b c.
  (KnownValueFeature b, KnownRequiredFeatures c) =>
  ModelValue a c ->
  Maybe (ModelValue b c)
filterModelValue = \case
  ModelValue x -> ModelValue <$> traverse filterModelValueVars x

instance KnownValueFeature v => RequiredFeatures (ModelValue v) where
  filterFeatures tag (ModelValue val) = ModelValue <$> traverse (hasKnownRequiredFeatures tag filterModelValueVars) val

instance RequiredFeatures ModelTx where
  filterFeatures :: forall a b. KnownRequiredFeatures a => FeatureTag b -> ModelTx a -> Maybe (ModelTx b)
  filterFeatures tag@(FeatureTag _ sf) (ModelTx ins outs fee dcert wdrl g cins valid rdmr wits) =
    ModelTx ins
      <$> (traverse . traverse) (filterFeatures tag) outs
      <*> (filterFeatures tag fee)
      <*> traverse (filterFeatures tag) dcert
      <*> fmap Map.fromList (for (Map.toList wdrl) $ \(k, v) -> (,) <$> filterModelCredential tag k <*> filterFeatures tag v)
      <*> ( case g of
              NoMintSupport () -> case tag of
                FeatureTag ValueFeatureTag_AdaOnly _ -> pure $ NoMintSupport ()
                FeatureTag ValueFeatureTag_AnyOutput _ -> pure (SupportsMint . ModelValue . ModelValue_Inject $ Coin 0)
              SupportsMint g' -> case tag of
                FeatureTag ValueFeatureTag_AdaOnly _ | g' == ModelValue (ModelValue_Inject $ Val.zero) -> pure $ NoMintSupport ()
                FeatureTag ValueFeatureTag_AdaOnly _ -> Nothing
                FeatureTag ValueFeatureTag_AnyOutput _ -> SupportsMint <$> filterFeatures tag g'
          )
      <*> ( let setNotEmpty :: Set x -> Maybe (Set x)
                setNotEmpty x
                  | Set.null x = Nothing
                  | otherwise = Just x
             in (fmap (mapSupportsPlutus fold) $ filterSupportsPlutus tag $ mapSupportsPlutus setNotEmpty cins)
          )
      <*> filterModelValidity sf valid
      <*> fmap Map.fromList ((traverse . _1) (filterFeatures tag) $ Map.toList rdmr)
      <*> pure wits

filterModelAddress ::
  FeatureTag b ->
  ModelAddress a ->
  Maybe (ModelAddress (ScriptFeature b))
filterModelAddress tag (ModelAddress pmt stk) =
  ModelAddress
    <$> filterModelCredential tag pmt
    <*> filterModelCredential tag stk

filterModelCredential ::
  FeatureTag b ->
  ModelCredential r a ->
  Maybe (ModelCredential r' (ScriptFeature b))
filterModelCredential (FeatureTag _ s) = \case
  ModelKeyHashObj a -> Just (ModelKeyHashObj a)
  ModelScriptHashObj a -> case s of
    ScriptFeatureTag_None -> Nothing
    ScriptFeatureTag_Simple -> Nothing
    ScriptFeatureTag_PlutusV1 -> Just (ModelScriptHashObj a)

filterModelValidity ::
  forall a b.
  ScriptFeatureTag b ->
  IfSupportsPlutus () IsValid a ->
  Maybe (IfSupportsPlutus () IsValid b)
filterModelValidity sf = hasKnownScriptFeature sf $ \case
  NoPlutusSupport () -> Just $ ifSupportsPlutus sf () (IsValid True)
  SupportsPlutus v@(IsValid True) -> Just $ ifSupportsPlutus sf () v
  SupportsPlutus v@(IsValid False) -> bitraverseSupportsPlutus id id $ ifSupportsPlutus sf Nothing (Just v)

instance RequiredFeatures ModelBlock where
  filterFeatures tag (ModelBlock slotNo txns) =
    ModelBlock slotNo
      <$> traverse (filterFeatures tag) txns

instance RequiredFeatures ModelEpoch where
  filterFeatures tag (ModelEpoch blocks x) =
    ModelEpoch
      <$> traverse (filterFeatures tag) blocks
      <*> pure x

type ModelMA era = (ModelScript era, AssetName)

data ModelValueVars era (k :: TyValueExpected) where
  ModelValue_Reward :: ModelCredential 'Staking (ScriptFeature era) -> ModelValueVars era k
  ModelValue_MA ::
    ('ExpectAnyOutput ~ ValueFeature era) =>
    ModelMA (ScriptFeature era) ->
    ModelValueVars era 'ExpectAnyOutput

instance NFData (ModelValueVars era k) where
  rnf = \case
    ModelValue_Reward a -> rnf a
    ModelValue_MA a -> rnf a

deriving instance Show (ModelValueVars era valF)

deriving instance Eq (ModelValueVars era valF)

deriving instance Ord (ModelValueVars era valF)

newtype ModelValue k era = ModelValue {unModelValue :: ModelValueF (ModelValueVars era k)}
  deriving (Eq, Ord, Generic, NFData)
  deriving (Show) via Quiet (ModelValue k era)

modelValueInject :: Coin -> ModelValue k era
modelValueInject = ModelValue . ModelValue_Inject

instance Semigroup (ModelValue k era) where
  ModelValue x <> ModelValue y = ModelValue (x `ModelValue_Add` y)

instance Monoid (ModelValue k era) where
  mempty = modelValueInject $ Coin 0

data ModelTxOut era = ModelTxOut
  { _mtxo_address :: !(ModelAddress (ScriptFeature era)),
    _mtxo_value :: !(ModelValue (ValueFeature era) era),
    _mtxo_data :: !(IfSupportsPlutus () (Maybe PlutusTx.Data) (ScriptFeature era))
  }
  deriving (Eq, Ord, Generic)
  deriving (Show) via Quiet (ModelTxOut era)

instance NFData (ModelTxOut era)

-- | Convenience function to create a spendable ModelTxOut
modelTxOut :: forall era. KnownScriptFeature (ScriptFeature era) => ModelAddress (ScriptFeature era) -> ModelValue (ValueFeature era) era -> ModelTxOut era
modelTxOut a v = ModelTxOut a v dh
  where
    dh = ifSupportsPlutus (Proxy :: Proxy (ScriptFeature era)) () $
      case _modelAddress_pmt a of
        ModelKeyHashObj _ -> Nothing
        ModelScriptHashObj _ -> Just $ PlutusTx.I 42

modelTxOut_address :: forall era. Lens' (ModelTxOut era) (ModelAddress (ScriptFeature era))
modelTxOut_address = lens _mtxo_address (\s b -> s {_mtxo_address = b})
{-# INLINE modelTxOut_address #-}

modelTxOut_value :: Lens' (ModelTxOut era) (ModelValue (ValueFeature era) era)
modelTxOut_value = lens _mtxo_value (\s b -> s {_mtxo_value = b})
{-# INLINE modelTxOut_value #-}

modelTxOut_data :: Lens' (ModelTxOut era) (IfSupportsPlutus () (Maybe PlutusTx.Data) (ScriptFeature era))
modelTxOut_data = lens _mtxo_data (\s b -> s {_mtxo_data = b})
{-# INLINE modelTxOut_data #-}

newtype ModelUTxOId = ModelUTxOId {unModelUTxOId :: Integer}
  deriving (Eq, Ord, Num, Enum, Generic, NFData)

instance Show ModelUTxOId where
  showsPrec n (ModelUTxOId x) = showsPrec n x

data ModelScriptPurpose era where
  ModelScriptPurpose_Minting :: ModelScript (ScriptFeature era) -> ModelScriptPurpose era
  ModelScriptPurpose_Spending :: ModelUTxOId -> ModelScriptPurpose era
  ModelScriptPurpose_Rewarding :: ModelCredential 'Staking (ScriptFeature era) -> ModelScriptPurpose era
  ModelScriptPurpose_Certifying :: (ModelDCert era) -> ModelScriptPurpose era

deriving instance Eq (ModelScriptPurpose era)

deriving instance Ord (ModelScriptPurpose era)

deriving instance Show (ModelScriptPurpose era)

instance NFData (ModelScriptPurpose era) where
  rnf = rwhnf

instance RequiredFeatures ModelScriptPurpose where
  filterFeatures tag@(FeatureTag _ sf) = \case
    ModelScriptPurpose_Minting policy ->
      ModelScriptPurpose_Minting
        <$> hasKnownScriptFeature sf (filterModelScript policy)
    ModelScriptPurpose_Spending uid -> ModelScriptPurpose_Spending <$> pure uid
    ModelScriptPurpose_Rewarding ra -> ModelScriptPurpose_Rewarding <$> filterModelCredential tag ra
    ModelScriptPurpose_Certifying mdc -> ModelScriptPurpose_Certifying <$> filterFeatures tag mdc

data ModelTx (era :: FeatureSet) = ModelTx
  { _mtxInputs :: !(Set ModelUTxOId),
    _mtxOutputs :: ![(ModelUTxOId, ModelTxOut era)],
    _mtxFee :: !(ModelValue 'ExpectAdaOnly era),
    _mtxDCert :: ![ModelDCert era],
    _mtxWdrl :: !(Map.Map (ModelCredential 'Staking (ScriptFeature era)) (ModelValue 'ExpectAdaOnly era)),
    _mtxMint :: !(IfSupportsMint () (ModelValue (ValueFeature era) era) (ValueFeature era)),
    _mtxCollateral :: !(IfSupportsPlutus () (Set ModelUTxOId) (ScriptFeature era)),
    _mtxValidity :: !(IfSupportsPlutus () IsValid (ScriptFeature era)),
    _mtxRedeemers :: !(Map.Map (ModelScriptPurpose era) (PlutusTx.Data, ExUnits)),
    _mtxWitnessSigs :: !(Set (ModelCredential 'Witness ('TyScriptFeature 'False 'False)))
  }
  deriving (Show, Generic)

instance NFData (ModelTx era)

class HasModelTx era a | a -> era where
  modelTxs :: Traversal' a (ModelTx era)

instance HasModelTx era (ModelTx era) where
  modelTxs = id
  {-# INLINE modelTxs #-}

instance HasModelDCert era (ModelTx era) where
  modelDCerts = modelTx_dCert . traverse
  {-# INLINE modelDCerts #-}

modelTx_inputs :: Lens' (ModelTx era) (Set ModelUTxOId)
modelTx_inputs = lens _mtxInputs (\s b -> s {_mtxInputs = b})
{-# INLINE modelTx_inputs #-}

modelTx_outputs :: Lens' (ModelTx era) [(ModelUTxOId, ModelTxOut era)]
modelTx_outputs = lens _mtxOutputs (\s b -> s {_mtxOutputs = b})
{-# INLINE modelTx_outputs #-}

-- focus on a specified output with the given id;
modelTx_outputAt :: ModelUTxOId -> Lens' (ModelTx era) (Maybe (ModelTxOut era))
modelTx_outputAt k = modelTx_outputs . lens (List.lookup k) (flip f)
  where
    f :: forall a. Maybe a -> [(ModelUTxOId, a)] -> [(ModelUTxOId, a)]
    f = \case
      Nothing ->
        let g [] = []
            g ((k', v) : rest) = if k == k' then rest else (k', v) : g rest
         in g
      Just v' ->
        let h [] = [(k, v')]
            h ((k', v) : rest) = if k == k' then (k, v') : rest else (k', v) : h rest
         in h
{-# INLINE modelTx_outputAt #-}

modelTx_fee :: Lens' (ModelTx era) (ModelValue 'ExpectAdaOnly era)
modelTx_fee = lens _mtxFee (\s b -> s {_mtxFee = b})
{-# INLINE modelTx_fee #-}

modelTx_dCert :: Lens' (ModelTx era) [ModelDCert era]
modelTx_dCert = lens _mtxDCert (\s b -> s {_mtxDCert = b})
{-# INLINE modelTx_dCert #-}

modelTx_wdrl :: Lens' (ModelTx era) (Map.Map (ModelCredential 'Staking (ScriptFeature era)) (ModelValue 'ExpectAdaOnly era))
modelTx_wdrl = lens _mtxWdrl (\s b -> s {_mtxWdrl = b})
{-# INLINE modelTx_wdrl #-}

modelTx_mint :: Lens' (ModelTx era) (IfSupportsMint () (ModelValue (ValueFeature era) era) (ValueFeature era))
modelTx_mint = lens _mtxMint (\s b -> s {_mtxMint = b})
{-# INLINE modelTx_mint #-}

modelTx_collateral :: Lens' (ModelTx era) (IfSupportsPlutus () (Set ModelUTxOId) (ScriptFeature era))
modelTx_collateral = lens _mtxCollateral (\s b -> s {_mtxCollateral = b})
{-# INLINE modelTx_collateral #-}

modelTx_validity :: Lens' (ModelTx era) (IfSupportsPlutus () IsValid (ScriptFeature era))
modelTx_validity = lens _mtxValidity (\s b -> s {_mtxValidity = b})
{-# INLINE modelTx_validity #-}

modelTx_redeemers :: Lens' (ModelTx era) (Map.Map (ModelScriptPurpose era) (PlutusTx.Data, ExUnits))
modelTx_redeemers = lens _mtxRedeemers (\s b -> s {_mtxRedeemers = b})
{-# INLINE modelTx_redeemers #-}

modelTx_witnessSigs :: Lens' (ModelTx era) (Set (ModelCredential 'Witness ('TyScriptFeature 'False 'False)))
modelTx_witnessSigs = lens _mtxWitnessSigs (\s b -> s {_mtxWitnessSigs = b})
{-# INLINE modelTx_witnessSigs #-}

-- | helper to produce a "blank" ModelTx with most fields set to a reasonable
-- "default"
modelTx :: forall (era :: FeatureSet). KnownRequiredFeatures era => ModelTx era
modelTx =
  ModelTx
    { _mtxInputs = Set.empty,
      _mtxOutputs = [],
      _mtxFee = ModelValue $ ModelValue_Inject $ Coin 0,
      _mtxDCert = [],
      _mtxWdrl = Map.empty,
      _mtxMint = case reifyRequiredFeatures (Proxy :: Proxy era) of
        FeatureTag v _ -> case v of
          ValueFeatureTag_AdaOnly -> NoMintSupport ()
          ValueFeatureTag_AnyOutput -> SupportsMint $ ModelValue $ ModelValue_Inject $ Coin 0,
      _mtxCollateral = mapSupportsPlutus (const Set.empty) $ reifySupportsPlutus (Proxy :: Proxy (ScriptFeature era)),
      _mtxValidity = mapSupportsPlutus (const $ IsValid True) $ reifySupportsPlutus (Proxy :: Proxy (ScriptFeature era)),
      _mtxRedeemers = Map.empty,
      _mtxWitnessSigs = Set.empty
    }

-- TODO: there's some extra degrees of freedom hidden in this function, they
-- should be exposed
-- - redeemer value/exunits
-- - how timelocks are signed (which n of m)
witnessModelTx ::
  forall (era :: FeatureSet). ModelTx era -> ModelLedger era -> ModelTx era
witnessModelTx mtx ml =
  let mkRdmr :: ModelScript (ScriptFeature era) -> ModelScriptPurpose era -> (PlutusTx.Data, ExUnits)
      mkRdmr _ _ = (PlutusTx.I 2, ExUnits 1 1)

      lookupOutput :: ModelUTxOId -> Maybe (ModelUTxOId, ModelCredential 'Payment (ScriptFeature era))
      lookupOutput ui = (,) ui <$> preview (modelLedger_utxos . at ui . _Just . modelTxOut_address @era . modelAddress_pmt) ml

      matchDCert :: ModelDCert era -> Maybe (ModelDCert era, ModelCredential 'Staking (ScriptFeature era))
      matchDCert cert = case cert of
        ModelDelegate (ModelDelegation cred _) -> Just (cert, cred)
        ModelDeRegisterStake cred -> Just (cert, cred)
        _ -> Nothing

      matchPoolCert :: ModelDCert era -> [ModelCredential 'Witness ('TyScriptFeature 'False 'False)]
      matchPoolCert = \case
        ModelRegisterPool mpp -> [coerceKeyRole' $ unModelPoolId $ _mppId mpp] <> fmap coerceKeyRole' (_mppOwners mpp)
        _ -> []

      witnessMint :: ModelValueVars era (ValueFeature era) -> (Set (ModelCredential 'Witness ('TyScriptFeature 'False 'False)), Map.Map (ModelScriptPurpose era) (PlutusTx.Data, ExUnits))
      witnessMint = \case
        ModelValue_Reward _ -> mempty
        ModelValue_MA (modelPolicy, _) -> case modelPolicy of
          ModelScript_Timelock tl -> foldMap (\wit -> (Set.singleton wit, Map.empty)) (modelScriptNeededSigs tl)
          ModelScript_PlutusV1 _s1 ->
            let sp = ModelScriptPurpose_Minting modelPolicy
             in (Set.empty, Map.singleton sp (mkRdmr modelPolicy sp))

      witnessCredential ::
        ModelScriptPurpose era ->
        ModelCredential k (ScriptFeature era) ->
        ( Set (ModelCredential 'Witness ('TyScriptFeature 'False 'False)),
          Map.Map (ModelScriptPurpose era) (PlutusTx.Data, ExUnits)
        )
      witnessCredential msp = \case
        ModelKeyHashObj k -> (Set.singleton (ModelKeyHashObj k), Map.empty)
        ModelScriptHashObj s -> (Set.empty, Map.singleton msp (mkRdmr (ModelScript_PlutusV1 s) msp))

      witnessSigs :: Set (ModelCredential 'Witness ('TyScriptFeature 'False 'False))
      redeemers :: Map.Map (ModelScriptPurpose era) (PlutusTx.Data, ExUnits)
      (witnessSigs, redeemers) =
        foldMap (uncurry witnessCredential . first ModelScriptPurpose_Spending) (mapMaybe lookupOutput $ Set.toList $ _mtxInputs mtx)
          <> foldMap (uncurry witnessCredential . first ModelScriptPurpose_Certifying) (mapMaybe matchDCert $ _mtxDCert mtx)
          <> foldMap (\c -> (Set.singleton c, Map.empty)) (matchPoolCert =<< _mtxDCert mtx)
          <> foldMap (uncurry witnessCredential . (ModelScriptPurpose_Rewarding &&& id)) (Map.keys $ _mtxWdrl mtx)
          <> fromSupportsMint mempty (foldMap witnessMint . unModelValue) (_mtxMint mtx)
          <> fromSupportsPlutus
            mempty
            (foldMap (uncurry witnessCredential . first ModelScriptPurpose_Spending) . mapMaybe lookupOutput . Set.toList)
            (_mtxCollateral mtx)
   in mtx
        { _mtxWitnessSigs = witnessSigs,
          _mtxRedeemers = redeemers
        }

data ModelBlock era = ModelBlock
  { _modelBlock_slot :: SlotNo,
    _modelBlock_txSeq :: [ModelTx era]
  }
  deriving (Show, Generic)

instance NFData (ModelBlock era)

instance HasModelDCert era (ModelBlock era) where
  modelDCerts = modelBlock_txSeq . traverse . modelDCerts
  {-# INLINE modelDCerts #-}

instance HasModelTx era (ModelBlock era) where
  modelTxs = modelBlock_txSeq . traverse
  {-# INLINE modelTxs #-}

modelBlock_slot :: Lens' (ModelBlock era) SlotNo
modelBlock_slot = lens _modelBlock_slot (\s b -> s {_modelBlock_slot = b})
{-# INLINE modelBlock_slot #-}

modelBlock_txSeq :: Lens' (ModelBlock era) [ModelTx era]
modelBlock_txSeq = lens _modelBlock_txSeq (\s b -> s {_modelBlock_txSeq = b})
{-# INLINE modelBlock_txSeq #-}

newtype ModelPoolId = ModelPoolId {unModelPoolId :: ModelCredential 'StakePool ('TyScriptFeature 'False 'False)}
  deriving (Eq, Ord, GHC.IsString, NFData)

instance Show ModelPoolId where
  showsPrec n (ModelPoolId x) = showsPrec n x

newtype ModelBlocksMade = ModelBlocksMade {unModelBlocksMade :: Map.Map ModelPoolId Rational}
  deriving (Generic, NFData)
  deriving (Show) via Quiet ModelBlocksMade
  deriving (Semigroup) via GrpMap ModelPoolId (Sum Rational)
  deriving (Monoid) via GrpMap ModelPoolId (Sum Rational)

_ModelBlocksMade :: Iso' ModelBlocksMade (Map.Map ModelPoolId Rational)
_ModelBlocksMade = iso unModelBlocksMade ModelBlocksMade

repartition :: forall a b t. (Traversable t, Integral a, RealFrac b) => a -> t b -> t a
repartition total weights = State.evalState (traverse step weights) (0 :: b)
  where
    step weight = do
      err <- State.get
      let fracValue :: b
          fracValue = err + fromIntegral total * weight
          value :: a
          value = round fracValue
      State.put (fracValue - fromIntegral value)
      pure value

-- TODO: explicit Epoch.
data ModelEpoch era = ModelEpoch
  { _modelEpoch_blocks :: [ModelBlock era],
    _modelEpoch_blocksMade :: ModelBlocksMade
  }
  deriving (Show, Generic)

instance NFData (ModelEpoch era)

instance HasModelDCert era (ModelEpoch era) where
  modelDCerts = modelEpoch_blocks . traverse . modelDCerts
  {-# INLINE modelDCerts #-}

instance HasModelTx era (ModelEpoch era) where
  modelTxs = modelEpoch_blocks . traverse . modelTxs
  {-# INLINE modelTxs #-}

modelEpoch_blocks :: Lens' (ModelEpoch era) [ModelBlock era]
modelEpoch_blocks = lens _modelEpoch_blocks (\s b -> s {_modelEpoch_blocks = b})
{-# INLINE modelEpoch_blocks #-}

modelEpoch_blocksMade :: Lens' (ModelEpoch era) ModelBlocksMade
modelEpoch_blocksMade = lens _modelEpoch_blocksMade (\s b -> s {_modelEpoch_blocksMade = b})
{-# INLINE modelEpoch_blocksMade #-}

data ModelDelegation era = ModelDelegation
  { _mdDelegator :: !(ModelCredential 'Staking (ScriptFeature era)),
    _mdDelegatee :: !ModelPoolId
  }
  deriving (Generic, Eq, Ord)
  deriving (Show) via Quiet (ModelDelegation era)

modelDelegation_delegator :: Lens' (ModelDelegation era) (ModelCredential 'Staking (ScriptFeature era))
modelDelegation_delegator a2fb s = (\b -> s {_mdDelegator = b}) <$> a2fb (_mdDelegator s)
{-# INLINE modelDelegation_delegator #-}

modelDelegation_delegatee :: Lens' (ModelDelegation era) ModelPoolId
modelDelegation_delegatee a2fb s = (\b -> s {_mdDelegatee = b}) <$> a2fb (_mdDelegatee s)
{-# INLINE modelDelegation_delegatee #-}

instance NFData (ModelDelegation era)

instance RequiredFeatures ModelDelegation where
  filterFeatures tag (ModelDelegation a b) =
    ModelDelegation
      <$> filterModelCredential tag a
      <*> pure b

data ModelPoolParams era = ModelPoolParams
  { _mppId :: !ModelPoolId,
    _mppVrm :: !(ModelCredential 'StakePool ('TyScriptFeature 'False 'False)),
    _mppPledge :: !Coin,
    _mppCost :: !Coin,
    _mppMargin :: !UnitInterval,
    _mppRAcnt :: !(ModelCredential 'Staking (ScriptFeature era)),
    _mppOwners :: ![ModelCredential 'Staking ('TyScriptFeature 'False 'False)]
  }
  deriving (Show, Eq, Ord, Generic)

instance NFData (ModelPoolParams era)

instance RequiredFeatures ModelPoolParams where
  filterFeatures tag (ModelPoolParams poolId poolVrf pledge cost margin rAcnt owners) =
    ModelPoolParams poolId poolVrf pledge cost margin
      <$> filterModelCredential tag rAcnt
      <*> pure owners

-- ignores genesis delegation details.
data ModelDCert era
  = ModelRegisterStake (ModelCredential 'Staking (ScriptFeature era))
  | ModelDeRegisterStake (ModelCredential 'Staking (ScriptFeature era))
  | ModelDelegate (ModelDelegation era)
  | ModelRegisterPool (ModelPoolParams era)
  | ModelRetirePool ModelPoolId EpochNo
  deriving (Show, Generic, Eq, Ord)

instance NFData (ModelDCert era)

_ModelRegisterStake :: Prism' (ModelDCert era) (ModelCredential 'Staking (ScriptFeature era))
_ModelRegisterStake = prism ModelRegisterStake $ \case
  ModelRegisterStake x -> Right x
  x -> Left x
{-# INLINE _ModelRegisterStake #-}

_ModelDeRegisterStake :: Prism' (ModelDCert era) (ModelCredential 'Staking (ScriptFeature era))
_ModelDeRegisterStake = prism ModelDeRegisterStake $ \case
  ModelDeRegisterStake x -> Right x
  x -> Left x
{-# INLINE _ModelDeRegisterStake #-}

_ModelDelegate :: Prism' (ModelDCert era) (ModelDelegation era)
_ModelDelegate = prism ModelDelegate $ \case
  ModelDelegate x -> Right x
  x -> Left x
{-# INLINE _ModelDelegate #-}

_ModelRegisterPool :: Prism' (ModelDCert era) (ModelPoolParams era)
_ModelRegisterPool = prism ModelRegisterPool $ \case
  ModelRegisterPool x -> Right x
  x -> Left x
{-# INLINE _ModelRegisterPool #-}

_ModelRetirePool :: Prism' (ModelDCert era) (ModelPoolId, EpochNo)
_ModelRetirePool = prism (uncurry ModelRetirePool) $ \case
  ModelRetirePool x y -> Right (x, y)
  x -> Left x
{-# INLINE _ModelRetirePool #-}

class HasModelDCert era a | a -> era where
  modelDCerts :: Traversal' a (ModelDCert era)

instance HasModelDCert era (ModelDCert era) where
  modelDCerts = id
  {-# INLINE modelDCerts #-}

instance RequiredFeatures ModelDCert where
  filterFeatures tag = \case
    ModelRegisterStake a -> ModelRegisterStake <$> filterModelCredential tag a
    ModelDeRegisterStake a -> ModelDeRegisterStake <$> filterModelCredential tag a
    ModelDelegate a -> ModelDelegate <$> filterFeatures tag a
    ModelRegisterPool a -> ModelRegisterPool <$> filterFeatures tag a
    ModelRetirePool a b -> pure $ ModelRetirePool a b

-- TODO: | ModelMIRCert Shelley.MIRPot (Map.Map ModelAddress DeltaCoin)

data ModelPredicateFailure era
  = ModelValueNotConservedUTxO
      !(ModelValue (ValueFeature era) era)
      -- ^ the Coin consumed by this transaction
      !(ModelValue (ValueFeature era) era)
      -- ^ the Coin produced by this transaction

type ModelLedgerInputs era =
  ( [(ModelUTxOId, ModelAddress (ScriptFeature era), Coin)],
    [ModelEpoch era]
  )

data ModelSnapshot era = ModelSnapshot
  { _modelSnapshot_stake :: Map.Map (ModelCredential 'Staking (ScriptFeature era)) Coin,
    _modelSnapshot_delegations :: Map.Map (ModelCredential 'Staking (ScriptFeature era)) ModelPoolId,
    _modelSnapshot_pools :: Map.Map ModelPoolId (ModelPoolParams era)
  }
  deriving (Eq, Generic)
  deriving (Show) via Quiet (ModelSnapshot era)

instance NFData (ModelSnapshot era)

emptyModelSnapshot :: ModelSnapshot era
emptyModelSnapshot = ModelSnapshot Map.empty Map.empty Map.empty

modelSnapshot_stake :: Lens' (ModelSnapshot era) (Map.Map (ModelCredential 'Staking (ScriptFeature era)) Coin)
modelSnapshot_stake a2fb s = (\b -> s {_modelSnapshot_stake = b}) <$> a2fb (_modelSnapshot_stake s)
{-# INLINE modelSnapshot_stake #-}

modelSnapshot_delegations :: Lens' (ModelSnapshot era) (Map.Map (ModelCredential 'Staking (ScriptFeature era)) ModelPoolId)
modelSnapshot_delegations a2fb s = (\b -> s {_modelSnapshot_delegations = b}) <$> a2fb (_modelSnapshot_delegations s)
{-# INLINE modelSnapshot_delegations #-}

modelSnapshot_pools :: Lens' (ModelSnapshot era) (Map.Map ModelPoolId (ModelPoolParams era))
modelSnapshot_pools a2fb s = (\b -> s {_modelSnapshot_pools = b}) <$> a2fb (_modelSnapshot_pools s)
{-# INLINE modelSnapshot_pools #-}

data ModelUtxoMap era = ModelUtxoMap
  { _modelUtxoMap_utxos :: !(Map.Map ModelUTxOId (Coin, ModelTxOut era)),
    _modelUtxoMap_stake :: !(GrpMap (ModelCredential 'Staking (ScriptFeature era)) Coin),
    _modelUtxoMap_collateralUtxos :: !(Set ModelUTxOId)
  }
  deriving (Eq, Show, Generic)

instance Semigroup (ModelUtxoMap era) where
  ModelUtxoMap utxos stake collateral <> ModelUtxoMap utxos' stake' collateral' =
    ModelUtxoMap
      (Map.unionWith (\x y -> if x == y then x else error $ unwords ["unmergable ModelUtxoMap:", show x, "/=", show y]) utxos utxos')
      (stake <> stake')
      (Set.union collateral collateral')

instance Monoid (ModelUtxoMap era) where
  mempty = ModelUtxoMap Map.empty mempty Set.empty

mkModelUtxoMap ::
  forall era.
  KnownScriptFeature (ScriptFeature era) =>
  [(ModelUTxOId, ModelAddress (ScriptFeature era), Coin)] ->
  ModelUtxoMap era
mkModelUtxoMap =
  foldMap $ \(ui, ma, val) ->
    ModelUtxoMap
      (Map.singleton ui (val, ModelTxOut ma (modelValueInject val) dh))
      (grpMapSingleton (_modelAddress_stk ma) val)
      (bool Set.empty (Set.singleton ui) $ has (modelAddress_pmt . _ModelKeyHashObj) ma)
  where
    dh = ifSupportsPlutus (Proxy :: Proxy (ScriptFeature era)) () Nothing

getStake :: Map.Map ModelUTxOId (Coin, ModelTxOut era) -> GrpMap (ModelCredential 'Staking (ScriptFeature era)) Coin
getStake = foldMap (\(val, txo) -> grpMapSingleton (_modelAddress_stk $ _mtxo_address txo) val)

getModelValueCoin :: ModelValue a c -> Coin
getModelValueCoin = foldMap Val.coin . evalModelValueSimple . unModelValue

spendModelUTxOs ::
  Set ModelUTxOId ->
  [(ModelUTxOId, ModelTxOut era)] ->
  ModelUtxoMap era ->
  ModelUtxoMap era
spendModelUTxOs ins outs xs =
  let ins' = Map.restrictKeys (_modelUtxoMap_utxos xs) ins
      outs' = Map.fromList $ (fmap . fmap) (getModelValueCoin . _mtxo_value &&& id) outs
      newCollateral = foldMap (\(ui, txo) -> bool Set.empty (Set.singleton ui) $ has (modelTxOut_address . modelAddress_pmt . _ModelKeyHashObj) txo) outs
   in ModelUtxoMap
        { _modelUtxoMap_utxos = Map.withoutKeys (_modelUtxoMap_utxos xs `Map.union` outs') ins,
          _modelUtxoMap_stake = _modelUtxoMap_stake xs <> getStake outs' ~~ getStake ins',
          _modelUtxoMap_collateralUtxos =
            Set.difference (_modelUtxoMap_collateralUtxos xs) ins
              `Set.union` newCollateral
        }

instance NFData (ModelUtxoMap era)

type instance Index (ModelUtxoMap era) = ModelUTxOId

type instance IxValue (ModelUtxoMap era) = ModelTxOut era

instance Ixed (ModelUtxoMap era)

instance At (ModelUtxoMap era) where
  at :: ModelUTxOId -> Lens' (ModelUtxoMap era) (Maybe (ModelTxOut era))
  at k = \a2fb s ->
    let a = Map.lookup k $ _modelUtxoMap_utxos s
        b2t :: Maybe (ModelTxOut era) -> ModelUtxoMap era
        b2t b =
          let val = foldMap (getModelValueCoin . _mtxo_value) b
           in ModelUtxoMap
                { _modelUtxoMap_utxos = set (at k) (fmap ((,) val) b) (_modelUtxoMap_utxos s),
                  _modelUtxoMap_collateralUtxos =
                    set
                      (at k)
                      (() <$ preview (_Just . modelTxOut_address . modelAddress_pmt . _ModelKeyHashObj) b)
                      (_modelUtxoMap_collateralUtxos s),
                  _modelUtxoMap_stake =
                    _modelUtxoMap_stake s
                      <> foldMap (\(val', ui) -> grpMapSingleton (_modelAddress_stk $ _mtxo_address ui) (invert val')) a
                      <> foldMap (\ui -> grpMapSingleton (_modelAddress_stk $ _mtxo_address ui) val) b
                }
     in b2t <$> (a2fb $ fmap snd a)

data ModelLedger era = ModelLedger
  { _modelLedger_utxos :: (ModelUtxoMap era),
    _modelLedger_stake :: (SnapshotQueue (ModelSnapshot era)),
    _modelLedger_epoch :: EpochNo,
    _modelLedger_rewards :: (Set (ModelCredential 'Staking (ScriptFeature era))),
    _modelLedger_rewardUpdates :: (Set (ModelCredential 'Staking (ScriptFeature era)))
  }
  deriving (Eq, Show, Generic)

instance NFData (ModelLedger era)

mkModelLedger ::
  forall era.
  KnownScriptFeature (ScriptFeature era) =>
  [(ModelUTxOId, ModelAddress (ScriptFeature era), Coin)] ->
  ModelLedger era
mkModelLedger utxos =
  ModelLedger
    { _modelLedger_utxos = mkModelUtxoMap utxos,
      _modelLedger_stake = pure emptyModelSnapshot,
      _modelLedger_epoch = 0,
      _modelLedger_rewards = Set.empty,
      _modelLedger_rewardUpdates = Set.empty
    }

class HasModelLedger era a | a -> era where
  modelLedger :: Lens' a (ModelLedger era)

instance HasModelLedger era (ModelLedger era) where
  modelLedger = id

modelLedger_utxos :: Lens' (ModelLedger era) (ModelUtxoMap era) -- (Map.Map ModelUTxOId (ModelTxOut era))
modelLedger_utxos a2fb s = (\b -> s {_modelLedger_utxos = b}) <$> a2fb (_modelLedger_utxos s)
{-# INLINE modelLedger_utxos #-}

modelLedger_stake :: Lens' (ModelLedger era) (SnapshotQueue (ModelSnapshot era))
modelLedger_stake a2fb s = (\b -> s {_modelLedger_stake = b}) <$> a2fb (_modelLedger_stake s)
{-# INLINE modelLedger_stake #-}

modelLedger_epoch :: Lens' (ModelLedger era) EpochNo
modelLedger_epoch a2fb s = (\b -> s {_modelLedger_epoch = b}) <$> a2fb (_modelLedger_epoch s)
{-# INLINE modelLedger_epoch #-}

modelLedger_rewards :: Lens' (ModelLedger era) (Set (ModelCredential 'Staking (ScriptFeature era)))
modelLedger_rewards a2fb s = (\b -> s {_modelLedger_rewards = b}) <$> a2fb (_modelLedger_rewards s)
{-# INLINE modelLedger_rewards #-}

modelLedger_rewardUpdates :: Lens' (ModelLedger era) (Set (ModelCredential 'Staking (ScriptFeature era)))
modelLedger_rewardUpdates a2fb s = (\b -> s {_modelLedger_rewardUpdates = b}) <$> a2fb (_modelLedger_rewardUpdates s)
{-# INLINE modelLedger_rewardUpdates #-}

-- applyModelDCert :: ModelDCert era -> ModelSnapshot era -> ModelSnapshot era
applyModelDCert :: ModelDCert era -> ModelLedger era -> ModelLedger era
applyModelDCert =
  let mark = modelLedger_stake . snapshotQueue_mark
   in State.execState . \case
        ModelRegisterStake maddr -> mark . modelSnapshot_stake . at maddr .= Just mempty
        ModelDeRegisterStake maddr -> do
          mark . modelSnapshot_stake . at maddr .= Nothing
          mark . modelSnapshot_delegations . at maddr .= Nothing
        ModelDelegate (ModelDelegation maddr poolId) -> mark . modelSnapshot_delegations . at maddr .= Just poolId
        ModelRegisterPool pool -> mark . modelSnapshot_pools . at (_mppId pool) .= Just pool
        -- TODO: deal with epochNo
        ModelRetirePool poolId _epochNo -> mark . modelSnapshot_pools . at poolId .= Nothing

applyModelTx :: ModelTx era -> ModelLedger era -> ModelLedger era
applyModelTx tx = State.execState $ do
  -- spend inputs/add outputs
  modelLedger_utxos %= spendModelUTxOs (_mtxInputs tx) (_mtxOutputs tx)
  -- withdraw rewards
  modelLedger_rewards %= (`Set.difference` Map.keysSet (_mtxWdrl tx))
  -- apply certs
  forOf_ (modelTx_dCert . traverse) tx $ State.modify . applyModelDCert

minStakeForRewards :: Coin
minStakeForRewards = Coin 200

applyModelBlocksMade :: forall era. ModelBlocksMade -> ModelLedger era -> ModelLedger era
applyModelBlocksMade (ModelBlocksMade blocksMade) = State.execState $ do
  -- we don't actually keep the stake qty in the mark field up to date, we need
  -- to compute it's correct value at the time of snapshot.
  -- TODO: keep the stake qty up to date.
  stakeMark ::
    GrpMap (ModelCredential 'Staking (ScriptFeature era)) Coin <-
    uses modelLedger_utxos $ _modelUtxoMap_stake
  modelLedger_stake . snapshotQueue_mark . modelSnapshot_stake
    %= Map.merge
      Map.dropMissing
      (Map.mapMissing (\_ _ -> mempty))
      (Map.zipWithMatched (\_ x _ -> x))
      (unGrpMap stakeMark)

  -- take a snapshot
  ModelSnapshot stakes' delegs' pools <- modelLedger_stake %%= shiftSnapshotQueue

  let stakes :: GrpMap (ModelCredential 'Staking (ScriptFeature era)) Coin
      stakes = mkGrpMap stakes'
      delegs :: GrpMap ModelPoolId (Coin, Set (ModelCredential 'Staking (ScriptFeature era)))
      delegs = ifoldMap (\addr poolId -> GrpMap . Map.singleton poolId $ (view (grpMap addr) stakes, Set.singleton addr)) delegs'

      rewards :: Set (ModelCredential 'Staking (ScriptFeature era))
      rewards = flip ifoldMap (Map.intersectionWith (,) blocksMade pools) $ \poolId (blockWeight, pool) -> fold $ do
        guard (blockWeight >= 0) -- only if the pool makes *some* number of blocks
        let (dstake, deleg) = view (grpMap poolId) delegs
        guard (dstake >= _mppPledge pool) -- and the pool met its pledge
        let rewardAccts =
              Map.keysSet $
                Map.filter (>= minStakeForRewards) $ -- only if they have a minimum stake amount
                  Map.restrictKeys (unGrpMap stakes) deleg -- pay the delegates
            reward =
              (if _mppMargin pool < maxBound then rewardAccts else Set.empty) -- pay delegates if margin is less than 100%
                <> (if _mppMargin pool > minBound then Set.singleton (_mppRAcnt pool) else Set.empty) -- pay the pool if the margin is more than 0%
        Just reward

  -- accumulate new rewards
  rewardUpdates <- modelLedger_rewardUpdates <<.= rewards

  -- distribute accumulated rewards
  modelLedger_rewards <>= rewardUpdates

  modelLedger_epoch += 1

applyModelEpoch :: ModelEpoch era -> ModelLedger era -> ModelLedger era
applyModelEpoch epoch = State.execState $ do
  forOf_ (modelEpoch_blocks . traverse . modelBlock_txSeq . traverse) epoch $ State.modify . applyModelTx
  State.modify $ applyModelBlocksMade (_modelEpoch_blocksMade epoch)

data SnapshotQueue a = SnapshotQueue
  { _snapshotQueue_mark :: a,
    _snapshotQueue_set :: a,
    _snapshotQueue_go :: a
  }
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable, Generic)

instance NFData a => NFData (SnapshotQueue a)

snapshotQueue_mark :: Lens' (SnapshotQueue a) a
snapshotQueue_mark = lens _snapshotQueue_mark (\s b -> s {_snapshotQueue_mark = b})
{-# INLINE snapshotQueue_mark #-}

snapshotQueue_set :: Lens' (SnapshotQueue a) a
snapshotQueue_set = lens _snapshotQueue_set (\s b -> s {_snapshotQueue_set = b})
{-# INLINE snapshotQueue_set #-}

snapshotQueue_go :: Lens' (SnapshotQueue a) a
snapshotQueue_go = lens _snapshotQueue_go (\s b -> s {_snapshotQueue_go = b})
{-# INLINE snapshotQueue_go #-}

shiftSnapshotQueue :: SnapshotQueue a -> (a, SnapshotQueue a)
shiftSnapshotQueue (SnapshotQueue markX setX goX) = (goX, SnapshotQueue markX markX setX)

instance Applicative SnapshotQueue where
  pure x = SnapshotQueue x x x
  SnapshotQueue markF setF goF <*> SnapshotQueue markX setX goX =
    SnapshotQueue (markF markX) (setF setX) (goF goX)

instance Monad SnapshotQueue where
  SnapshotQueue markX setX goX >>= cont =
    SnapshotQueue
      (_snapshotQueue_mark $ cont markX)
      (_snapshotQueue_set $ cont setX)
      (_snapshotQueue_go $ cont goX)

instance Semigroup a => Semigroup (SnapshotQueue a) where (<>) = liftA2 (<>)

instance Monoid a => Monoid (SnapshotQueue a) where mempty = pure mempty

instance NFData IsValid
