{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}

module Cardano.Ledger.Props where

import Cardano.Crypto.DSIGN.Class (Signable)
import qualified Cardano.Crypto.Hash as CH
import qualified Cardano.Crypto.Hash.Class as CCH (Hash (..))
import Cardano.Ledger.Alonzo.Data (Data (..), hashData)
import Cardano.Ledger.Alonzo.Language (Language (..))
-- import qualified Cardano.Ledger.Alonzo.PParams as Alonzo(PParams'(..))
import Cardano.Ledger.Alonzo.Scripts
  ( CostModel (..),
    ExUnits (..),
    Tag (Spend),
  )
import Cardano.Ledger.Alonzo.TxWitness (RdmrPtr (..), Redeemers (..))
import Cardano.Ledger.Coin (Coin (..))
import Cardano.Ledger.Core (EraRule)
import qualified Cardano.Ledger.Core as Core
import qualified Cardano.Ledger.Crypto as CC (DSIGN, HASH)
import Cardano.Ledger.Era (Era (..), ValidateScript (..))
import Cardano.Ledger.Hashes (EraIndependentTxBody)
import Cardano.Ledger.Indexed
import Cardano.Ledger.Pretty (PDoc, PrettyA (..))
import Cardano.Ledger.Proof
import Cardano.Ledger.SafeHash (hashAnnotated)
import Cardano.Ledger.Updaters
import Cardano.Ledger.Val (inject)
import Cardano.Slotting.Slot (SlotNo (..))
import Control.State.Transition.Extended hiding (Assertion)
import Data.Default.Class (Default (..))
import qualified Data.Map as Map
import qualified PlutusTx as Plutus
import Shelley.Spec.Ledger.Address (Addr (..))
import Shelley.Spec.Ledger.BaseTypes (Network (..))
import Shelley.Spec.Ledger.Credential (Credential (..), StakeReference (..))
import Shelley.Spec.Ledger.Keys (GenDelegs (..), KeyPair (..), KeyRole (..), hashKey)
import Shelley.Spec.Ledger.LedgerState (UTxOState (..))
import Shelley.Spec.Ledger.STS.Utxo (UtxoEnv (..))
import Shelley.Spec.Ledger.TxBody (TxIn (..))
import Shelley.Spec.Ledger.UTxO (UTxO (..), makeWitnessVKey, txid)
import Test.Cardano.Crypto.Utils (genesisId, mkKeyPair)

-- ===========================================
-- A Parametric era, supports lots of functionality
-- All Witnessed Eras are Parametric

type Parametric era =
  ( Reflect era, -- reify, evidence, lift, liftC
    Good era, -- makeWitnessVKey
    Scriptic era, -- always, never, allOf ...
    Signable -- makeWitnessVKey
      (CC.DSIGN (Crypto era))
      (CCH.Hash (CC.HASH (Crypto era)) EraIndependentTxBody),
    Era era
  )

-- ========================================================
-- JAREDS Utxo example tests  Test.Cardano.Ledger.Alonzo.Examples.Utxow
-- ========================================================

pp :: Proof era -> Core.PParams era
pp wit =
  newPParams
    wit
    [ Costmdls $ Map.singleton PlutusV1 (CostModel mempty),
      MaxValSize 1000000000,
      MaxTxExUnits $ ExUnits 1000000 1000000,
      MaxBlockExUnits $ ExUnits 1000000 1000000
    ]

utxoEnv :: Proof era -> UtxoEnv era
utxoEnv wit =
  UtxoEnv
    (SlotNo 0)
    (pp wit)
    mempty
    (GenDelegs mempty)

-- | Create an address with a given payment script.
scriptAddr :: forall era. Reflect era => Core.Script era -> Proof era -> Addr (Crypto era)
scriptAddr s _wit = Addr Testnet pCred sCred
  where
    pCred = ScriptHashObj . hashScript @era $ s
    (_ssk, svk) = mkKeyPair @(Crypto era) (0, 0, 0, 0, 0)
    sCred = StakeRefBase . KeyHashObj . hashKey $ svk

feeKeys :: forall era. Era era => Proof era -> KeyPair 'Payment (Crypto era)
feeKeys _wit = KeyPair vk sk
  where
    (sk, vk) = mkKeyPair @(Crypto era) (0, 0, 0, 0, 1)

feeAddr :: forall era. Reflect era => Proof era -> Addr (Crypto era)
feeAddr wit = Addr Testnet pCred sCred
  where
    (_ssk, svk) = mkKeyPair @(Crypto era) (0, 0, 0, 0, 2)
    pCred = KeyHashObj . hashKey . vKey $ feeKeys wit
    sCred = StakeRefBase . KeyHashObj . hashKey $ svk

feeOutput :: Reflect era => Proof era -> Core.TxOut era
feeOutput wit =
  newTxOut Override wit [Address $ feeAddr wit, Amount (inject $ Coin 1000)]

initUTxO :: (Parametric era) => Proof era -> UTxO era
initUTxO wit =
  UTxO $
    Map.fromList
      [ (TxIn genesisId 0, alwaysSucceedsOutput wit),
        (TxIn genesisId 1, alwaysFailsOutput wit),
        (TxIn genesisId 2, feeOutput wit)
      ]

-- =========================================================================
--  Example 1: Process a SPEND transaction with a succeeding Plutus script.
-- =========================================================================

datumExample1 :: Data era
datumExample1 = Data (Plutus.I 0)

redeemerExample1 :: Data era
redeemerExample1 = Data (Plutus.I 42)

alwaysSucceedsOutput :: forall era. (Parametric era) => Proof era -> Core.TxOut era
alwaysSucceedsOutput wit =
  newTxOut
    Override
    wit
    [ Address (scriptAddr (always 3 wit) wit),
      Amount (inject $ Coin 5000),
      DHash [hashData $ datumExample1 @era]
    ]

validatingRedeemersEx1 :: Era era => Redeemers era
validatingRedeemersEx1 = Redeemers (Map.fromList [(RdmrPtr Spend 0, (redeemerExample1, ExUnits 5000 5000))])

outEx1 :: Reflect era => Proof era -> Core.TxOut era
outEx1 wit = newTxOut Override wit [Address (feeAddr wit), Amount (inject $ Coin 5995)]

validatingBody :: Reflect era => Proof era -> Core.TxBody era
validatingBody wit =
  newTxBody
    Override
    wit
    [ Inputs [TxIn genesisId 0],
      Collateral [TxIn genesisId 2],
      Outputs [outEx1 wit],
      Txfee (Coin 5),
      WppHash (newWppHash wit (pp wit) [PlutusV1] validatingRedeemersEx1)
    ]

validatingTx ::
  forall era.
  ( Reflect era,
    Scriptic era,
    Signable
      (CC.DSIGN (Crypto era))
      (CH.Hash (CC.HASH (Crypto era)) EraIndependentTxBody)
  ) =>
  Proof era ->
  Core.Tx era
validatingTx wit =
  newTx
    Override
    wit
    [ Body (validatingBody wit),
      Witnesses'
        [ AddrWits [makeWitnessVKey (hashAnnotated (validatingBody wit)) (feeKeys wit)],
          ScriptWits [always 3 wit],
          DataWits [datumExample1],
          RdmrWits validatingRedeemersEx1
        ]
    ]

utxoEx1 :: forall era. Parametric era => Proof era -> UTxO era
utxoEx1 wit =
  UTxO $
    Map.fromList
      [ (TxIn genesisId 1, alwaysFailsOutput wit),
        ( TxIn (txid @era (validatingBody wit)) 0,
          outEx1 wit
        )
      ]

utxoStEx1 ::
  forall era.
  (Default (State (EraRule "PPUP" era)), Parametric era) =>
  Proof era ->
  UTxOState era
utxoStEx1 wit = UTxOState (utxoEx1 wit) (Coin 0) (Coin 5) def

{-
utxoStEx1 wit@(Shelley c)  = UTxOState (utxoEx1 wit) (Coin 0) (Coin 5) def
utxoStEx1 wit@(Allegra c)  = UTxOState (utxoEx1 wit) (Coin 0) (Coin 5) def
utxoStEx1 wit@(Mary c)  = UTxOState (utxoEx1 wit) (Coin 0) (Coin 5) def
utxoStEx1 wit@(Alonzo c)  = UTxOState (utxoEx1 wit) (Coin 0) (Coin 5) def
-}

-- instance DSIGNAlgorithm C_Crypto where

go :: Cardano.Ledger.Pretty.PDoc
go = prettyA (validatingTx (Alonzo Mock))

-- ======================================================================
--  Example 2: Process a SPEND transaction with a failing Plutus script.
-- ======================================================================

datumExample2 :: Data era
datumExample2 = Data (Plutus.I 0)

redeemerExample2 :: Data era
redeemerExample2 = Data (Plutus.I 1)

notValidatingRedeemers :: Era era => Redeemers era
notValidatingRedeemers =
  Redeemers
    ( Map.fromList
        [ ( RdmrPtr Spend 0,
            (redeemerExample2, ExUnits 5000 5000)
          )
        ]
    )

alwaysFailsOutput :: forall era. (Scriptic era, Reflect era) => Proof era -> Core.TxOut era
alwaysFailsOutput wit =
  newTxOut
    Override
    wit
    [ Address (scriptAddr (never 0 wit) wit),
      Amount (inject $ Coin 3000),
      DHash [hashData $ datumExample2 @era]
    ]

outEx2 :: Reflect era => Proof era -> Core.TxOut era
outEx2 wit = newTxOut Override wit [Address (feeAddr wit), Amount (inject $ Coin 3995)]

notValidatingBody :: Reflect era => Proof era -> Core.TxBody era
notValidatingBody wit =
  newTxBody
    Override
    wit
    [ Inputs [TxIn genesisId 1],
      Collateral [TxIn genesisId 2],
      Outputs [outEx2 wit],
      Txfee (Coin 5),
      WppHash (newWppHash wit (pp wit) [PlutusV1] notValidatingRedeemers)
    ]

notValidatingTx :: forall era. (Parametric era) => Proof era -> Core.Tx era
notValidatingTx wit =
  newTx
    Override
    wit
    [ Body (notValidatingBody wit),
      Witnesses'
        [ AddrWits [makeWitnessVKey (hashAnnotated (notValidatingBody wit)) (feeKeys wit)],
          ScriptWits [never 0 wit],
          DataWits [datumExample2],
          RdmrWits notValidatingRedeemers
        ]
    ]

utxoEx2 :: forall era. Parametric era => Proof era -> UTxO era
utxoEx2 wit =
  UTxO $
    Map.fromList
      [ (TxIn genesisId 0, alwaysSucceedsOutput wit),
        (TxIn genesisId 1, alwaysFailsOutput wit)
      ]

utxoStEx2 ::
  forall era.
  (Default (State (EraRule "PPUP" era)), Parametric era) =>
  Proof era ->
  UTxOState era
utxoStEx2 wit = UTxOState (utxoEx2 wit) (Coin 0) (Coin 1000) def
