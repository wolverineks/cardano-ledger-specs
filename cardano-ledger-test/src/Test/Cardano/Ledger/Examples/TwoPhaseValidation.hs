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

module Test.Cardano.Ledger.Examples.TwoPhaseValidation where

import Test.Tasty (TestTree, testGroup)
import Cardano.Ledger.Alonzo.PParams (PParams' (..))
import Cardano.Ledger.Alonzo (AlonzoEra)
import Test.Shelley.Spec.Ledger.ConcreteCryptoTypes (C_Crypto)
import Control.State.Transition.Trace (checkTrace, (.-), (.->))
import Numeric.Natural (Natural)
import Data.Time.Clock.POSIX (posixSecondsToUTCTime)
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
import Cardano.Ledger.Hashes (EraIndependentTxBody, ScriptHash)
import Cardano.Ledger.SafeHash (hashAnnotated)
import Cardano.Ledger.Val (inject)
import Cardano.Slotting.EpochInfo (EpochInfo, fixedEpochInfo)
import Cardano.Slotting.Slot (SlotNo (..), EpochSize (..))
import Cardano.Slotting.Time (SystemStart (..), mkSlotLength)
import Control.State.Transition.Extended hiding (Assertion)
import Data.Default.Class (Default (..))
import Data.Functor.Identity (Identity)
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
import Test.Cardano.Ledger.Generic.Proof
import Test.Cardano.Ledger.Generic.Indexed
import Test.Cardano.Ledger.Generic.Updaters
import Test.Shelley.Spec.Ledger.Generator.EraGen (genesisId)
import Test.Shelley.Spec.Ledger.Utils (applySTSTest, mkKeyPair, runShelleyBase)
import Test.Tasty.HUnit (Assertion, testCase, (@?=))
import Cardano.Ledger.Alonzo.Rules.Utxow (AlonzoPredFail (..), AlonzoUTXOW)
import Cardano.Ledger.Alonzo.Tx (ValidatedTx)

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

-- =======================
-- Setup the initial state
-- =======================

testEpochInfo :: EpochInfo Identity
testEpochInfo = fixedEpochInfo (EpochSize 100) (mkSlotLength 1)

testSystemStart :: SystemStart
testSystemStart = SystemStart $ posixSecondsToUTCTime 0

pp :: Proof era -> Core.PParams era
pp pf =
  newPParams
    pf
    [ Costmdls $ Map.singleton PlutusV1 (CostModel mempty),
      MaxValSize 1000000000,
      MaxTxExUnits $ ExUnits 1000000 1000000,
      MaxBlockExUnits $ ExUnits 1000000 1000000
    ]

utxoEnv :: Proof era -> UtxoEnv era
utxoEnv pf =
  UtxoEnv
    (SlotNo 0)
    (pp pf)
    mempty
    (GenDelegs mempty)

-- | Create an address with a given payment script.
scriptAddr :: forall era. Reflect era => Core.Script era -> Proof era -> Addr (Crypto era)
scriptAddr s _pf = Addr Testnet pCred sCred
  where
    pCred = ScriptHashObj . hashScript @era $ s
    (_ssk, svk) = mkKeyPair @(Crypto era) (0, 0, 0, 0, 0)
    sCred = StakeRefBase . KeyHashObj . hashKey $ svk

someKeys :: forall era. Era era => Proof era -> KeyPair 'Payment (Crypto era)
someKeys _pf = KeyPair vk sk
  where
    (sk, vk) = mkKeyPair @(Crypto era) (0, 0, 0, 0, 1)

someAddr :: forall era. Reflect era => Proof era -> Addr (Crypto era)
someAddr pf = Addr Testnet pCred sCred
  where
    (_ssk, svk) = mkKeyPair @(Crypto era) (0, 0, 0, 0, 2)
    pCred = KeyHashObj . hashKey . vKey $ someKeys pf
    sCred = StakeRefBase . KeyHashObj . hashKey $ svk

collateralOutput :: Reflect era => Proof era -> Core.TxOut era
collateralOutput pf =
  newTxOut Override pf [Address $ someAddr pf, Amount (inject $ Coin 1000)]

someOutput :: Reflect era => Proof era -> Core.TxOut era
someOutput pf =
  newTxOut Override pf [Address $ someAddr pf, Amount (inject $ Coin 1000)]

alwaysSucceedsHash1 :: forall era. Parametric era => Proof era -> ScriptHash (Crypto era)
alwaysSucceedsHash1 pf = hashScript @era $ (always 1 pf)

alwaysSucceedsHash2 :: forall era. Parametric era => Proof era -> ScriptHash (Crypto era)
alwaysSucceedsHash2 pf = hashScript @era $ (always 2 pf)

alwaysSucceedsHash3 :: forall era. Parametric era => Proof era -> ScriptHash (Crypto era)
alwaysSucceedsHash3 pf = hashScript @era $ (always 3 pf)

alwaysFailsHash0 :: forall era. Parametric era => Proof era -> ScriptHash (Crypto era)
alwaysFailsHash0 pf = hashScript @era $ (never 0 pf)

alwaysFailsHash1 :: forall era. Parametric era => Proof era -> ScriptHash (Crypto era)
alwaysFailsHash1 pf = hashScript @era $ (never 1 pf)

initUTxO :: (Parametric era) => Proof era -> UTxO era
initUTxO pf =
  UTxO $
    Map.fromList $
      [ (TxIn genesisId 1, alwaysSucceedsOutput pf),
        (TxIn genesisId 2, alwaysFailsOutput pf)
      ]
        ++ map (\i -> (TxIn genesisId i, someOutput pf)) [3 .. 8]
        ++ map (\i -> (TxIn genesisId i, collateralOutput pf)) [11 .. 18]
        -- ++ [(TxIn genesisId 100, timelockOut)]

initialUtxoSt
  :: (Default (State (EraRule "PPUP" era)))
  => (Parametric era)
  => Proof era
  -> UTxOState era
initialUtxoSt pf = UTxOState (initUTxO pf) (Coin 0) (Coin 0) def

-- | This is a helper type for the expectedUTxO function.
--  ExpectSuccess indicates that we created a valid transaction
--  where the IsValidating flag is true.
data Expect era = ExpectSuccess (Core.TxBody era) (Core.TxOut era) | ExpectFailure

-- | In each of our main eight examples, the UTxO map obtained
-- by applying the transaction is straightforward. This function
-- captures the logic.
--
-- Each example transaction (given a number i) will use
-- (TxIn genesisId (10+i), someOutput) for its' single input,
-- and (TxIn genesisId i, collateralOutput) for its' single collateral output.
--
-- If we expect the transaction script to validate, then
-- the UTxO for (TxIn genesisId i) will be consumed and a UTxO will be created.
-- Otherwise, the UTxO for (TxIn genesisId (10+i)) will be consumed.
expectedUTxO :: forall era. (Parametric era) => Proof era -> Expect era -> Natural -> UTxO era
expectedUTxO pf ex idx = UTxO utxo
  where
    utxo = case ex of
      ExpectSuccess txb newOut ->
        Map.insert (TxIn (txid @era txb) 0) newOut (filteredUTxO idx)
      ExpectFailure -> filteredUTxO (10 + idx)
    filteredUTxO :: Natural -> Map.Map (TxIn (Crypto era)) (Core.TxOut era)
    filteredUTxO x = Map.filterWithKey (\(TxIn _ i) _ -> i /= x) (unUTxO . initUTxO $ pf)


-- =========================================================================
--  Example 1: Process a SPEND transaction with a succeeding Plutus script.
-- =========================================================================

datumExample1 :: Data era
datumExample1 = Data (Plutus.I 123)

redeemerExample1 :: Data era
redeemerExample1 = Data (Plutus.I 42)

alwaysSucceedsOutput :: forall era. (Parametric era) => Proof era -> Core.TxOut era
alwaysSucceedsOutput pf =
  newTxOut
    Override
    pf
    [ Address (scriptAddr (always 3 pf) pf),
      Amount (inject $ Coin 5000),
      DHash [hashData $ datumExample1 @era]
    ]

validatingRedeemersEx1 :: Era era => Redeemers era
validatingRedeemersEx1 =
  Redeemers $
    Map.singleton (RdmrPtr Spend 0) (redeemerExample1, ExUnits 5000 5000)

outEx1 :: Reflect era => Proof era -> Core.TxOut era
outEx1 pf = newTxOut Override pf [Address (someAddr pf), Amount (inject $ Coin 4995)]

validatingBody :: Reflect era => Proof era -> Core.TxBody era
validatingBody pf =
  newTxBody
    Override
    pf
    [ Inputs [TxIn genesisId 1],
      Collateral [TxIn genesisId 11],
      Outputs [outEx1 pf],
      Txfee (Coin 5),
      WppHash (newWppHash pf (pp pf) [PlutusV1] validatingRedeemersEx1)
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
validatingTx pf =
  newTx
    Override
    pf
    [ Body (validatingBody pf),
      Witnesses'
        [ AddrWits [makeWitnessVKey (hashAnnotated (validatingBody pf)) (someKeys pf)],
          ScriptWits [always 3 pf],
          DataWits [datumExample1],
          RdmrWits validatingRedeemersEx1
        ]
    ]

utxoEx1 :: forall era. Parametric era => Proof era -> UTxO era
utxoEx1 pf = expectedUTxO pf (ExpectSuccess (validatingBody pf) (outEx1 pf)) 1

utxoStEx1 ::
  forall era.
  (Default (State (EraRule "PPUP" era)), Parametric era) =>
  Proof era ->
  UTxOState era
utxoStEx1 pf = UTxOState (utxoEx1 pf) (Coin 0) (Coin 5) def

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
alwaysFailsOutput pf =
  newTxOut
    Override
    pf
    [ Address (scriptAddr (never 0 pf) pf),
      Amount (inject $ Coin 3000),
      DHash [hashData $ datumExample2 @era]
    ]

outEx2 :: Reflect era => Proof era -> Core.TxOut era
outEx2 pf = newTxOut Override pf [Address (someAddr pf), Amount (inject $ Coin 3995)]

notValidatingBody :: Reflect era => Proof era -> Core.TxBody era
notValidatingBody pf =
  newTxBody
    Override
    pf
    [ Inputs [TxIn genesisId 1],
      Collateral [TxIn genesisId 2],
      Outputs [outEx2 pf],
      Txfee (Coin 5),
      WppHash (newWppHash pf (pp pf) [PlutusV1] notValidatingRedeemers)
    ]

notValidatingTx :: forall era. (Parametric era) => Proof era -> Core.Tx era
notValidatingTx pf =
  newTx
    Override
    pf
    [ Body (notValidatingBody pf),
      Witnesses'
        [ AddrWits [makeWitnessVKey (hashAnnotated (notValidatingBody pf)) (someKeys pf)],
          ScriptWits [never 0 pf],
          DataWits [datumExample2],
          RdmrWits notValidatingRedeemers
        ]
    ]

utxoEx2 :: forall era. Parametric era => Proof era -> UTxO era
utxoEx2 pf =
  UTxO $
    Map.fromList
      [ (TxIn genesisId 0, alwaysSucceedsOutput pf),
        (TxIn genesisId 1, alwaysFailsOutput pf)
      ]

utxoStEx2 ::
  forall era.
  (Default (State (EraRule "PPUP" era)), Parametric era) =>
  Proof era ->
  UTxOState era
utxoStEx2 pf = UTxOState (utxoEx2 pf) (Coin 0) (Coin 1000) def

--testUTXOW ::
--  forall era.
--  Proof era ->
--  UTxOState era ->
--  Core.Tx era ->
--  Either [[PredicateFailure (Core.EraRule "UTXOW" era)]] (UTxOState era) ->
--  Assertion
--testUTXOW pf initSt tx (Right expectedSt) =
--  checkTrace @(Core.EraRule "UTXOW" era) runShelleyBase (utxoEnv pf) $
--    pure initSt .- tx .-> expectedSt
--testUTXOW pf initSt tx predicateFailure@(Left _) = do
--  let st = runShelleyBase $ applySTSTest @(Core.EraRule "UTXOW" era) (TRC (utxoEnv pf, initSt, tx))
--  st @?= predicateFailure

--utxowExamples :: TestTree
--utxowExamples =
--  testGroup
--    "utxow examples"
--    [ testGroup
--        "valid transactions"
--        [ testCase "validating SPEND script" $
--            testUTXOW
--              (Alonzo Mock)
--              (initialUtxoSt $ Alonzo Mock)
--              (validatingTx $ Alonzo Mock)
--              (Right . utxoStEx1 $ Alonzo Mock)
--        ]
--    ]
