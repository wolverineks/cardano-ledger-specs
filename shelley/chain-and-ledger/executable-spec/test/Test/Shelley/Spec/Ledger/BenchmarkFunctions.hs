{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}

module Test.Shelley.Spec.Ledger.BenchmarkFunctions
{-
  ( ledgerSpendOneUTxO,
    ledgerSpendOneGivenUTxO,
    initUTxO,                       -- How to precompute env for the UTxO transactions

    ledgerRegisterOneStakeKey,
    ledgerDeRegisterOneStakeKey,
    ledgerOneRewardWithdrawal,
    ledgerStateWithNregisteredKeys, -- How to precompute env for the StakeKey transactions

    ledgerRegisterOneStakePool,
    ledgerReRegisterOneStakePool,
    ledgerRetireOneStakePool,
    ledgerStateWithNregisteredPools, -- How to precompute env for the Stake Pool transactions

    ledgerDelegateOneStakeKey,
    ledgerStateWithNkeysMpools, -- How to precompute env for the Stake Delegation transactions
  )
  -}
where

import Control.State.Transition.Extended (TRC (..), applySTS)
import qualified Data.Map as Map
import Data.Sequence.Strict (StrictSeq)
import qualified Data.Sequence.Strict as StrictSeq
import qualified Data.Set as Set
import Data.Word (Word64)
import Numeric.Natural (Natural)
import Shelley.Spec.Ledger.BaseTypes (
  Network (..),
  StrictMaybe (..))
import Shelley.Spec.Ledger.Coin (Coin (..))
import Shelley.Spec.Ledger.Credential (pattern KeyHashObj)
import Shelley.Spec.Ledger.Delegation.Certificates
  ( pattern DeRegKey,
    pattern Delegate,
    pattern RegKey,
  )
import Shelley.Spec.Ledger.Keys
  ( KeyRole (..),
    asWitness,
    hashKey,
    vKey,
  )
import Shelley.Spec.Ledger.LedgerState
  ( AccountState (..),
    emptyDPState,
    genesisCoins,
    genesisId,
    pattern UTxOState,
  )
import Shelley.Spec.Ledger.PParams (PParams, PParams' (..), emptyPPPUpdates)
import Shelley.Spec.Ledger.STS.Ledger (pattern LedgerEnv)
import Shelley.Spec.Ledger.Slot (EpochNo (..), SlotNo (..))
import Shelley.Spec.Ledger.Tx (WitnessSetHKD (..), pattern Tx)
import Shelley.Spec.Ledger.TxData
  ( pattern DCertDeleg,
    pattern TxBody,
    pattern TxIn,
    pattern TxOut,
    pattern Wdrl,
    pattern PoolParams,
    pattern RewardAcnt,
    _poolPubKey,
    _poolVrf,
    _poolPledge,
    _poolCost,
    _poolMargin,
    _poolRAcnt,
    _poolOwners,
    _poolRelays,
    _poolMD,
    pattern DCertPool,
    PoolCert(..),
    Delegation(..),
  )
import Shelley.Spec.Ledger.UTxO (hashTxBody, makeWitnessesVKey)
import Test.Shelley.Spec.Ledger.ConcreteCryptoTypes
  ( DCert,
    DPState,
    KeyPair,
    LEDGER,
    LedgerEnv,
    Tx,
    TxBody,
    TxOut,
    UTxOState,
    VRFKeyHash,
    PoolParams,
    hashKeyVRF,
    Credential,
    KeyHash,
  )
import Test.Shelley.Spec.Ledger.Examples
  ( aliceAddr,
    alicePay,
    ppsEx1,
  )
import Test.Shelley.Spec.Ledger.Utils
  ( mkKeyPair',
    runShelleyBase,
    unsafeMkUnitInterval,
    mkVRFKeyPair,
  )

coins :: Integer -> [TxOut]
coins n = fmap (\_ -> TxOut aliceAddr (Coin $ 100)) [0 .. n]

initUTxO :: Integer -> UTxOState
initUTxO n =
  UTxOState
    (genesisCoins (coins n))
    (Coin 0)
    (Coin 0)
    emptyPPPUpdates

ppsBench :: PParams
ppsBench =
  ppsEx1
    { _minUTxOValue = 10,
      _keyDeposit = Coin 0,
      _poolDeposit = Coin 0,
      _minfeeA = 0,
      _minfeeB = 0,
      _maxTxSize = 1000000000
    }

ledgerEnv :: LedgerEnv
ledgerEnv = LedgerEnv (SlotNo 0) 0 ppsBench (AccountState 0 0)

testLEDGER ::
  (UTxOState, DPState) ->
  Tx ->
  LedgerEnv ->
  Bool
testLEDGER initSt tx env = do
  let st = runShelleyBase $ applySTS @LEDGER (TRC (env, initSt, tx))
  case st of
    Right _ -> True
    Left e -> error $ show e

txbSpendOneUTxO :: TxBody
txbSpendOneUTxO =
  TxBody
    (Set.fromList [TxIn genesisId 0])
    (StrictSeq.fromList [TxOut aliceAddr (Coin 10), TxOut aliceAddr (89)])
    StrictSeq.empty
    (Wdrl Map.empty)
    (Coin 1)
    (SlotNo 10)
    SNothing
    SNothing

txSpendOneUTxO :: Tx
txSpendOneUTxO =
  Tx
    txbSpendOneUTxO
    mempty
      { addrWits = makeWitnessesVKey (hashTxBody txbSpendOneUTxO) [asWitness alicePay]
      }
    SNothing

ledgerSpendOneUTxO :: Integer -> Bool
ledgerSpendOneUTxO n = testLEDGER (initUTxO n, emptyDPState) txSpendOneUTxO ledgerEnv


ledgerSpendOneGivenUTxO ::  UTxOState -> Bool
ledgerSpendOneGivenUTxO state = testLEDGER (state, emptyDPState) txSpendOneUTxO ledgerEnv

-- ===========================================================================
--
-- Register a stake keys when there are a lot of registered stake keys
--

-- Create n-many stake key pairs
stakeKeys :: Word64 -> [KeyPair 'Staking]
stakeKeys n = fmap (\w -> mkKeyPair' (w, 0, 0, 0, 0)) [1 .. n]

firstStakeKey :: KeyPair 'Staking
firstStakeKey = head $ stakeKeys 1

firstStakeKeyCred :: Credential 'Staking
firstStakeKeyCred = KeyHashObj . hashKey . vKey $ firstStakeKey

-- Create n-many stake key registration certificates
stakeKeyRegistrations :: [KeyPair 'Staking] -> StrictSeq DCert
stakeKeyRegistrations keys =
  StrictSeq.fromList $
    fmap (DCertDeleg . RegKey . (KeyHashObj . hashKey . vKey)) keys

-- Create a transaction body given a sequence of certificates.
-- It spends the genesis coin given by the index ix.
txbFromCerts :: Natural -> StrictSeq DCert -> TxBody
txbFromCerts ix regCerts =
  TxBody
    (Set.fromList [TxIn genesisId ix])
    (StrictSeq.fromList [TxOut aliceAddr (Coin 100)])
    -- Fees and Deposits are set to zero
    regCerts
    (Wdrl Map.empty)
    (Coin 0)
    (SlotNo 10)
    SNothing
    SNothing


makeSimpleTx
  :: TxBody
  -> [KeyPair 'AWitness]
  -> [KeyPair 'RWitness]
  -> Tx
makeSimpleTx body keysAddr keysReg =
  Tx
    body
    mempty { addrWits = makeWitnessesVKey (hashTxBody body) keysAddr
           , regWits = makeWitnessesVKey (hashTxBody body) keysReg
           }
    SNothing

-- Create a transaction that registers n stake credentials.
txRegStakeKeys :: Natural -> [KeyPair 'Staking] -> Tx
txRegStakeKeys ix keys =
  makeSimpleTx
    (txbFromCerts ix $ stakeKeyRegistrations keys)
    [asWitness alicePay]
    []

initLedgerState :: Integer -> (UTxOState, DPState)
initLedgerState n = (initUTxO n, emptyDPState)

makeLEDGERState :: (UTxOState, DPState) -> Tx -> (UTxOState, DPState)
makeLEDGERState start tx =
  let st = applySTS @LEDGER (TRC (ledgerEnv, start, tx))
  in
  case runShelleyBase st of
    Right st' -> st'
    Left e -> error $ show e

-- Create a ledger state that has n registered stake credentials.
-- The keys are seeded with (1, 0, 0, 0, 0) to (n, 0, 0, 0, 0)
-- It is pre-populated with 2 genesis coins.
ledgerStateWithNregisteredKeys :: Word64 -> (UTxOState, DPState)
ledgerStateWithNregisteredKeys n =
  makeLEDGERState (initLedgerState 1) $ txRegStakeKeys 0 (stakeKeys n)


-- ===========================================================
-- Stake Key Registration example

-- Create a ledger state that has n registers one stake credential,
-- and register a new stake key seeded with (0, 0, 0, 0, 0).
ledgerRegisterOneStakeKey :: (UTxOState, DPState) -> Bool
ledgerRegisterOneStakeKey state =
  testLEDGER
    state
    (txRegStakeKeys 1 [mkKeyPair' (0, 0, 0, 0, 0)])
    ledgerEnv

-- ===========================================================
-- Deregistration example

-- Create a transaction body that de-registers ONE stake credential,
-- corresponding to the key seeded with (1, 0, 0, 0, 0)
txbDeRegStakeKey :: TxBody
txbDeRegStakeKey =
  TxBody
    (Set.fromList [TxIn genesisId 1])
    (StrictSeq.fromList [TxOut aliceAddr (Coin 100)])
    -- Fees and Deposits are set to zero
    ( StrictSeq.singleton $
        DCertDeleg . DeRegKey $ firstStakeKeyCred
    )
    (Wdrl Map.empty)
    (Coin 0)
    (SlotNo 10)
    SNothing
    SNothing

-- Create a transaction that deregisters a stake credentials.
-- It spends the genesis coin indexed by 1.
txDeRegStakeKey :: Tx
txDeRegStakeKey =
  makeSimpleTx
    txbDeRegStakeKey
    [asWitness alicePay, asWitness firstStakeKey]
    []

-- Create a ledger state that has n registers one stake credential,
-- and degregister one of the keys.
ledgerDeRegisterOneStakeKey :: (UTxOState, DPState)  -> Bool
ledgerDeRegisterOneStakeKey state =
  testLEDGER
    state
    txDeRegStakeKey
    ledgerEnv

-- ===========================================================
-- Reward Withdrawal example

-- Create a transaction body that withdrawls from ONE reward account,
-- corresponding to the key seeded with (1, 0, 0, 0, 0)
txbWithdrawal :: TxBody
txbWithdrawal =
  TxBody
    (Set.fromList [TxIn genesisId 1])
    (StrictSeq.fromList [TxOut aliceAddr (Coin 100)])
    -- Fees and Deposits are set to zero
    StrictSeq.empty
    (Wdrl $ Map.singleton (RewardAcnt Testnet firstStakeKeyCred) (Coin 0))
    (Coin 0)
    (SlotNo 10)
    SNothing
    SNothing

-- Create a transaction that withdrawls from a reward account.
-- It spends the genesis coin indexed by 1.
txWithdrawal :: Tx
txWithdrawal =
  makeSimpleTx
    txbWithdrawal
    [asWitness alicePay, asWitness firstStakeKey]
    []

-- Create a ledger state that has n registers one stake credential,
-- and degregister one of the keys.
ledgerOneRewardWithdrawal :: (UTxOState, DPState)  -> Bool
ledgerOneRewardWithdrawal state = testLEDGER state txWithdrawal ledgerEnv


-- ===========================================================================
--
-- Register a stake pool when there are a lot of registered stake pool
--


-- Create n-many stake key pairs
poolColdKeys :: Word64 -> [KeyPair 'StakePool]
poolColdKeys n = fmap (\w -> mkKeyPair' (w, 1, 0, 0, 0)) [1 .. n]

firstStakePool :: KeyPair 'StakePool
firstStakePool = head $ poolColdKeys 1

firstStakePoolKeyHash :: KeyHash 'StakePool
firstStakePoolKeyHash = hashKey . vKey $ firstStakePool

vrfKeyHash :: VRFKeyHash
vrfKeyHash = hashKeyVRF . snd . mkVRFKeyPair $ (0, 0, 0, 0, 0)

mkPoolParameters :: KeyPair 'StakePool -> PoolParams
mkPoolParameters keys =
  PoolParams
    { _poolPubKey = (hashKey . vKey) keys,
      _poolVrf = vrfKeyHash,
      _poolPledge = Coin 0,
      _poolCost = Coin 0,
      _poolMargin = unsafeMkUnitInterval 0,
      _poolRAcnt = RewardAcnt Testnet firstStakeKeyCred,
      _poolOwners = Set.singleton $ (hashKey . vKey) firstStakeKey,
      _poolRelays = StrictSeq.empty,
      _poolMD = SNothing
    }

-- Create n-many stake pool registration certs
poolRegCerts :: [KeyPair 'StakePool] -> StrictSeq DCert
poolRegCerts = StrictSeq.fromList . fmap (DCertPool . RegPool . mkPoolParameters)

-- Create a transaction that registers n stake pools.
txRegStakePools :: Natural -> [KeyPair 'StakePool] -> Tx
txRegStakePools ix keys =
  makeSimpleTx
    (txbFromCerts ix $ poolRegCerts keys)
    [asWitness alicePay, asWitness firstStakeKey]
    (fmap asWitness keys)

-- Create a ledger state that has n registered stake pools.
-- The keys are seeded with (1, 0, 0, 0, 0) to (n, 0, 0, 0, 0)
-- It is pre-populated with 2 genesis coins.
ledgerStateWithNregisteredPools :: Word64 -> (UTxOState, DPState)
ledgerStateWithNregisteredPools n =
  makeLEDGERState (initLedgerState 1) $ txRegStakePools 0 (poolColdKeys n)

-- ===========================================================
-- Stake Pool Registration example

-- Create a ledger state with n stake pools and register a new pool
-- whose key is seeded with (0, 0, 0, 0, 0).
ledgerRegisterOneStakePool :: (UTxOState, DPState) -> Bool
ledgerRegisterOneStakePool state =
  testLEDGER
    state
    (txRegStakePools 1 [mkKeyPair' (0, 0, 0, 0, 0)])
    ledgerEnv

-- ===========================================================
-- Stake Pool Re-Registration/Update example

-- Create a ledger state with n stake pools and re-register the pool
-- whose key is seeded with (1, 0, 0, 0, 0).
ledgerReRegisterOneStakePool :: (UTxOState, DPState) -> Bool
ledgerReRegisterOneStakePool state =
  testLEDGER
    state
    (txRegStakePools 1 (poolColdKeys 1))
    ledgerEnv


-- ===========================================================
-- Stake Pool Retirement example

-- Create a transaction body that retires ONE stake pool,
-- corresponding to the key seeded with (1, 0, 0, 0, 0)
txbRetireStakePool :: TxBody
txbRetireStakePool =
  TxBody
    (Set.fromList [TxIn genesisId 1])
    (StrictSeq.fromList [TxOut aliceAddr (Coin 100)])
    -- Fees and Deposits are set to zero
    ( StrictSeq.singleton $
        DCertPool $ RetirePool firstStakePoolKeyHash (EpochNo 1)
    )
    (Wdrl Map.empty)
    (Coin 0)
    (SlotNo 10)
    SNothing
    SNothing

-- Create a transaction that retires a stake pool.
-- It spends the genesis coin indexed by 1.
txRetireStakePool :: Tx
txRetireStakePool = makeSimpleTx txbRetireStakePool [asWitness alicePay] [asWitness firstStakePool]

-- Create a ledger state with n stake pools and retire the new pool
-- whose key is seeded with (1, 0, 0, 0, 0).
ledgerRetireOneStakePool :: (UTxOState, DPState) -> Bool
ledgerRetireOneStakePool state = testLEDGER state txRetireStakePool ledgerEnv


-- ===========================================================================
--
-- Delegate Stake Credentials when many stake keys and stake pools are registered.
--


-- Create a ledger state that has n registered stake keys and m stake pools.
-- The stake keys are seeded with (1, 0, 0, 0, 0) to (n, 0, 0, 0, 0)
-- The stake pools are seeded with (1, 1, 0, 0, 0) to (m, 1, 0, 0, 0)
-- It is pre-populated with 3 genesis coins.
ledgerStateWithNkeysMpools :: Word64 -> Word64 -> (UTxOState, DPState)
ledgerStateWithNkeysMpools n m =
  makeLEDGERState
    (makeLEDGERState (initLedgerState 2) $ txRegStakeKeys 0 (stakeKeys n))
    (txRegStakePools 1 (poolColdKeys m))

-- Create a transaction body that retires ONE stake pool,
-- corresponding to the key seeded with (1, 0, 0, 0, 0)
txbDelegate :: TxBody
txbDelegate =
  TxBody
    (Set.fromList [TxIn genesisId 2])
    (StrictSeq.fromList [TxOut aliceAddr (Coin 100)])
    -- Fees and Deposits are set to zero
    ( StrictSeq.singleton $
        DCertDeleg $ Delegate (Delegation firstStakeKeyCred firstStakePoolKeyHash)
    )
    (Wdrl Map.empty)
    (Coin 0)
    (SlotNo 10)
    SNothing
    SNothing

-- Create a transaction that delegates stake.
txDelegate :: Tx
txDelegate = makeSimpleTx txbDelegate [asWitness alicePay, asWitness firstStakeKey] []

-- Create a ledger state with n stake keys and m stake pools,
-- and delegate the first stake key to the first stake pool.
ledgerDelegateOneStakeKey :: (UTxOState, DPState) -> Bool
ledgerDelegateOneStakeKey state = testLEDGER state txDelegate ledgerEnv
