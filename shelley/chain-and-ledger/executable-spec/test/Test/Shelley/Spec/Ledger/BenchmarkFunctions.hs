{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}

module Test.Shelley.Spec.Ledger.BenchmarkFunctions where

{-
  ( ledgerSpendOneUTxO,
    ledgerSpendOneGivenUTxO,
    initUTxO,                       -- How to precompute env for the UTxO transactions

    ledgerRegisterStakeKeys,
    ledgerDeRegisterStakeKeys,
    ledgerRewardWithdrawals,
    ledgerStateWithNregisteredKeys, -- How to precompute env for the StakeKey transactions

    ledgerRegisterStakePools,
    ledgerReRegisterStakePools,
    ledgerRetireStakePools,
    ledgerStateWithNregisteredPools, -- How to precompute env for the Stake Pool transactions

    ledgerDelegateManyKeysOnePool,
    ledgerStateWithNkeysMpools, -- How to precompute env for the Stake Delegation transactions
  )
  -}

import Control.State.Transition.Extended (TRC (..), applySTS)
import qualified Data.Map as Map
import Data.Sequence.Strict (StrictSeq)
import qualified Data.Sequence.Strict as StrictSeq
import qualified Data.Set as Set
import Data.Word (Word64)
import Numeric.Natural (Natural)
import Shelley.Spec.Ledger.BaseTypes
  ( Network (..),
    StrictMaybe (..),
  )
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
  ( Delegation (..),
    PoolCert (..),
    _poolCost,
    _poolMD,
    _poolMargin,
    _poolOwners,
    _poolPledge,
    _poolPubKey,
    _poolRAcnt,
    _poolRelays,
    _poolVrf,
    pattern DCertDeleg,
    pattern DCertPool,
    pattern PoolParams,
    pattern RewardAcnt,
    pattern TxBody,
    pattern TxIn,
    pattern TxOut,
    pattern Wdrl,
  )
import Shelley.Spec.Ledger.UTxO (hashTxBody, makeWitnessesVKey)
import Test.Shelley.Spec.Ledger.BenchmarkCrypto -- Types with fixed type parameter: BenchmarkCrypto
  ( -- Below this line are operations to make things with BenchmarkCrypto fixed types.
    Addr,
    Credential,
    DCert,
    DPState,
    KeyHash,
    KeyPair,
    LEDGER,
    LedgerEnv,
    PoolParams,
    Tx,
    TxBody,
    TxOut,
    UTxOState,
    VRFKeyHash,
    hashKeyVRF,
    mkAddr,
    mkKeyPair,
    mkKeyPair',
    mkVRFKeyPair,
    ppsEx1,
    runShelleyBase,
    unsafeMkUnitInterval,
    pattern KeyPair,
  )

-- =========================================================

aliceStake :: KeyPair 'Staking
aliceStake = KeyPair vk sk
  where
    (sk, vk) = mkKeyPair (0, 0, 0, 0, 1)

alicePay :: KeyPair 'Payment
alicePay = KeyPair vk sk
  where
    (sk, vk) = mkKeyPair (0, 0, 0, 0, 0)

aliceAddr :: Addr
aliceAddr = mkAddr (alicePay, aliceStake)

-- ==========================================================

coins :: Integer -> [TxOut]
coins n = fmap (\_ -> TxOut aliceAddr (Coin $ 100)) [0 .. n]

-- Cretae an initial UTxO set with n-many transaction outputs
initUTxO :: Integer -> UTxOState
initUTxO n =
  UTxOState
    (genesisCoins (coins n))
    (Coin 0)
    (Coin 0)
    emptyPPPUpdates

-- Protocal Parameters used for the benchmarknig tests.
-- Note that the fees and deposits are set to zero for
-- ease of creating transactions.
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
  ()
testLEDGER initSt tx env = do
  let st = runShelleyBase $ applySTS @LEDGER (TRC (env, initSt, tx))
  case st of
    Right _ -> ()
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

ledgerSpendOneUTxO :: Integer -> ()
ledgerSpendOneUTxO n = testLEDGER (initUTxO n, emptyDPState) txSpendOneUTxO ledgerEnv

ledgerSpendOneGivenUTxO :: UTxOState -> ()
ledgerSpendOneGivenUTxO state = testLEDGER (state, emptyDPState) txSpendOneUTxO ledgerEnv

-- ===========================================================================
--
-- Register a stake keys when there are a lot of registered stake keys
--

-- Create stake key pairs, corresponding to seeds
-- (start, 0, 0, 0, 0) through (end, 0, 0, 0, 0)
stakeKeys :: Word64 -> Word64 -> [KeyPair 'Staking]
stakeKeys start end = fmap (\w -> mkKeyPair' (w, 0, 0, 0, 0)) [start .. end]

stakeKeyOne :: KeyPair 'Staking
stakeKeyOne = mkKeyPair' (1, 0, 0, 0, 0)

stakeKeyToCred :: KeyPair 'Staking -> Credential 'Staking
stakeKeyToCred = KeyHashObj . hashKey . vKey

firstStakeKeyCred :: Credential 'Staking
firstStakeKeyCred = stakeKeyToCred stakeKeyOne

-- Create stake key registration certificates
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
    regCerts
    (Wdrl Map.empty)
    (Coin 0)
    (SlotNo 10)
    SNothing
    SNothing

makeSimpleTx ::
  TxBody ->
  [KeyPair 'AWitness] ->
  [KeyPair 'RWitness] ->
  Tx
makeSimpleTx body keysAddr keysReg =
  Tx
    body
    mempty
      { addrWits = makeWitnessesVKey (hashTxBody body) keysAddr,
        regWits = makeWitnessesVKey (hashTxBody body) keysReg
      }
    SNothing

-- Create a transaction that registers stake credentials.
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
   in case runShelleyBase st of
        Right st' -> st'
        Left e -> error $ show e

-- Create a ledger state that has registered stake credentials that
-- are seeded with (n, 0, 0, 0, 0) to (m, 0, 0, 0, 0).
-- It is pre-populated with 2 genesis coins.
ledgerStateWithNregisteredKeys :: Word64 -> Word64 -> (UTxOState, DPState)
ledgerStateWithNregisteredKeys n m =
  makeLEDGERState (initLedgerState 1) $ txRegStakeKeys 0 (stakeKeys n m)

-- ===========================================================
-- Stake Key Registration example

-- Given a ledger state, presumably created by ledgerStateWithNregisteredKeys n m,
-- so that keys (n, 0, 0, 0, 0) through (m, 0, 0, 0, 0) are already registered,
-- register new keys (x, 0, 0, 0, 0) through (y, 0, 0, 0, 0).
-- Note that [n, m] must be disjoint from [x, y].
ledgerRegisterStakeKeys :: Word64 -> Word64 -> (UTxOState, DPState) -> ()
ledgerRegisterStakeKeys x y state =
  testLEDGER
    state
    (txRegStakeKeys 1 (stakeKeys x y))
    ledgerEnv

-- ===========================================================
-- Deregistration example

-- Create a transaction body that de-registers stake credentials,
-- corresponding to the keys seeded with (x, 0, 0, 0, 0) to (y, 0, 0, 0, 0)
txbDeRegStakeKey :: Word64 -> Word64 -> TxBody
txbDeRegStakeKey x y =
  TxBody
    (Set.fromList [TxIn genesisId 1])
    (StrictSeq.fromList [TxOut aliceAddr (Coin 100)])
    ( StrictSeq.fromList $
        fmap (DCertDeleg . DeRegKey . stakeKeyToCred) (stakeKeys x y)
    )
    (Wdrl Map.empty)
    (Coin 0)
    (SlotNo 10)
    SNothing
    SNothing

-- Create a transaction that deregisters stake credentials numbered x through y.
-- It spends the genesis coin indexed by 1.
txDeRegStakeKeys :: Word64 -> Word64 -> Tx
txDeRegStakeKeys x y =
  makeSimpleTx
    (txbDeRegStakeKey x y)
    (asWitness alicePay : (fmap asWitness (stakeKeys x y)))
    []

-- Given a ledger state, presumably created by ledgerStateWithNregisteredKeys n m,
-- so that keys (n, 0, 0, 0, 0) through (m, 0, 0, 0, 0) are already registered,
-- deregister keys (x, 0, 0, 0, 0) through (y, 0, 0, 0, 0).
-- Note that [x, y] must be contained in [n, m].
ledgerDeRegisterStakeKeys :: Word64 -> Word64 -> (UTxOState, DPState) -> ()
ledgerDeRegisterStakeKeys x y state =
  testLEDGER
    state
    (txDeRegStakeKeys x y)
    ledgerEnv

-- ===========================================================
-- Reward Withdrawal example

-- Create a transaction body that withdrawls from reward accounts,
-- corresponding to the keys seeded with (x, 0, 0, 0, 0) to (y, 0, 0, 0, 0).
txbWithdrawals :: Word64 -> Word64 -> TxBody
txbWithdrawals x y =
  TxBody
    (Set.fromList [TxIn genesisId 1])
    (StrictSeq.fromList [TxOut aliceAddr (Coin 100)])
    StrictSeq.empty
    ( Wdrl $ Map.fromList $
        fmap (\ks -> (RewardAcnt Testnet (stakeKeyToCred ks), Coin 0)) (stakeKeys x y)
    )
    (Coin 0)
    (SlotNo 10)
    SNothing
    SNothing

-- Create a transaction that withdrawls from a reward accounts.
-- It spends the genesis coin indexed by 1.
txWithdrawals :: Word64 -> Word64 -> Tx
txWithdrawals x y =
  makeSimpleTx
    (txbWithdrawals x y)
    (asWitness alicePay : (fmap asWitness (stakeKeys x y)))
    []

-- Given a ledger state, presumably created by ledgerStateWithNregisteredKeys n m,
-- so that keys (n, 0, 0, 0, 0) through (m, 0, 0, 0, 0) are already registered,
-- make reward withdrawls for keys (x, 0, 0, 0, 0) through (y, 0, 0, 0, 0).
-- Note that [x, y] must be contained in [n, m].
ledgerRewardWithdrawals :: Word64 -> Word64 -> (UTxOState, DPState) -> ()
ledgerRewardWithdrawals x y state = testLEDGER state (txWithdrawals x y) ledgerEnv

-- ===========================================================================
--
-- Register a stake pool when there are a lot of registered stake pool
--

-- Create stake pool key pairs, corresponding to seeds
-- (start, 0, 0, 0, 0) through (end, 0, 0, 0, 0)
poolColdKeys :: Word64 -> Word64 -> [KeyPair 'StakePool]
poolColdKeys start end = fmap (\w -> mkKeyPair' (w, 1, 0, 0, 0)) [start .. end]

firstStakePool :: KeyPair 'StakePool
firstStakePool = mkKeyPair' (1, 1, 0, 0, 0)

mkPoolKeyHash :: KeyPair 'StakePool -> KeyHash 'StakePool
mkPoolKeyHash = hashKey . vKey

firstStakePoolKeyHash :: KeyHash 'StakePool
firstStakePoolKeyHash = mkPoolKeyHash firstStakePool

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
      _poolOwners = Set.singleton $ (hashKey . vKey) stakeKeyOne,
      _poolRelays = StrictSeq.empty,
      _poolMD = SNothing
    }

-- Create stake pool registration certs
poolRegCerts :: [KeyPair 'StakePool] -> StrictSeq DCert
poolRegCerts = StrictSeq.fromList . fmap (DCertPool . RegPool . mkPoolParameters)

-- Create a transaction that registers stake pools.
txRegStakePools :: Natural -> [KeyPair 'StakePool] -> Tx
txRegStakePools ix keys =
  makeSimpleTx
    (txbFromCerts ix $ poolRegCerts keys)
    [asWitness alicePay, asWitness stakeKeyOne]
    (fmap asWitness keys)

-- Create a ledger state that has n registered stake pools.
-- The keys are seeded with (n, 1, 0, 0, 0) to (m, 1, 0, 0, 0)
-- It is pre-populated with 2 genesis coins.
ledgerStateWithNregisteredPools :: Word64 -> Word64 -> (UTxOState, DPState)
ledgerStateWithNregisteredPools n m =
  makeLEDGERState (initLedgerState 1) $ txRegStakePools 0 (poolColdKeys n m)

-- ===========================================================
-- Stake Pool Registration example

-- Given a ledger state, presumably created by ledgerStateWithNregisteredPools n m,
-- so that pool keys (n, 1, 0, 0, 0) through (m, 1, 0, 0, 0) are already registered,
-- register new pools (x, 0, 0, 0, 0) through (y, 0, 0, 0, 0).
-- Note that [n, m] must be disjoint from [x, y].
ledgerRegisterStakePools :: Word64 -> Word64 -> (UTxOState, DPState) -> ()
ledgerRegisterStakePools x y state =
  testLEDGER
    state
    (txRegStakePools 1 (poolColdKeys x y))
    ledgerEnv

-- ===========================================================
-- Stake Pool Re-Registration/Update example

-- Given a ledger state, presumably created by ledgerStateWithNregisteredPools n m,
-- so that pool keys (n, 1, 0, 0, 0) through (m, 1, 0, 0, 0) are already registered,
-- re-register pools (x, 0, 0, 0, 0) through (y, 0, 0, 0, 0).
-- Note that [n, m] must be contained in [x, y].
ledgerReRegisterStakePools :: Word64 -> Word64 -> (UTxOState, DPState) -> ()
ledgerReRegisterStakePools x y state =
  testLEDGER
    state
    (txRegStakePools 1 (poolColdKeys x y))
    ledgerEnv

-- ===========================================================
-- Stake Pool Retirement example

-- Create a transaction body that retires stake pools,
-- corresponding to the keys seeded with (x, 1, 0, 0, 0) to (y, 1, 0, 0, 0)
txbRetireStakePool :: Word64 -> Word64 -> TxBody
txbRetireStakePool x y =
  TxBody
    (Set.fromList [TxIn genesisId 1])
    (StrictSeq.fromList [TxOut aliceAddr (Coin 100)])
    ( StrictSeq.fromList $
        fmap
          (\ks -> DCertPool $ RetirePool (mkPoolKeyHash ks) (EpochNo 1))
          (poolColdKeys x y)
    )
    (Wdrl Map.empty)
    (Coin 0)
    (SlotNo 10)
    SNothing
    SNothing

-- Create a transaction that retires stake pools x through y.
-- It spends the genesis coin indexed by 1.
txRetireStakePool :: Word64 -> Word64 -> Tx
txRetireStakePool x y =
  makeSimpleTx
    (txbRetireStakePool x y)
    [asWitness alicePay]
    (fmap asWitness (poolColdKeys x y))

-- Given a ledger state, presumably created by ledgerStateWithNregisteredPools n m,
-- so that pool keys (n, 1, 0, 0, 0) through (m, 1, 0, 0, 0) are already registered,
-- retire pools (x, 0, 0, 0, 0) through (y, 0, 0, 0, 0).
-- Note that [n, m] must be contained in [x, y].
ledgerRetireStakePools :: Word64 -> Word64 -> (UTxOState, DPState) -> ()
ledgerRetireStakePools x y state = testLEDGER state (txRetireStakePool x y) ledgerEnv

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
    (makeLEDGERState (initLedgerState 2) $ txRegStakeKeys 0 (stakeKeys 1 n))
    (txRegStakePools 1 (poolColdKeys 1 m))

-- Create a transaction body that delegates several keys to ONE stake pool,
-- corresponding to the keys seeded with (n, 0, 0, 0, 0) to (m, 0, 0, 0, 0)
txbDelegate :: Word64 -> Word64 -> TxBody
txbDelegate n m =
  TxBody
    (Set.fromList [TxIn genesisId 2])
    (StrictSeq.fromList [TxOut aliceAddr (Coin 100)])
    ( StrictSeq.fromList $
        fmap
          (\ks -> DCertDeleg $ Delegate (Delegation (stakeKeyToCred ks) firstStakePoolKeyHash))
          (stakeKeys n m)
    )
    (Wdrl Map.empty)
    (Coin 0)
    (SlotNo 10)
    SNothing
    SNothing

-- Create a transaction that delegates stake.
txDelegate :: Word64 -> Word64 -> Tx
txDelegate n m =
  makeSimpleTx
    (txbDelegate n m)
    (asWitness alicePay : fmap asWitness (stakeKeys n m))
    []

-- Given a ledger state, presumably created by ledgerStateWithNkeysMpools n m,
-- so that stake keys (1, 0, 0, 0, 0) through (n, 0, 0, 0, 0) are already registered
-- and pool keys (1, 1, 0, 0, 0) through (m, 1, 0, 0, 0) are already registered,
-- delegate stake keys (x, 0, 0, 0, 0) through (y, 0, 0, 0, 0) to ONE pool.
-- Note that [x, y] must be contained in [1, n].
ledgerDelegateManyKeysOnePool :: Word64 -> Word64 -> (UTxOState, DPState) -> ()
ledgerDelegateManyKeysOnePool x y state = testLEDGER state (txDelegate x y) ledgerEnv
