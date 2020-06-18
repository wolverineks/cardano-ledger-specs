{-# LANGUAGE DataKinds #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}

-- | This module is similar to ConcreteCryptoTypes, we made a changes to use a longer hash
--   function than ShortHash for benchmarking.  We have replace ShortHash with Blake2b_256.
-- It also includes a few versions of functions defined in Utils.hs, specialized to Benchmark Crypto
module Test.Shelley.Spec.Ledger.BenchmarkCrypto where

import Cardano.Crypto.DSIGN (MockDSIGN, VerKeyDSIGN, deriveVerKeyDSIGN, genKeyDSIGN)
import Cardano.Crypto.Hash (Hash (UnsafeHash), MD5, hash)
import Cardano.Crypto.Hash.Blake2b (Blake2b_256)
import Cardano.Crypto.KES (MockKES)
import Cardano.Crypto.Seed (Seed, mkSeedFromBytes)
import Cardano.Crypto.VRF (deriveVerKeyVRF, genKeyVRF)
import Control.Monad.Trans.Reader (runReaderT)
import Data.Coerce (coerce)
import Data.Functor.Identity (runIdentity)
import Data.Map (Map)
import Data.Maybe (fromMaybe)
import Data.Ratio (Ratio)
import Data.Word (Word64)
import Shelley.Spec.Ledger.Address (pattern Addr)
import qualified Shelley.Spec.Ledger.Address as TxData
import Shelley.Spec.Ledger.BaseTypes (Network (..), ShelleyBase, UnitInterval, mkUnitInterval)
import qualified Shelley.Spec.Ledger.BlockChain as BlockChain
import Shelley.Spec.Ledger.Coin (Coin (..))
import Shelley.Spec.Ledger.Credential (Credential (..), StakeReference (..))
import qualified Shelley.Spec.Ledger.Credential as TxData
import Shelley.Spec.Ledger.Crypto
import qualified Shelley.Spec.Ledger.Delegation.Certificates as Delegation.Certificates
import qualified Shelley.Spec.Ledger.EpochBoundary as EpochBoundary
import Shelley.Spec.Ledger.Keys (KeyRole (..), hashKey, vKey)
import qualified Shelley.Spec.Ledger.Keys as Keys
import qualified Shelley.Spec.Ledger.LedgerState as LedgerState
import qualified Shelley.Spec.Ledger.OCert as OCert
import Shelley.Spec.Ledger.PParams
import qualified Shelley.Spec.Ledger.PParams as PParams
import qualified Shelley.Spec.Ledger.Rewards as Rewards
import qualified Shelley.Spec.Ledger.STS.Chain as STS.Chain
import qualified Shelley.Spec.Ledger.STS.Deleg as STS.Deleg
import qualified Shelley.Spec.Ledger.STS.Delegs as STS.Delegs
import qualified Shelley.Spec.Ledger.STS.Delpl as STS.Delpl
import qualified Shelley.Spec.Ledger.STS.Ledger as STS.Ledger
import qualified Shelley.Spec.Ledger.STS.Ledgers as STS.Ledgers
import qualified Shelley.Spec.Ledger.STS.NewEpoch as STS.NewEpoch
import qualified Shelley.Spec.Ledger.STS.Ocert as STS.Ocert
import qualified Shelley.Spec.Ledger.STS.Pool as STS.Pool
import qualified Shelley.Spec.Ledger.STS.PoolReap as STS.PoolReap
import qualified Shelley.Spec.Ledger.STS.Ppup as STS.Ppup
import qualified Shelley.Spec.Ledger.STS.Tick as STS.Tick
import qualified Shelley.Spec.Ledger.STS.Utxo as STS.Utxo
import qualified Shelley.Spec.Ledger.STS.Utxow as STS.Utxow
import qualified Shelley.Spec.Ledger.Scripts as Scripts
import Shelley.Spec.Ledger.Slot (EpochNo (..))
import qualified Shelley.Spec.Ledger.Tx as Tx
import qualified Shelley.Spec.Ledger.TxData as TxData
import qualified Shelley.Spec.Ledger.UTxO as UTxO
import Test.Cardano.Crypto.VRF.Fake (FakeVRF)
import Test.Shelley.Spec.Ledger.Utils (testGlobals)

data BenchmarkCrypto

instance Crypto BenchmarkCrypto where
  type ADDRHASH BenchmarkCrypto = Blake2b_256
  type HASH BenchmarkCrypto = Blake2b_256
  type DSIGN BenchmarkCrypto = MockDSIGN
  type KES BenchmarkCrypto = MockKES 10
  type VRF BenchmarkCrypto = FakeVRF

type DCert = Delegation.Certificates.DCert BenchmarkCrypto

type PoolDistr = Delegation.Certificates.PoolDistr BenchmarkCrypto

type Delegation = TxData.Delegation BenchmarkCrypto

type PoolParams = TxData.PoolParams BenchmarkCrypto

type RewardAcnt = TxData.RewardAcnt BenchmarkCrypto

type StakePools = TxData.StakePools BenchmarkCrypto

type KeyHash kr = Keys.KeyHash kr BenchmarkCrypto

pattern KeyHash ::
  forall (h :: Keys.HashType) (kr :: Keys.KeyRole h).
  ( Keys.AlgorithmForHashType BenchmarkCrypto h
      ~ Blake2b_256
  ) =>
  Keys.Hash BenchmarkCrypto (VerKeyDSIGN (DSIGN BenchmarkCrypto)) ->
  KeyHash (kr :: Keys.KeyRole h)
pattern KeyHash h = Keys.KeyHash h

{-# COMPLETE KeyHash #-}

type GenDelegPair = Keys.GenDelegPair BenchmarkCrypto

pattern GenDelegPair :: KeyHash 'Keys.GenesisDelegate -> VRFKeyHash -> GenDelegPair
pattern GenDelegPair kh vrfKH = Keys.GenDelegPair kh vrfKH

{-# COMPLETE GenDelegPair #-}

type GenDelegs = Keys.GenDelegs BenchmarkCrypto

pattern GenDelegs :: (Map (KeyHash 'Keys.Genesis) GenDelegPair) -> GenDelegs
pattern GenDelegs m = Keys.GenDelegs m

{-# COMPLETE GenDelegs #-}

type KeyPair kr = Keys.KeyPair kr BenchmarkCrypto

pattern KeyPair :: VKey kr -> SignKeyDSIGN -> KeyPair kr
pattern KeyPair vk sk = Keys.KeyPair vk sk

{-# COMPLETE KeyPair #-}

type GenesisKeyPair = Keys.KeyPair 'Keys.Genesis BenchmarkCrypto

type SignedDSIGN = Keys.SignedDSIGN BenchmarkCrypto

type SignKeyDSIGN = Keys.SignKeyDSIGN BenchmarkCrypto

type VKey kr = Keys.VKey kr BenchmarkCrypto

pattern VKey :: VerKeyDSIGN (DSIGN BenchmarkCrypto) -> VKey kr
pattern VKey x = Keys.VKey x

{-# COMPLETE VKey #-}

type KeyPairs = LedgerState.KeyPairs BenchmarkCrypto

type MultiSigPairs = [(MultiSig, MultiSig)]

type VKeyGenesis = Keys.VKey 'Keys.Genesis BenchmarkCrypto

type EpochState = LedgerState.EpochState BenchmarkCrypto

type NEWEPOCH = STS.NewEpoch.NEWEPOCH BenchmarkCrypto

type LedgerState = LedgerState.LedgerState BenchmarkCrypto

type UTxOState = LedgerState.UTxOState BenchmarkCrypto

type DState = LedgerState.DState BenchmarkCrypto

type PState = LedgerState.PState BenchmarkCrypto

type DPState = LedgerState.DPState BenchmarkCrypto

type StakeReference = TxData.StakeReference BenchmarkCrypto

type Addr = TxData.Addr BenchmarkCrypto

type Tx = Tx.Tx BenchmarkCrypto

type TxBody = Tx.TxBody BenchmarkCrypto

type TxIn = Tx.TxIn BenchmarkCrypto

type TxOut = Tx.TxOut BenchmarkCrypto

type TxId = TxData.TxId BenchmarkCrypto

type UTxO = UTxO.UTxO BenchmarkCrypto

type Block = BlockChain.Block BenchmarkCrypto

type LaxBlock = BlockChain.LaxBlock BenchmarkCrypto

type BHBody = BlockChain.BHBody BenchmarkCrypto

type SignKeyKES = Keys.SignKeyKES BenchmarkCrypto

type VerKeyKES = Keys.VerKeyKES BenchmarkCrypto

type SignKeyVRF = Keys.SignKeyVRF BenchmarkCrypto

type VerKeyVRF = Keys.VerKeyVRF BenchmarkCrypto

type VrfKeyPairs = [(SignKeyVRF, VerKeyVRF)]

type CertifiedVRF = Keys.CertifiedVRF BenchmarkCrypto

type BHeader = BlockChain.BHeader BenchmarkCrypto

type OCert = OCert.OCert BenchmarkCrypto

type OCertEnv = STS.Ocert.OCertEnv BenchmarkCrypto

type HashHeader = BlockChain.HashHeader BenchmarkCrypto

type PrevHash = BlockChain.PrevHash BenchmarkCrypto

type NewEpochState = LedgerState.NewEpochState BenchmarkCrypto

type NonMyopic = Rewards.NonMyopic BenchmarkCrypto

type RewardUpdate = LedgerState.RewardUpdate BenchmarkCrypto

type OBftSlot = LedgerState.OBftSlot BenchmarkCrypto

type ChainState = STS.Chain.ChainState BenchmarkCrypto

type CHAIN = STS.Chain.CHAIN BenchmarkCrypto

type TICK = STS.Tick.TICK BenchmarkCrypto

type TickEnv = STS.Tick.TickEnv BenchmarkCrypto

type UTXOW = STS.Utxow.UTXOW BenchmarkCrypto

type UTXO = STS.Utxo.UTXO BenchmarkCrypto

type UtxoEnv = STS.Utxo.UtxoEnv BenchmarkCrypto

type DELEG = STS.Deleg.DELEG BenchmarkCrypto

type DELPL = STS.Delpl.DELPL BenchmarkCrypto

type LEDGER = STS.Ledger.LEDGER BenchmarkCrypto

type LEDGERS = STS.Ledgers.LEDGERS BenchmarkCrypto

type LedgerEnv = STS.Ledger.LedgerEnv

type DELEGS = STS.Delegs.DELEGS BenchmarkCrypto

type POOL = STS.Pool.POOL BenchmarkCrypto

type POOLREAP = STS.PoolReap.POOLREAP BenchmarkCrypto

type PPUP = STS.Ppup.PPUP BenchmarkCrypto

type Credential kr = TxData.Credential kr BenchmarkCrypto

type StakeCreds = TxData.StakeCreds BenchmarkCrypto

type MultiSig = Scripts.MultiSig BenchmarkCrypto

type ScriptHash = Scripts.ScriptHash BenchmarkCrypto

type WitVKey = TxData.WitVKey BenchmarkCrypto

type WitnessSet = Tx.WitnessSet BenchmarkCrypto

type Wdrl = TxData.Wdrl BenchmarkCrypto

type SnapShot = EpochBoundary.SnapShot BenchmarkCrypto

type SnapShots = EpochBoundary.SnapShots BenchmarkCrypto

type Stake = EpochBoundary.Stake BenchmarkCrypto

type Update = PParams.Update BenchmarkCrypto

type ProposedPPUpdates = PParams.ProposedPPUpdates BenchmarkCrypto

type VRFKeyHash = Keys.Hash BenchmarkCrypto (Keys.VerKeyVRF BenchmarkCrypto)

hashKeyVRF ::
  Keys.VerKeyVRF BenchmarkCrypto ->
  VRFKeyHash
hashKeyVRF = Keys.hashVerKeyVRF

-- ==================================================================

-- | Construct a seed from a bunch of Word64s
--
--   We multiply these words by some extra stuff to make sure they contain
--   enough bits for our seed.
mkSeedFromWords ::
  (Word64, Word64, Word64, Word64, Word64) ->
  Seed
mkSeedFromWords stuff =
  mkSeedFromBytes . coerce $ hash @MD5 stuff

-- | For testing purposes, generate a deterministic genesis key pair given a seed.
mkGenKey :: (Word64, Word64, Word64, Word64, Word64) -> (SignKeyDSIGN, VKeyGenesis)
mkGenKey seed =
  let sk = genKeyDSIGN $ mkSeedFromWords seed
   in (sk, VKey $ deriveVerKeyDSIGN sk)

-- | For testing purposes, generate a deterministic key pair given a seed.
mkKeyPair :: (Word64, Word64, Word64, Word64, Word64) -> (SignKeyDSIGN, VKey kr)
mkKeyPair seed =
  let sk = genKeyDSIGN $ mkSeedFromWords seed
   in (sk, VKey $ deriveVerKeyDSIGN sk)

-- | For testing purposes, generate a deterministic key pair given a seed.
mkKeyPair' :: (Word64, Word64, Word64, Word64, Word64) -> KeyPair kr
mkKeyPair' seed = KeyPair vk sk
  where
    (sk, vk) = mkKeyPair seed

mkAddr :: (KeyPair 'Payment, KeyPair 'Staking) -> Addr
mkAddr (payKey, stakeKey) =
  Addr
    Testnet
    (KeyHashObj . hashKey $ vKey payKey)
    (StakeRefBase . KeyHashObj . hashKey $ vKey stakeKey)

-- | You vouch that argument is in [0; 1].
unsafeMkUnitInterval :: Ratio Word64 -> UnitInterval
unsafeMkUnitInterval r =
  fromMaybe (error "could not construct unit interval") $ mkUnitInterval r

-- | For testing purposes, generate a deterministic VRF key pair given a seed.
mkVRFKeyPair :: (Word64, Word64, Word64, Word64, Word64) -> (SignKeyVRF, VerKeyVRF)
mkVRFKeyPair seed =
  let sk = genKeyVRF $ mkSeedFromWords seed
   in (sk, deriveVerKeyVRF sk)

runShelleyBase :: ShelleyBase a -> a
runShelleyBase act = runIdentity $ runReaderT act testGlobals

ppsEx1 :: PParams
ppsEx1 =
  emptyPParams
    { _maxBBSize = 50000,
      _maxBHSize = 10000,
      _maxTxSize = 10000,
      _eMax = EpochNo 10000,
      _keyDeposit = Coin 7,
      _poolDeposit = Coin 250,
      _d = unsafeMkUnitInterval 0.5,
      _tau = unsafeMkUnitInterval 0.2,
      _rho = unsafeMkUnitInterval 0.0021,
      _minUTxOValue = 100
    }
