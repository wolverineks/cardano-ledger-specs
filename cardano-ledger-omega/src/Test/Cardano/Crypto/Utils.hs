{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}

module Test.Cardano.Crypto.Utils
  ( mkKeyPair,
    testGlobals,
    genesisId,
  )
where

import Cardano.Binary (ToCBOR (..))
import Cardano.Crypto.DSIGN.Class (DSIGNAlgorithm (..))
import Cardano.Crypto.Hash
  ( Blake2b_256,
    hashToBytes,
    hashWithSerialiser,
  )
import qualified Cardano.Crypto.Hash as Hash
import Cardano.Crypto.Seed (Seed, mkSeedFromBytes)
import Cardano.Ledger.Crypto (DSIGN, HASH)
import Cardano.Ledger.SafeHash (unsafeMakeSafeHash)
import Cardano.Slotting.EpochInfo (fixedEpochInfo)
import Cardano.Slotting.Time (SystemStart (..), mkSlotLength)
import Data.Coerce (coerce)
import Data.Maybe (fromMaybe)
import Data.Ratio (Ratio)
import Data.Time.Clock.POSIX (posixSecondsToUTCTime)
import Data.Word (Word64)
import Shelley.Spec.Ledger.BaseTypes
  ( Globals (..),
    Network (..),
    UnitInterval,
    mkActiveSlotCoeff,
    mkUnitInterval,
  )
import Shelley.Spec.Ledger.Keys (VKey (..))
import Shelley.Spec.Ledger.Slot (EpochSize (..))
import Shelley.Spec.Ledger.Tx (TxId (TxId))

-- | Construct a seed from a bunch of Word64s
--
--   We multiply these words by some extra stuff to make sure they contain
--   enough bits for our seed.
mkSeedFromWords ::
  (Word64, Word64, Word64, Word64, Word64) ->
  Seed
mkSeedFromWords stuff =
  mkSeedFromBytes . hashToBytes $ hashWithSerialiser @Blake2b_256 toCBOR stuff

-- | For testing purposes, generate a deterministic key pair given a seed.
mkKeyPair ::
  forall crypto kd.
  DSIGNAlgorithm (DSIGN crypto) =>
  (Word64, Word64, Word64, Word64, Word64) ->
  (SignKeyDSIGN (DSIGN crypto), VKey kd crypto)
mkKeyPair seed =
  let sk = genKeyDSIGN $ mkSeedFromWords seed
   in (sk, VKey $ deriveVerKeyDSIGN sk)

-- | You vouch that argument is in [0; 1].
unsafeMkUnitInterval :: Ratio Word64 -> UnitInterval
unsafeMkUnitInterval r =
  fromMaybe (error "could not construct unit interval") $ mkUnitInterval r

testGlobals :: Globals
testGlobals =
  Globals
    { epochInfoWithErr = fixedEpochInfo (EpochSize 100) (mkSlotLength 1),
      slotsPerKESPeriod = 20,
      stabilityWindow = 33,
      randomnessStabilisationWindow = 33,
      securityParameter = 10,
      maxKESEvo = 10,
      quorum = 5,
      maxMajorPV = 1000,
      maxLovelaceSupply = 45 * 1000 * 1000 * 1000 * 1000 * 1000,
      activeSlotCoeff = mkActiveSlotCoeff . unsafeMkUnitInterval $ 0.9,
      networkId = Testnet,
      systemStart = SystemStart $ posixSecondsToUTCTime 0
    }

-- | We share this dummy TxId as genesis transaction id across eras
genesisId ::
  Hash.HashAlgorithm (HASH crypto) =>
  TxId crypto
genesisId = TxId (unsafeMakeSafeHash (mkDummyHash 0))
  where
    mkDummyHash :: forall h a. Hash.HashAlgorithm h => Int -> Hash.Hash h a
    mkDummyHash = coerce . Hash.hashWithSerialiser @h toCBOR
