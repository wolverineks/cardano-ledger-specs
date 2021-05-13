{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}

module Cardano.Ledger.Proof where

import Cardano.Crypto.DSIGN (MockDSIGN)
import Cardano.Crypto.Hash (MD5Prefix)
import Cardano.Crypto.KES (MockKES)
import Cardano.Ledger.Allegra (AllegraEra)
import Cardano.Ledger.Alonzo (AlonzoEra)
import Cardano.Ledger.Crypto (StandardCrypto)
import qualified Cardano.Ledger.Crypto as CC (Crypto)
import qualified Cardano.Ledger.Crypto as CryptoClass
import Cardano.Ledger.Era (Era (..), ValidateScript (..))
import Cardano.Ledger.Mary (MaryEra)
import Cardano.Ledger.Shelley (ShelleyEra)
import Shelley.Spec.Ledger.API (PraosCrypto)
import Test.Cardano.Crypto.VRF.Fake (FakeVRF)

-- =================================================
-- GADTs for witnessing Crypto and Era

data C_Crypto

instance CryptoClass.Crypto C_Crypto where
  type HASH C_Crypto = MD5Prefix 10
  type ADDRHASH C_Crypto = MD5Prefix 8
  type DSIGN C_Crypto = MockDSIGN
  type KES C_Crypto = MockKES 10
  type VRF C_Crypto = FakeVRF

instance PraosCrypto C_Crypto

type Mock = C_Crypto

type Standard = StandardCrypto

type ShelleyMock = ShelleyEra Mock

type ShelleyReal = ShelleyEra Standard

type AllegraMock = AllegraEra Mock

type AllegraReal = AllegraEra Standard

type MaryMock = MaryEra Mock

type MaryReal = MaryEra Standard

type AlonzoMock = AlonzoEra Mock

type AlonzoReal = AlonzoEra Standard

data Evidence c where
  Standard :: Evidence Standard
  Mock :: Evidence Mock

-- | Proof of a valid (predefined) era
data Proof era where
  Shelley :: forall c. CC.Crypto c => Evidence c -> Proof (ShelleyEra c)
  Mary :: forall c. CC.Crypto c => Evidence c -> Proof (MaryEra c)
  Allegra :: forall c. CC.Crypto c => Evidence c -> Proof (AllegraEra c)
  Alonzo :: forall c. CC.Crypto c => Evidence c -> Proof (AlonzoEra c)

instance Show (Proof e) where
  show (Shelley c) = "Shelley " ++ show c
  show (Allegra c) = "Allegra " ++ show c
  show (Mary c) = "Mary " ++ show c
  show (Alonzo c) = "Alonzo " ++ show c

instance Show (Evidence c) where
  show Mock = "Mock"
  show Standard = "Standard"

-- ==================================
-- Reflection over Crypto and Era

class CC.Crypto c => ReflectC c where
  evidence :: Evidence c
  liftC :: forall a. (Evidence c -> a) -> a
  liftC f = f (evidence @c)

instance ReflectC StandardCrypto where
  evidence = Standard

instance ReflectC C_Crypto where
  evidence = Mock

class
  ( Era era,
    ValidateScript era,
    ReflectC (Crypto era)
  ) =>
  Reflect era
  where
  reify :: Proof era
  lift :: forall a. (Proof era -> a) -> a
  lift f = f (reify @era)

instance ReflectC c => Reflect (AlonzoEra c) where
  reify = Alonzo evidence

instance ReflectC c => Reflect (MaryEra c) where
  reify = Mary evidence

instance ReflectC c => Reflect (AllegraEra c) where
  reify = Allegra evidence

instance ReflectC c => Reflect (ShelleyEra c) where
  reify = Shelley evidence
