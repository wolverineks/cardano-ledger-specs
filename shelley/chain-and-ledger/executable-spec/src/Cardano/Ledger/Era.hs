{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DataKinds #-}

-- | Support for multiple (Shelley-based) eras in the ledger.
module Cardano.Ledger.Era
  ( Era,
    Crypto,
    PreviousEra,
    TranslationContext,
    TranslateEra (..),
    translateEra',
    translateEraMaybe,
  )
where

import qualified Cardano.Ledger.Crypto as CryptoClass
import Control.Monad.Except (Except, runExcept)
import Data.Coerce (Coercible, coerce)
import Data.Kind (Type)
import Data.Typeable (Typeable)
import Data.Void (Void, absurd)
import GHC.Generics (Generic1 (..), Generic (..), U1 (..), (:+:)(..), (:*:)(..), K1 (..), M1 (..), V1)

--------------------------------------------------------------------------------
-- Era
--------------------------------------------------------------------------------

class
  ( CryptoClass.Crypto (Crypto e),
    Typeable e
  ) =>
  Era e
  where
  type Crypto e :: Type

--------------------------------------------------------------------------------
-- Era translation
--------------------------------------------------------------------------------

-- | Map an era to its predecessor.
--
-- For example:
--
-- > type instance PreviousEra (AllegraEra c) = ShelleyEra c
type family PreviousEra era :: Type

-- | Per-era context used for 'TranslateEra'.
--
-- This context will be passed to the translation instances of /all/ types of
-- that particular era. In practice, most instances won't need the context, but
-- this approach makes the translation composable (as opposed to having a
-- separate context per type).
type family TranslationContext era :: Type

-- | Translation of types between eras, e.g., from Shelley to Allegra.
--
-- When @era@ is just a phantom type parameter, an empty standalone deriving can be used:
--
-- > newtype Foo era = Foo Int
-- >
-- > instance TranslateEra (Allegra c) Foo
--
-- Note that one could use @DerivingAnyClass@ (@deriving (TranslateEra (Allegra
-- c))@), but this would introduce an undesired coupling between the
-- era-parametric type and (a) particular era(s). The intention is to have a
-- module with orphan instances per era.
--
-- In most cases, the @era@ parameter won't be phantom, and a manual instance
-- will have to be written:
--
-- > newtype Bar era = Bar (Addr era)
-- >
-- > instance CryptoClass.Crypto c => TranslateEra (Allegra c) Bar where
-- >     translateEra ctxt = Bar <$> translateEra ctxt
-- >
-- > -- With the following instance being in scope:
-- > instance CryptoClass.Crypto c => TranslatEra (Allegra c) Addr
--
-- Note: we use 'PreviousEra' instead of @NextEra@ as an era definitely knows
-- its predecessor, but not necessarily its successor. Moreover, one could argue
-- that it makes more sense to define the translation from era A to era B where
-- era B is defined, than where era A is defined.
class (Era era, Era (PreviousEra era)) => TranslateEra era f where
  -- | Most translations should be infallible (default instance), but we leave
  -- the door open for partial translations.
  --
  -- For a partial translation, override the default type to be '()' or a
  -- concrete error type.
  type TranslationError era f :: Type

  type TranslationError era f = Void

  -- | Translate a type @f@ parameterised by the era from an era to the era
  -- after it.
  --
  -- The translation is a given the translation context of @era@.
  --
  -- A default instance is provided for when the two types are 'Coercible'.
  translateEra :: TranslationContext era -> f (PreviousEra era) -> Except (TranslationError era f) (f era)
  default translateEra ::
    Coercible (f (PreviousEra era)) (f era) =>
    TranslationContext era ->
    f (PreviousEra era) ->
    Except (TranslationError era f) (f era)
  translateEra _ = return . coerce

-- | Variant of 'translateEra' for when 'TranslationError' is 'Void' and the
-- translation thus cannot fail.
translateEra' ::
  (TranslateEra era f, TranslationError era f ~ Void) =>
  TranslationContext era ->
  f (PreviousEra era) ->
  f era
translateEra' ctxt = either absurd id . runExcept . translateEra ctxt

-- | Variant of 'translateEra' for when 'TranslationError' is '()', converting
-- the result to a 'Maybe'.
translateEraMaybe ::
  (TranslateEra era f, TranslationError era f ~ ()) =>
  TranslationContext era ->
  f (PreviousEra era) ->
  Maybe (f era)
translateEraMaybe ctxt =
  either (const Nothing) Just . runExcept . translateEra ctxt


--------------------------------------------------------------------------------------------
-- Generic support
--------------------------------------------------------------------------------------------

gTranslateEra :: forall era (f :: * -> *).
  ( Generic1 f
  , GTranslateEra era (Rep1 f)
  , TranslationError era f ~ Void
  ) =>
  TranslationContext era ->
  f (PreviousEra era) ->
  Except (TranslationError era f) (f era)
gTranslateEra ctxt x = fromCurrentRep <$> gTranslateEra' ctxt prevRep
  where
    prevRep :: Rep1 f (PreviousEra era)
    prevRep = from1 x
    fromCurrentRep :: Rep1 f era -> f era
    fromCurrentRep = to1

class GTranslateEra era f where
  gTranslateEra' ::
    TranslationContext era ->
    f (PreviousEra era) ->
    Except Void (f era)

instance GTranslateEra era U1 where
  gTranslateEra' _ctxt U1 = pure U1

instance (GTranslateEra era f, GTranslateEra era g) => GTranslateEra era (f :+: g) where
  gTranslateEra' ctxt (L1 f) = L1 <$> gTranslateEra' ctxt f
  gTranslateEra' ctxt (R1 g) = R1 <$> gTranslateEra' ctxt g

instance (GTranslateEra era f, GTranslateEra era g) => GTranslateEra era (f :*: g) where
  gTranslateEra' ctxt (f :*: g) = (:*:)  <$> gTranslateEra' ctxt f <*> gTranslateEra' ctxt g

instance (GTranslateEra era f) => GTranslateEra era (M1 i t f) where
  gTranslateEra' ctxt (M1 f) = M1 <$> gTranslateEra' ctxt f

instance GTranslateEra era V1 where
  gTranslateEra' ctxt v = undefined

-- type family EraParam (era :: *) (f :: *) where
  -- EraParam era (f era) = 'True
  -- EraParam era f = 'False

instance (TranslateEra era f) => GTranslateEra era (K1 i (f era)) where
  gTranslateEra' ctxt (K1 x) = something
    where
      something :: Either Void (K1 (f era) p)
      something = K1 <$> foo
      foo :: Either Void (f era)
      foo = _help

