{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FunctionalDependencies #-}

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

import Data.Proxy (Proxy (..))
import qualified Cardano.Ledger.Crypto as CryptoClass
import Control.Monad.Except (Except, runExcept)
import Data.Coerce (Coercible, coerce)
import Data.Kind (Type)
import Data.Typeable (Typeable)
import Data.Void (Void, absurd)
import GHC.Generics (Generic1 (..), Generic (..), U1 (..), (:+:)(..), (:*:)(..), K1 (..), M1 (..), V1)
import Data.Maybe (Maybe (..))

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
  ( Generic (f era)
  , Generic (f (PreviousEra era))
  , GTranslateEra era (Rep (f (PreviousEra era))) (Rep (f era))
  , TranslationError era f ~ Void
  ) =>
  TranslationContext era ->
  f (PreviousEra era) ->
  Except (TranslationError era f) (f era)
gTranslateEra ctxt x = fromCurrentRep <$> gTranslateEra' eraProxy ctxt prevRep
  where
    eraProxy = Proxy :: Proxy era
    prevRep :: Rep f (PreviousEra era)
    prevRep = from x
    fromCurrentRep :: Rep f era -> f era
    fromCurrentRep = to

class GTranslateEra era prev current | current era -> prev where
  gTranslateEra' :: proxy era -> TranslationContext era -> prev x -> Except Void (current x)

instance (PreviousEra era ~ e0) => GTranslateEra era (U1 e0) (U1 era) where
  gTranslateEra' _proxy _ctxt U1 = pure U1

{-
instance (GTranslateEra era f, GTranslateEra era g) => GTranslateEra era ((f :+: g) where
  gTranslateEra' ctxt (L1 f) = L1 <$> gTranslateEra' ctxt f
  gTranslateEra' ctxt (R1 g) = R1 <$> gTranslateEra' ctxt g

instance (GTranslateEra era f, GTranslateEra era g) => GTranslateEra era (f :*: g) where
  gTranslateEra' ctxt (f :*: g) = (:*:)  <$> gTranslateEra' ctxt f <*> gTranslateEra' ctxt g

instance (GTranslateEra era f) => GTranslateEra era (M1 i t f) where
  gTranslateEra' ctxt (M1 f) = M1 <$> gTranslateEra' ctxt f

instance GTranslateEra era V1 where
  gTranslateEra' ctxt v = undefined

instance (GTranslateBranch era x (EraParam era x)) => GTranslateEra era (K1 i x) where
  gTranslateEra' ctxt arg = K1 <$> translationResult
    where
    foo0 :: K1 i x (PreviousEra era)
    foo0 = arg
    foo1 :: x
    foo1 = unK1 foo0
    foo :: Prev era x (EraParam era x)
    foo = undefined
    translationResult ::  Except Void x
    translationResult = gTranslateEraBranch eraProxy tfProxy ctxt foo
    --result = gTranslateEraBranch eraProxy tfProxy ctxt x :: x
    eraProxy = Proxy :: Proxy era
    tfProxy :: Proxy (EraParam era x)
    tfProxy = undefined


type family EraParam (era :: *) (f :: *) where
  EraParam era (g era) = 'Just g
  EraParam era g = 'Nothing

class GTranslateBranch era x (m :: Maybe (* -> *)) where
  type Prev era x m :: *
  gTranslateEraBranch :: proxy1 era -> proxy2 m -> TranslationContext era -> Prev era x m -> Except Void x

-- era appears as a type parameter
instance
  ( TranslationError era f ~ Void, x ~ f era, TranslateEra era f)
   => GTranslateBranch era x ('Just f) where
  type Prev era x ('Just f) = f (PreviousEra era)
  gTranslateEraBranch _ _ = translateEra

-- era doesnt appear as a type parameter
instance GTranslateBranch era x 'Nothing where
  type Prev era x 'Nothing = x
  gTranslateEraBranch _ _ ctxt x = pure x
-}
