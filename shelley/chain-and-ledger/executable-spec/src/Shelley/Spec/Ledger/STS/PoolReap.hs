{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE EmptyDataDeriving #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Shelley.Spec.Ledger.STS.PoolReap
  ( POOLREAP,
    PoolreapEvent (..),
    PoolreapState (..),
    PredicateFailure,
    PoolreapPredicateFailure,
  )
where

import Cardano.Ledger.BaseTypes (ShelleyBase)
import Cardano.Ledger.Coin (Coin)
import qualified Cardano.Ledger.Core as Core
import Cardano.Ledger.Credential (Credential)
import Cardano.Ledger.Era (Crypto)
import Cardano.Ledger.Keys (KeyHash, KeyRole (StakePool, Staking))
import Cardano.Ledger.Slot (EpochNo (..))
import Cardano.Ledger.Val ((<+>), (<->))
import Control.SetAlgebra (dom, eval, setSingleton, (∈), (∪+), (⋪), (⋫), (▷), (◁))
import Control.State.Transition
  ( Assertion (..),
    STS (..),
    TRC (..),
    TransitionRule,
    judgmentContext,
    tellEvent,
  )
import Data.Default.Class (Default, def)
import Data.Foldable (fold)
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import Data.Typeable (Typeable)
import GHC.Generics (Generic)
import GHC.Records
import NoThunks.Class (NoThunks (..))
import Shelley.Spec.Ledger.EpochBoundary (obligation)
import Shelley.Spec.Ledger.LedgerState
  ( AccountState (..),
    DState (..),
    PState (..),
    TransUTxOState,
    UTxOState (..),
  )
import Shelley.Spec.Ledger.TxBody (RewardAcnt, getRwdCred, _poolRAcnt)

data POOLREAP era

data PoolreapState era = PoolreapState
  { prUTxOSt :: UTxOState era,
    prAcnt :: AccountState,
    prDState :: DState (Crypto era),
    prPState :: PState (Crypto era)
  }

deriving stock instance
  (TransUTxOState Show era) =>
  Show (PoolreapState era)

data PoolreapPredicateFailure era -- No predicate failures
  deriving (Show, Eq, Generic)

data PoolreapEvent era = RetiredPools
  { refundPools :: Map.Map (Credential 'Staking (Crypto era)) (Map.Map (KeyHash 'StakePool (Crypto era)) Coin),
    unclaimedPools :: Map.Map (Credential 'Staking (Crypto era)) (Map.Map (KeyHash 'StakePool (Crypto era)) Coin)
  }

instance NoThunks (PoolreapPredicateFailure era)

instance Default (UTxOState era) => Default (PoolreapState era) where
  def = PoolreapState def def def def

instance
  forall era.
  ( Typeable era,
    Default (PoolreapState era),
    HasField "_poolDeposit" (Core.PParams era) Coin,
    HasField "_keyDeposit" (Core.PParams era) Coin
  ) =>
  STS (POOLREAP era)
  where
  type State (POOLREAP era) = PoolreapState era
  type Signal (POOLREAP era) = EpochNo
  type Environment (POOLREAP era) = Core.PParams era
  type BaseM (POOLREAP era) = ShelleyBase
  type PredicateFailure (POOLREAP era) = PoolreapPredicateFailure era
  type Event (POOLREAP era) = PoolreapEvent era
  transitionRules = [poolReapTransition]
  assertions =
    [ PostCondition
        "Deposit pot must equal obligation"
        ( \(TRC (pp, _, _)) st ->
            obligation pp (_rewards $ prDState st) (_pParams $ prPState st)
              == _deposited (prUTxOSt st)
        ),
      PostCondition
        "PoolReap may not create or remove reward accounts"
        ( \(TRC (_, st, _)) st' ->
            let r = _rewards . prDState
             in length (r st) == length (r st')
        )
    ]

poolReapTransition ::
  forall era.
  HasField "_poolDeposit" (Core.PParams era) Coin =>
  TransitionRule (POOLREAP era)
poolReapTransition = do
  TRC (pp, PoolreapState us a ds ps, e) <- judgmentContext

  let retired :: Set (KeyHash 'StakePool (Crypto era))
      retired = eval (dom (_retiring ps ▷ setSingleton e))
      pr :: Map.Map (KeyHash 'StakePool (Crypto era)) Coin
      pr = Map.fromSet (const (getField @"_poolDeposit" pp)) retired
      rewardAcnts :: Map.Map (KeyHash 'StakePool (Crypto era)) (RewardAcnt (Crypto era))
      rewardAcnts = Map.map _poolRAcnt $ eval (retired ◁ _pParams ps)
      rewardAcnts_ :: Map.Map (KeyHash 'StakePool (Crypto era)) (RewardAcnt (Crypto era), Coin)
      rewardAcnts_ = Map.intersectionWith (,) rewardAcnts pr
      rewardAcnts' :: Map.Map (RewardAcnt (Crypto era)) Coin
      rewardAcnts' =
        Map.fromListWith (<+>)
          . Map.elems
          $ rewardAcnts_
      refunds :: Map.Map (Credential 'Staking (Crypto era)) Coin
      mRefunds :: Map.Map (Credential 'Staking (Crypto era)) Coin
      (refunds, mRefunds) =
        Map.partitionWithKey
          (\k _ -> eval (k ∈ dom (_rewards ds)))
          (Map.mapKeys getRwdCred rewardAcnts')
      refunded = fold $ Map.elems refunds
      unclaimed = fold $ Map.elems mRefunds

  tellEvent $
    let rewardAcntsWithPool =
          Map.foldlWithKey'
            ( \acc sp (ra, coin) ->
                Map.insertWith (Map.unionWith (<>)) (getRwdCred ra) (Map.singleton sp coin) acc
            )
            Map.empty
            rewardAcnts_
        (refundPools', unclaimedPools') =
          Map.partitionWithKey
            (\k _ -> eval (k ∈ dom (_rewards ds)))
            rewardAcntsWithPool
     in RetiredPools
          { refundPools = refundPools',
            unclaimedPools = unclaimedPools'
          }

  pure $
    PoolreapState
      us {_deposited = _deposited us <-> (unclaimed <+> refunded)}
      a {_treasury = _treasury a <+> unclaimed}
      ds
        { _rewards = eval (_rewards ds ∪+ refunds),
          _delegations = eval (_delegations ds ⋫ retired)
        }
      ps
        { _pParams = eval (retired ⋪ _pParams ps),
          _fPParams = eval (retired ⋪ _fPParams ps),
          _retiring = eval (retired ⋪ _retiring ps)
        }
