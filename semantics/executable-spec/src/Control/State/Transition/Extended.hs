
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE UndecidableInstances #-}

-- | Small step state transition systems.
module Control.State.Transition.Extended where

import           Cardano.Prelude (NoUnexpectedThunks(..))
-- import           Control.Monad.Except (MonadError(..))
import           Control.Monad.Identity (Identity(..))
import           Control.Monad.Free.Church(F, liftF, wrap, foldF)
import           Control.Monad.Trans.Class (lift)
import           Control.Monad.Trans.State.Strict (modify, runStateT)
import qualified Control.Monad.Trans.State.Strict as MonadState
import           Data.Data (Data, Typeable)
import           Data.Foldable (find, traverse_)
import           Data.Functor ((<&>))
import           Data.Kind (Type)

-- =================================================================

data RuleType
  = Initial
  | Transition

-- | Singleton instances.
--
--   Since our case is so small we don't bother with the singletons library.
data SRuleType a where
  SInitial :: SRuleType 'Initial
  STransition :: SRuleType 'Transition

class RuleTypeRep t where
  rTypeRep :: SRuleType t

instance RuleTypeRep 'Initial where
  rTypeRep = SInitial

instance RuleTypeRep 'Transition where
  rTypeRep = STransition

-- | Context available to initial rules.
newtype IRC sts = IRC (Environment sts)

-- | Context available to transition rules.
newtype TRC sts = TRC (Environment sts, State sts, Signal sts)

deriving instance
  ( Show (Environment sts)
  , Show (State sts)
  , Show (Signal sts)
  ) => Show (TRC sts)

type family RuleContext (t :: RuleType) = (ctx :: Type -> Type) | ctx -> t where
  RuleContext 'Initial = IRC
  RuleContext 'Transition = TRC

type InitialRule sts = Rule sts 'Initial (State sts)
type TransitionRule sts = Rule sts 'Transition (State sts)

-- =================================================================


-- | State transition system.
class ( Eq (PredicateFailure a)
      , Show (PredicateFailure a)
      , Monad (BaseM a)
      )
  => STS a where
  -- | Type of the state which the system transitions between.
  type State a :: *
  -- | Signal triggering a state change.
  type Signal a :: *
  -- | Environment type.
  type Environment a :: *

  -- | Monad into which to interpret the rules.
  type BaseM a :: * -> *
  type BaseM a = Identity

  -- | Descriptive type for the possible failures which might cause a transition
  -- to fail.
  --
  -- As a convention, `PredicateFailure`s which are "structural" (meaning that
  -- they are not "throwable" in practice, and are used to pass control from
  -- one transition rule to another) are prefixed with `S_`.
  --
  -- Structural `PredicateFailure`s represent conditions between rules where
  -- the disjunction of all rules' preconditions is equal to `True`. That is,
  -- either one rule will throw a structural `PredicateFailure` and the other
  -- will succeed, or vice-versa.
  data PredicateFailure a :: *

  -- | Rules governing transition under this system.
  initialRules :: [InitialRule a]
  transitionRules :: [TransitionRule a]

-- | Embed one STS within another.
class (STS sub, STS super, BaseM sub ~ BaseM super) => Embed sub super where
  -- | Wrap a predicate failure of the subsystem in a failure of the super-system.
  wrapFailed :: PredicateFailure sub -> PredicateFailure super

instance STS sts => Embed sts sts where
  wrapFailed = id


-- =================================================================================
-- The language that describes how things happen


-- | Think of x::(Clause sts `type a) as a statement in a language, with variables of type "a".
-- A variable can be "computed" by another statement of type (Clause sts `type a), so the variables of type "a"
-- denote sub computations. We might think of the language of statments as the fix point of (Clause sts `type), like this
-- data Stmt sts t = InStmt (Clause sts t (Stmt sts t)). This would be OK if we were interested in building programs,
-- but insead, we are interested in executing them. So the ultimate use of Clause is as the uderlying Functor of a Free monad.


data Clause sts (rtype :: RuleType) a where
  Lift  -- Computations in the Base monad of the (STS instance) can be used as programs. This is where things happen.
    :: STS sts
    => (BaseM sts) a
    -> (a -> b)
    -> Clause sts rtype b
  GetCtx  -- function to Extract the current context
    :: (RuleContext rtype sts -> a)
    -> Clause sts rtype a
  SubTrans
    :: Embed sub sts
    => RuleContext rtype sub
       -- Subsequent computation with state introduced
    -> (State sub -> a)
    -> Clause sts rtype a
  Predicate
    :: Either e a
       -- Type of failure to return if the predicate fails
    -> (e -> PredicateFailure sts)
    -> a
    -> Clause sts rtype a

deriving instance Functor (Clause sts rtype)

-- | Here we define a Rule, as the Free Monad of the Clause functor. So we can think of x:: Rule sts type, as a lazy computation.
-- We can extract the value of the conputation by using the foldF morphism on Free Monads.
-- if x:: Rule sts type, Think of (foldF phi x) as an abstract eval function, where phi::(forall ans. f ans -> m ans) tells how
-- do the evaluation. phi reduces a Clause of answers to an answer in any monad "m" the user chooses. Note that answer must
-- be completely abstract. In the code below, phi is the function runClause.

type Rule sts rtype = F (Clause sts rtype)

-- ============================================================================
-- Code to create Clauses

-- ========================
-- | Oh noes!
--
--   This takes a condition (a boolean expression) and a failure and results in
--   a clause which will throw that failure if the condition fails.
(?!) :: Bool -> PredicateFailure sts -> Rule sts ctx ()
cond ?! orElse = liftF $ Predicate (if cond then Right () else Left ()) (const orElse) ()
              -- liftF takes a Clause, and lifts it to a Rule (An abstract computation in the Free Monad of Clause)

infix 1 ?!

failBecause :: PredicateFailure sts -> Rule sts ctx ()
failBecause = (False ?!)

-- | Oh noes with an explanation
--
--   We interpret this as "What?" "No!" "Because:"
(?!:) :: Either e () -> (e -> PredicateFailure sts) -> Rule sts ctx ()
cond ?!: orElse = liftF $ Predicate cond orElse ()

-- ================================
-- | Simple SubTrans
--

trans
  :: Embed sub super => RuleContext rtype sub -> Rule super rtype (State sub)
trans ctx = wrap $ SubTrans ctx pure

-- =================================
-- | Lifting the underlying actions in the Base monad of the STS instance to a Rule
--

liftSTS
  :: STS sts
  => (BaseM sts) a
  -> Rule sts ctx a
liftSTS f = wrap $ Lift f pure

-- ================================
-- | Get the judgment context
--

judgmentContext :: Rule sts rtype (RuleContext rtype sts)
judgmentContext = wrap $ GetCtx pure

-- ========================================================================================
-- Applying (running, evaluating) Rules


-- | Apply a rule even if its predicates fail.
--   If the rule successfully applies with no failures, the list of predicate failures will be empty.
applyRuleIndifferently
  :: forall s m rtype
   . (STS s, RuleTypeRep rtype, m ~ BaseM s)
  => RuleContext rtype s
  -> Rule s rtype (State s)
  -> m (State s, [PredicateFailure s])
applyRuleIndifferently jc r =
    -- Use state monad to collect a list of Predicate Failures
    -- Start the state of the monad as the empty list
    -- The underlying state computation is the application (run or evaluation) of r::Rule (in the free monad of Clause)
    -- and return the m (equal to BaseM s) computation (of the (STS s) instance).
    -- NOTE there are 3 monads here:
    -- 1) (BaseM s) ~ m, the underlying monad of the (STS s) instance
    -- 2) (F (Clause s t)) ~ Rule s t,  the execution of the rule.
    -- 3) MonadState.StateT [PredicateFailure s] (Rule s t), used temporarily to accumulate Predicate failures.
    runStateT (foldF runClause r) []
 where

  runClause :: Clause s rtype a -> MonadState.StateT [PredicateFailure s] m a
  runClause (Lift f next) = next <$> lift f
  runClause (GetCtx next              ) = next <$> pure jc
  runClause (Predicate cond orElse val) = do
    case cond of
      Left err -> modify (orElse err :) >> pure val  -- compute which PredicateFalure (orElse err) and cons (:) it onto the state.
      Right x -> pure x
  runClause (SubTrans subCtx next) = do
    (ss, sfails) <- lift $ applySTSIndifferently subCtx
    traverse_ (\a -> modify (a :)) $ wrapFailed <$> concat sfails
    next <$> pure ss

applySTSIndifferently  -- Indifferently means carry on even if we finds errors
  :: forall s m rtype
   . (STS s, RuleTypeRep rtype, m ~ BaseM s)
  => RuleContext rtype s
  -> m (State s, [[PredicateFailure s]])
applySTSIndifferently ctx =
  successOrFirstFailure <$> applySTSIndifferently' rTypeRep ctx
 where
  successOrFirstFailure xs =
    case find (null . snd) xs of   -- if (null . snd) x is true then the set of errors is empty. So (Just _) means No errors
      -- Oops, there are some errors in xs, or we couldn't find a pair with no errors because xs is empty.
      Nothing ->
        case xs of
          [] -> error "applySTSIndifferently was called with an empty set of rules"
          (s, _): _ -> (s, snd <$> xs )   -- e.g.  (s,[ [er1],[],[err2,err3],[] ])
      -- We found one where there are No errors
      Just (s, _) -> (s, [])
{- An alternate way?
  successOrFirstFailure [] = error "applySTSIndifferently was called with an empty set of rules"
  successOrFirstFailure xs | Just (s,[]) <- find (null . snd) xs = (s,[])  -- The first pair without an error
  successOrFirstFailure (xs@((s,_):_)) = (s,map snd xs)  -- Oops, there are some errors in xs
                                                         -- e.g.  (s,[ [err1],[],[err2,err3],[] ])
-}


  applySTSIndifferently'
    :: SRuleType rtype
    -> RuleContext rtype s
    -> m [(State s, [PredicateFailure s])]
  applySTSIndifferently' SInitial env =
    applyRuleIndifferently env `traverse` initialRules
  applySTSIndifferently' STransition jc =
    applyRuleIndifferently jc `traverse` transitionRules

applySTS :: forall s m rtype
   . (STS s, RuleTypeRep rtype, m ~ BaseM s)
  => RuleContext rtype s
  -> m (Either [[PredicateFailure s]] (State s))
applySTS ctx = applySTSIndifferently ctx <&> \case
  (st, []) -> Right st
  (_, pfs) -> Left pfs

-- | This can be used to specify predicate failures in STS rules where a value
-- is beyond a certain threshold.
newtype Threshold a = Threshold a
  deriving (Eq, Ord, Show, Data, Typeable, NoUnexpectedThunks)


-- =============================================================================

testtt :: Int
testtt = 99


runClauseCollectFailure
   :: (STS s,m ~ BaseM s,RuleTypeRep rtype)
   => RuleContext rtype s
   -> Clause s rtype a
   -> MonadState.StateT [PredicateFailure s] m a
runClauseCollectFailure _ (Lift f next) = next <$> lift f
runClauseCollectFailure jc (GetCtx next              ) = next <$> pure jc
runClauseCollectFailure _ (Predicate cond orElse val) = do
    case cond of
      Left err -> modify (orElse err :) >> pure val  -- compute which PredicateFalure (orElse err) and cons (:) it onto the state.
      Right x -> pure x
runClauseCollectFailure _ (SubTrans subCtx next) = do
    (ss, sfails) <- lift $ applySTSIndifferently subCtx
    traverse_ (\a -> modify (a :)) $ wrapFailed <$> concat sfails
    next <$> pure ss


runClauseIgnorePredicate
   :: (STS s,m ~ BaseM s,RuleTypeRep rtype)
   => RuleContext rtype s
   -> Clause s rtype a
   -> m a
runClauseIgnorePredicate _ (Lift f next) =  next <$> f
runClauseIgnorePredicate jc (GetCtx next) = pure(next jc)
runClauseIgnorePredicate _  (Predicate _ _ val) = pure val
runClauseIgnorePredicate _ (SubTrans subCtx next) = do
    (ss, _) <- applySTSIndifferently subCtx
    next <$> pure ss

applyRuleIgnorePredicate
  :: forall s m rtype
   . (STS s, RuleTypeRep rtype, m ~ BaseM s)
  => RuleContext rtype s
  -> Rule s rtype (State s)
  -> m (State s)
applyRuleIgnorePredicate jc r = foldF (runClauseIgnorePredicate jc) r

applySTSIgnorePredicate
  :: (STS s,RuleTypeRep rtype,m ~ BaseM s)
  => SRuleType rtype
  -> RuleContext rtype s
  -> m [State s]
applySTSIgnorePredicate SInitial env = applyRuleIgnorePredicate env `traverse` initialRules
applySTSIgnorePredicate STransition jc = applyRuleIgnorePredicate jc `traverse` transitionRules


reapplySTS :: forall s m rtype
   . (STS s, RuleTypeRep rtype, m ~ BaseM s)
  => RuleContext rtype s
  -> m (Either [[PredicateFailure s]] (State s))
reapplySTS ctx = (Right . head) <$> applySTSIgnorePredicate rTypeRep ctx