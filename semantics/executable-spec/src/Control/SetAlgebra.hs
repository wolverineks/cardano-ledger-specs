{-# LANGUAGE GADTs #-}

module Control.SetAlgebra
  ( -- In addition to Data.Map.Map and Data.Set.Set, the following new types can be used in the set algegra
    List, -- A list type whose constructor is hidden (sorted [(key,value)] pairs, with no duplicate keys).
    -- Use 'fromList' to constuct concrete values
    BiMap,
    Bimap, -- Maps for Bijections. Use 'biMapFromList' and 'biMapEmpty' toconstruct concrete values.
    Single (..), -- Sets with a single pair. Visible constructors 'Singleton', 'SetSingleton', and 'Fail'.

    -- Classes supporting abstract constructors of Set Algebra Expressions. These show up in the types of overloaded functions.
    Basic (..),
    Iter (..),
    Embed (..),
    HasExp (..),
    BaseRep (..),
    -- Overloaded functions acting as abstract constructors of Set Algebra Expressions. These correspond
    -- with the operators in the specification, except here sets are thought of as a map with a Unit value. (Map k ())
    dom,
    rng,
    dexclude,
    drestrict,
    rexclude,
    rrestrict,
    unionleft,
    unionright,
    unionplus,
    singleton,
    setSingleton,
    intersect,
    subset,
    keyeq,
    (◁),
    (⋪),
    (▷),
    (⋫),
    (∈),
    (∉),
    (∪),
    (⨃),
    (∪+),
    (∩),
    (⊆),
    (≍),
    (<|),
    (|>),
    (➖),
    -- The only exported concrete Constructor of Set Algebra Expressons. Needed to make 'HasExp' and 'Embed'
    -- instances of new kinds of sets (Basically,  Data.Map's wrapped in a newtype).
    -- See: Shelley.Spec.Ledger.TxBody and Shelley/Spec/Ledger/UTxO.hs and helley/Spec/Ledger/Delegation/Certificates.hs
    -- for example uses of this.
    Exp (Base),
    -- Evaluate an abstract Set Algebra Expression to the Set (Map) it represents.
    eval,
    -- Functions to build concrete Set-like things useable as Set Algebra Expressions
    materialize,
    biMapFromList,
    biMapEmpty,
    fromList,
    keysEqual,
    forwards,
    backwards,
  )
where

import Control.Iterate.SetAlgebra
import Data.Map (Map)
import Data.Set (Set)

forwards :: BiMap v k v -> Map k v
forwards (MkBiMap l _r) = l

backwards :: BiMap v k v -> Map v (Set k)
backwards (MkBiMap _l r) = r
