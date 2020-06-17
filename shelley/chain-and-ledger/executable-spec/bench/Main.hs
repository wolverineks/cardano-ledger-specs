{-# OPTIONS_GHC -fno-warn-orphans  -Wno-unused-binds  -Wno-unused-imports #-}

module Main where

import Control.DeepSeq(NFData)
import Criterion.Main -- (bench, bgroup, defaultMain, whnf)

import Data.Word (Word64)

import Test.Shelley.Spec.Ledger.ConcreteCryptoTypes(UTxOState)

import Test.Shelley.Spec.Ledger.BenchmarkFunctions
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
    ledgerStateWithNregisteredPools,  -- How to compute an initial state with N StakePools

    ledgerDelegateManyKeysOnePool,
    ledgerStateWithNkeysMpools, -- How to precompute env for the Stake Delegation transactions
  )

import Shelley.Spec.Ledger.LedgerState(DPState(..),  UTxOState(..))

-- =================================================
-- Spending 1 UTxO

includes_init_SpendOneUTxO :: IO ()
includes_init_SpendOneUTxO =
  defaultMain
    [ bgroup "Spend 1 UTXO with initialization" $
        fmap
          (\n -> bench (show n) $ whnf ledgerSpendOneUTxO n)
          [50, 500, 5000, 50000]
    ]

profileUTxO :: IO ()
profileUTxO = do
  putStrLn "Enter profiling"
  let ans = ledgerSpendOneGivenUTxO (initUTxO 500000)
  putStrLn ("Exit profiling "++show ans)

-- ==========================================
-- Registering Stake Keys

touchDPState :: DPState crypto -> Int
touchDPState (DPState _x _y) = 1

touchUTxOState:: Shelley.Spec.Ledger.LedgerState.UTxOState cryto -> Int
touchUTxOState (UTxOState _utxo _deposited _fees _ppups) = 2

profileCreateRegKeys :: IO ()
profileCreateRegKeys = do
  putStrLn "Enter profiling stake key creation"
  let state =  ledgerStateWithNregisteredKeys 1 500000  -- using 75,000 and 100,000 causes
                                                        -- mainbench: internal error: PAP object entered!
                                                        -- (GHC version 8.6.5 for x86_64_unknown_linux)
                                                        -- Please report this as a GHC bug:  http://www.haskell.org/ghc/reportabug
  let touch (x,y) = touchUTxOState x + touchDPState y
  putStrLn ("Exit profiling "++show (touch state))


-- ==========================================
-- Registering Pools

profileCreateRegPools :: Word64 -> IO ()
profileCreateRegPools size = do
  putStrLn "Enter profiling pool creation"
  let state =  ledgerStateWithNregisteredPools 1 size
  let touch (x,y) = touchUTxOState x + touchDPState y
  putStrLn ("Exit profiling "++show (touch state))


-- =========================================================================================
-- Generic function to run 1 transaction over different size environments and States

makeBench :: NFData state => String -> (Word64 -> state) -> (state -> ()) -> Benchmark
makeBench tag initstate action = bgroup tag $ map runAtSize [50,500,5000,50000,500000]
  where runAtSize n = env(return $ initstate n) (\ state -> bench (show n) (whnf action state))

makeBenchMany
  :: NFData state
  => String
  -> (Word64 -> Word64 -> state)
  -> (Word64 -> Word64 -> state -> ())
  -> Benchmark
makeBenchMany tag initstate action =
  bgroup tag $ map runAtSize [50,500,5000,50000]
  where
    runAtSize n =
      env
        (return $ initstate 1 50000)
        (\ state -> bench (show n) (whnf (action (50001) (50000+n)) state))

makeBenchMany'
  :: NFData state
  => String
  -> (Word64 -> Word64 -> state)
  -> (Word64 -> Word64 -> state -> ())
  -> Benchmark
makeBenchMany' tag initstate action =
  bgroup tag $ map runAtSize [50,500,5000,50000]
  where
    runAtSize n =
      env
        (return $ initstate 1 50000)
        (\ state -> bench (show n) (whnf (action 1 n) state))

makeBenchDeleg
  :: NFData state
  => String
  -> (Word64 -> Word64 -> state)
  -> (Word64 -> Word64 -> state -> ())
  -> Benchmark
makeBenchDeleg tag initstate action =
  bgroup tag $ map runAtSize [50,500,5000,50000]
  where
    runAtSize n =
      env
        (return $ initstate 50000 50000)
        (\ state -> bench (show n) (whnf (action 1 n) state))

-- ======================================

main :: IO ()
main = defaultMain $
         [ bgroup "utxo" $
             [ makeBench "spendOne"  (initUTxO . fromIntegral) ledgerSpendOneGivenUTxO
             ],
           bgroup "stake-key" $
             [ makeBenchMany "register" ledgerStateWithNregisteredKeys ledgerRegisterStakeKeys
             , makeBenchMany' "deregister" ledgerStateWithNregisteredKeys ledgerDeRegisterStakeKeys
             , makeBenchMany' "withdrawal" ledgerStateWithNregisteredKeys ledgerRewardWithdrawals
             ],
           bgroup "stake-pool" $
             [ makeBenchMany "register" ledgerStateWithNregisteredPools ledgerRegisterStakePools
             , makeBenchMany' "reregister" ledgerStateWithNregisteredPools ledgerReRegisterStakePools
             , makeBenchMany' "retire" ledgerStateWithNregisteredPools ledgerRetireStakePools
             ],
           bgroup "delegation" $
             [ makeBenchDeleg "manyKeysOnePool" ledgerStateWithNkeysMpools ledgerDelegateManyKeysOnePool
             ]
         ]
-- main = profileUTxO
-- main = includes_init_SpendOneUTxO
-- main = profileCreateRegPools 10000
-- main = profileCreateRegPools 100000
