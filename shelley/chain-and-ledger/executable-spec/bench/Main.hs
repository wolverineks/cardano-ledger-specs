{-# OPTIONS_GHC -fno-warn-orphans  -Wno-unused-binds  -Wno-unused-imports #-}

module Main where

import Criterion.Main -- (bench, bgroup, defaultMain, whnf)

import Data.Word (Word64)

import Test.Shelley.Spec.Ledger.ConcreteCryptoTypes(UTxOState)

import Test.Shelley.Spec.Ledger.BenchmarkFunctions
 ( ledgerSpendOneUTxO,
    ledgerSpendOneGivenUTxO,
    initUTxO,                       -- How to precompute env for the UTxO transactions

    ledgerRegisterOneStakeKey,
    ledgerDeRegisterOneStakeKey,
    ledgerStateWithNregisteredKeys, -- How to precompute env for the StakeKey transactions

    ledgerRegisterOneStakePool,
    ledgerReRegisterOneStakePool,
    ledgerRetireOneStakePool,
    ledgerStateWithNregisteredPools
  )

import Shelley.Spec.Ledger.LedgerState(DPState(..),  UTxOState(..))

given:: Integer -> Benchmark
given n  = env (return $ initUTxO n) (\ state -> bench ("given "++show n) (whnf ledgerSpendOneGivenUTxO state))


includes_init_SpendOneUTxO :: IO ()
includes_init_SpendOneUTxO =
  defaultMain
    [ bgroup "ledger" $
        fmap
          (\n -> bench (show n) $ whnf ledgerSpendOneUTxO n)
          [50, 500, 5000, 50000]
    ]


excludes_init_SpendOneUTxO :: IO ()
excludes_init_SpendOneUTxO =
  defaultMain
    [ bgroup "ledger" $
       [ given 50, given 500, given 5000, given 50000, given 500000]
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
  let state =  ledgerStateWithNregisteredKeys 500000  -- using 75,000 and 100,000 causes
                                                     -- mainbench: internal error: PAP object entered!
                                                     -- (GHC version 8.6.5 for x86_64_unknown_linux)
                                                     -- Please report this as a GHC bug:  http://www.haskell.org/ghc/reportabug
  let touch (x,y) = touchUTxOState x + touchDPState y
  putStrLn ("Exit profiling "++show (touch state))

givenStake:: Word64 -> Benchmark
givenStake n  = env (return $ ledgerStateWithNregisteredKeys n) (\ state -> bench ("given "++show n) (whnf ledgerRegisterOneStakeKey state))


excludes_init_RegOneStakeKey :: IO ()
excludes_init_RegOneStakeKey =
  defaultMain
    [ bgroup "RegStake " $
       [ givenStake 50, givenStake 500, givenStake 5000, givenStake 50000]
    ]

givenDeRegStake:: Word64 -> Benchmark
givenDeRegStake n  = env (return $ ledgerStateWithNregisteredKeys n) (\ state -> bench ("given "++show n) (whnf ledgerDeRegisterOneStakeKey state))


profile_DeRegOneStakeKey :: IO ()
profile_DeRegOneStakeKey = do
  putStrLn "Enter profiling"
  let state =  ledgerStateWithNregisteredKeys 50000
  let ans = ledgerDeRegisterOneStakeKey state
  putStrLn ("Exit profiling "++show ans)

excludes_init_DeRegOneStakeKey :: IO ()
excludes_init_DeRegOneStakeKey =
  defaultMain
    [ bgroup "RegStake " $ (map givenDeRegStake [50,500,5000,50000])
    ]

-- ==========================================
-- Registering Pools

profileCreateRegPools :: Word64 -> IO ()
profileCreateRegPools size = do
  putStrLn "Enter profiling pool creation"
  let state =  ledgerStateWithNregisteredPools size
  let touch (x,y) = touchUTxOState x + touchDPState y
  putStrLn ("Exit profiling "++show (touch state))

-- ======================================

main :: IO ()
-- main = excludes_init_SpendOneUTxO
-- main = excludes_init_RegOneStakeKey
-- main = excludes_init_DeRegOneStakeKey
-- main = profile_DeRegOneStakeKey
main = profileCreateRegPools 10000