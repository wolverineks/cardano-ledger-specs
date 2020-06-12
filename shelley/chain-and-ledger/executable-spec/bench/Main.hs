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
  )

import Shelley.Spec.Ledger.LedgerState(DPState(..),  UTxOState(..))

given:: Integer -> Benchmark
given n  = env (return $ initUTxO n) (\ state -> bench ("given "++show n) (whnf ledgerSpendOneGivenUTxO state))



includes_init :: IO ()
includes_init =
  defaultMain
    [ bgroup "ledger" $
        fmap
          (\n -> bench (show n) $ whnf ledgerSpendOneUTxO n)
          [50, 500, 5000, 50000]
    ]


excludes_init :: IO ()
excludes_init =
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
-- Registering Stake Pool Keys

touchDPState :: DPState crypto -> Int
touchDPState (DPState _x _y) = 1

touchUTxOState:: Shelley.Spec.Ledger.LedgerState.UTxOState cryto -> Int
touchUTxOState (UTxOState _utxo _deposited _fees _ppups) = 2

profileCreateRegKeys :: IO ()
profileCreateRegKeys = do
  putStrLn "Enter profiling"
  let state =  ledgerStateWithNregisteredKeys 500000  -- using 75,000 and 100,000 causes
                                                     -- mainbench: internal error: PAP object entered!
                                                     -- (GHC version 8.6.5 for x86_64_unknown_linux)
                                                     -- Please report this as a GHC bug:  http://www.haskell.org/ghc/reportabug
  let touch (x,y) = touchUTxOState x + touchDPState y
  putStrLn ("Exit profiling "++show (touch state))

givenStake:: Word64 -> Benchmark
givenStake n  = env (return $ ledgerStateWithNregisteredKeys n) (\ state -> bench ("given "++show n) (whnf ledgerRegisterOneStakeKey state))


excludes_init_StakePool_Reg_One_Key :: IO ()
excludes_init_StakePool_Reg_One_Key =
  defaultMain
    [ bgroup "RegStake " $
       [ givenStake 50, givenStake 500, givenStake 5000, givenStake 50000]
    ]

-- ======================================

main :: IO ()
main = excludes_init_StakePool_Reg_One_Key