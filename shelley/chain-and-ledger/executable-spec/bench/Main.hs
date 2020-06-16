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

    ledgerRegisterOneStakeKey,
    ledgerDeRegisterOneStakeKey,
    ledgerStateWithNregisteredKeys, -- How to precompute env for the StakeKey transactions

    ledgerRegisterOneStakePool,
    ledgerReRegisterOneStakePool,
    ledgerRetireOneStakePool,
    ledgerOneRewardWithdrawal,
    ledgerStateWithNregisteredPools,  -- How to compute an initial state with N StakePools
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
  let state =  ledgerStateWithNregisteredKeys 500000  -- using 75,000 and 100,000 causes
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
  let state =  ledgerStateWithNregisteredPools size
  let touch (x,y) = touchUTxOState x + touchDPState y
  putStrLn ("Exit profiling "++show (touch state))


-- =========================================================================================
-- Generic function to run 1 transaction over different size environments and States

makeBench :: NFData state => String -> (Word64 -> state) -> (state -> Bool) -> IO()
makeBench tag initstate action = defaultMain [ bgroup tag $ map runAtSize [50,500,5000,50000,500000] ]
  where runAtSize n = env(return $ initstate n) (\ state -> bench ("given "++show n) (whnf action state))

-- ======================================

main :: IO ()
-- main = profileUTxO
-- main = includes_init_SpendOneUTxO
-- main = makeBench "SpendOneUTxO "  (initUTxO . fromIntegral) ledgerSpendOneGivenUTxO
-- main = profileCreateRegPools 10000
-- main = makeBench "RegisterStakeKey " ledgerStateWithNregisteredKeys ledgerRegisterOneStakeKey
-- main = makeBench "DeRegisterStakeKey " ledgerStateWithNregisteredKeys ledgerDeRegisterOneStakeKey
-- main = profileCreateRegPools 100000
-- main = makeBench "RegisterStakePool" ledgerStateWithNregisteredPools ledgerRegisterOneStakePool
-- main = makeBench "ReRegisterStakePool" ledgerStateWithNregisteredPools ledgerReRegisterOneStakePool
-- main = makeBench "RetireStakePool" ledgerStateWithNregisteredPools ledgerRetireOneStakePool
main = makeBench "RewardWithdrawal" ledgerStateWithNregisteredKeys ledgerOneRewardWithdrawal