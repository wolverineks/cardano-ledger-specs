module MockTypes where

import           Cardano.Crypto.DSIGN (MockDSIGN)
import           Cardano.Crypto.Hash (SHA256)
import           Cardano.Crypto.KES (MockKES)

import qualified BlockChain
import qualified Delegation.Certificates
import qualified Keys
import qualified LedgerState
import qualified OCert
import qualified STS.Chain
import qualified STS.Utxow
import qualified Tx
import qualified TxData
import qualified UTxO

type DCert = Delegation.Certificates.DCert SHA256 MockDSIGN

type Delegation = TxData.Delegation SHA256 MockDSIGN

type PoolParams = TxData.PoolParams SHA256 MockDSIGN

type RewardAcnt = TxData.RewardAcnt SHA256 MockDSIGN

type KeyHash = Keys.KeyHash SHA256 MockDSIGN

type KeyPair = Keys.KeyPair MockDSIGN

type VKey = Keys.VKey MockDSIGN

type SKey = Keys.SKey MockDSIGN

type KeyPairs = LedgerState.KeyPairs MockDSIGN

type VKeyGenesis = Keys.VKeyGenesis MockDSIGN

type EpochState = LedgerState.EpochState SHA256 MockDSIGN

type LedgerState = LedgerState.LedgerState SHA256 MockDSIGN

type LedgerValidation = LedgerState.LedgerValidation SHA256 MockDSIGN

type UTxOState = LedgerState.UTxOState SHA256 MockDSIGN

type DState = LedgerState.DState SHA256 MockDSIGN

type PState = LedgerState.PState SHA256 MockDSIGN

type DPState = LedgerState.DPState SHA256 MockDSIGN

type Addr = TxData.Addr SHA256 MockDSIGN

type Tx = Tx.Tx SHA256 MockDSIGN

type TxBody = Tx.TxBody SHA256 MockDSIGN

type TxIn = Tx.TxIn SHA256 MockDSIGN

type TxOut = Tx.TxOut SHA256 MockDSIGN

type TxId = TxData.TxId SHA256 MockDSIGN

type UTxO = UTxO.UTxO SHA256 MockDSIGN

type Block = BlockChain.Block SHA256 MockDSIGN MockKES

type BHBody = BlockChain.BHBody SHA256 MockDSIGN MockKES

type SKeyES = Keys.SKeyES MockKES

type VKeyES = Keys.VKeyES MockKES

type KESig = Keys.KESig MockKES BHBody

type Sig a = Keys.Sig MockDSIGN a

type Proof a = BlockChain.Proof MockDSIGN

type BHeader = BlockChain.BHeader SHA256 MockDSIGN MockKES

type OCert = OCert.OCert MockDSIGN MockKES

type HashHeader = BlockChain.HashHeader SHA256 MockDSIGN MockKES

type NewEpochState = LedgerState.NewEpochState SHA256 MockDSIGN

type CHAIN = STS.Chain.CHAIN SHA256 MockDSIGN MockKES

type UTXOW = STS.Utxow.UTXOW SHA256 MockDSIGN

type Credential = TxData.Credential SHA256 MockDSIGN

type StakeCredential = TxData.StakeCredential SHA256 MockDSIGN

type MultiSig = TxData.MultiSig SHA256 MockDSIGN

type ScriptHash = TxData.ScriptHash SHA256 MockDSIGN

type WitVKey = TxData.WitVKey SHA256 MockDSIGN

type Wdrl = TxData.Wdrl SHA256 MockDSIGN
