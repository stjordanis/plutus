# plutus-use-cases: Smart contracts in PlutusTx

```haskell
{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE RecordWildCards   #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE DeriveGeneric     #-}
{-# OPTIONS -fplugin=Language.PlutusTx.Plugin -fplugin-opt Language.PlutusTx.Plugin:dont-typecheck #-}
module README where
import Language.PlutusTx.TH
import Language.PlutusTx.Lift
import Language.PlutusCore
import Language.PlutusCore.Pretty
import Language.PlutusCore.Quote
import Language.PlutusCore.Evaluation.CkMachine
import qualified Language.Haskell.TH as TH
import Data.Functor
import GHC.Generics (Generic)

main :: IO ()
main = pure ()
```

## How to verify the data script

Let's imagine a game called _Inc_ with two players. The state of the game is a counter `i :: Int`, and a fixed `k :: Int`. At the beginning, `i = 0` and `k` is agreed on by the players. The two players take turns. The player whose turn it is must increase `i` by a number between 1 and 5. If they can make `i` equal to `k` then they win, if they can't, then it's the other player's turn. If a player fails to commit a value during their turn, then the other player wins.

How can we encode the rules of this game in a PlutusTx contract? Let's start with the basic parameters.

```haskell

data IncGame = IncGame {
    player1 :: PubKey,
    player2 :: PubKey,
    k       :: Int,
    stake   :: Value
    } deriving Generic

makeLift ''IncGame
```

The rules of the game will be encoded in Plutus Core (PLC) scripts, which we generate from Template Haskell quotes. In PlutusTx, each pay-to-script unspent transaction output (UTXO) has three slots available for PLC scripts:

1. The validator script. The hash of this script is part of the UTXO, but the value of it is provided only when the UTXO is consumed.
2. The data script. The script is part of the UTXO.
3. The redeemer script. The script is part of the consumer of the UTXO.

For the first implementation of this contract we will store the current value of `i` in the data script, and use the redeemer to capture the number chosen by the player.

```haskell

newtype IncData = IncData { currentValue :: Int }
    deriving Generic

newtype IncRedeemer = IncRedeemer { increase :: Int }
    deriving Generic

makeLift ''IncData

```

We can think of the validator script as a function `f :: data -> redeemer -> PendingTx -> Bool` (in reality, the codomain of the script is `()` instead of `Bool`, but is is easier to combine predicates). `data` and `redeemer` are arbitrary types, and `PendingTx` contains information about the transaction that is currently being validated.


```haskell

versionOne :: Game -> Validator
versionOne gm = Validator val where
    val = UTXO.applyScript inner (UTXO.lifted gm)
    inner = UTXO.fromPlcCode $$(plutus [||
        \Game{..} IncData{..} IncRedeemer{..} (p :: PendingTx ValidatorHash) ->
            Builtins.error ()
    ||])

```


