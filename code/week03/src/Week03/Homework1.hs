{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# OPTIONS_GHC -fno-warn-unused-imports #-}

module Week03.Homework1 where

import Control.Monad hiding (fmap)
import Data.Aeson (FromJSON, ToJSON)
import Data.Map as Map
import Data.Text (Text)
import Data.Void (Void)
import GHC.Generics (Generic)
import Ledger hiding (singleton)
import Ledger.Ada as Ada
import Ledger.Constraints (TxConstraints)
import qualified Ledger.Constraints as Constraints
import qualified Ledger.Typed.Scripts as Scripts
import Playground.Contract (ToSchema, ensureKnownCurrencies, printJson, printSchemas, stage)
import Playground.TH (mkKnownCurrencies, mkSchemaDefinitions)
import Playground.Types (KnownCurrency (..))
import Plutus.Contract
import qualified PlutusTx
import PlutusTx.Prelude hiding (unless)
import Text.Printf (printf)
import Prelude (IO)
import qualified Prelude as P

data VestingDatum = VestingDatum
  { beneficiary1 :: PaymentPubKeyHash,
    beneficiary2 :: PaymentPubKeyHash,
    deadline :: POSIXTime
  }
  deriving (P.Show)

PlutusTx.unstableMakeIsData ''VestingDatum

{-# INLINEABLE mkValidator #-}
-- This should validate if either beneficiary1 has signed the transaction and the current slot is before or at the deadline
-- or if beneficiary2 has signed the transaction and the deadline has passed.
mkValidator :: VestingDatum -> () -> ScriptContext -> Bool
mkValidator d _ ctx =
  if deadlineReached
    then traceIfFalse "beneficiary2's signature missing" $ signedBy $ beneficiary2 d
    else traceIfFalse "beneficiary1's signature missing" $ signedBy $ beneficiary1 d
  where
    info :: TxInfo
    info = scriptContextTxInfo ctx

    signedBy :: PaymentPubKeyHash -> Bool
    signedBy = txSignedBy info . unPaymentPubKeyHash

    deadlineReached :: Bool
    deadlineReached = contains (from $ deadline d) $ txInfoValidRange info

data Vesting

instance Scripts.ValidatorTypes Vesting where
  type DatumType Vesting = VestingDatum
  type RedeemerType Vesting = ()

typedValidator :: Scripts.TypedValidator Vesting
typedValidator =
  Scripts.mkTypedValidator @Vesting
    $$(PlutusTx.compile [||mkValidator||])
    $$(PlutusTx.compile [||wrap||])
  where
    wrap = Scripts.wrapValidator @VestingDatum @()

validator :: Validator
validator = Scripts.validatorScript typedValidator

scrAddress :: Ledger.Address
scrAddress = scriptAddress validator

data GiveParams = GiveParams
  { gpBeneficiary :: !PaymentPubKeyHash,
    gpDeadline :: !POSIXTime,
    gpAmount :: !Integer
  }
  deriving (Generic, ToJSON, FromJSON, ToSchema)

type VestingSchema =
  Endpoint "give" GiveParams
    .\/ Endpoint "grab" ()

give :: AsContractError e => GiveParams -> Contract w s e ()
give gp = do
  pkh <- ownPaymentPubKeyHash
  let dat =
        VestingDatum
          { beneficiary1 = gpBeneficiary gp,
            beneficiary2 = pkh,
            deadline = gpDeadline gp
          }
      tx = Constraints.mustPayToTheScript dat $ Ada.lovelaceValueOf $ gpAmount gp
  ledgerTx <- submitTxConstraints typedValidator tx
  void $ awaitTxConfirmed $ getCardanoTxId ledgerTx
  logInfo @P.String $
    printf
      "made a gift of %d lovelace to %s with deadline %s"
      (gpAmount gp)
      (P.show $ gpBeneficiary gp)
      (P.show $ gpDeadline gp)

grab :: forall w s e. AsContractError e => Contract w s e ()
grab = do
  now <- currentTime
  pkh <- ownPaymentPubKeyHash
  utxos <- utxosAt scrAddress
  let utxos1 = Map.filter (isSuitable $ \dat -> beneficiary1 dat == pkh && now <= deadline dat) utxos
      utxos2 = Map.filter (isSuitable $ \dat -> beneficiary2 dat == pkh && now > deadline dat) utxos
  logInfo @P.String $ printf "found %d gift(s) to grab" (Map.size utxos1 P.+ Map.size utxos2)
  unless (Map.null utxos1) $ do
    let orefs = fst <$> Map.toList utxos1
        lookups =
          Constraints.unspentOutputs utxos1
            P.<> Constraints.otherScript validator
        tx :: TxConstraints Void Void
        tx =
          mconcat [Constraints.mustSpendScriptOutput oref unitRedeemer | oref <- orefs]
            P.<> Constraints.mustValidateIn (to now)
    void $ submitTxConstraintsWith @Void lookups tx
  unless (Map.null utxos2) $ do
    let orefs = fst <$> Map.toList utxos2
        lookups =
          Constraints.unspentOutputs utxos2
            P.<> Constraints.otherScript validator
        tx :: TxConstraints Void Void
        tx =
          mconcat [Constraints.mustSpendScriptOutput oref $ unitRedeemer | oref <- orefs]
            P.<> Constraints.mustValidateIn (from now)
    void $ submitTxConstraintsWith @Void lookups tx
  where
    isSuitable :: (VestingDatum -> Bool) -> ChainIndexTxOut -> Bool
    isSuitable p o = case _ciTxOutDatum o of
      Left _ -> False
      Right (Datum d) -> maybe False p $ PlutusTx.fromBuiltinData d

endpoints :: Contract () VestingSchema Text ()
endpoints = awaitPromise (give' `select` grab') >> endpoints
  where
    give' = endpoint @"give" give
    grab' = endpoint @"grab" $ const grab

mkSchemaDefinitions ''VestingSchema

mkKnownCurrencies []
