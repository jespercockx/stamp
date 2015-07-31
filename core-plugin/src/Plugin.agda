module Plugin where

{-# IMPORT GhcPlugins #-}
{-# IMPORT Find #-}
{-# IMPORT Data.Text #-}
{-# IMPORT Data.Text.Encoding #-}

open import Prelude
open import Data.Traversable using (mapM)

open import CoreMonad
open import CoreSyn
open import TypedCore
open import ToCore
open import MkPick using (pick1Of3)
open import HelloWorld using (printHelloWorld)
open import DeriveEq using (`eqFoo`; `eqPair`)
-- open import DeriveLenses using (`aBool`)

postulate
  CommandLineOption : Set
  Text              : Set
  error             : {A : Set} → String → A
  decodeUtf8        : ByteString → Text
  unpack            : Text → String

{-# COMPILED_TYPE CommandLineOption String #-}
{-# COMPILED_TYPE Text  Data.Text.Text #-}
{-# COMPILED error (\_ -> error) #-}
{-# COMPILED decodeUtf8 Data.Text.Encoding.decodeUtf8 #-}
{-# COMPILED unpack Data.Text.unpack #-}

pick : ModGuts → CoreM CoreExpr
pick guts = runToCoreM guts (toCore pick1Of3)

hello : ModGuts → CoreM CoreExpr
hello guts = runToCoreM guts (toCore printHelloWorld)

eqFoo : ModGuts → CoreM CoreExpr
eqFoo guts = runToCoreM guts (toCore `eqFoo`)

asString : CoreExpr → Maybe String
asString (App (Var' _) (Lit (MachStr bs)))  = just (unpack (decodeUtf8 bs))
-- The underscore above will be the Id GHC.CString.unpackCString#
asString _ = nothing

selectMetaProgram : ModGuts → List CoreArg → CoreM CoreExpr
selectMetaProgram guts [] = error "No meta-program selected"
selectMetaProgram guts (arg ∷ _) with asString arg
... | just "hello" = hello guts
... | just "pick"  = pick  guts
... | just "eqFoo" = eqFoo guts
... | just str = error ("Unknown meta-program: " & str)
... | nothing  = error "Non-string argument"

agdaMetaPass : List CommandLineOption → ModGuts → CoreProgram → CoreM CoreProgram
agdaMetaPass options guts prog = replaceAgdaSpliceWith (selectMetaProgram guts) prog
{-# COMPILED_EXPORT agdaMetaPass agdaMetaPass #-}


-- TODO get rid of this
main : IO Unit
main = ioReturn tt
