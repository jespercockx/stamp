module Plugin where

{-# IMPORT GhcPlugins #-}
{-# IMPORT Find #-}

open import Prelude
open import Data.Traversable using (mapM)

open import CoreMonad
open import CoreSyn
open import TypedCore
open import ToCore
open import MkPick using (pick1Of3)
open import HelloWorld using (printHelloWorld)
-- open import DeriveShow using (`showFoo`; deriveShow; `Foo`)
open import DeriveEq using (`eqFoo`)

postulate
  CommandLineOption : Set

{-# COMPILED_TYPE CommandLineOption String #-}

pick : ModGuts → CoreM CoreExpr
pick guts = runToCoreM guts (toCore pick1Of3)

hello : ModGuts → CoreM CoreExpr
hello guts = runToCoreM guts (toCore printHelloWorld)

program : ModGuts → CoreM CoreExpr
program guts = runToCoreM guts (toCore `eqFoo`)

agdaMetaPass : List CommandLineOption → ModGuts → CoreProgram → CoreM CoreProgram
agdaMetaPass options guts prog = replaceAgdaWith′ (program guts) prog
{-# COMPILED_EXPORT agdaMetaPass agdaMetaPass #-}


-- TODO get rid of this
main : IO Unit
main = ioReturn tt
