module Plugin where

{-# IMPORT GhcPlugins #-}

open import Prelude.String
open import Prelude.Unit
open import Prelude.IO
open import Prelude.List
open import Prelude.Monad
open import Prelude.Maybe

open import CoreMonad
open import CoreSyn

postulate
  CommandLineOption : Set

{-# COMPILED_TYPE CommandLineOption String #-}




agdaMetaPass : List CommandLineOption → CoreProgram → CoreM CoreProgram
agdaMetaPass options bindings = return bindings
{-# COMPILED_EXPORT agdaMetaPass agdaMetaPass #-}


-- TODO get rid of this
main : IO Unit
main = ioReturn tt
