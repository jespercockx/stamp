module Plugin where

{-# IMPORT GhcPlugins #-}

open import Prelude.String
open import Prelude.Unit
open import Prelude.IO
open import Prelude.List
open import Prelude.Monad
open import Prelude.Maybe


postulate
  CoreM             : Set → Set
  CommandLineOption : Set
  Var               : Set
  putMsgS           : String → CoreM Unit
  coreReturn        : ∀ {A : Set} → A → CoreM A
  coreBind          : ∀ {A B : Set} → CoreM A → (A → CoreM B) → CoreM B

{-# COMPILED_TYPE CoreM GhcPlugins.CoreM #-}
{-# COMPILED putMsgS GhcPlugins.putMsgS #-}
{-# COMPILED_TYPE CommandLineOption String #-}
{-# COMPILED_TYPE Var GhcPlugins.Var #-}
{-# COMPILED coreReturn (\ _ -> return)  #-}
{-# COMPILED coreBind   (\ _ _ -> (>>=)) #-}




agdaMetaPass : List CommandLineOption → CoreProgram → CoreM CoreProgram
agdaMetaPass options bindings = return bindings
{-# COMPILED_EXPORT agdaMetaPass agdaMetaPass #-}


-- TODO get rid of this
main : IO Unit
main = ioReturn tt
