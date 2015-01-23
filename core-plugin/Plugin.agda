module Plugin where

{-# IMPORT GhcPlugins #-}

open import Prelude.String
open import Prelude.Unit
open import Prelude.IO


postulate
  CoreM   : Set → Set
  putMsgS : String → CoreM Unit

{-# COMPILED_TYPE CoreM GhcPlugins.CoreM #-}
{-# COMPILED putMsgS GhcPlugins.putMsgS #-}

hello : CoreM Unit
hello = putMsgS "Hello"
{-# COMPILED_EXPORT hello hello #-}

-- TODO get rid of this
main : IO Unit
main = ioReturn tt
