module CoreMonad where

open import Prelude.String using (String)
open import Prelude.Unit using (Unit)
open import Prelude.Monad using (Monad)

postulate
  CoreM      : Set → Set
  putMsgS    : String → CoreM Unit
  coreReturn : ∀ {A : Set} → A → CoreM A
  coreBind   : ∀ {A B : Set} → CoreM A → (A → CoreM B) → CoreM B

{-# COMPILED_TYPE CoreM GhcPlugins.CoreM #-}
{-# COMPILED putMsgS GhcPlugins.putMsgS #-}
{-# COMPILED coreReturn (\ _ -> return)  #-}
{-# COMPILED coreBind   (\ _ _ -> (>>=)) #-}


instance
  MonadCoreM : Monad CoreM
  MonadCoreM = record { return = coreReturn ; _>>=_ = coreBind }
