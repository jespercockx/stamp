module CoreMonad where

open import Prelude.Monad public
open import Prelude.Functor public
open import Prelude.Applicative public
open import Prelude.Unit using (Unit; tt) public
open import Prelude.String using (String)

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

  ApplicativeCoreM : Applicative CoreM
  ApplicativeCoreM = defaultMonadApplicative

  FunctorCoreM : Functor CoreM
  FunctorCoreM = defaultMonadFunctor
