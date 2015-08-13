module Control.Monad.Trans where

open import Prelude
open import Control.Monad.State renaming (lift to liftStateT)


record MonadTrans {a b} (T : (Set a → Set b) → Set a → Set a) : Set (lsuc (a ⊔ b)) where
  field
    lift : ∀ {M : Set a → Set b} {{MonadM : Monad M}} {A : Set a} → M A → T M A

open MonadTrans {{...}} public


instance
  MonadTransStateT : ∀ {a} {S : Set a} → MonadTrans (StateT S)
  MonadTransStateT = record { lift = liftStateT }
