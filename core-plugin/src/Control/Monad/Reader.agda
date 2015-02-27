module Control.Monad.Reader where

open import Prelude
open import Control.Monad.Trans


data ReaderT {a} (R : Set a) (M : Set a → Set a) (A : Set a): Set a where
  readerT : (R → M A) → ReaderT R M A

runReaderT : ∀ {a} {R : Set a} {M : Set a → Set a} {A : Set a} →
               ReaderT R M A → R → M A
runReaderT (readerT f) r = f r

private
  returnReaderT : ∀ {a} {R : Set a} {M : Set a → Set a} {{MonadM : Monad M}} {A : Set a} →
                    A → ReaderT R M A
  returnReaderT a = readerT (λ _ → return a)

  bindReaderT : ∀ {a} {R : Set a} {M : Set a → Set a} {{MonadM : Monad M}} {A B : Set a} →
                  ReaderT R M A → (A → ReaderT R M B) → ReaderT R M B
  bindReaderT (readerT f) g = readerT $ λ r →
    f r >>= (λ a → runReaderT (g a) r)

instance
  MonadReaderT : ∀ {a} {R : Set a} {M : Set a → Set a} {{MonadM : Monad M}} →
                   Monad (ReaderT R M)
  MonadReaderT = record { return = returnReaderT
                        ; _>>=_  = bindReaderT
                        }

  FunctorReaderT : ∀ {a} {R : Set a} {M : Set a → Set a} {{MonadM : Monad M}} →
                    Functor {a = a} (ReaderT R M)
  FunctorReaderT = defaultMonadFunctor {{MonadReaderT}}

  ApplicativeReaderT : ∀ {a} {R : Set a} {M : Set a → Set a} {{MonadM : Monad M}} →
                      Applicative {a = a} (ReaderT R M)
  ApplicativeReaderT = defaultMonadApplicative {{MonadReaderT}}


instance
  MonadTransReaderT : ∀ {a} {R : Set a} → MonadTrans (ReaderT R)
  MonadTransReaderT = record { lift = liftReaderT }
    where
      liftReaderT : ∀ {a} {S : Set a} {M : Set a → Set a} {{MonadM : Monad M}} {A : Set a} →
               M A → ReaderT S M A
      liftReaderT {M = M} m = readerT (λ _ → m)


ask : ∀ {a} {R : Set a} {M : Set a → Set a} {{MonadM : Monad M}} → ReaderT R M R
ask = readerT return

local : ∀ {a} {R A : Set a} {M : Set a → Set a} {{MonadM : Monad M}} →
          (R → R) → ReaderT R M A → ReaderT R M A
local f (readerT g) = readerT (g ∘ f)


asks : ∀ {a} {R A : Set a} {M : Set a → Set a} {{MonadM : Monad M}} →
         (R → A) → ReaderT R M A
asks f = readerT (return ∘ f)
