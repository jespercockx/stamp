module MyPrelude where

open import Prelude hiding (trans) public
open import Control.Monad.Reader public
open import Control.Monad.Trans public
open import Control.Monad.State hiding (lift) public
open import Data.Int public


module Exists where
  open import Prelude.Product public
  open import Agda.Primitive using (_⊔_)

  ∃ : ∀ {a b} {A : Set a} → (A → Set b) → Set (a ⊔ b)
  ∃ = Σ _

  ∃₂ : ∀ {a b c} {A : Set a} {B : A → Set b}
       (C : (x : A) → B x → Set c) → Set (a ⊔ b ⊔ c)
  ∃₂ C = ∃ λ a → ∃ λ b → C a b

open Exists public

data WeakDec {a} (P : Set a) : Set a where
  yes : P → WeakDec P
  no  : WeakDec P

data Identity (a : Set) : Set where
  identity : a → Identity a

runIdentity : {a : Set} → Identity a → a
runIdentity (identity x) = x

instance
  MonadIdentity : Monad Identity
  MonadIdentity = record { return = identity ; _>>=_ = bindI }
    where
      bindI : {a b : Set} → Identity a → (a → Identity b) → Identity b
      bindI m k = k (runIdentity m)

  ApplicativeIdentity : Applicative Identity
  ApplicativeIdentity = defaultMonadApplicative

  FunctorIdentity : Functor Identity
  FunctorIdentity = defaultMonadFunctor



data _∈_ {A : Set} (x : A) : List A → Set where
  hd : ∀ {xs}            → x ∈ (x ∷ xs)
  tl : ∀ {y xs} → x ∈ xs → x ∈ (y ∷ xs)

∈2i : ∀ {A : Set} {x : A} {xs : List A} → x ∈ xs → Nat
∈2i hd = 0
∈2i (tl p) = suc (∈2i p)

∈2el : ∀ {A : Set} {x : A} {xs : List A} → x ∈ xs → A
∈2el {x = x} _ = x

_⊆_ : ∀ {A : Set} → List A → List A → Set
xs ⊆ ys = ∀ {x} → x ∈ xs → x ∈ ys

_⊈_ : ∀ {A : Set} → List A → List A → Set
xs ⊈ ys = ¬ xs ⊆ ys

⊆-refl : ∀ {A : Set} {xs : List A} → xs ⊆ xs
⊆-refl = id

⊆-swap : ∀ {A : Set} {x y : A} {xs : List A} → (x ∷ y ∷ xs) ⊆ (y ∷ x ∷ xs)
⊆-swap hd = tl hd
⊆-swap (tl hd) = hd
⊆-swap (tl (tl p)) = tl (tl p)

⊆-skip : ∀ {A : Set} {x : A} {xs ys : List A} → xs ⊆ ys → xs ⊆ (x ∷ ys)
⊆-skip p q = tl (p q)

⊆-keep : ∀ {A : Set} {x : A} {xs ys : List A} → xs ⊆ ys → (x ∷ xs) ⊆ (x ∷ ys)
⊆-keep p hd = hd
⊆-keep p (tl q) = tl (p q)

∈-over-⊆ : ∀ {A : Set} {x : A} {xs ys : List A} → xs ⊆ ys → x ∈ xs → x ∈ ys
∈-over-⊆ p q = p q
