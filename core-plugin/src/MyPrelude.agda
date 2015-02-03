module MyPrelude where

open import Prelude public

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
  hd : ∀ {xs}            → x ∈ (x :: xs)
  tl : ∀ {y xs} → x ∈ xs → x ∈ (y :: xs)


data _⊆_ {A : Set} : List A → List A → Set where
  stop : [] ⊆ []
  skip : ∀ {x xs ys} → xs ⊆ ys →        xs ⊆ (x :: ys)
  keep : ∀ {x xs ys} → xs ⊆ ys → (x :: xs) ⊆ (x :: ys)

⊆-refl : ∀ {A : Set} {xs : List A} → xs ⊆ xs
⊆-refl {xs = []} = stop
⊆-refl {xs = (y :: ys)} = keep (⊆-refl {xs = ys})

subInList : ∀ {A : Set} {x : A} {xs ys : List A} →
            xs ⊆ ys → x ∈ xs → x ∈ ys
subInList stop     q      = q
subInList (skip p) q      = tl (subInList p q)
subInList (keep p) hd     = hd
subInList (keep p) (tl q) = tl (subInList p q)
