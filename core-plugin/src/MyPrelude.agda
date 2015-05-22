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



catMaybes : ∀ {A : Set} → List (Maybe A) → List A
catMaybes [] = []
catMaybes (nothing ∷ l) = catMaybes l
catMaybes (just x ∷ l) = x ∷ catMaybes l

mapMaybe : ∀ {A B : Set} → (A → Maybe B) → List A → List B
mapMaybe f = catMaybes ∘ map f

++-[] : ∀ {A : Set} {xs : List A} → xs ++ [] ≡ xs
++-[] {xs = []} = refl
++-[] {xs = x ∷ xs} = cong (λ zs → x ∷ zs) ++-[]

cons-middle-snoc : ∀ {A : Set} {y : A} (xs ys : List A) →
                     xs ++ (y ∷ ys) ≡ (xs ++ [ y ]) ++ ys
cons-middle-snoc [] _ = refl
cons-middle-snoc (x ∷ xs′) ys = cong (λ zs → x ∷ zs) (cons-middle-snoc xs′ ys)

data _∈_ {A : Set} (x : A) : List A → Set where
  hd : ∀ {xs}            → x ∈ (x ∷ xs)
  tl : ∀ {y xs} → x ∈ xs → x ∈ (y ∷ xs)

∈2i : ∀ {A : Set} {x : A} {xs : List A} → x ∈ xs → Nat
∈2i hd = 0
∈2i (tl p) = suc (∈2i p)

∈2el : ∀ {A : Set} {x : A} {xs : List A} → x ∈ xs → A
∈2el {x = x} _ = x

∈-prefix : ∀ {A : Set} {x : A} {xs ys : List A} →
             x ∈ xs → x ∈ (ys ++ xs)
∈-prefix {ys = []} p = p
∈-prefix {ys = _ ∷ ys} p = tl (∈-prefix {ys = ys} p)

∈-suffix : ∀ {A : Set} {x : A} {xs ys : List A} →
             x ∈ xs → x ∈ (xs ++ ys)
∈-suffix hd = hd
∈-suffix (tl p) = tl (∈-suffix p)

∈-++ : ∀ {A : Set} {x : A} {xs ys : List A} →
          x ∈ (xs ++ ys) → Either (x ∈ xs) (x ∈ ys)
∈-++ {xs = []} p = right p
∈-++ {xs = x₁ ∷ xs} {[]} p rewrite ++-[] {xs = x₁ ∷ xs} = left p
∈-++ {xs = ._ ∷ xs} {ys} hd = left hd
∈-++ {x = x} {xs = x₁ ∷ xs} {ys} (tl p) with ∈-++ {x = x} {xs = xs} {ys = ys} p
... | left  q = left (tl q)
... | right q = right q

∈-++′ : ∀ {A : Set} {x : A} {xs ys : List A} →
          Either (x ∈ xs) (x ∈ ys) → x ∈ (xs ++ ys)
∈-++′ (left p) = (∈-suffix p)
∈-++′ {xs = xs} (right p) = ∈-prefix {ys = xs} p

∈-++-prefix : ∀ {A : Set} {x : A} {xs ys : List A} → x ∈ xs → x ∈ (xs ++ ys)
∈-++-prefix p = ∈-++′ (left p)

∈-++-suffix : ∀ {A : Set} {x : A} {xs ys : List A} → x ∈ xs → x ∈ (ys ++ xs)
∈-++-suffix {ys = ys} p = ∈-++′ {xs = ys} (right p)

∈-++-swap : ∀ {A : Set} {x : A} {xs ys : List A} →
             x ∈ (xs ++ ys) → x ∈ (ys ++ xs)
∈-++-swap {xs = []} {ys} p rewrite ++-[] {xs = ys} = p
∈-++-swap {xs = ._ ∷ xs} {[]} hd = hd
∈-++-swap {xs = _ ∷ xs} {[]} (tl p) rewrite ++-[] {xs = xs} = tl p
∈-++-swap {xs = ._ ∷ _} {x₂ ∷ ys} hd = ∈-prefix {ys = x₂ ∷ ys} hd
∈-++-swap {xs = _ ∷ xs} {_ ∷ _} (tl p) with ∈-++ {xs = xs} p
∈-++-swap {xs = x₃ ∷ _} {x₂ ∷ ys} (tl p)
    | left q = ∈-++′ {xs = x₂ ∷ ys} (right (tl {y = x₃} q))
... | right hd = hd
... | right (tl q) = tl (∈-++′ (left q))



infix 4 _⊆_

_⊆_ : ∀ {A : Set} → List A → List A → Set
xs ⊆ ys = ∀ {x} → x ∈ xs → x ∈ ys

_⊈_ : ∀ {A : Set} → List A → List A → Set
xs ⊈ ys = ¬ (xs ⊆ ys)

⊆-refl : ∀ {A : Set} {xs : List A} → xs ⊆ xs
⊆-refl = id

⊆-empty : ∀ {A : Set} {xs : List A} → [] ⊆ xs
⊆-empty ()

⊆-swap : ∀ {A : Set} {x y : A} {xs : List A} → (x ∷ y ∷ xs) ⊆ (y ∷ x ∷ xs)
⊆-swap hd = tl hd
⊆-swap (tl hd) = hd
⊆-swap (tl (tl p)) = tl (tl p)

⊆-skip : ∀ {A : Set} {x : A} {xs ys : List A} → xs ⊆ ys → xs ⊆ (x ∷ ys)
⊆-skip p q = tl (p q)

⊆-keep : ∀ {A : Set} {x : A} {xs ys : List A} → xs ⊆ ys → (x ∷ xs) ⊆ (x ∷ ys)
⊆-keep p hd = hd
⊆-keep p (tl q) = tl (p q)

⊆-trans : ∀ {A : Set} {xs ys zs : List A} → xs ⊆ ys → ys ⊆ zs → xs ⊆ zs
⊆-trans p q = λ {x} z → q (p z)

∈-over-⊆ : ∀ {A : Set} {x : A} {xs ys : List A} → xs ⊆ ys → x ∈ xs → x ∈ ys
∈-over-⊆ p q = p q

⊆-++-swap : ∀ {A : Set} (xs ys : List A) → xs ++ ys ⊆ ys ++ xs
⊆-++-swap xs ys = ∈-++-swap {xs = xs} {ys = ys}


⊆-cons-middle : ∀ {A : Set} {x : A} {xs ys : List A} →
                  xs ++ (x ∷ ys) ⊆ (x ∷ xs) ++ ys
⊆-cons-middle {_} {x} {xs} {ys} p with ∈-++ {xs = xs} {ys = x ∷ ys} p
⊆-cons-middle {x = x₁} {xs = xs} _ | left  q = ∈-++′ {xs = x₁ ∷ xs} (left (tl q))
⊆-cons-middle _ | right hd = hd
⊆-cons-middle {x = x} {xs = xs} _ | right (tl q) = ∈-++′ {xs = x ∷ xs} (right q)
