module MyPrelude where

open import Prelude hiding (trans; reverse) public
open import Control.Monad.Reader public
open import Control.Monad.Trans public
open import Control.Monad.State hiding (lift) public
open import Data.Int public
open import Data.List using (All; _∷_; []) public


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



¬true-false : ∀ {b : Bool} → ¬ (b ≡ true) → b ≡ false
¬true-false {false} p = refl
¬true-false {true} p = ⊥-elim (p refl)


catMaybes : ∀ {A : Set} → List (Maybe A) → List A
catMaybes [] = []
catMaybes (nothing ∷ l) = catMaybes l
catMaybes (just x ∷ l) = x ∷ catMaybes l

mapMaybe : ∀ {A B : Set} → (A → Maybe B) → List A → List B
mapMaybe f = catMaybes ∘ map f


compose-map : ∀ {A B C : Set} → (xs : List A) (f : A → B) (g : B → C)  →
                map g (map f xs) ≡ map (g ∘ f) xs
compose-map [] _ _ = refl
compose-map (x ∷ xs) f g rewrite compose-map xs f g = refl


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


tl-inj : ∀ {A : Set} {x y : A} {xs : List A} {p q : x ∈ xs} →
           tl {y = y} p ≡ tl q → p ≡ q
tl-inj refl = refl

∈2i : ∀ {A : Set} {x : A} {xs : List A} → x ∈ xs → Nat
∈2i hd = 0
∈2i (tl p) = suc (∈2i p)

∈2el : ∀ {A : Set} {x : A} {xs : List A} → x ∈ xs → A
∈2el {x = x} _ = x

∈-All : ∀ {A : Set} {P : A → Set} {xs x} → All P xs → x ∈ xs → P x
∈-All [] ()
∈-All (p ∷ _) hd = p
∈-All (_ ∷ ps) (tl i) = ∈-All ps i

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

infixr 5 _+++_

-- [1, 2] +++ [3, 4] = [2, 1, 3, 4]
_+++_ : ∀ {A : Set} → List A → List A → List A
[] +++ ys = ys
(x ∷ xs) +++ ys = xs +++ x ∷ ys

∈-+++ : ∀ {A : Set} {x : A} {xs ys : List A} →
          x ∈ (xs +++ ys) → Either (x ∈ xs) (x ∈ ys)
∈-+++ {xs = []} p = right p
∈-+++ {x = x} {xs = y ∷ xs′} p with ∈-+++ {x = x} {xs = xs′} p
... | left q = left (tl q)
∈-+++ {A} {y} {.y ∷ xs′} p | right hd = left hd
∈-+++ {A} {x} {y ∷ xs′} p | right (tl q) = right q

∈-+++-suffix : ∀ {A : Set} {x : A} {xs ys : List A} → x ∈ xs → x ∈ (ys +++ xs)
∈-+++-suffix {ys = []} p = p
∈-+++-suffix {xs = xs} {ys = y ∷ ys} p
  = ∈-+++-suffix {xs = y ∷ xs} {ys = ys} (tl p)

∈-+++-prefix : ∀ {A : Set} {x : A} {xs ys : List A} → x ∈ xs → x ∈ (xs +++ ys)
∈-+++-prefix {xs = []} ()
∈-+++-prefix {xs = ._ ∷ xs′} hd = ∈-+++-suffix {ys = xs′} hd
∈-+++-prefix {xs = y ∷ xs′} (tl p) = ∈-+++-prefix p

∈-+++′ : ∀ {A : Set} {x : A} {xs ys : List A} →
           Either (x ∈ xs) (x ∈ ys) → x ∈ (xs +++ ys)
∈-+++′ (left p) = ∈-+++-prefix p
∈-+++′ {xs = xs} (right p) = ∈-+++-suffix {ys = xs} p

∈-+++-assoc₁ : ∀ {A : Set} {x : A} {xs ys zs : List A} →
                x ∈ (xs +++ (ys +++ zs)) → x ∈ ((xs +++ ys) +++ zs)
∈-+++-assoc₁ {xs = xs} {ys = ys} p with ∈-+++ {xs = xs} p
... | left q = ∈-+++′ (left (∈-+++′ (left q)))
... | right q with ∈-+++ {xs = ys} q
... | left r = ∈-+++′ {xs = xs +++ ys} (left (∈-+++′ {xs = xs} (right r)))
... | right r = ∈-+++′ {xs = xs +++ ys} (right r)

∈-+++-assoc₂ : ∀ {A : Set} {x : A} {xs ys zs : List A} →
                x ∈ ((xs +++ ys) +++ zs) → x ∈ (xs +++ (ys +++ zs))
∈-+++-assoc₂ {xs = xs} {ys = ys} p with ∈-+++ {xs = xs +++ ys} p
... | right q = ∈-+++′ {xs = xs} (right (∈-+++′ {xs = ys} (right q)))
... | left q with ∈-+++ {xs = xs} q
... | left r = ∈-+++′ (left r)
... | right r = ∈-+++′ {xs = xs} (right (∈-+++′ (left r)))

∈-concatMap : ∀ {A B : Set} {a} {b} {as} {f : A → List B} →
                b ∈ f a → a ∈ as → b ∈ concatMap f as
∈-concatMap {as = []} p ()
∈-concatMap {as = ._ ∷ _} p hd = ∈-++-prefix p
∈-concatMap {as = a′ ∷ _} {f = f} p (tl q)
  = ∈-++-suffix {ys = f a′} (∈-concatMap p q)

∈-map-inj : ∀ {A B : Set} {x : A} {xs : List A} {f : A → B} →
              x ∈ xs → f x ∈ map f xs
∈-map-inj {xs = []} ()
∈-map-inj {xs = ._ ∷ xs} hd = hd
∈-map-inj {xs = y ∷ xs} (tl p) = tl (∈-map-inj p)


∈-filter : ∀ {A : Set} {x : A} {xs : List A} {test : A → Bool} →
             x ∈ xs → test x ≡ true → x ∈ filter test xs
∈-filter hd q rewrite q = hd
∈-filter {test = test} (tl {y} p) q with test y
... | true = tl (∈-filter p q)
... | false = ∈-filter p q

∈-filter-not : ∀ {A : Set} {x : A} {xs : List A} {test : A → Bool} →
                 x ∈ xs → ¬(test x ≡ true) → x ∈ filter (not ∘ test) xs
∈-filter-not hd q rewrite ¬true-false q = hd
∈-filter-not {test = test} (tl {y} p) q with test y
... | true = ∈-filter-not p q
... | false = tl (∈-filter-not p q)


-- Less efficient than the reverse in Prelude.List, but easier to prove
-- properties about.
reverse : ∀ {A : Set} → List A → List A
reverse []       = []
reverse (x ∷ xs) = reverse xs ++ [ x ]

∈-reverse : ∀ {A : Set} {x : A} {xs : List A} → x ∈ xs → x ∈ reverse xs
∈-reverse {xs = []} ()
∈-reverse {xs = ._ ∷ xs} hd    = ∈-++-suffix {ys = reverse xs} hd
∈-reverse {xs = y ∷ xs} (tl p) = ∈-++-prefix (∈-reverse p)




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

⊆-map-inj : ∀ {A B : Set} {xs ys : List A} {f : A → B} →
              xs ⊆ ys → map f xs ⊆ map f ys
⊆-map-inj {xs = []} p ()
⊆-map-inj {xs = x ∷ xs} p hd = ∈-map-inj (p hd)
⊆-map-inj {xs = x ∷ xs} p (tl q) = ⊆-map-inj (λ z → p (tl z)) q


allFin : (n : Nat) → List (Fin n)
allFin zero = []
allFin (suc n) = zero ∷ map suc (allFin n)


Fin∈allFin : ∀ {n : Nat} → (i : Fin n) → i ∈ allFin n
Fin∈allFin {zero} ()
Fin∈allFin {suc n} zero = hd
Fin∈allFin {suc n} (suc i) = tl (∈-map-inj (Fin∈allFin i))
