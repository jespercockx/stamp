module MyPrelude where

open import Prelude hiding (reverse) renaming (sym to ≡-sym; trans to ≡-trans) public
open import Builtin.Size public
open import Control.Monad.Reader public
open import Control.Monad.Trans public
open import Control.Monad.State hiding (lift) public
open import Data.Int public
open import Data.List using (All; _∷_; []) public
open import Tactic.Deriving.Eq

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


map-≡ : ∀ {A B : Set} {xs : List A} → (f g : A → B) →
          (∀ {x} → f x ≡ g x) → map f xs ≡ map g xs
map-≡ {xs = []} _ _ h = refl
map-≡ {xs = x ∷ xs} f g h rewrite h {x} | map-≡ {xs = xs} f g h = refl

map-id : ∀ {A : Set} {xs : List A} (f : A → A)
       → (∀ {x} → f x ≡ x) → map f xs ≡ xs
map-id {xs = []} f h = refl
map-id {xs = x ∷ xs} f h = cong₂ _∷_ h (map-id f h)


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

instance
  Eq_∈_ : ∀ {A : Set} {x : A} {xs : List A} → Eq (x ∈ xs)
  Eq_∈_ = record { _==_ = eq }
    where
      eq : ∀ {A : Set} {x : A} {xs : List A} → (p q : x ∈ xs) → Dec (p ≡ q)
      unquoteDef eq = deriveEqDef (quote _∈_)


tl-inj : ∀ {A : Set} {x y : A} {xs : List A} {p q : x ∈ xs} →
           tl {y = y} p ≡ tl q → p ≡ q
tl-inj refl = refl

∈2i : ∀ {A : Set} {x : A} {xs : List A} → x ∈ xs → Nat
∈2i hd = 0
∈2i (tl p) = suc (∈2i p)

∈2el : ∀ {A : Set} {x : A} {xs : List A} → x ∈ xs → A
∈2el {x = x} _ = x


lift∈ : ∀ {A} {xs ys : List A} zs → (f : ∀ {x} → x ∈ xs → x ∈ ys) → ∀ {x} → x ∈ (zs ++ xs) → x ∈ (zs ++ ys)
lift∈ [] f p = f p
lift∈ (x ∷ zs) f hd = hd
lift∈ (x ∷ zs) f (tl p) = tl (lift∈ zs f p)


∈-All : ∀ {A : Set} {P : A → Set} {xs x} → All P xs → x ∈ xs → P x
∈-All (p ∷ _) hd = p
∈-All (_ ∷ ps) (tl i) = ∈-All ps i

tailAll : ∀ {A : Set} {P : A → Set} {x : A} {xs : List A} → All P (x ∷ xs) → All P xs
tailAll (_ ∷ xs) = xs

_++All_ : ∀ {A : Set} {P : A → Set} {xs ys : List A} → All P xs → All P ys → All P (xs ++ ys)
[] ++All qs = qs
(p ∷ ps) ++All qs = p ∷ (ps ++All qs)

All-ext : ∀ {A : Set} {P : A → Set} {xs : List A} → {ps ps′ : All P xs} →
          (∀ {x : A} (p : x ∈ xs) → ∈-All ps p ≡ ∈-All ps′ p) →
          ps ≡ ps′
All-ext {ps = []} {[]} hyp = refl
All-ext {ps = p ∷ ps} {p′ ∷ ps′} hyp = cong₂ _∷_ (hyp hd) (All-ext (hyp ∘ tl))

mapAll : ∀ {A : Set} {P Q : A → Set} (f : {x : A} → P x → Q x) {xs : List A} → All P xs → All Q xs
mapAll f [] = []
mapAll f (x ∷ xs) = f x ∷ mapAll f xs

∈-mapAll : ∀ {A : Set} {P Q : A → Set} (f : {x : A} → P x → Q x) {xs : List A} {x : A} →
           (ps : All P xs) (i : x ∈ xs) → ∈-All (mapAll f ps) i ≡ f (∈-All ps i)
∈-mapAll f (p ∷ ps) hd = refl
∈-mapAll f (p ∷ ps) (tl i) = ∈-mapAll f ps i

mapAll-mapAll : ∀ {A : Set} {P Q R : A → Set}
  (f : {x : A} → P x → Q x)  (g : {x : A} → Q x → R x) →
  ∀ {xs : List A} → (ps : All P xs) →
  mapAll g (mapAll f ps) ≡ mapAll (g ∘ f) ps
mapAll-mapAll f g [] = refl
mapAll-mapAll f g (p ∷ ps) = cong₂ _∷_ refl (mapAll-mapAll f g ps)

mapAll-cong : ∀ {A : Set} {P Q : A → Set} (f g : {x : A} → P x → Q x)
  {xs : List A} → (∀ {x : A} (p : P x) → f p ≡ g p) →
  (ps : All P xs) → mapAll f ps ≡ mapAll g ps
mapAll-cong f g f≡g [] = refl
mapAll-cong f g f≡g (p ∷ ps) = cong₂ _∷_ (f≡g _) (mapAll-cong f g f≡g ps)

mapAll-id : ∀ {A : Set} {P : A → Set}
  {xs : List A} → (ps : All P xs) → mapAll id ps ≡ ps
mapAll-id [] = refl
mapAll-id (p ∷ ps) = cong₂ _∷_ refl (mapAll-id ps)


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


map-+++-assoc : ∀ {A B : Set} {xs ys : List A} (f : A → B) →
                  map f (xs +++ ys) ≡ map f xs +++ map f ys
map-+++-assoc {xs = []} f = refl
map-+++-assoc {xs = x ∷ xs} {ys} f = map-+++-assoc {xs = xs} {ys = x ∷ ys} f


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

_⊆_ : ∀ {A : Set} → (xs ys : List A) → Set
xs ⊆ ys = All (λ x → x ∈ ys) xs

_⊈_ : ∀ {A : Set} → List A → List A → Set
xs ⊈ ys = ¬ (xs ⊆ ys)

∈-over-⊆ : ∀ {A : Set} {xs ys : List A} {x} → xs ⊆ ys → x ∈ xs → x ∈ ys
∈-over-⊆ = ∈-All

⊆-over-∈ : ∀ {A : Set} {xs ys : List A} →
             (∀ {x} → x ∈ xs → x ∈ ys) →
             xs ⊆ ys
⊆-over-∈ {xs = []} f = []
⊆-over-∈ {xs = _ ∷ xs} f = (f hd) ∷ (⊆-over-∈ (λ p → f (tl p)))

⊆-skip : ∀ {A : Set} {x : A} {xs ys : List A} → xs ⊆ ys → xs ⊆ (x ∷ ys)
⊆-skip p = mapAll tl p

⊆-skip-n : ∀ {A : Set} {xs zs : List A} (ys : List A) → xs ⊆ zs → xs ⊆ (ys ++ zs)
⊆-skip-n [] p = p
⊆-skip-n (y ∷ ys) p = ⊆-skip (⊆-skip-n ys p)

⊆-refl : ∀ {A : Set} {xs : List A} → xs ⊆ xs
⊆-refl {xs = []} = []
⊆-refl {xs = x ∷ xs} = hd ∷ ⊆-skip ⊆-refl

⊆-empty : ∀ {A : Set} {xs : List A} → [] ⊆ xs
⊆-empty = []

⊆-empty-⊥ : ∀ {A : Set} {x : A} {xs : List A} → x ∷ xs ⊆ [] → ⊥
⊆-empty-⊥ (() ∷ _)

⊆-swap : ∀ {A : Set} {x y : A} {xs : List A} → (x ∷ y ∷ xs) ⊆ (y ∷ x ∷ xs)
⊆-swap = tl hd ∷ hd ∷ (⊆-skip (⊆-skip ⊆-refl))

⊆-keep : ∀ {A : Set} {x : A} {xs ys : List A} → xs ⊆ ys → (x ∷ xs) ⊆ (x ∷ ys)
⊆-keep p = hd ∷ (⊆-skip p)

⊆-keep-n : ∀ {A : Set} {xs ys : List A} (zs : List A) → xs ⊆ ys → (zs ++ xs) ⊆ (zs ++ ys)
⊆-keep-n [] p = p
⊆-keep-n (_ ∷ zs) p = ⊆-keep (⊆-keep-n zs p)

-- ⊆-trans : ∀ {A : Set} {xs ys zs : List A} → xs ⊆ ys → ys ⊆ zs → xs ⊆ zs
-- ⊆-trans p q = ⊆-over-∈ (∈-over-⊆ q ∘ ∈-over-⊆ p)

⊆-trans : ∀ {A : Set} {xs ys zs : List A} → xs ⊆ ys → ys ⊆ zs → xs ⊆ zs
⊆-trans {xs = []} p q = []
⊆-trans {xs = x ∷ xs} (px ∷ pxs) q = ∈-over-⊆ q px ∷ ⊆-trans pxs q

⊆-prefix : ∀ {A : Set} (xs ys : List A) → xs ⊆ xs ++ ys
⊆-prefix [] ys = []
⊆-prefix (x ∷ xs) ys = hd ∷ mapAll tl (⊆-prefix xs ys)

⊆-++-swap : ∀ {A : Set} (xs ys : List A) → xs ++ ys ⊆ ys ++ xs
⊆-++-swap xs ys = ⊆-over-∈ (∈-++-swap {xs = xs} {ys = ys})

⊆-++-prefix : ∀ {A : Set} {xs ys zs : List A} → xs ⊆ ys →
                zs ++ xs ⊆ zs ++ ys
⊆-++-prefix {zs = []} p = p
⊆-++-prefix {zs = z ∷ zs} p = hd ∷ ⊆-skip (⊆-++-prefix {zs = zs} p)

⊆-+++-prefix : ∀ {A : Set} {xs ys zs : List A} → xs ⊆ ys →
                 zs +++ xs ⊆ zs +++ ys
⊆-+++-prefix {zs = []} p = p
⊆-+++-prefix {zs = z ∷ zs} p = ⊆-+++-prefix {zs = zs} (⊆-keep p)

⊆-+++-suffix : ∀ {A : Set} {xs ys zs : List A} → xs ⊆ ys →
                 xs +++ zs ⊆ ys +++ zs
⊆-+++-suffix p = ⊆-over-∈ (⊆-+++-suffix′ (∈-over-⊆ p))
  where
    ⊆-+++-suffix′ : ∀ {A : Set} {xs ys zs : List A} →
                      (∀ {x} → x ∈ xs → x ∈ ys) →
                      (∀ {x} → x ∈ (xs +++ zs) → x ∈ (ys +++ zs))
    ⊆-+++-suffix′ {xs = xs} p q with ∈-+++ {xs = xs} q
    ⊆-+++-suffix′ p q | left r = ∈-+++-prefix (p r)
    ⊆-+++-suffix′ {ys = ys} p q | right r = ∈-+++-suffix {ys = ys} r

∈-over-⊆-trans : ∀ {A : Set} {Σ₁ Σ₂ Σ₃ : List A} {κ} → (p : Σ₁ ⊆ Σ₂) → (q : Σ₂ ⊆ Σ₃) →
                   (i : κ ∈ Σ₁) →
                   (∈-over-⊆ q (∈-over-⊆ p i)) ≡ (∈-over-⊆ (⊆-trans p q) i)
∈-over-⊆-trans (p ∷ ps) q hd = refl
∈-over-⊆-trans (p ∷ ps) q (tl i) = ∈-over-⊆-trans ps q i

∈-over-⊆-skip : ∀ {A : Set} {Σ₁ Σ₂ : List A} {κ₁ κ₂ : A} → (p : κ₁ ∈ Σ₁) → (q : Σ₁ ⊆ Σ₂) →
                ∈-over-⊆ (⊆-skip q) p ≡ tl {y = κ₂} (∈-over-⊆ q p)
∈-over-⊆-skip x ps = ∈-mapAll tl ps x

⊆-skip-⊆-trans : ∀ {A : Set} {Σ₁ Σ₂ Σ₃ : List A} {κ} → (p : Σ₁ ⊆ Σ₂) → (q : Σ₂ ⊆ Σ₃) →
                   ⊆-trans (⊆-skip  {x = κ} p) (hd ∷ ⊆-skip q)
                   ≡ ⊆-skip (⊆-trans p q)
⊆-skip-⊆-trans [] q = refl
⊆-skip-⊆-trans (p ∷ ps) q = cong₂ _∷_ (∈-over-⊆-skip p q) (⊆-skip-⊆-trans ps q)

∈-over-skip : ∀ {A : Set} {Σ₁ Σ₂ : List A} {κ₁ κ₂} → (p : Σ₁ ⊆ Σ₂) (q : κ₁ ∈ Σ₁) →
      tl {y = κ₂} {xs = Σ₂} (∈-over-⊆ p q) ≡ ∈-over-⊆ (⊆-skip p) q
∈-over-skip ps x = ≡-sym (∈-over-⊆-skip x ps)

∈-over-refl : ∀ {A : Set} {Σ : List A} {κ} → (p : κ ∈ Σ) → p ≡ ∈-over-⊆ ⊆-refl p
∈-over-refl {Σ = []} ()
∈-over-refl {Σ = x ∷ Σ} hd = refl
∈-over-refl {Σ = x ∷ Σ} (tl p) = ≡-trans (cong tl (∈-over-refl p)) (∈-over-skip ⊆-refl p)

⊆-trans-⊆-skip₁ : ∀ {A : Set} {Σ₁ Σ₂ Σ₃ : List A} {κ} (p : Σ₁ ⊆ Σ₂) (q : κ ∷ Σ₂ ⊆ Σ₃) →
  ⊆-trans (⊆-skip p) q ≡ ⊆-trans p (tailAll q)
⊆-trans-⊆-skip₁ [] _ = refl
⊆-trans-⊆-skip₁ (p ∷ ps) (q ∷ qs) = cong₂ _∷_ refl (⊆-trans-⊆-skip₁ ps (q ∷ qs))

⊆-trans-⊆-skip₂ : ∀ {A : Set} {Σ₁ Σ₂ Σ₃ : List A} {κ} (p : Σ₁ ⊆ Σ₂) (q : Σ₂ ⊆ Σ₃) →
  ⊆-trans p (⊆-skip {x = κ} q) ≡ ⊆-skip {x = κ} (⊆-trans p q)
⊆-trans-⊆-skip₂ [] q = refl
⊆-trans-⊆-skip₂ (p ∷ ps) q = cong₂ _∷_ (∈-over-⊆-skip p q) (⊆-trans-⊆-skip₂ ps q)

⊆-trans-⊆-refl₁ : ∀ {A : Set} {Σ₁ Σ₂ : List A} → (p : Σ₁ ⊆ Σ₂) → ⊆-trans ⊆-refl p ≡ p
⊆-trans-⊆-refl₁ [] = refl
⊆-trans-⊆-refl₁ (p ∷ ps) =
  cong₂ _∷_ refl (≡-trans (⊆-trans-⊆-skip₁ ⊆-refl (p ∷ ps)) (⊆-trans-⊆-refl₁ ps))

⊆-trans-⊆-refl₂ : ∀ {A : Set} {Σ₁ Σ₂ : List A} → (p : Σ₁ ⊆ Σ₂) → ⊆-trans p ⊆-refl ≡ p
⊆-trans-⊆-refl₂ [] = refl
⊆-trans-⊆-refl₂ (p ∷ ps) = cong₂ _∷_ (≡-sym (∈-over-refl p)) (⊆-trans-⊆-refl₂ ps)

⊆-trans-⊆-skip-⊆-refl : ∀ {A : Set} {Σ₁ Σ₂ : List A} {κ : A} → (p : Σ₁ ⊆ Σ₂) →
      ⊆-trans (⊆-skip {x = κ} ⊆-refl) (hd ∷ ⊆-skip p) ≡
      ⊆-trans p (⊆-skip ⊆-refl)
⊆-trans-⊆-skip-⊆-refl {Σ₁} {Σ₂} {κ} p =
  ⊆-trans (⊆-skip ⊆-refl) (hd ∷ ⊆-skip p)
    ≡⟨ ⊆-trans-⊆-skip₁ ⊆-refl _ ⟩
  ⊆-trans ⊆-refl (⊆-skip p)
    ≡⟨ ⊆-trans-⊆-refl₁ _ ⟩
  ⊆-skip p
    ≡⟨ cong ⊆-skip (⊆-trans-⊆-refl₂ _) ⟩ʳ
  ⊆-skip (⊆-trans p ⊆-refl)
    ≡⟨ ⊆-trans-⊆-skip₂ _ _ ⟩ʳ
  ⊆-trans p (⊆-skip ⊆-refl) ∎

⊆-map-inj : ∀ {A B : Set} {xs ys : List A} {f : A → B} →
              xs ⊆ ys → map f xs ⊆ map f ys
⊆-map-inj {xs = []} p = []
⊆-map-inj {xs = x ∷ xs} (p₁ ∷ p₂) = (∈-map-inj p₁) ∷ (⊆-map-inj p₂)


allFin : (n : Nat) → List (Fin n)
allFin zero = []
allFin (suc n) = zero ∷ map suc (allFin n)


Fin∈allFin : ∀ {n : Nat} → (i : Fin n) → i ∈ allFin n
Fin∈allFin {zero} ()
Fin∈allFin {suc n} zero = hd
Fin∈allFin {suc n} (suc i) = tl (∈-map-inj (Fin∈allFin i))

