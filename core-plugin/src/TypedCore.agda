module TypedCore where

open import MyPrelude hiding (_$_)
import UntypedCore as U
open import UntypedCore using (Kind; ∗; _⇒_; TyLit; Literal)

Context : Set → Set
Context = List

TyCxt : Set
TyCxt = Context Kind


data Type (Σ : TyCxt) : Kind → Set where
  var : ∀ {κ} → κ ∈ Σ → Type Σ κ
  _$_ : ∀ {κ₁ κ₂} → Type Σ (κ₁ ⇒ κ₂) → Type Σ κ₁ → Type Σ κ₂
  _⇒_ : Type Σ ∗ → Type Σ ∗ → Type Σ ∗
  forAll : ∀ κ → Type (κ :: Σ) ∗ → Type Σ ∗
  lit : TyLit → Type Σ ∗


Cxt : TyCxt → Set
Cxt Σ = Context (Type Σ ∗)

-- weakenType : ∀ {Σ₁ Σ₂ k} → Type Σ₁ k → Σ₁ ⊆ Σ₂ → Type Σ₂ k
-- weakenType (var i)      p = var (subInList p i)
-- weakenType (τ₁ $ τ₂)    p = weakenType τ₁ p $ weakenType τ₂ p
-- weakenType (τ₁ ⇒ τ₂)    p = weakenType τ₁ p ⇒ weakenType τ₂ p
-- weakenType (forAll κ τ) p = forAll κ (weakenType τ (keep p))
-- weakenType (lit l)      p = lit l

-- weakenCxt : ∀ {Σ₁ Σ₂} → Cxt Σ₁ → Σ₁ ⊆ Σ₂ → Cxt Σ₂
-- weakenCxt [] _ = []
-- weakenCxt (τ :: τs) p = weakenType τ p :: weakenCxt τs p

data Expr (Σ : TyCxt) (Γ : Cxt Σ) : Type Σ ∗ → Set

shift : (d cutoff : Nat) → Expr → Expr



litType : ∀ {Σ} → Literal → Type Σ ∗
litType = {!!}

data Expr Σ Γ where
  var : ∀ {τ} → τ ∈ Γ → Expr Σ Γ τ
  lit : (l : Literal) → Expr Σ Γ (litType l)
  _$_ : ∀ {τ₁ τ₂} → Expr Σ Γ (τ₁ ⇒ τ₂) → Expr Σ Γ τ₁ → Expr Σ Γ τ₂
  -- _[_] : ∀ {} → Expr Σ Γ (forAll κ τ₂) → (τ₁ : Type Σ κ) → Expr Σ Γ ?
  lam  : ∀ τ₁ {τ₂} → Expr Σ (τ₁ :: Γ) τ₂ → Expr Σ Γ (τ₁ ⇒ τ₂)
  Λ : ∀ κ {τ}  → Expr (κ :: Σ) {!weakenCxt Γ (skip ⊆-refl)!} τ →
      Expr Σ Γ (forAll κ τ)
