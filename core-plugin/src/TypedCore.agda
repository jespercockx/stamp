module TypedCore where

open import MyPrelude hiding (_$_; [_])
import UntypedCore as U
open import UntypedCore using
     (Kind; ∗; _⇒_; TyLit; Literal; Shiftable; _⇑_;
      Substitutable; Subst; _↦_)

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

weakenType : ∀ {Σ₁ Σ₂ κ} → Type Σ₁ κ → Σ₁ ⊆ Σ₂ → Type Σ₂ κ
weakenType (var i)      p = var (∈-over-⊆ p i)
weakenType (τ₁ $ τ₂)    p = weakenType τ₁ p $ weakenType τ₂ p
weakenType (τ₁ ⇒ τ₂)    p = weakenType τ₁ p ⇒ weakenType τ₂ p
weakenType (forAll κ τ) p = forAll κ (weakenType τ (⊆-keep p))
weakenType (lit l)      p = lit l

weakenCxt : ∀ {Σ₁ Σ₂} → Cxt Σ₁ → Σ₁ ⊆ Σ₂ → Cxt Σ₂
weakenCxt [] _ = []
weakenCxt (τ :: τs) p = weakenType τ p :: weakenCxt τs p

shift : ∀ {κ κ′ Σ} → Type Σ κ → Type (κ′ ∷ Σ) κ
shift τ = weakenType τ (⊆-skip ⊆-refl)

{-# TERMINATING #-}
substTop : ∀ {Σ κ κ′} → Type Σ κ′ → Type (κ′ ∷ Σ) κ → Type Σ κ
substTop τ (var hd) = τ
substTop τ (var (tl x)) = var x
substTop τ (t₁ $ t₂) = substTop τ t₁ $ substTop τ t₂
substTop τ (t₁ ⇒ t₂) = substTop τ t₁ ⇒ substTop τ t₂
substTop τ (forAll κ t) = forAll κ (substTop (weakenType τ (⊆-skip ⊆-refl))
                                             (weakenType t ⊆-swap))
substTop τ (lit x) = lit x

data Expr (Σ : TyCxt) (Γ : Cxt Σ) : Type Σ ∗ → Set


postulate
  intLit : TyLit
  one : Literal

Int : ∀ {Σ} → Type Σ ∗
Int = lit intLit

litType : ∀ {Σ} → Literal → Type Σ ∗
litType one = Int -- TEMPORARY


data Expr Σ Γ where
  var  : ∀ {τ} → τ ∈ Γ → Expr Σ Γ τ
  lit  : (l : Literal) → Expr Σ Γ (litType l)
  _$_  : ∀ {τ₁ τ₂} → Expr Σ Γ (τ₁ ⇒ τ₂) → Expr Σ Γ τ₁ → Expr Σ Γ τ₂
  _[_] : ∀ {κ τ₁} → Expr Σ Γ (forAll κ τ₁) → (τ₂ : Type Σ κ) →
         Expr Σ Γ (substTop τ₂ τ₁)
  lam  : ∀ τ₁ {τ₂} → Expr Σ (τ₁ :: Γ) τ₂ → Expr Σ Γ (τ₁ ⇒ τ₂)
  Λ    : ∀ κ {τ}  → Expr (κ :: Σ) (weakenCxt Γ (⊆-skip ⊆-refl)) τ →
         Expr Σ Γ (forAll κ τ)


ex₁ : ∀ {Σ Γ} → Expr Σ Γ (Int ⇒ Int)
ex₁ = lam Int (var hd)

ex₂ : ∀ {Σ Γ} → Expr Σ Γ (forAll ∗ (var hd ⇒ var hd))
ex₂ = Λ ∗ (lam (var hd) (var hd))

ex₃ : ∀ {Σ Γ} → Expr Σ Γ (Int ⇒ Int)
ex₃ = ex₂ [ Int ]

ex₄ : ∀ {Σ Γ} → Expr Σ Γ Int
ex₄ = ex₃ $ lit one
