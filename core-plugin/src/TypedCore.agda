module TypedCore where

open import MyPrelude hiding (_$_; [_])
open import CoreSyn
  hiding (module Type; module Expr; Expr)
  renaming (Kind to CKind; Type to CType)

data Kind : Set where
  ∗   : Kind
  _⇒_ : Kind → Kind → Kind


Context : Set → Set
Context = List

TyCxt : Set
TyCxt = Context Kind


data ForeignTy (κ : Kind) : Set where
  lit : TyLit → ForeignTy κ
  var : NameSpace → String → String → ForeignTy κ
  con : TyCon → ForeignTy κ

infixr 2 _⇒_

infixl 3 _$_

data Type (Σ : TyCxt) : Kind → Set where
  var     : ∀ {κ} → κ ∈ Σ → Type Σ κ
  _$_     : ∀ {κ₁ κ₂} → Type Σ (κ₁ ⇒ κ₂) → Type Σ κ₁ → Type Σ κ₂
  _⇒_     : Type Σ ∗ → Type Σ ∗ → Type Σ ∗
  forAll  : ∀ κ → Type (κ ∷ Σ) ∗ → Type Σ ∗
  foreign : ∀ {κ} → ForeignTy κ → Type Σ κ


Cxt : TyCxt → Set
Cxt Σ = Context (Type Σ ∗)

weakenType : ∀ {Σ₁ Σ₂ κ} → Type Σ₁ κ → Σ₁ ⊆ Σ₂ → Type Σ₂ κ
weakenType (var i)      p = var (∈-over-⊆ p i)
weakenType (τ₁ $ τ₂)    p = weakenType τ₁ p $ weakenType τ₂ p
weakenType (τ₁ ⇒ τ₂)    p = weakenType τ₁ p ⇒ weakenType τ₂ p
weakenType (forAll κ τ) p = forAll κ (weakenType τ (⊆-keep p))
weakenType (foreign f)  p = foreign f

weakenCxt : ∀ {Σ₁ Σ₂} → Cxt Σ₁ → Σ₁ ⊆ Σ₂ → Cxt Σ₂
weakenCxt [] _ = []
weakenCxt (τ :: τs) p = weakenType τ p :: weakenCxt τs p

shift : ∀ {κ κ′ Σ} → Type Σ κ → Type (κ′ ∷ Σ) κ
shift τ = weakenType τ (⊆-skip ⊆-refl)

{-# TERMINATING #-}
substTop : ∀ {Σ κ κ′} → Type Σ κ′ → Type (κ′ ∷ Σ) κ → Type Σ κ
substTop τ (var hd)     = τ
substTop τ (var (tl x)) = var x
substTop τ (t₁ $ t₂)    = substTop τ t₁ $ substTop τ t₂
substTop τ (t₁ ⇒ t₂)    = substTop τ t₁ ⇒ substTop τ t₂
substTop τ (forAll κ t) = forAll κ (substTop (weakenType τ (⊆-skip ⊆-refl))
                                             (weakenType t ⊆-swap))
substTop τ (foreign f)  = foreign f



data ForeignExpr (Σ : TyCxt) (τ : Type Σ ∗) : Set where
  lit  : Literal → ForeignExpr Σ τ
  var  : NameSpace → String → String → ForeignExpr Σ τ
  con  : DataCon → ForeignExpr Σ τ
  dict : ForeignExpr Σ τ

data Expr (Σ : TyCxt) (Γ : Cxt Σ) : Type Σ ∗ → Set where
  var     : ∀ {τ} → τ ∈ Γ → Expr Σ Γ τ
  _$_     : ∀ {τ₁ τ₂} → Expr Σ Γ (τ₁ ⇒ τ₂) → Expr Σ Γ τ₁ → Expr Σ Γ τ₂
  _[_]    : ∀ {κ τ₁} → Expr Σ Γ (forAll κ τ₁) → (τ₂ : Type Σ κ) →
            Expr Σ Γ (substTop τ₂ τ₁)
  lam     : ∀ τ₁ {τ₂} → Expr Σ (τ₁ :: Γ) τ₂ → Expr Σ Γ (τ₁ ⇒ τ₂)
  Λ       : ∀ κ {τ} → Expr (κ :: Σ) (weakenCxt Γ (⊆-skip ⊆-refl)) τ →
            Expr Σ Γ (forAll κ τ)
  foreign : ∀ {τ} → ForeignExpr Σ τ → Expr Σ Γ τ

ex₁ : ∀ {Σ Γ} → Expr Σ Γ (forAll ∗ (var hd ⇒ var hd))
ex₁ = Λ ∗ (lam (var hd) (var hd))
