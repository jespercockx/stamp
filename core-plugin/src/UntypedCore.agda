module UntypedCore where

open import MyPrelude hiding (_$_; [_])
open import CoreSyn using
  ( Var; TyCon; KindOrType; TyLit; Id; Literal ) public

data Kind : Set where
  ∗   : Kind
  _⇒_ : Kind → Kind → Kind

data Type : Set where
  var    : Nat → Type
  _$_    : Type → Type → Type
  _⇒_   : Type → Type → Type
  forAll : Kind → Type → Type
  lit    : TyLit → Type

data Expr : Set where
  var   : Nat → Expr
  lit   : Literal → Expr
  _$_   : Expr → Expr → Expr
  _[_]   : Type → Expr → Expr
  lam   : Type → Expr → Expr
  Λ     : Kind → Expr → Expr


infix 3 _↦_

data Subst (A : Set) : Set where
  _↦_ : Nat → A → Subst A

record Shiftable (A : Set) : Set where
  field shift : (d cutoff : Nat) → A → A
open Shiftable {{...}} public

record Substitutable (A T : Set) {{_ : Shiftable A}} : Set where
  field
    subst : Subst A → T → T
open Substitutable {{...}} public

infix 5 _⇑_

_⇑_ : ∀ {A} {{_ : Shiftable A}} → (d : Nat) → A → A
d ⇑ e = shift d 0 e

instance
  ShiftableExpr : Shiftable Expr
  ShiftableExpr = record { shift = shiftE }
    where
      shiftE : (d cutoff : Nat) → Expr → Expr
      shiftE d c (var k) with compare k c
      shiftE d c (var k) | less _ = var k
      shiftE d c (var k) | _ = var (k + d)
      shiftE d c (lit l) = lit l
      shiftE d c (e₁ $ e₂) = shiftE d c e₁ $ shiftE d c e₂
      shiftE d c (τ [ e ]) = τ [ (shiftE d c e) ]
      shiftE d c (lam τ e) = lam τ (shiftE d (suc c) e)
      shiftE d c (Λ κ e) = Λ κ (shiftE d c e)

  SubstitutableExpr : Substitutable Expr Expr
  SubstitutableExpr = record { subst = substE }
    where
      substE : Subst Expr → Expr → Expr
      substE (i ↦ s) (var k) with compare k i
      ... | equal _ = s
      ... | _       = var k
      substE _ (lit l) = lit l
      substE σ (e₁ $ e₂) = substE σ e₁ $ substE σ e₂
      substE σ (τ [ e ]) = τ [ substE σ e ]
      substE (i ↦ s) (lam τ e) = lam τ (substE (suc i ↦ 1 ⇑ s) e)
      substE σ (Λ κ e) = Λ κ (substE σ e)

  ShiftableType : Shiftable Type
  ShiftableType = record { shift = shiftT }
    where
      shiftT : (d cutoff : Nat) → Type → Type
      shiftT d c (var k) with compare k c
      shiftT d c (var k) | less _ = var k
      shiftT d c (var k) | _ = var (k + d)
      shiftT d c (t₁ $ t₂) = shiftT d c t₁ $ shiftT d c t₂
      shiftT d c (t₁ ⇒ t₂) = shiftT d c t₁ ⇒ shiftT d c t₂
      shiftT d c (forAll κ t) = forAll κ (shiftT d (suc c) t)
      shiftT d c (lit l) = lit l

  SubstitutableType : Substitutable Type Type
  SubstitutableType = record { subst = substT }
    where
      substT : Subst Type → Type → Type
      substT (i ↦ s) (var k) with compare k i
      ... | equal _ = s
      ... | _       = var k
      substT σ (t₁ $ t₂) = substT σ t₁ $ substT σ t₂
      substT σ (t₁ ⇒ t₂) = substT σ t₁ ⇒ substT σ t₂
      substT (i ↦ s) (forAll κ t) = forAll κ (substT (suc i ↦ 1 ⇑ s) t)
      substT σ (lit l) = lit l


[_]_ : ∀ {A T} {{_ : Shiftable A}} {{_ : Substitutable A T}} →
       (σ : Subst A) → T → T
[_]_ = subst
