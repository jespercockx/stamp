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


shift : (d cutoff : Nat) → Expr → Expr
shift d c (var k) with compare k c
shift d c (var k) | less _ = var k
shift d c (var k) | _ = var (k + d)
shift d c (lit l) = lit l
shift d c (e₁ $ e₂) = shift d c e₁ $ shift d c e₂
shift d c (τ [ e ]) = τ [ (shift d c e) ]
shift d c (lam τ e) = lam τ (shift d (suc c) e)
shift d c (Λ κ e) = Λ κ (shift d c e)

_⇑_ : (d : Nat) → Expr → Expr
d ⇑ e = shift d 0 e

[_↦_]_ : (var : Nat) → (by orig : Expr) → Expr
[ i ↦ s ] var k with compare k i
... | equal _ = s
... | _       = var k
[ i ↦ s ] lit l = lit l
[ i ↦ s ] (e₁ $ e₂) = [ i ↦ s ] e₁ $ [ i ↦ s ] e₂
[ i ↦ s ] (τ [ e ]) = τ [ [ i ↦ s ] e ]
[ i ↦ s ] lam τ e = lam τ ([ i + 1 ↦ 1 ⇑ s ] e)
[ i ↦ s ] Λ κ e = Λ κ ([ i ↦ s ] e)
