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
  _⇒_    : Type → Type → Type
  forAll : Kind → Type → Type
  lit    : TyLit → Type

data Expr : Set where
  var   : Nat → Expr
  lit   : Literal → Expr
  _$_   : Expr → Expr → Expr
  _[_]  : Expr → Type → Expr
  lam   : Type → Expr → Expr
  Λ     : Kind → Expr → Expr
