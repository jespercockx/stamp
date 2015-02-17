module UntypedCore where

open import MyPrelude hiding (_$_; [_])
open import CoreSyn
  using (Var; TyCon; KindOrType; TyLit; Id; Literal) public
open import CoreSyn
  hiding (module Type; module Expr; Expr)
  renaming (Kind to CKind; Type to CType)

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


{-
module ToCore where

  open import Control.Monad.State
  open import CoreMonad

  DeBruijnEnv : Set
  DeBruijnEnv = List Id

  ToCoreM : Set → Set
  ToCoreM = StateT (DeBruijnEnv × DeBruijnEnv) CoreM

  extendΣ : ToCoreM ⊤
  extendΣ = modify {!!} >> return tt

  record ToCore (A : Set) (B : Set) : Set where
    field toCore : A → ToCoreM B
  open ToCore {{...}} public


  instance
    ToCoreKind : ToCore Kind CKind
    ToCoreKind = record { toCore = return ∘ tr }
      where
        tr : Kind → CKind
        tr ∗ = liftedTypeKind
        tr (κ₁ ⇒ κ₂) = mkArrowKind (tr κ₁) (tr κ₂)

    ToCoreType : ToCore Type CType
    ToCoreType = record { toCore = tr }
      where
        tr : Type → ToCoreM CType
        tr (var k)      = {!!}
        tr (τ₁ $ τ₂)    = AppTy <$> tr τ₁ <*> tr τ₂
        tr (τ₁ ⇒ τ₂)    = FunTy <$> tr τ₁ <*> tr τ₂
        tr (forAll κ τ) = {!!}
        tr (lit l)      = pure (LitTy l)

    ToCoreExpr : ToCore Expr CoreExpr
    ToCoreExpr = record { toCore = tr }
      where
        tr : Expr → ToCoreM CoreExpr
        tr (var k) = {!!}
        tr (lit l) = pure (Lit l)
        tr (e₁ $ e₂) = App <$> tr e₁ <*> tr e₂
        tr (e [ τ ]) = App <$> tr e <*> (Type' <$> toCore τ)
        tr (lam τ e) = {!!}
        tr (Λ κ e) = {!!}
-}
