{-# OPTIONS --allow-unsolved-metas #-}


module TypedUtils where

open import MyPrelude hiding (_$_; [_])
open import TypedCore
open import WeakenExpr


forAllⁿ : ∀ {Σ₀} (Σ : TyCxt) → Type (Σ ++ Σ₀) ∗ → Type Σ₀ ∗
forAllⁿ [] τ = τ
forAllⁿ (κ ∷ Σ) τ = forAllⁿ Σ (forAll κ τ)

weakenType-mkForAll : ∀ {Σ₀} Σ (τ : Type Σ ∗) 
                    → weakenType (mkForAll Σ τ) [] 
                    ≡ forAllⁿ {Σ₀} Σ (weakenType τ (⊆-prefix Σ Σ₀))
weakenType-mkForAll [] τ = refl
weakenType-mkForAll {Σ₀} (κ ∷ Σ) τ 
  rewrite weakenType-mkForAll {Σ₀} Σ (forAll κ τ) = refl

Λⁿ : ∀ {Σ₀} (Σ : TyCxt) {τ : Type (Σ ++ Σ₀) ∗} → Expr (Σ ++ Σ₀) [] τ → Expr Σ₀ [] (forAllⁿ Σ τ)
Λⁿ [] e = e
Λⁿ (κ ∷ Σ) e = Λⁿ Σ (Λ κ e)

mkΛ : ∀ (Σ : TyCxt) {τ : Type Σ ∗} → Expr Σ [] τ → Expr [] [] (mkForAll Σ τ)
mkΛ [] e = e
mkΛ (κ ∷ Σ) e = mkΛ Σ (Λ κ e)

_⇒ⁿ_ : ∀ {Σ : TyCxt} → Cxt Σ → Type Σ ∗ → Type Σ ∗
[] ⇒ⁿ τ = τ
(τ₁ ∷ Γ) ⇒ⁿ τ = Γ ⇒ⁿ (τ₁ ⇒ τ)

lamⁿ : ∀ {Σ : TyCxt} {Γ : Cxt Σ} {τ : Type Σ ∗} → Expr Σ Γ τ →
          Expr Σ [] (Γ ⇒ⁿ τ)
lamⁿ {Σ} {[]}     e = e
lamⁿ {Σ} {τ₁ ∷ Γ} e = lamⁿ {Γ = Γ} (lam τ₁ e)


_$ⁿ_ : ∀ {Σ Γ} {as : List (Type Σ ∗)} {b} → Expr Σ Γ (mkFunRev as b) → All (Expr Σ Γ) as → Expr Σ Γ b
f $ⁿ [] = f
f $ⁿ (x ∷ xs) = (f $ x) $ⁿ xs

applyTyCxt : ∀ {Σ₀} Σ {τ} → Expr Σ₀ [] (forAllⁿ Σ τ) → Expr (Σ ++ Σ₀) [] τ
applyTyCxt [] e = e
applyTyCxt (κ ∷ Σ) e = {!weakenExpr (applyTyCxt Σ e) (⊆-skip ⊆-refl) [ tvar hd ]!}

{-}
_[_]ⁿ {τ = τ₀} x [] rewrite applyTySubst-IdS τ₀ = x
_[_]ⁿ {τ = τ₀} x (τ ∷ τs) = 
 transport (Expr _ _) 
  {!substTop τ (applyTySubst (LiftS (τs ++All IdS)) τ₀) 
      ≡⟨ {!applyTySubst-applyTySubst sub (τ ∷ IdS)!} ⟩ 
    {!!} 
      ≡⟨ {!!} ⟩ 
    applyTySubst ((τ ∷ τs) ++All IdS) τ₀ ∎!} 
  ((x [ τs ]ⁿ) [ τ ]) --  (x [ τs ]ⁿ [ τ ])  
-}
