module WeakenInCxt where

open import MyPrelude hiding (_$_; [_])
open import TypedCore


∈-weakenCxt : ∀ {Σ₁ Σ₂} {Γ : Cxt Σ₁} {τ : Type Σ₁ ∗} → τ ∈ Γ → (p : Σ₁ ⊆ Σ₂) →
                weakenType τ p ∈ weakenCxt Γ p
∈-weakenCxt hd     p = hd
∈-weakenCxt (tl q) p = tl (∈-weakenCxt q p)


⊆-weakenCxt : ∀ {Σ₁ Σ₂} {Γ₁ Γ₂ : Cxt Σ₁} → Γ₁ ⊆ Γ₂ → (p : Σ₁ ⊆ Σ₂) →
                weakenCxt Γ₁ p ⊆ weakenCxt Γ₂ p
⊆-weakenCxt {Γ₁ = []}     q p ()
⊆-weakenCxt {Γ₁ = _ ∷ Γ₁} q p hd     = ∈-weakenCxt (q hd) p
⊆-weakenCxt {Γ₁ = _ ∷ Γ₁} q p (tl r) = ⊆-weakenCxt (q ∘ tl) p r



{-# TERMINATING #-}
weakenInCxt : ∀ {Σ} {Γ₁ Γ₂ : Cxt Σ} {τ : Type Σ ∗} → Expr Σ Γ₁ τ →
                Γ₁ ⊆ Γ₂ → Expr Σ Γ₂ τ



weakenInCxt-Branch : ∀ {Σ} {Γ₁ Γ₂ : Cxt Σ} {τ : Type Σ ∗} {κ} {adt : ADT κ}
                       {tyArgs : Types Σ (ADT.tyCxt adt)} →
                       Γ₁ ⊆ Γ₂ → Branch Σ Γ₁ adt tyArgs τ →
                       Branch Σ Γ₂ adt tyArgs τ
weakenInCxt-Branch p (alt pat e)
  = alt pat (weakenInCxt e (⊆-+++-prefix {zs = patBinders pat} p))


weakenInCxt-Branch-branchConstructorIndex :
  ∀ {Σ} {Γ₁ Γ₂ : Cxt Σ} {τ : Type Σ ∗} {κ} {adt : ADT κ}
    {tyArgs : Types Σ (ADT.tyCxt adt)} →
    (p : Γ₁ ⊆ Γ₂) → (b : Branch Σ Γ₁ adt tyArgs τ) →
    branchConstructorIndex (weakenInCxt-Branch p b) ≡ branchConstructorIndex b
weakenInCxt-Branch-branchConstructorIndex _ (alt ̺ _) = refl
weakenInCxt-Branch-branchConstructorIndex _ (alt (lit _) _) = refl
weakenInCxt-Branch-branchConstructorIndex _ (alt (con _) _) = refl


weakenInCxt-Branch-Exhaustive :
  ∀ {κ} {adt : ADT κ} {Σ} {Γ₁ Γ₂ : Cxt Σ} {τ : Type Σ ∗}
    {tyArgs : Types Σ (ADT.tyCxt adt)} →
    (p : Γ₁ ⊆ Γ₂) →
    (bs : List (Branch Σ Γ₁ adt tyArgs τ)) →
    Exhaustive bs →
    Exhaustive (map (weakenInCxt-Branch p) bs)
weakenInCxt-Branch-Exhaustive {adt = Adt ftc n cs} {τ = τ} p bs ex
  rewrite compose-map bs (weakenInCxt-Branch p) branchConstructorIndex |
          map-≡ {xs = bs}
                (λ x → branchConstructorIndex (weakenInCxt-Branch p x))
                branchConstructorIndex
                (λ {b} → weakenInCxt-Branch-branchConstructorIndex p b)
  = ex




weakenInCxt (var i) p = var (p i)
weakenInCxt (e₁ $ e₂) p = weakenInCxt e₁ p $ weakenInCxt e₂ p
weakenInCxt (e [ τ ]) p = weakenInCxt e p [ τ ]
weakenInCxt (lam τ e) p = lam τ (weakenInCxt e (⊆-keep p))
weakenInCxt (Λ κ e) p = Λ κ (weakenInCxt e (⊆-weakenCxt p (⊆-skip ⊆-refl)))
weakenInCxt (con dc) p = con dc
weakenInCxt (lit l) p = lit l
weakenInCxt (fvar fv) p = fvar fv
weakenInCxt (fdict fd) p = fdict fd
weakenInCxt {Σ} {Γ₁} {Γ₂} {τ} (match adt tyArgs e bs ex) p
  = match adt tyArgs (weakenInCxt e p) (map (weakenInCxt-Branch p) bs)
          (weakenInCxt-Branch-Exhaustive p bs ex)
