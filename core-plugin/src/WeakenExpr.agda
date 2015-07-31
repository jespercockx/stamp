module WeakenExpr where

open import Prelude using (_≡⟨_⟩_; _≡⟨_⟩ʳ_; _∎) renaming (sym to ≡-sym; trans to ≡-trans)
open import MyPrelude hiding (_$_; [_])
open import TypedCore
open import WeakenInCxt


weakenVar : ∀ {Σ₁ Σ₂ Γ} {τ : Type Σ₁ ∗} → τ ∈ Γ → (p : Σ₁ ⊆ Σ₂) →
              weakenType τ p ∈ weakenCxt Γ p
weakenVar hd p = hd
weakenVar (tl i) p = tl (weakenVar i p)


weakenPat : ∀ {Σ₁ Σ₂ κ} {adt : ADT κ} {tyArgs : Types Σ₁ (ADT.tyCxt adt)} →
              Pat Σ₁ adt tyArgs → (p : Σ₁ ⊆ Σ₂) →
              Pat Σ₂ adt (weakenTypes tyArgs p)
weakenPat ̺        _ = ̺
weakenPat (lit l)  _ = lit l
weakenPat (con dc) _ = con dc


weakenCxt-+++ :
  ∀ {Σ₁ Σ₂} → (Γ₁ Γ₂ : Cxt Σ₁) → (p : Σ₁ ⊆ Σ₂) →
    weakenCxt (Γ₁ +++ Γ₂) p ≡ weakenCxt Γ₁ p +++ weakenCxt Γ₂ p
weakenCxt-+++ Γ₁ Γ₂ p = map-+++-assoc {xs = Γ₁} (flip weakenType p)


⊆-weakenCxt-+++ : ∀ {Σ₁ Σ₂} {Γ₁ Γ₂ : Cxt Σ₁}
                    (p : Σ₁ ⊆ Σ₂) →
                    weakenCxt (Γ₁ +++ Γ₂) p ⊆ weakenCxt Γ₁ p +++ weakenCxt Γ₂ p
⊆-weakenCxt-+++ {Γ₁ = Γ₁} {Γ₂} p rewrite weakenCxt-+++ Γ₁ Γ₂ p = ⊆-refl

∈-over-⊆-trans : ∀ {Σ₁ Σ₂ Σ₃ : TyCxt} {κ} → (p : Σ₁ ⊆ Σ₂) → (q : Σ₂ ⊆ Σ₃) →
                   (i : κ ∈ Σ₁) →
                   (∈-over-⊆ q (∈-over-⊆ p i)) ≡ (∈-over-⊆ (⊆-trans p q) i)
∈-over-⊆-trans (p ∷ ps) q hd = refl
∈-over-⊆-trans (p ∷ ps) q (tl i) = ∈-over-⊆-trans ps q i

∈-over-⊆-skip : ∀ {A : Set} {Σ₁ Σ₂ : List A} {κ₁ κ₂ : A} → (p : κ₁ ∈ Σ₁) → (q : Σ₁ ⊆ Σ₂) →
                ∈-over-⊆ (⊆-skip q) p ≡ tl {y = κ₂} (∈-over-⊆ q p)
∈-over-⊆-skip {Σ₁ = κ₁ ∷ Σ₁} hd (q₁ ∷ q₂) = refl
∈-over-⊆-skip {Σ₁ = _ ∷ Σ₁} (tl p) (q₁ ∷ q₂) = ∈-over-⊆-skip p q₂

⊆-skip-⊆-trans : ∀ {Σ₁ Σ₂ Σ₃ : TyCxt} {κ} → (p : Σ₁ ⊆ Σ₂) → (q : Σ₂ ⊆ Σ₃) →
                   ⊆-trans (⊆-skip  {x = κ} p) (hd ∷ ⊆-skip q)
                   ≡ ⊆-skip (⊆-trans p q)
⊆-skip-⊆-trans [] q = refl
⊆-skip-⊆-trans (p ∷ ps) q = cong₂ _∷_ (∈-over-⊆-skip p q) (⊆-skip-⊆-trans ps q)

∈-over-skip : ∀ {A : Set} {Σ₁ Σ₂ : List A} {κ₁ κ₂} → (p : Σ₁ ⊆ Σ₂) (q : κ₁ ∈ Σ₁) →
      tl {y = κ₂} {xs = Σ₂} (∈-over-⊆ p q) ≡ ∈-over-⊆ (⊆-skip p) q
∈-over-skip (p ∷ ps) hd = refl
∈-over-skip (p ∷ ps) (tl q) = ∈-over-skip ps q

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

⊆-trans-⊆-skip-⊆-refl : ∀ {Σ₁ Σ₂} {κ : Kind} → (p : Σ₁ ⊆ Σ₂) →
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

weakenType-lookupTySubst :
  ∀ {Σ₁ Σ₂ Σ₃ κ} → (tyArgs : TySubst Σ₁ Σ₂) →
    (i : κ ∈ Σ₁) → (p : Σ₂ ⊆ Σ₃) →
    weakenType (lookupTySubst tyArgs i) p
    ≡ lookupTySubst (weakenTypes tyArgs p) i
weakenType-lookupTySubst (tyArg ∷ tyArgs) hd p = refl
weakenType-lookupTySubst (tyArg ∷ tyArgs) (tl i) p = weakenType-lookupTySubst tyArgs i p

weakenType-weakenType :
  ∀ {Σ₁ Σ₂ Σ₃} {κ} → (τ : Type Σ₁ κ) →
    (p : Σ₁ ⊆ Σ₂) → (q : Σ₂ ⊆ Σ₃) →
    weakenType (weakenType τ p) q ≡ weakenType τ (⊆-trans p q)
weakenType-weakenType (tvar i) p q = cong tvar (∈-over-⊆-trans p q i)
weakenType-weakenType (τ₁ $ τ₂) p q
  rewrite weakenType-weakenType τ₁ p q |
          weakenType-weakenType τ₂ p q = refl
weakenType-weakenType (τ₁ ⇒ τ₂) p q
  rewrite weakenType-weakenType τ₁ p q |
          weakenType-weakenType τ₂ p q = refl
weakenType-weakenType (forAll κ τ) p q
  rewrite weakenType-weakenType τ (⊆-keep p) (⊆-keep q)
  = cong (forAll κ ∘ weakenType τ ∘ λ x → (hd ∷ x)) (⊆-skip-⊆-trans p q)
weakenType-weakenType (con _) p q = refl
weakenType-weakenType (lit _) p q = refl

applyTySubst-lookupTySubst :
  ∀ {Σ₁ Σ₂ Σ₃} {κ} → (x : κ ∈ Σ₁) →
    (sub₁ : TySubst Σ₁ Σ₂) (sub₂ : TySubst Σ₂ Σ₃) →
    applyTySubst sub₂ (lookupTySubst sub₁ x) ≡ lookupTySubst (ComposeS sub₁ sub₂) x
applyTySubst-lookupTySubst hd     (_ ∷ sub₁) sub₂ = refl
applyTySubst-lookupTySubst (tl x) (_ ∷ sub₁) sub₂ = applyTySubst-lookupTySubst x sub₁ sub₂

weakenTypes-skip :
  ∀ {Σ₁ Σ₂ Σ₃} {κ} (tyArgs : Types Σ₁ Σ₃) → (p : Σ₁ ⊆ Σ₂) →
    weakenTypes (weakenTypes tyArgs (⊆-skip {x = κ} ⊆-refl)) (hd ∷ ⊆-skip p)
    ≡ weakenTypes (weakenTypes tyArgs p) (⊆-skip ⊆-refl)
weakenTypes-skip [] p = refl
weakenTypes-skip {Σ₁} {Σ₂} {κ = κ} (ty ∷ tyArgs) p
  rewrite weakenType-weakenType ty (⊆-skip {x = κ} ⊆-refl) (hd ∷ ⊆-skip p)
        | weakenType-weakenType ty p (⊆-skip {x = κ} ⊆-refl)
  = cong₂ _∷_ (cong (weakenType ty) (⊆-trans-⊆-skip-⊆-refl p)) (weakenTypes-skip tyArgs p)

weakenType-applyTySubst :
  ∀ {Σ₁ Σ₂ Σ₃ κ} → (tyArgs : TySubst Σ₁ Σ₂) →
    (τ : Type Σ₁ κ) → (p : Σ₂ ⊆ Σ₃) →
    weakenType (applyTySubst tyArgs τ) p
    ≡ applyTySubst (weakenTypes tyArgs p) τ
weakenType-applyTySubst {Σ₁} {Σ₂} {Σ₃} {κ} tyArgs (tvar i) p
  = weakenType-lookupTySubst tyArgs i p
weakenType-applyTySubst tyArgs (τ₁ $ τ₂) p
  rewrite weakenType-applyTySubst tyArgs τ₁ p |
          weakenType-applyTySubst tyArgs τ₂ p = refl
weakenType-applyTySubst tyArgs (τ₁ ⇒ τ₂) p
  rewrite weakenType-applyTySubst tyArgs τ₁ p |
          weakenType-applyTySubst tyArgs τ₂ p = refl
weakenType-applyTySubst tyArgs (forAll κ τ) p
  rewrite weakenType-applyTySubst (tvar hd ∷ weakenTypes tyArgs (⊆-skip ⊆-refl)) τ (⊆-keep p) |
          weakenTypes-skip {κ = κ} tyArgs p = refl
weakenType-applyTySubst tyArgs (con c) p = refl
weakenType-applyTySubst tyArgs (lit l) p = refl


applyShiftS : ∀ {Σ₁ Σ₂ κ₁ κ₂} → (sub : TySubst Σ₁ Σ₂) (τ : Type Σ₁ κ₁) → 
              applyTySubst (ShiftS {κ = κ₂} sub) τ ≡ shift (applyTySubst sub τ)

applyShiftS sub (tvar x) = ∈-mapAll shift sub x
applyShiftS sub (τ₁ $ τ₂) = cong₂ _$_ (applyShiftS sub τ₁) (applyShiftS sub τ₂)
applyShiftS sub (τ₁ ⇒ τ₂) = cong₂ _⇒_ (applyShiftS sub τ₁) (applyShiftS sub τ₂)
applyShiftS sub (forAll κ τ) = cong (forAll κ) {!!}
applyShiftS sub (con x) = refl
applyShiftS sub (lit x) = refl

applyWeakenS : ∀ {Σ₁ Σ₂ κ} → (p : Σ₁ ⊆ Σ₂) (τ : Type Σ₁ κ) → 
               applyTySubst (WeakenS p) τ ≡ weakenType τ p
applyWeakenS p (tvar x) = lookupWeakenS p x
  where lookupWeakenS : ∀ {Σ₁ Σ₂ κ} → (p : Σ₁ ⊆ Σ₂) (x : κ ∈ Σ₁) → 
                        lookupTySubst (WeakenS p) x ≡ tvar (∈-over-⊆ p x)
        lookupWeakenS (_ ∷ _) hd = refl
        lookupWeakenS (_ ∷ p) (tl x) = lookupWeakenS p x
applyWeakenS p (τ₁ $ τ₂) = cong₂ _$_ (applyWeakenS p τ₁) (applyWeakenS p τ₂)
applyWeakenS p (τ₁ ⇒ τ₂) = cong₂ _⇒_ (applyWeakenS p τ₁) (applyWeakenS p τ₂)
applyWeakenS p (forAll κ τ)
--  rewrite {!!}
  = cong (forAll κ) {!!}
applyWeakenS p (con x) = refl
applyWeakenS p (lit x) = refl


{-
applyTySubst-applyTySubst :
  ∀ {Σ₁ Σ₂ Σ₃} {κ} → (τ : Type Σ₁ κ) →
    (sub₁ : TySubst Σ₁ Σ₂) (sub₂ : TySubst Σ₂ Σ₃) →
    applyTySubst sub₂ (applyTySubst sub₁ τ) ≡ applyTySubst (ComposeS sub₁ sub₂) τ
applyTySubst-applyTySubst (tvar x) sub₁ sub₂ = applyTySubst-lookupTySubst x sub₁ sub₂
applyTySubst-applyTySubst (τ₁ $ τ₂) sub₁ sub₂ = cong₂ _$_ (applyTySubst-applyTySubst τ₁ sub₁ sub₂) (applyTySubst-applyTySubst τ₂ sub₁ sub₂)
applyTySubst-applyTySubst (τ₁ ⇒ τ₂) sub₁ sub₂ = cong₂ _⇒_ (applyTySubst-applyTySubst τ₁ sub₁ sub₂) (applyTySubst-applyTySubst τ₂ sub₁ sub₂)
applyTySubst-applyTySubst (forAll κ τ) sub₁ sub₂ = cong (forAll κ) {!!}
applyTySubst-applyTySubst (con x) sub₁ sub₂ = refl
applyTySubst-applyTySubst (lit x) sub₁ sub₂ = refl
-}

weakenCxt-applyTySubst :
  ∀ {Σ₁ Σ₂ κ} {adt : ADT κ} {tyArgs : Types Σ₁ (ADT.tyCxt adt)}
    (Γ : Cxt (ADT.tyCxt adt)) → (p : Σ₁ ⊆ Σ₂) →
    weakenCxt (map (applyTySubst tyArgs) Γ) p
    ≡ map (applyTySubst (weakenTypes tyArgs p)) Γ
weakenCxt-applyTySubst [] p = refl
weakenCxt-applyTySubst {adt = adt} {tyArgs} (τ ∷ Γ) p
  rewrite weakenCxt-applyTySubst {adt = adt} {tyArgs} Γ p |
          weakenType-applyTySubst tyArgs τ p = refl

weakenCxt-patBinders :
  ∀ {Σ₁ Σ₂ κ} {adt : ADT κ} {tyArgs : Types Σ₁ (ADT.tyCxt adt)}
    (pat : Pat Σ₁ adt tyArgs) → (p : Σ₁ ⊆ Σ₂) →
    weakenCxt (patBinders pat) p ≡ patBinders (weakenPat pat p)
weakenCxt-patBinders ̺ p = refl
weakenCxt-patBinders (lit x) p = refl
weakenCxt-patBinders {adt = adt} (con dc) p
  = weakenCxt-applyTySubst {adt = adt} (dataConArgs dc) p

⊆-weakenCxt-patBinders :
  ∀ {Σ₁ Σ₂ κ} {adt : ADT κ} {tyArgs : Types Σ₁ (ADT.tyCxt adt)}
    (pat : Pat Σ₁ adt tyArgs) → (p : Σ₁ ⊆ Σ₂) →
    weakenCxt (patBinders pat) p ⊆ patBinders (weakenPat pat p)
⊆-weakenCxt-patBinders pat p rewrite weakenCxt-patBinders pat p = ⊆-refl

weakenCxt-weakenCxt :
  ∀ {Σ₁ Σ₂ Σ₃} → (Γ : List (Type Σ₁ ∗)) →
    (p : Σ₁ ⊆ Σ₂) → (q : Σ₂ ⊆ Σ₃) →
    weakenCxt (weakenCxt Γ p) q ≡ weakenCxt Γ (⊆-trans p q)
weakenCxt-weakenCxt Γ p q
  rewrite compose-map Γ (flip weakenType p) (flip weakenType q) |
          map-≡ {xs = Γ} _ _ (λ {τ} → weakenType-weakenType τ p q)
          = refl

weakenType-substTop :
  ∀ {Σ₁ Σ₂} {κ κ′} →
    (τ₁ : Type Σ₁ κ) → (τ₂ : Type (κ ∷ Σ₁) κ′) →
    (p : Σ₁ ⊆ Σ₂) →
    weakenType (substTop τ₁ τ₂) p
    ≡ substTop (weakenType τ₁ p) (weakenType τ₂ (⊆-keep p))
weakenType-substTop τ₁ τ₂ p =
  weakenType (substTop τ₁ τ₂) p
    ≡⟨ weakenType-applyTySubst (τ₁ ∷ IdS) τ₂ p ⟩
  applyTySubst (weakenTypes (τ₁ ∷ IdS) p) τ₂
    ≡⟨ {!!} ⟩
  substTop (weakenType τ₁ p) (weakenType τ₂ (⊆-keep p)) ∎

-- τ = (weakenType τ (⊆-skip ⊆-refl))
-- τ′ = (weakenType τ′ ⊆-swap)

-- τ = (weakenType τ p)
-- τ′ = (weakenType τ′ (⊆-keep (⊆-keep p)))

-- weakenType
--       (substTop τ τ₁)
--       (⊆-keep p)
--       ≡
--       substTop (weakenType τ (⊆-skip ⊆-refl))
--       (weakenType τ′ ⊆-swap



-- weakenType-applyTyArgs :
--   ∀ {Σ₁ Σ₂} {κ} → (adt : ADT κ) → (p : Σ₁ ⊆ Σ₂) →
--     (tyArgs : Types Σ₁ (ADT.tyCxt adt)) →
--     weakenType (applyTyArgs (con (adtTyCon adt)) tyArgs) p
--     ≡ applyTyArgs (con (adtTyCon adt)) (weakenTypes tyArgs p)
-- weakenType-applyTyArgs {κ = ∗} adt p [] = refl
-- weakenType-applyTyArgs {Σ₁} {Σ₂} {κ ⇒ κ₁} adt p tyArgs = {!!}



-- -- weakenExpr : ∀ {Σ₁ Σ₂ Γ} {τ₁ : Type Σ₁ ∗} → Expr Σ₁ Γ τ₁ → (p : Σ₁ ⊆ Σ₂) →
-- --                Expr Σ₂ (weakenCxt Γ p) (weakenType τ₁ p)



eixample : ∀ {Σ₁ Σ₂} {κ} → (Γ : List (Type Σ₁ ∗)) →
             (p : Σ₁ ⊆ Σ₂) →
             weakenCxt (weakenCxt Γ (⊆-skip ⊆-refl)) (hd ∷ ⊆-skip p)
             ≡
             weakenCxt (weakenCxt Γ p) (⊆-skip {x = κ} ⊆-refl)
eixample {κ = κ} Γ p
  rewrite weakenCxt-weakenCxt Γ (⊆-skip {x = κ} ⊆-refl) (hd ∷ ⊆-skip p) |
          weakenCxt-weakenCxt Γ p (⊆-skip {x = κ} ⊆-refl) |
          ⊆-trans-⊆-skip-⊆-refl {κ = κ} p
  = refl


weakenExpr : ∀ {Σ₁ Σ₂ Γ} {τ₁ : Type Σ₁ ∗} → Expr Σ₁ Γ τ₁ → (p : Σ₁ ⊆ Σ₂) →
               Expr Σ₂ (weakenCxt Γ p) (weakenType τ₁ p)
weakenBranch : ∀ {Σ₁ Σ₂ Γ κ} {adt : ADT κ} {tyArgs : Types Σ₁ (ADT.tyCxt adt)}
                 {τ : Type Σ₁ ∗} →
                 Branch Σ₁ Γ adt tyArgs τ → (p : Σ₁ ⊆ Σ₂) →
                 Branch Σ₂ (weakenCxt Γ p) adt (weakenTypes tyArgs p)
                           (weakenType τ p)
branchConstructorIndex-weakenBranch :
  ∀ {Σ₁ Σ₂} {κ} →
    (p : Σ₁ ⊆ Σ₂) →
    (adt : ADT κ) →
    (tyArgs : Types Σ₁ (ADT.tyCxt adt)) →
    (Γ : List (Type Σ₁ ∗)) →
    (τ : Type Σ₁ ∗) →
    (b : Branch Σ₁ Γ adt tyArgs τ) →
    branchConstructorIndex (weakenBranch b p) ≡ branchConstructorIndex b
Exhaustive-weakenBranch :
  ∀ {Σ₁ Σ₂} {κ} →
    (p : Σ₁ ⊆ Σ₂) →
    (adt : ADT κ) →
    (tyArgs : Types Σ₁ (ADT.tyCxt adt)) →
    (Γ : List (Type Σ₁ ∗)) →
    (τ : Type Σ₁ ∗) →
    (bs : List (Branch Σ₁ Γ adt tyArgs τ)) →
    Exhaustive bs →
    Exhaustive (map (flip weakenBranch p) bs)


weakenExpr (var i) p = var (weakenVar i p)
weakenExpr (e₁ $ e₂) p = weakenExpr e₁ p $ weakenExpr e₂ p
weakenExpr (_[_] {τ₁ = τ₁} e τ) p = {!!}
--  rewrite weakenType-substTop τ τ₁ p = weakenExpr e p [ weakenType τ p ]
weakenExpr (lam τ e) p = lam (weakenType τ p) (weakenExpr e p)
weakenExpr {Σ₁} {Σ₂} {Γ} (Λ κ {τ} e) p
  = let we : Expr (κ ∷ Σ₂) (weakenCxt (weakenCxt Γ (⊆-skip ⊆-refl)) (hd ∷ ⊆-skip p))
                  (weakenType τ (⊆-keep p))
        we = {!!} --weakenExpr e (hd , ⊆-skip p)
        cxts : weakenCxt (weakenCxt Γ (⊆-skip ⊆-refl)) (hd ∷ ⊆-skip p)
               ≡
               weakenCxt (weakenCxt Γ p) (⊆-skip {x = κ} ⊆-refl)
        cxts = {!!} -- transport  = ?
    in Λ κ (transport (λ cxt → Expr (κ ∷ Σ₂) cxt (weakenType τ (⊆-keep p)))
                      (eixample Γ p) we)


-- Expr (κ ∷ Σ₂) (weakenCxt (weakenCxt Γ p) (⊆-skip ⊆-refl))
--       (weakenType τ (⊆-keep p))
--       ≡
--       Expr (κ ∷ Σ₂)
--       (weakenCxt (weakenCxt Γ (⊆-skip ⊆-refl)) (hd , ⊆-skip p))
--       (weakenType τ (⊆-keep p))

-- weakenCxt-weakenCxt :
--   ∀ {Σ₁ Σ₂ Σ₃} → (Γ : List (Type Σ₁ ∗)) →
--     (p : Σ₁ ⊆ Σ₂) → (q : Σ₂ ⊆ Σ₃) →
--     weakenCxt (weakenCxt Γ p) q ≡ weakenCxt Γ (⊆-trans p q)

weakenExpr (con dc) p rewrite weakenType-weakenType (dcType dc) [] p = con dc
weakenExpr (lit (flit l)) _ = lit (flit l)
weakenExpr (fvar (fvar m i)) _ = fvar (fvar m i)
weakenExpr (fdict fdict) _ = fdict fdict
weakenExpr {Σ₂ = Σ₂} {Γ} (match {τ₁} adt tyArgs e bs ex) p
  = match adt (weakenTypes tyArgs p)
              (transport (Expr Σ₂ (weakenCxt Γ p))
                         {! !}
                         {!(weakenExpr e p)!})
              {!(map (flip weakenBranch p) bs)!}
              (Exhaustive-weakenBranch p adt tyArgs Γ τ₁ bs ex)



weakenBranch {_} {Σ₂} {Γ} {_} {Adt ftc n cs} {_} {τ} (alt pat e) p
  = alt (weakenPat pat p)
        (weakenInCxt {!(weakenExpr e p)!}
                     (⊆-trans (⊆-weakenCxt-+++ {Γ₁ = patBinders pat} p)
                              (⊆-+++-suffix (⊆-weakenCxt-patBinders pat p))))

branchConstructorIndex-weakenBranch _ _ _ _ _ (alt ̺ _) = refl
branchConstructorIndex-weakenBranch _ _ _ _ _ (alt (lit _) _) = refl
branchConstructorIndex-weakenBranch _ _ _ _ _ (alt (con _) _) = refl


Exhaustive-weakenBranch p adt tyArgs Γ τ bs ex
  rewrite compose-map bs (flip weakenBranch p) branchConstructorIndex |
          map-≡ {xs = bs} _ _
                (λ {b} → branchConstructorIndex-weakenBranch p adt tyArgs Γ τ b)
          = ex
