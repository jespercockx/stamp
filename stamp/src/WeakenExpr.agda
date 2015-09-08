module WeakenExpr where

open import Prelude using (_≡⟨_⟩_; _≡⟨_⟩ʳ_; _∎) renaming (sym to ≡-sym; trans to ≡-trans)
open import MyPrelude hiding (_$_; [_])
open import TypedCore
open import WeakenInCxt

-- weakening variables

weakenVar : ∀ {Σ₁ Σ₂ Γ} {τ : Type Σ₁ ∗} → τ ∈ Γ → (p : Σ₁ ⊆ Σ₂) →
              weakenType τ p ∈ weakenCxt Γ p
weakenVar hd p = hd
weakenVar (tl i) p = tl (weakenVar i p)

-- weakening patterns

weakenPat : ∀ {Σ₁ Σ₂ κ} {adt : ADT κ} {tyArgs : Types Σ₁ (ADT.tyCxt adt)} →
              Pat Σ₁ adt tyArgs → (p : Σ₁ ⊆ Σ₂) →
              Pat Σ₂ adt (weakenTypes tyArgs p)
weakenPat ̺        _ = ̺
weakenPat (lit l)  _ = lit l
weakenPat (con dc) _ = con dc

-- properties of weakenCxt

weakenCxt-+++ :
  ∀ {Σ₁ Σ₂} → (Γ₁ Γ₂ : Cxt Σ₁) → (p : Σ₁ ⊆ Σ₂) →
    weakenCxt (Γ₁ +++ Γ₂) p ≡ weakenCxt Γ₁ p +++ weakenCxt Γ₂ p
weakenCxt-+++ Γ₁ Γ₂ p = map-+++-assoc {xs = Γ₁} (flip weakenType p)

⊆-weakenCxt-+++ : ∀ {Σ₁ Σ₂} {Γ₁ Γ₂ : Cxt Σ₁}
                    (p : Σ₁ ⊆ Σ₂) →
                    weakenCxt (Γ₁ +++ Γ₂) p ⊆ weakenCxt Γ₁ p +++ weakenCxt Γ₂ p
⊆-weakenCxt-+++ {Γ₁ = Γ₁} {Γ₂} p rewrite weakenCxt-+++ Γ₁ Γ₂ p = ⊆-refl

-- properties of weakenType

-- looking up a type in a weakened context gives the same result as first looking
-- up the type and then weakening it
weakenType-lookupTySubst :
  ∀ {Σ₁ Σ₂ Σ₃ κ} → (tyArgs : TySubst Σ₁ Σ₂) →
    (i : κ ∈ Σ₁) → (p : Σ₂ ⊆ Σ₃) →
    weakenType (lookupTySubst tyArgs i) p
    ≡ lookupTySubst (weakenTypes tyArgs p) i
weakenType-lookupTySubst (tyArg ∷ tyArgs) hd p = refl
weakenType-lookupTySubst (tyArg ∷ tyArgs) (tl i) p = weakenType-lookupTySubst tyArgs i p

-- collecting two weakenings
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

weakenTypes-skip :
  ∀ {Σ₁ Σ₂ Σ₃} {κ} (tyArgs : Types Σ₁ Σ₃) → (p : Σ₁ ⊆ Σ₂) →
    weakenTypes (weakenTypes tyArgs (⊆-skip {x = κ} ⊆-refl)) (hd ∷ ⊆-skip p)
    ≡ weakenTypes (weakenTypes tyArgs p) (⊆-skip ⊆-refl)
weakenTypes-skip [] p = refl
weakenTypes-skip {Σ₁} {Σ₂} {κ = κ} (ty ∷ tyArgs) p
  rewrite weakenType-weakenType ty (⊆-skip {x = κ} ⊆-refl) (hd ∷ ⊆-skip p)
        | weakenType-weakenType ty p (⊆-skip {x = κ} ⊆-refl)
  = cong₂ _∷_ (cong (weakenType ty) (⊆-trans-⊆-skip-⊆-refl p)) (weakenTypes-skip tyArgs p)


wk-lookupTySubst : ∀ {Σ₁ Σ₂} (p : Σ₁ ⊆ Σ₂) → ∀ {κ} (x : κ ∈ Σ₁) →
                   lookupTySubst (WeakenS p) x ≡ tvar (∈-over-⊆ p x)
wk-lookupTySubst p = ∈-mapAll tvar p

lookup-skip-refl : ∀ {A : Set} {Σ : List A}  {κ κ′} → (x : κ ∈ Σ) →
                   ∈-over-⊆ (⊆-skip {x = κ′} ⊆-refl) x ≡ tl x
lookup-skip-refl x =
  ∈-over-⊆ (⊆-skip ⊆-refl) x
  ≡⟨ ∈-over-⊆-skip x ⊆-refl ⟩
  tl (∈-over-⊆ ⊆-refl x)
  ≡⟨ cong tl (≡-sym (∈-over-refl x)) ⟩
  tl x ∎

shift-tvar : ∀ {Σ κ κ′} → (x : κ ∈ Σ) →
             shift {κ′ = κ′} (tvar x) ≡ tvar (tl x)
shift-tvar x = cong tvar (lookup-skip-refl x)

ShiftS-wk-skip : ∀ {Σ₁ Σ₂ κ} (p : Σ₁ ⊆ Σ₂) →
                 ShiftS {κ = κ} (WeakenS p) ≡ WeakenS (⊆-skip p)
ShiftS-wk-skip p =
  ShiftS (WeakenS p)
  ≡⟨ mapAll-mapAll tvar shift p ⟩
  mapAll (shift ∘ tvar) p
  ≡⟨ mapAll-cong (shift ∘ tvar) (tvar ∘ tl) (λ x → shift-tvar x) p ⟩
  mapAll (tvar ∘ tl) p
  ≡⟨ ≡-sym (mapAll-mapAll tl tvar p) ⟩
  WeakenS (⊆-skip p)
  ∎

LiftS-wk-keep : ∀ {Σ₁ Σ₂ κ} (p : Σ₁ ⊆ Σ₂) →
           LiftS {κ = κ} (WeakenS p) ≡ WeakenS (⊆-keep p)
LiftS-wk-keep p = cong (_∷_ (tvar hd)) (ShiftS-wk-skip p)

wk-weaken : ∀ {Σ₁ Σ₂ κ} (p : Σ₁ ⊆ Σ₂) → (τ : Type Σ₁ κ) →
            weakenType τ p ≡ applyTySubst (WeakenS p) τ
wk-weaken p (tvar x) = ≡-sym (wk-lookupTySubst p x)
wk-weaken p (τ $ τ₁) = cong₂ _$_ (wk-weaken p τ) (wk-weaken p τ₁)
wk-weaken p (τ ⇒ τ₁) = cong₂ _⇒_ (wk-weaken p τ) (wk-weaken p τ₁)
wk-weaken p (forAll κ τ) =
  cong (forAll κ)
    (≡-trans (wk-weaken (⊆-keep p) τ)
      (cong (λ ps → applyTySubst ps τ) (≡-sym (LiftS-wk-keep p))))
wk-weaken p (con x) = refl
wk-weaken p (lit x) = refl



-- -- properties of applyTySubst

∈-ComposeS : ∀ {Σ₁ Σ₂ Σ₃ κ} (sub₁ : TySubst Σ₁ Σ₂) (sub₂ : TySubst Σ₂ Σ₃) (x : κ ∈ Σ₁) →
                ∈-All (ComposeS sub₁ sub₂) x ≡ applyTySubst sub₂ (∈-All sub₁ x)
∈-ComposeS sub₁ sub₂ = ∈-mapAll (applyTySubst sub₂) sub₁

-- applying a weakened substitution gives the same result as first applying the substitution
-- and then weakening the result
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

map-shift : ∀ {Σ₁ Σ₂ κ} → (sub : TySubst Σ₁ Σ₂) → ComposeS sub (WeakenS (⊆-skip ⊆-refl)) ≡ mapAll (shift {κ′ = κ}) sub
map-shift sub = mapAll-cong (applyTySubst (WeakenS (⊆-skip ⊆-refl))) shift (λ x → ≡-sym (wk-weaken (⊆-skip ⊆-refl) x)) sub

weakenType-⊆-refl : ∀ {Σ κ} (τ : Type Σ κ) → weakenType τ ⊆-refl ≡ τ
weakenType-⊆-refl (tvar x) = cong tvar (≡-sym (∈-over-refl x))
weakenType-⊆-refl (τ $ τ₁) = cong₂ _$_ (weakenType-⊆-refl τ) (weakenType-⊆-refl τ₁)
weakenType-⊆-refl (τ ⇒ τ₁) = cong₂ _⇒_ (weakenType-⊆-refl τ) (weakenType-⊆-refl τ₁)
weakenType-⊆-refl (forAll κ τ) = cong (forAll κ) (weakenType-⊆-refl τ)
weakenType-⊆-refl (con x) = refl
weakenType-⊆-refl (lit x) = refl

applyTySubst-IdS : ∀ {Σ κ} (τ : Type Σ κ) → applyTySubst IdS τ ≡ τ
applyTySubst-IdS τ =
  applyTySubst IdS τ
    ≡⟨ ≡-sym (wk-weaken ⊆-refl τ) ⟩
  weakenType τ ⊆-refl
    ≡⟨ weakenType-⊆-refl τ ⟩
  τ ∎

ComposeS-IdS₁ : ∀ {Σ₁ Σ₂} (sub : TySubst Σ₁ Σ₂) → ComposeS sub IdS ≡ sub
ComposeS-IdS₁ sub =
  ComposeS sub IdS ≡⟨ mapAll-cong (applyTySubst IdS) id applyTySubst-IdS sub ⟩
  mapAll id sub ≡⟨ mapAll-id sub ⟩
  sub ∎

ComposeS-IdS₂ : ∀ {Σ₁ Σ₂} (sub : TySubst Σ₁ Σ₂) → ComposeS IdS sub ≡ sub
ComposeS-IdS₂ {Σ₁} sub = All-ext lemma
  where lemma : ∀ {x} (p : x ∈ Σ₁) → ∈-All (ComposeS IdS sub) p ≡ ∈-All sub p
        lemma p = ∈-All (ComposeS IdS sub) p
                        ≡⟨ ∈-mapAll (applyTySubst sub) IdS p ⟩
                  applyTySubst sub (∈-All IdS p)
                        ≡⟨ cong (applyTySubst sub) (applyTySubst-IdS (tvar p)) ⟩
                  ∈-All sub p ∎

wk-commutes : ∀ {Σ₁ Σ₂ κ} → (sub : TySubst Σ₁ Σ₂) → ComposeS sub (WeakenS (⊆-skip ⊆-refl)) ≡ ComposeS (WeakenS (⊆-skip ⊆-refl)) (LiftS {κ = κ} sub)
wk-commutes sub =
  ComposeS sub (WeakenS (⊆-skip ⊆-refl)) ≡⟨ map-shift sub ⟩
  mapAll shift sub  ≡⟨ All-ext helper ⟩
  ComposeS (WeakenS (⊆-skip ⊆-refl)) (LiftS sub) ∎
  where helper : ∀ {κ} (x : κ ∈ _ ) → ∈-All (mapAll shift sub) x ≡ ∈-All (ComposeS (WeakenS (⊆-skip ⊆-refl)) (LiftS sub)) x
        helper x = ∈-All (mapAll shift sub) x
                         ≡⟨ refl ⟩
                   ∈-All (LiftS sub) (tl x)
                         ≡⟨ refl ⟩
                   applyTySubst (LiftS sub) (tvar (tl x))
                         ≡⟨ cong (applyTySubst (LiftS sub)) (≡-sym (cong tvar (≡-trans (∈-over-⊆-skip x ⊆-refl) (cong tl (≡-sym (∈-over-refl x)))))) ⟩
                   applyTySubst (LiftS sub) (tvar (∈-over-⊆ (⊆-skip ⊆-refl) x))
                         ≡⟨ cong (applyTySubst (LiftS sub)) (≡-sym (wk-lookupTySubst (⊆-skip ⊆-refl) x)) ⟩
                   applyTySubst (LiftS sub) (∈-All (WeakenS (⊆-skip ⊆-refl)) x)
                         ≡⟨ ≡-sym (∈-ComposeS (WeakenS (⊆-skip ⊆-refl)) (LiftS sub) x) ⟩
                   ∈-All (ComposeS (WeakenS (⊆-skip ⊆-refl)) (LiftS sub)) x ∎

lookup-var-keep : ∀ {A : Set} {Σ₁ : List A} Σ₂ {κ κ′}
                  (x : κ ∈ (Σ₂ ++ Σ₁)) →
                  ∈-over-⊆ (⊆-keep-n Σ₂ (⊆-skip {x = κ′} ⊆-refl)) x ≡
                    lift∈ Σ₂ tl x
lookup-var-keep [] x = lookup-skip-refl x
lookup-var-keep (κ ∷ Σ₂) hd = refl
lookup-var-keep (_ ∷ Σ₂) (tl x) =
  ∈-over-⊆ (⊆-keep (⊆-keep-n Σ₂ (⊆-skip ⊆-refl))) (tl x)
    ≡⟨ ∈-mapAll tl (⊆-keep-n Σ₂ (⊆-skip ⊆-refl)) x ⟩
  tl (∈-over-⊆ (⊆-keep-n Σ₂ (⊆-skip ⊆-refl)) x)
    ≡⟨ cong tl (lookup-var-keep Σ₂ x) ⟩
  tl (lift∈ Σ₂ tl x) ∎

lookupTySubst-LiftS : ∀ {Σ₁ Σ₂ κ′} Σ₃ (sub : TySubst Σ₁ Σ₂) {κ} (x : κ ∈ (Σ₃ ++ Σ₁)) →
                      lookupTySubst (LiftS-n Σ₃ (LiftS {κ = κ′} sub)) (lift∈ Σ₃ tl x) ≡
                      weakenType (lookupTySubst (LiftS-n Σ₃ sub) x) (⊆-keep-n Σ₃ (⊆-skip ⊆-refl))
lookupTySubst-LiftS [] sub x = ∈-mapAll shift sub x
lookupTySubst-LiftS (κ ∷ Σ₃) sub hd = refl
lookupTySubst-LiftS (κ ∷ Σ₃) sub (tl x) =
  lookupTySubst (LiftS (LiftS-n Σ₃ (LiftS sub))) (tl (lift∈ Σ₃ tl x))
      ≡⟨ ∈-mapAll shift (LiftS-n Σ₃ (LiftS sub)) (lift∈ Σ₃ tl x) ⟩
  shift (lookupTySubst (LiftS-n Σ₃ (LiftS sub)) (lift∈ Σ₃ tl x))
      ≡⟨ cong shift (lookupTySubst-LiftS Σ₃ sub x) ⟩
  shift (weakenType (lookupTySubst (LiftS-n Σ₃ sub) x) (⊆-keep-n Σ₃ (⊆-skip ⊆-refl)))
      ≡⟨ weakenType-weakenType (lookupTySubst (LiftS-n Σ₃ sub) x) (⊆-keep-n Σ₃ (⊆-skip ⊆-refl)) (⊆-skip ⊆-refl) ⟩
  weakenType (lookupTySubst (LiftS-n Σ₃ sub) x) (⊆-trans (⊆-keep-n Σ₃ (⊆-skip ⊆-refl)) (⊆-skip ⊆-refl))
      ≡⟨ cong (weakenType (lookupTySubst (LiftS-n Σ₃ sub) x)) (≡-sym (⊆-trans-⊆-skip-⊆-refl (⊆-keep-n Σ₃ (⊆-skip ⊆-refl)))) ⟩
  weakenType (lookupTySubst (LiftS-n Σ₃ sub) x) (⊆-trans (⊆-skip ⊆-refl) (⊆-keep (⊆-keep-n Σ₃ (⊆-skip ⊆-refl))))
      ≡⟨ ≡-sym (weakenType-weakenType (lookupTySubst (LiftS-n Σ₃ sub) x) (⊆-skip ⊆-refl) (⊆-keep (⊆-keep-n Σ₃ (⊆-skip ⊆-refl))))  ⟩
  weakenType (shift (lookupTySubst (LiftS-n Σ₃ sub) x)) (⊆-keep (⊆-keep-n Σ₃ (⊆-skip ⊆-refl)))
      ≡⟨ cong (λ τ → weakenType τ (⊆-keep (⊆-keep-n Σ₃ (⊆-skip ⊆-refl)))) (≡-sym (∈-mapAll shift (LiftS-n Σ₃ sub) x)) ⟩
  weakenType (lookupTySubst (LiftS (LiftS-n Σ₃ sub)) (tl x)) (⊆-keep (⊆-keep-n Σ₃ (⊆-skip ⊆-refl))) ∎

applyTySubst-LiftS-shift : ∀ {Σ₁ Σ₂} Σ₃ {κ′} (sub : TySubst Σ₁ Σ₂) {κ} (τ : Type (Σ₃ ++ Σ₁) κ) →
                           applyTySubst (LiftS-n Σ₃ (LiftS {κ = κ′} sub)) (weakenType τ (⊆-keep-n Σ₃ (⊆-skip ⊆-refl))) ≡
                           weakenType (applyTySubst (LiftS-n Σ₃ sub) τ) (⊆-keep-n Σ₃ (⊆-skip ⊆-refl))
applyTySubst-LiftS-shift Σ₃ sub (tvar x) =
  lookupTySubst (LiftS-n Σ₃ (LiftS sub)) (∈-over-⊆ (⊆-keep-n Σ₃ (⊆-skip ⊆-refl)) x)
      ≡⟨ cong (lookupTySubst (LiftS-n Σ₃ (LiftS sub))) (lookup-var-keep Σ₃ x) ⟩
  lookupTySubst (LiftS-n Σ₃ (LiftS sub)) (lift∈ Σ₃ tl x)
      ≡⟨ lookupTySubst-LiftS Σ₃ sub x ⟩
  weakenType (lookupTySubst (LiftS-n Σ₃ sub) x) (⊆-keep-n Σ₃ (⊆-skip ⊆-refl)) ∎
applyTySubst-LiftS-shift Σ₃ sub (τ $ τ₁) = cong₂ _$_ (applyTySubst-LiftS-shift Σ₃ sub τ) (applyTySubst-LiftS-shift Σ₃ sub τ₁)
applyTySubst-LiftS-shift Σ₃ sub (τ ⇒ τ₁) = cong₂ _⇒_ (applyTySubst-LiftS-shift Σ₃ sub τ) (applyTySubst-LiftS-shift Σ₃ sub τ₁)
applyTySubst-LiftS-shift Σ₃ sub (forAll κ τ) = cong (forAll κ) (applyTySubst-LiftS-shift (κ ∷ Σ₃) sub τ)
applyTySubst-LiftS-shift Σ₃ sub (con x) = refl
applyTySubst-LiftS-shift Σ₃ sub (lit x) = refl

applyTySubst-LiftS-shift′ : ∀ {Σ₁ Σ₂} {κ′} (sub : TySubst Σ₁ Σ₂) {κ} (τ : Type Σ₁ κ) →
                            applyTySubst (LiftS {κ = κ′} sub) (shift τ) ≡
                            shift (applyTySubst sub τ)
applyTySubst-LiftS-shift′ = applyTySubst-LiftS-shift []

ComposeS-Lift : ∀ {Σ₁ Σ₂ Σ₃ κ} (sub₁ : TySubst Σ₁ Σ₂) (sub₂ : TySubst Σ₂ Σ₃) →
                ComposeS (LiftS {κ = κ} sub₁) (LiftS sub₂) ≡
                LiftS (ComposeS sub₁ sub₂)
ComposeS-Lift sub₁ sub₂ = cong₂ _∷_ refl
  (mapAll (applyTySubst (LiftS sub₂)) (ShiftS sub₁)
    ≡⟨ mapAll-mapAll shift (applyTySubst (LiftS sub₂)) sub₁ ⟩
   mapAll (applyTySubst (LiftS sub₂) ∘ shift) sub₁
    ≡⟨ mapAll-cong (applyTySubst (LiftS sub₂) ∘ shift) (shift ∘ applyTySubst sub₂) lemma sub₁ ⟩
   mapAll (shift ∘ applyTySubst sub₂) sub₁
    ≡⟨ ≡-sym (mapAll-mapAll (applyTySubst sub₂) shift sub₁) ⟩
   ShiftS (ComposeS sub₁ sub₂) ∎)
  where lemma : ∀ {κ} (τ : Type _ κ) →
                applyTySubst (LiftS sub₂) (shift τ) ≡ shift (applyTySubst sub₂ τ)
        lemma τ = applyTySubst-LiftS-shift [] sub₂ τ




applyTySubst-applyTySubst :
  ∀ {Σ₁ Σ₂ Σ₃} → (sub₁ : TySubst Σ₁ Σ₂) (sub₂ : TySubst Σ₂ Σ₃) →
  ∀ {κ} (τ : Type Σ₁ κ) →
    applyTySubst sub₂ (applyTySubst sub₁ τ) ≡ applyTySubst (ComposeS sub₁ sub₂) τ
applyTySubst-applyTySubst sub₁ sub₂ (tvar x) = ≡-sym (∈-ComposeS sub₁ sub₂ x)
applyTySubst-applyTySubst sub₁ sub₂ (τ $ τ₁) = cong₂ _$_ (applyTySubst-applyTySubst sub₁ sub₂ τ) (applyTySubst-applyTySubst sub₁ sub₂ τ₁)
applyTySubst-applyTySubst sub₁ sub₂ (τ ⇒ τ₁) = cong₂ _⇒_ (applyTySubst-applyTySubst sub₁ sub₂ τ) (applyTySubst-applyTySubst sub₁ sub₂ τ₁)
applyTySubst-applyTySubst sub₁ sub₂ (forAll κ τ) = cong (forAll κ) (
  applyTySubst (LiftS sub₂) (applyTySubst (LiftS sub₁) τ)
    ≡⟨ applyTySubst-applyTySubst (LiftS sub₁) (LiftS sub₂) τ ⟩
  applyTySubst (ComposeS (LiftS sub₁) (LiftS sub₂)) τ
    ≡⟨ cong (λ ps → applyTySubst ps τ) (ComposeS-Lift sub₁ sub₂) ⟩
  applyTySubst (LiftS (ComposeS sub₁ sub₂)) τ ∎)
applyTySubst-applyTySubst sub₁ sub₂ (con x) = refl
applyTySubst-applyTySubst sub₁ sub₂ (lit x) = refl

sub-weak-commute : ∀ {Σ₁ Σ₂} {κ} → (τ₁ : Type Σ₁ κ) → (p : Σ₁ ⊆ Σ₂) →
                   ComposeS (τ₁ ∷ IdS) (WeakenS p) ≡
                   ComposeS (WeakenS (⊆-keep p)) (weakenType τ₁ p ∷ IdS)
sub-weak-commute {Σ₁} {Σ₂} {κ} τ₁ p = All-ext lemma
  where
    lemma : {κ′ : Kind} (x : κ′ ∈ (κ ∷ Σ₁)) →
            ∈-All (ComposeS (τ₁ ∷ IdS) (WeakenS p)) x ≡
            ∈-All (ComposeS (WeakenS (⊆-keep p)) (weakenType τ₁ p ∷ IdS)) x
    lemma hd = ≡-sym (wk-weaken p τ₁)
    lemma (tl x) = cong (flip ∈-All x) (
      ComposeS IdS (WeakenS p)
        ≡⟨ ComposeS-IdS₂ (WeakenS p) ⟩
      WeakenS p
        ≡⟨ refl ⟩
      mapAll tvar p
        ≡⟨ mapAll-cong tvar (applyTySubst (weakenType τ₁ p ∷ IdS) ∘ tvar ∘ tl) (λ x → ≡-sym (applyTySubst-IdS (tvar x))) p ⟩
      mapAll (applyTySubst (weakenType τ₁ p ∷ IdS) ∘ tvar ∘ tl) p
        ≡⟨ ≡-sym (mapAll-mapAll (tvar ∘ tl) (applyTySubst (weakenType τ₁ p ∷ IdS)) p) ⟩
      ComposeS (mapAll (tvar ∘ tl) p) (weakenType τ₁ p ∷ IdS)
        ≡⟨ cong (flip ComposeS _) (≡-sym (mapAll-mapAll tl tvar p)) ⟩
      ComposeS (WeakenS (⊆-skip p)) (weakenType τ₁ p ∷ IdS) ∎)

weakenType-substTop :
  ∀ {Σ₁ Σ₂} {κ κ′} →
    (τ₁ : Type Σ₁ κ) → (τ₂ : Type (κ ∷ Σ₁) κ′) →
    (p : Σ₁ ⊆ Σ₂) →
    weakenType (substTop τ₁ τ₂) p
    ≡ substTop (weakenType τ₁ p) (weakenType τ₂ (⊆-keep p))
weakenType-substTop τ₁ τ₂ p =
  weakenType (applyTySubst (τ₁ ∷ IdS) τ₂) p
    ≡⟨ wk-weaken p (applyTySubst (τ₁ ∷ IdS) τ₂) ⟩
  applyTySubst (WeakenS p) (applyTySubst (τ₁ ∷ IdS) τ₂)
    ≡⟨ applyTySubst-applyTySubst (τ₁ ∷ IdS) (WeakenS p) τ₂ ⟩
  applyTySubst (ComposeS (τ₁ ∷ IdS) (WeakenS p)) τ₂
    ≡⟨ cong (flip applyTySubst τ₂) (sub-weak-commute τ₁ p) ⟩
  applyTySubst (ComposeS (WeakenS (⊆-keep p)) (weakenType τ₁ p ∷ IdS)) τ₂
    ≡⟨ ≡-sym (applyTySubst-applyTySubst (WeakenS (⊆-keep p)) (weakenType τ₁ p ∷ IdS) τ₂) ⟩
  applyTySubst (weakenType τ₁ p ∷ IdS) (applyTySubst (WeakenS (⊆-keep p)) τ₂)
    ≡⟨ cong (applyTySubst (weakenType τ₁ p ∷ IdS)) (≡-sym (wk-weaken (⊆-keep p) τ₂)) ⟩
  applyTySubst (weakenType τ₁ p ∷ IdS) (weakenType τ₂ (⊆-keep p)) ∎


-- properties of weakenCxt

weakenCxt-applyTySubst :
  ∀ {Σ₁ Σ₂ κ} {adt : ADT κ} {tyArgs : Types Σ₁ (ADT.tyCxt adt)}
    (Γ : Cxt (ADT.tyCxt adt)) → (p : Σ₁ ⊆ Σ₂) →
    weakenCxt (map (applyTySubst tyArgs) Γ) p
    ≡ map (applyTySubst (weakenTypes tyArgs p)) Γ
weakenCxt-applyTySubst [] p = refl
weakenCxt-applyTySubst {adt = adt} {tyArgs} (τ ∷ Γ) p
  rewrite weakenCxt-applyTySubst {adt = adt} {tyArgs} Γ p |
          weakenType-applyTySubst tyArgs τ p = refl

weakenCxt-weakenCxt :
  ∀ {Σ₁ Σ₂ Σ₃} → (Γ : List (Type Σ₁ ∗)) →
    (p : Σ₁ ⊆ Σ₂) → (q : Σ₂ ⊆ Σ₃) →
    weakenCxt (weakenCxt Γ p) q ≡ weakenCxt Γ (⊆-trans p q)
weakenCxt-weakenCxt Γ p q
  rewrite compose-map Γ (flip weakenType p) (flip weakenType q) |
          map-≡ {xs = Γ} _ _ (λ {τ} → weakenType-weakenType τ p q)
          = refl





-- properties of weakenPat

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










-- liftShiftS : ∀ {Σ₁ Σ₂ κ₁ κ₂ κ} → (sub : TySubst Σ₁ Σ₂) (τ : Type (κ₁ ∷ Σ₁) κ) →
--                  applyTySubst (LiftS {κ = κ₁} (ShiftS {κ = κ₂} sub)) τ
--                  ≡ weakenType (applyTySubst (LiftS sub) τ) (⊆-keep (⊆-skip ⊆-refl))
-- liftShiftS {Σ₁} {Σ₂} {κ₁} {κ₂} {κ} sub τ = applyTySubst (LiftS (ShiftS sub)) τ
--                    ≡⟨ cong (flip applyTySubst τ) (All-ext lemma) ⟩
--                    applyTySubst (weakenTypes (LiftS sub) (⊆-keep (⊆-skip ⊆-refl))) τ
--                    ≡⟨ ≡-sym (weakenType-applyTySubst (LiftS sub) τ (⊆-keep (⊆-skip ⊆-refl))) ⟩
--                    weakenType (applyTySubst (LiftS sub) τ) (⊆-keep (⊆-skip ⊆-refl)) ∎
--   where lemma : ∀ {κ′ : Kind} → (x : κ′ ∈ (κ₁ ∷ Σ₁)) → ∈-All (LiftS (ShiftS sub)) x ≡ ∈-All (weakenTypes (LiftS sub) (⊆-keep (⊆-skip ⊆-refl))) x
--         lemma hd = refl
--         lemma (tl x) = {!!}


applyShiftS : ∀ {Σ₁ Σ₂ κ₁ κ₂} → (sub : TySubst Σ₁ Σ₂) (τ : Type Σ₁ κ₁) →
              applyTySubst (ShiftS {κ = κ₂} sub) τ ≡ shift (applyTySubst sub τ)
applyShiftS sub τ = ≡-sym (weakenType-applyTySubst sub τ (⊆-skip ⊆-refl))

weakenType-applyTyArgs :
  ∀ {Σ₁ Σ₂} → (p : Σ₁ ⊆ Σ₂) →
    ∀ {κ} (τ : Type Σ₁ κ) (tyArgs : Types Σ₁ (saturatedTyCxt κ)) →
    weakenType (applyTyArgs τ tyArgs) p
    ≡ applyTyArgs (weakenType τ p) (weakenTypes tyArgs p)
weakenType-applyTyArgs p {∗} τ [] = refl
weakenType-applyTyArgs p {κ₁ ⇒ κ₂} τ tyArgs rewrite lastAll-mapAll (saturatedTyCxt κ₂) (λ τ → weakenType τ p) tyArgs
  with lastAll (satTyCxt (saturate κ₂)) tyArgs
weakenType-applyTyArgs p {κ₁ ⇒ κ₂} τ tyArgs
  | tyArgs′ , tyArg = weakenType-applyTyArgs p (τ $ tyArg) tyArgs′

weakenType-applyTyArgs′ :
  ∀ {Σ₁ Σ₂} {κ} → (adt : ADT κ) → (p : Σ₁ ⊆ Σ₂) →
    (tyArgs : Types Σ₁ (ADT.tyCxt adt)) →
    weakenType (applyTyArgs (con (adtTyCon adt)) tyArgs) p
    ≡ applyTyArgs (con (adtTyCon adt)) (weakenTypes tyArgs p)
weakenType-applyTyArgs′ adt p tyArgs = weakenType-applyTyArgs p (con (adtTyCon adt)) tyArgs

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
    (bs : Branches Σ₁ Γ adt tyArgs τ) →
    Exhaustive bs →
    Exhaustive ((flip weakenBranch p) ∘ bs)


weakenExpr (var i) p = var (weakenVar i p)
weakenExpr (e₁ $ e₂) p = weakenExpr e₁ p $ weakenExpr e₂ p
weakenExpr (_[_] {τ₁ = τ₁} e τ) p
  rewrite weakenType-substTop τ τ₁ p
  = weakenExpr e p [ weakenType τ p ]
weakenExpr (lam τ e) p = lam (weakenType τ p) (weakenExpr e p)
weakenExpr {Σ₁} {Σ₂} {Γ} (Λ κ {τ} e) p
  = let we : Expr (κ ∷ Σ₂) (weakenCxt (weakenCxt Γ (⊆-skip ⊆-refl)) (hd ∷ ⊆-skip p))
                  (weakenType τ (⊆-keep p))
        we = weakenExpr e (⊆-keep p)
        cxts : weakenCxt (weakenCxt Γ (⊆-skip ⊆-refl)) (hd ∷ ⊆-skip p)
               ≡
               weakenCxt (weakenCxt Γ p) (⊆-skip {x = κ} ⊆-refl)
        cxts = eixample Γ p
    in Λ κ (transport (λ cxt → Expr (κ ∷ Σ₂) cxt (weakenType τ (⊆-keep p)))
                      (eixample Γ p) we)

weakenExpr (con dc) p rewrite weakenType-weakenType (dcType dc) [] p = con dc
weakenExpr (lit (flit l)) _ = lit (flit l)
weakenExpr (fvar (fvar m i)) _ = fvar (fvar m i)
weakenExpr (fdict fdict) _ = fdict fdict
weakenExpr {Σ₂ = Σ₂} {Γ} (match {τ₁} adt tyArgs e bs ex) p
  = match adt (weakenTypes tyArgs p)
              (transport (Expr Σ₂ (weakenCxt Γ p))
                         (weakenType-applyTyArgs′ adt p tyArgs)
                         (weakenExpr e p))
              (λ i → weakenBranch (bs i) p)
              (Exhaustive-weakenBranch p adt tyArgs Γ τ₁ bs ex)



weakenBranch {_} {Σ₂} {Γ} {_} {Adt ftc cs} {_} {τ} (alt pat e) p
  = alt (weakenPat pat p)
        (weakenInCxt (weakenExpr e p)
                     (⊆-trans (⊆-weakenCxt-+++ {Γ₁ = patBinders pat} p)
                              (⊆-+++-suffix (⊆-weakenCxt-patBinders pat p))))

branchConstructorIndex-weakenBranch _ _ _ _ _ (alt ̺ _) = refl
branchConstructorIndex-weakenBranch _ _ _ _ _ (alt (lit _) _) = refl
branchConstructorIndex-weakenBranch _ _ _ _ _ (alt (con _) _) = refl

Exhaustive-weakenBranch p adt tyArgs Γ τ bs ex i
  rewrite branchConstructorIndex-weakenBranch p adt tyArgs Γ τ (bs i)
  = ex i
