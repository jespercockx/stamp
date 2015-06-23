module WeakenExpr where

open import MyPrelude hiding (_$_; [_])
open import TypedCore
open import WeakenInCxt


{-# TERMINATING #-}
weakenExpr : ∀ {Σ₁ Σ₂ Γ} {τ₁ : Type Σ₁ ∗} → Expr Σ₁ Γ τ₁ → (p : Σ₁ ⊆ Σ₂) →
               Expr Σ₂ (weakenCxt Γ p) (weakenType τ₁ p)




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
⊆-weakenCxt-+++ {Γ₁ = Γ₁} {Γ₂} p q rewrite weakenCxt-+++ Γ₁ Γ₂ p = q


weakenType-substTyArg :
  ∀ {Σ₁ Σ₂ Σ₃ κ} → (tyArgs : Types Σ₁ Σ₃) →
    (i : κ ∈ Σ₃) → (p : Σ₁ ⊆ Σ₂) →
    weakenType (substTyArg i tyArgs) p
    ≡ substTyArg i (weakenTypes tyArgs p)
weakenType-substTyArg [] () p
weakenType-substTyArg (tyArg ∷ tyArgs) hd p = refl
weakenType-substTyArg (tyArg ∷ tyArgs) (tl i) p = weakenType-substTyArg tyArgs i p


weakenType-substTyArgs :
  ∀ {Σ₁ Σ₂ Σ₃ κ} → (tyArgs : Types Σ₁ Σ₃) →
    (τ : Type Σ₃ κ) → (p : Σ₁ ⊆ Σ₂) →
    weakenType (substTyArgs tyArgs τ) p
    ≡ substTyArgs (weakenTypes tyArgs p) τ
weakenType-substTyArgs tyArgs (tvar i) p = weakenType-substTyArg tyArgs i p
weakenType-substTyArgs tyArgs (τ₁ $ τ₂) p
  rewrite weakenType-substTyArgs tyArgs τ₁ p |
          weakenType-substTyArgs tyArgs τ₂ p = refl
weakenType-substTyArgs tyArgs (τ₁ ⇒ τ₂) p
  rewrite weakenType-substTyArgs tyArgs τ₁ p |
          weakenType-substTyArgs tyArgs τ₂ p = refl
weakenType-substTyArgs tyArgs (forAll κ τ) p = {!!}
weakenType-substTyArgs tyArgs (con c) p = refl
weakenType-substTyArgs tyArgs (lit l) p = refl


-- (weakenType (substTyArgs (tvar hd ∷ weakenTypes tyArgs tl) τ) (⊆-keep p)
-- ≡ (substTyArgs (tvar hd ∷ weakenTypes (weakenTypes tyArgs p) tl) τ)

weakenCxt-substTyArgs :
  ∀ {Σ₁ Σ₂ κ} {adt : ADT κ} {tyArgs : Types Σ₁ (ADT.tyCxt adt)}
    (Γ : Cxt (ADT.tyCxt adt)) → (p : Σ₁ ⊆ Σ₂) →
    weakenCxt (map (substTyArgs tyArgs) Γ) p
    ≡ map (substTyArgs (weakenTypes tyArgs p)) Γ
weakenCxt-substTyArgs [] p = refl
weakenCxt-substTyArgs {adt = adt} {tyArgs} (τ ∷ Γ) p
  rewrite weakenCxt-substTyArgs {adt = adt} {tyArgs} Γ p |
          weakenType-substTyArgs tyArgs τ p = refl


weakenCxt-patBinders :
  ∀ {Σ₁ Σ₂ κ} {adt : ADT κ} {tyArgs : Types Σ₁ (ADT.tyCxt adt)}
    (pat : Pat Σ₁ adt tyArgs) → (p : Σ₁ ⊆ Σ₂) →
    weakenCxt (patBinders pat) p ≡ patBinders (weakenPat pat p)
weakenCxt-patBinders ̺ p = refl
weakenCxt-patBinders (lit x) p = refl
weakenCxt-patBinders {adt = adt} (con dc) p
  = weakenCxt-substTyArgs {adt = adt} (dataConArgs dc) p


⊆-weakenCxt-patBinders :
  ∀ {Σ₁ Σ₂ κ} {adt : ADT κ} {tyArgs : Types Σ₁ (ADT.tyCxt adt)}
    (pat : Pat Σ₁ adt tyArgs) → (p : Σ₁ ⊆ Σ₂) →
    weakenCxt (patBinders pat) p ⊆ patBinders (weakenPat pat p)
⊆-weakenCxt-patBinders pat p rewrite weakenCxt-patBinders pat p = ⊆-refl


weakenBranch : ∀ {Σ₁ Σ₂ Γ κ} {adt : ADT κ} {tyArgs : Types Σ₁ (ADT.tyCxt adt)}
                 {τ : Type Σ₁ ∗} →
                 Branch Σ₁ Γ adt tyArgs τ → (p : Σ₁ ⊆ Σ₂) →
                 Branch Σ₂ (weakenCxt Γ p) adt (weakenTypes tyArgs p)
                           (weakenType τ p)
weakenBranch {_} {Σ₂} {Γ} {_} {Adt ftc n cs} {_} {τ} (alt pat e) p
  = alt (weakenPat pat p)
        (weakenInCxt (weakenExpr e p)
                     (⊆-trans (⊆-weakenCxt-+++ {Γ₁ = patBinders pat} p)
                              (⊆-+++-suffix (⊆-weakenCxt-patBinders pat p))))


-- (weakenType
--        (substTop (weakenType τ (⊆-skip ⊆-refl)) (weakenType τ′ ⊆-swap))
--        (⊆-keep p))
--       ≡
-- (substTop (weakenType (weakenType τ p) (⊆-skip ⊆-refl))
--           (weakenType (weakenType τ′ (⊆-keep (⊆-keep p))) ⊆-swap))


-- τ = (weakenType τ (⊆-skip ⊆-refl)) / (weakenType τ p)
-- τ′ = (weakenType τ′ ⊆-swap) / (weakenType τ′ (⊆-keep (⊆-keep p)))
-- (weakenType
--        (substTop τ τ′)
--        (⊆-keep p))
--       ≡
-- (substTop (weakenType τ (⊆-skip ⊆-refl))
--           (weakenType τ′ ⊆-swap))



-- ⊆-keep-⊆-keep : ∀ {A : Set} {x : A} → (xs ys zs : List A) →
--                   (p : xs ⊆ ys) → (q : ys ⊆ zs) →
--                   -- (λ {x} x → ⊆-keep q (⊆-keep p x)) ≡
--                   -- ⊆-keep (λ {x} x → q (p x))
--                   ⊆-keep {x = x} (q ∘ p) {x = x} ≡
--                   (⊆-keep {x = x} q) ∘ (⊆-keep {x = x} p)
-- ⊆-keep-⊆-keep xs ys zs p q = {!!}


⊆-keep-⊆-keep :
  ∀ {A : Set} {xs ys zs : List A} → (p : xs ⊆ ys) (q : ys ⊆ zs) →
    (λ {x : A} y → ⊆-keep {x = x} q {x = x} (⊆-keep p y))
    ≡ ⊆-keep (λ y → q (p y))
⊆-keep-⊆-keep p q = {!!}



weakenType-weakenType :
  ∀ {Σ₁ Σ₂ Σ₃} {κ} → (τ : Type Σ₁ κ) →
    (p : Σ₁ ⊆ Σ₂) → (q : Σ₂ ⊆ Σ₃) →
    weakenType (weakenType τ p) q ≡ weakenType τ (q ∘ p)
weakenType-weakenType (tvar x) p q = refl
weakenType-weakenType (τ₁ $ τ₂) p q
  rewrite weakenType-weakenType τ₁ p q |
          weakenType-weakenType τ₂ p q = refl
weakenType-weakenType (τ₁ ⇒ τ₂) p q
  rewrite weakenType-weakenType τ₁ p q |
          weakenType-weakenType τ₂ p q = refl
weakenType-weakenType {Σ₁} {Σ₂} {Σ₃} (forAll κ τ) p q
  rewrite weakenType-weakenType τ (⊆-keep p) (⊆-keep q)
  = {!!}
  -- = cong (forAll κ) (weakenType-eq τ {!⊆-keep {x = κ} {Σ₁} {Σ₃} ? !} {!!} {!!})
        -- | ⊆-keep-⊆-keep p q = {!!}
  -- = cong (forAll κ ∘ weakenType τ) {! !}
weakenType-weakenType (con _) p q = refl
weakenType-weakenType (lit _) p q = refl

-- w (⊆-keep p)
--   (s (w (⊆-skip ⊆-refl) τ)
--      (w ⊆-swap τ′))
-- ≡
-- s (w (⊆-skip ⊆-refl)
--      (w p τ))
--   (w ⊆-swap
--      (w (⊆-keep (⊆-keep p)) τ′))


-- w p
--   (s τ τ′)
-- ≡
-- s (w p τ)
--   (w (⊆-keep p)
--      τ′)



weakenType-substTop :
  ∀ {Σ₁ Σ₂} {κ κ′} →
    (τ : Type Σ₁ κ) → (τ′ : Type (κ ∷ Σ₁) κ′) →
    (p : Σ₁ ⊆ Σ₂) →
    weakenType (substTop τ τ′) p
    ≡ substTop (weakenType τ p) (weakenType τ′ (⊆-keep p))
weakenType-substTop _ (tvar hd) p = refl
weakenType-substTop _ (tvar (tl i)) p = refl
weakenType-substTop τ (τ′₁ $ τ′₂) p
  rewrite weakenType-substTop τ τ′₁ p |
          weakenType-substTop τ τ′₂ p = refl
weakenType-substTop τ (τ′₁ ⇒ τ′₂) p
  rewrite weakenType-substTop τ τ′₁ p |
          weakenType-substTop τ τ′₂ p = refl
weakenType-substTop τ (forAll κ τ′) p
  -- rewrite weakenType-substTop (weakenType τ (⊆-skip ⊆-refl)) (weakenType τ′ ⊆-swap) (⊆-keep p)
  = {!!}
weakenType-substTop _ (con _) p = refl
weakenType-substTop _ (lit _) p = refl



-- TODO CONTINUE probleem met gelijkheid van functies
-- TODO IDEA: introduceer EquivType zoals Jesper en Sophie voor om te gaan met weakenType
-- NEW IDEA: introduceer judgement voor equivalentie van ⊆-proofs

-- CONTINUE MET:
-- (λ {x} → p {x}) ≡ (λ {x} → q {x})
-- OF: alternatieve subset definitie in MyPrelude.agda


subset : ∀ {A : Set} → (xs ys : List A) → Set
subset []       _ = ⊤
subset (x ∷ xs) ys = (x ∈ ys) × (subset xs ys)

⊆-drop : ∀ {A : Set} {x : A} {xs ys : List A} → (x ∷ xs) ⊆ (x ∷ ys) → xs ⊆ ys
⊆-drop p q with p (tl q)
⊆-drop p q | hd = ⊆-drop p q
⊆-drop p q | tl r = r


⊆-subset : ∀ {A : Set} → {xs ys : List A} → xs ⊆ ys → subset xs ys
⊆-subset {xs = []} p = tt
⊆-subset {xs = x ∷ xs} {[]} p = ⊥-elim (⊆-empty-⊥ p)
⊆-subset {xs = x ∷ xs} {y ∷ ys} p with p hd
⊆-subset {xs = x ∷ xs} {.x ∷ ys} p | hd   = hd , (⊆-subset (⊆-skip (⊆-drop p)))
⊆-subset {xs = x ∷ xs} {y ∷ ys}  p | tl q = (tl q) , (⊆-subset (p ∘ tl))

subset-⊆ : ∀ {A : Set} → {xs ys : List A} → subset xs ys → xs ⊆ ys
subset-⊆ {xs = []} s ()
subset-⊆ {xs = x ∷ xs} (p , q) hd = p
subset-⊆ {xs = x ∷ xs} (p , q) (tl r) = subset-⊆ q r


-- barry : ∀ {Σ₁ Σ₂ : TyCxt} → (p : Σ₁ ⊆ Σ₂) →
--           (λ {x : Kind} x → p (⊆-empty x)) ≡ (λ {x} x → ⊆-empty x)
-- barry p = {!!}

-- weakenExpr : ∀ {Σ₁ Σ₂ Γ} {τ₁ : Type Σ₁ ∗} → Expr Σ₁ Γ τ₁ → (p : Σ₁ ⊆ Σ₂) →
--                Expr Σ₂ (weakenCxt Γ p) (weakenType τ₁ p)

weakenExpr (var i) p = var (weakenVar i p)
weakenExpr (e₁ $ e₂) p = weakenExpr e₁ p $ weakenExpr e₂ p
weakenExpr (_[_] {τ₁ = τ₁} e τ) p
  rewrite weakenType-substTop τ τ₁ p = weakenExpr e p [ weakenType τ p ]
weakenExpr (lam τ e) p = lam (weakenType τ p) (weakenExpr e p)
weakenExpr (Λ κ e) p = Λ κ {!!}
weakenExpr (con dc) p
  rewrite weakenType-weakenType (dcType dc) ⊆-empty p
  = {!!}
  -- = let foo : ∀ {x} → p {x} ∘ ⊆-empty ≡ ⊆-empty
  --       foo = {!!}
     -- in transport _ foo (con dc)

weakenExpr (lit (flit l)) _ = lit (flit l)
weakenExpr (fvar (fvar m i)) _ = fvar (fvar m i)
weakenExpr (fdict fdict) _ = fdict fdict
weakenExpr (match adt tyArgs e bs ex) p
  = match adt (weakenTypes tyArgs p) {!!} (map (flip weakenBranch p) bs) {!!}

-- substTop τ τ₂
