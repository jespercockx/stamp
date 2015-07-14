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
⊆-weakenCxt-+++ {Γ₁ = Γ₁} {Γ₂} p rewrite weakenCxt-+++ Γ₁ Γ₂ p = ⊆-refl


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
weakenType-substTyArgs tyArgs (forAll κ τ) p
  = cong (forAll κ) {!!} -- TODO recursion
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


-- infixr 5 _∷_
-- data Subset {A : Set} : List A → List A → Set where
--   []  : ∀ {ys} → Subset [] ys
--   _∷_ : ∀ {x xs ys} → x ∈ ys → Subset xs ys → Subset (x ∷ xs) ys

-- ⊆-to-Subset : ∀ {A : Set} {xs ys : List A} → xs ⊆ ys → Subset xs ys
-- ⊆-to-Subset {xs = []} tt = []
-- ⊆-to-Subset {xs = x ∷ xs} (p₁ , p₂) = p₁ ∷ (⊆-to-Subset p₂)

-- Subset-to-⊆ : ∀ {A : Set} {xs ys : List A} → Subset xs ys → xs ⊆ ys
-- Subset-to-⊆ {xs = []} p = tt
-- Subset-to-⊆ {xs = x ∷ xs} (p₁ ∷ p₂) = p₁ , Subset-to-⊆ p₂


∈-over-⊆-trans : ∀ {Σ₁ Σ₂ Σ₃ : TyCxt} {κ} → (p : Σ₁ ⊆ Σ₂) → (q : Σ₂ ⊆ Σ₃) →
                   (i : κ ∈ Σ₁) →
                   (∈-over-⊆ q (∈-over-⊆ p i)) ≡ (∈-over-⊆ (⊆-trans p q) i)
∈-over-⊆-trans {[]} {[]} tt tt ()
∈-over-⊆-trans {[]} {_ ∷ Σ₂} tt (q₁ , q₂) ()
∈-over-⊆-trans {_ ∷ _} {[]} (() , p₂) tt i
∈-over-⊆-trans {_ ∷ _} {._ ∷ _} (hd , p₂) (q₁ , q₂) hd = refl
∈-over-⊆-trans {_ ∷ _} {._ ∷ _} (hd , p₂) (q₁ , q₂) (tl i)
  = ∈-over-⊆-trans p₂ (q₁ , q₂) i
∈-over-⊆-trans {_ ∷ _} {_ ∷ _} (tl p₁ , p₂) q i
  = ∈-over-⊆-trans (tl p₁ , p₂) q i


∈-over-⊆-skip : ∀ {Σ₁ Σ₂} {κ₁ κ₂ : Kind} → (p : κ₁ ∈ Σ₁) → (q : Σ₁ ⊆ Σ₂) →
                ∈-over-⊆ (⊆-skip q) p ≡ tl {y = κ₂} (∈-over-⊆ q p)
∈-over-⊆-skip {[]} () _
∈-over-⊆-skip {κ₁ ∷ Σ₁} hd (q₁ , q₂) = refl
∈-over-⊆-skip {_ ∷ Σ₁} (tl p) (q₁ , q₂) = ∈-over-⊆-skip p q₂


⊆-skip-⊆-trans : ∀ {Σ₁ Σ₂ Σ₃ : TyCxt} {κ} → (p : Σ₁ ⊆ Σ₂) → (q : Σ₂ ⊆ Σ₃) →
                   ⊆-trans (⊆-skip  {x = κ} p) (hd , ⊆-skip q)
                   ≡ ⊆-skip (⊆-trans p q)
⊆-skip-⊆-trans {[]} p q = refl
⊆-skip-⊆-trans {x ∷ Σ₁} {[]} (() , _) _
⊆-skip-⊆-trans {x₁ ∷ Σ₁} {.x₁ ∷ Σ₂} (hd , p₂) (q₁ , q₂)
  = cong (λ r → tl q₁ , r) (⊆-skip-⊆-trans p₂ (q₁ , q₂))
⊆-skip-⊆-trans {x ∷ Σ₁} {x₁ ∷ Σ₂} (tl p₁ , p₂) (q₁ , q₂)
  = cong-× (∈-over-⊆-skip p₁ q₂) (⊆-skip-⊆-trans p₂ (q₁ , q₂))

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
weakenType-weakenType {Σ₁} {Σ₂} {Σ₃} (forAll κ τ) p q
  rewrite weakenType-weakenType τ (⊆-keep p) (⊆-keep q)
  = cong (forAll κ ∘ weakenType τ ∘ λ x → (hd , x)) (⊆-skip-⊆-trans p q)
weakenType-weakenType (con _) p q = refl
weakenType-weakenType (lit _) p q = refl

weakenCxt-weakenCxt :
  ∀ {Σ₁ Σ₂ Σ₃} → (Γ : List (Type Σ₁ ∗)) →
    (p : Σ₁ ⊆ Σ₂) → (q : Σ₂ ⊆ Σ₃) →
    weakenCxt (weakenCxt Γ p) q ≡ weakenCxt Γ (⊆-trans p q)
weakenCxt-weakenCxt Γ p q
  rewrite compose-map Γ (flip weakenType p) (flip weakenType q) |
          map-≡ {xs = Γ} _ _ (λ {τ} → weakenType-weakenType τ p q)
          = refl

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

tl-∈-over-⊆ : ∀ {Σ₁ Σ₂ : TyCxt} {κ κ′} → (p : Σ₁ ⊆ Σ₂) → (i : κ′ ∈ Σ₁) →
                ∈-over-⊆ (⊆-skip {x = κ} p) i ≡ tl (∈-over-⊆ p i)
tl-∈-over-⊆ {[]} p ()
tl-∈-over-⊆ {_ ∷ Σ₁} (_ , _) hd = refl
tl-∈-over-⊆ {_ ∷ Σ₁} (p₁ , p₂) (tl i) = tl-∈-over-⊆ p₂ i

weakenType-substTop :
  ∀ {Σ₁ Σ₂} {κ κ′} →
    (τ : Type Σ₁ κ) → (τ′ : Type (κ ∷ Σ₁) κ′) →
    (p : Σ₁ ⊆ Σ₂) →
    weakenType (substTop τ τ′) p
    ≡ substTop (weakenType τ p) (weakenType τ′ (⊆-keep p))
weakenType-substTop _ (tvar hd) p = refl
weakenType-substTop {κ = κ} τ (tvar (tl i)) p rewrite tl-∈-over-⊆ {κ = κ} p i = refl
weakenType-substTop τ (τ′₁ $ τ′₂) p
  rewrite weakenType-substTop τ τ′₁ p |
          weakenType-substTop τ τ′₂ p = refl
weakenType-substTop τ (τ′₁ ⇒ τ′₂) p
  rewrite weakenType-substTop τ τ′₁ p |
          weakenType-substTop τ τ′₂ p = refl
weakenType-substTop {κ = κ} τ (forAll κ₁ τ′) p
  -- rewrite weakenType-substTop (weakenType τ (⊆-skip ⊆-refl)) (weakenType τ′ ⊆-swap) (⊆-keep p)
  rewrite weakenType-weakenType τ p (⊆-skip {x = κ₁} ⊆-refl) |
          weakenType-weakenType τ′ (⊆-keep (⊆-keep p)) ⊆-swap
  = cong (forAll κ₁) {!!} -- (weakenType-substTop (weakenType τ {!!}) {!weakenType τ′ ⊆-swap!} {!!})
weakenType-substTop _ (con _) p = refl
weakenType-substTop _ (lit _) p = refl


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



-- CONTINUE MET:
-- (λ {x} → p {x}) ≡ (λ {x} → q {x})
-- OF: alternatieve subset definitie in MyPrelude.agda


-- subset : ∀ {A : Set} → (xs ys : List A) → Set
-- subset []       _ = ⊤
-- subset (x ∷ xs) ys = (x ∈ ys) × (subset xs ys)

-- ⊆-drop : ∀ {A : Set} {x : A} {xs ys : List A} → (x ∷ xs) ⊆ (x ∷ ys) → xs ⊆ ys
-- ⊆-drop p q with p (tl q)
-- ⊆-drop p q | hd = ⊆-drop p q
-- ⊆-drop p q | tl r = r


-- ⊆-subset : ∀ {A : Set} → {xs ys : List A} → xs ⊆ ys → subset xs ys
-- ⊆-subset {xs = []} p = tt
-- ⊆-subset {xs = x ∷ xs} {[]} p = ⊥-elim (⊆-empty-⊥ p)
-- ⊆-subset {xs = x ∷ xs} {y ∷ ys} p with p hd
-- ⊆-subset {xs = x ∷ xs} {.x ∷ ys} p | hd   = hd , (⊆-subset (⊆-skip (⊆-drop p)))
-- ⊆-subset {xs = x ∷ xs} {y ∷ ys}  p | tl q = (tl q) , (⊆-subset (p ∘ tl))

-- subset-⊆ : ∀ {A : Set} → {xs ys : List A} → subset xs ys → xs ⊆ ys
-- subset-⊆ {xs = []} s ()
-- subset-⊆ {xs = x ∷ xs} (p , q) hd = p
-- subset-⊆ {xs = x ∷ xs} (p , q) (tl r) = subset-⊆ q r

weakenType-applyTyArgs :
  ∀ {Σ₁ Σ₂} {κ} → (adt : ADT κ) → (p : Σ₁ ⊆ Σ₂) →
    (tyArgs : Types Σ₁ (ADT.tyCxt adt)) →
    weakenType (applyTyArgs (con (adtTyCon adt)) tyArgs) p
    ≡ applyTyArgs (con (adtTyCon adt)) (weakenTypes tyArgs p)
weakenType-applyTyArgs {κ = ∗} adt p [] = refl
weakenType-applyTyArgs {Σ₁} {Σ₂} {κ ⇒ κ₁} adt p tyArgs = {!!}



branchConstructorIndex-weakenBranch :
  ∀ {Σ₁ Σ₂} {κ} →
    (p : Σ₁ ⊆ Σ₂) →
    (adt : ADT κ) →
    (tyArgs : Types Σ₁ (ADT.tyCxt adt)) →
    (Γ : List (Type Σ₁ ∗)) →
    (τ : Type Σ₁ ∗) →
    (b : Branch Σ₁ Γ adt tyArgs τ) →
    branchConstructorIndex (weakenBranch b p) ≡ branchConstructorIndex b
branchConstructorIndex-weakenBranch _ _ _ _ _ (alt ̺ _) = refl
branchConstructorIndex-weakenBranch _ _ _ _ _ (alt (lit _) _) = refl
branchConstructorIndex-weakenBranch _ _ _ _ _ (alt (con _) _) = refl



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
Exhaustive-weakenBranch p adt tyArgs Γ τ bs ex
  rewrite compose-map bs (flip weakenBranch p) branchConstructorIndex |
          map-≡ {xs = bs} _ _
                (λ {b} → branchConstructorIndex-weakenBranch p adt tyArgs Γ τ b)
          = ex

-- weakenExpr : ∀ {Σ₁ Σ₂ Γ} {τ₁ : Type Σ₁ ∗} → Expr Σ₁ Γ τ₁ → (p : Σ₁ ⊆ Σ₂) →
--                Expr Σ₂ (weakenCxt Γ p) (weakenType τ₁ p)



tl-++ : ∀ {κ′} {Σ₂} → (Σ₁ : TyCxt) → κ′ ∈ Σ₂ → κ′ ∈ (Σ₁ ++ Σ₂)
tl-++ [] p = p
tl-++ (κ ∷ Σ₁) p = tl (tl-++ Σ₁ p)

⊆-skip-++ : ∀ {Σ₁ Σ₃} → (Σ₂ : TyCxt) → Σ₁ ⊆ Σ₃ → Σ₁ ⊆ (Σ₂ ++ Σ₃)
⊆-skip-++ {[]} Σ₂ p = tt
⊆-skip-++ {x ∷ Σ₁} Σ₂ (p₁ , p₂) = (tl-++ Σ₂ p₁) , ⊆-skip-++ Σ₂ p₂
-- ⊆-skip-++ [] p = p
-- ⊆-skip-++ (κ ∷ Σ₂) p = ⊆-skip (⊆-skip-++ Σ₂ p)
-- κ ∈ (Σ₂ ++ Σ₁)

-- helper : ∀ {Σ₁ Σ₂ Σ x} → (sub : Σ₁ ⊆ Σ₂) → (p : x ∈ Σ₁) → ∈-over-⊆ (⊆-skip-++ Σ sub) p ≡ tl (∈-over-⊆ sub p)
-- helper = ?

tl-⊆-skip : ∀ {Σ₁ : TyCxt} {κ} → (Σ₂ : TyCxt) → (p : κ ∈ Σ₁) →
              tl-++ Σ₂ p ≡ ∈-over-⊆ (⊆-skip-++ Σ₂ ⊆-refl) p
-- tl-⊆-skip {[]} [] ()
-- tl-⊆-skip {κ ∷ Σ₁} [] hd = refl
-- tl-⊆-skip {y ∷ Σ₁} [] p = {!!}
-- tl-⊆-skip (x ∷ Σ₂) p = {!!}
tl-⊆-skip [] hd = refl
tl-⊆-skip [] (tl p) = tl-⊆-skip [] (tl p)
tl-⊆-skip {[]} (κ₁ ∷ Σ₂) ()
tl-⊆-skip {κ₁ ∷ Σ₁} (κ₂ ∷ Σ₂) hd = {! !}
tl-⊆-skip {κ₁ ∷ Σ₁} (κ₂ ∷ Σ₂) (tl p) = {!!}

-- tl-⊆-skip {Σ₁} Σ₂ p with ⊆-skip-++ {Σ₁ = Σ₁} Σ₂ ⊆-refl
-- ... | q = {!!}

-- tl-⊆-skip [] hd = refl
-- tl-⊆-skip [] (tl p) = tl-⊆-skip [] (tl p)
-- tl-⊆-skip (κ₁ ∷ Σ₂) p rewrite tl-⊆-skip Σ₂ p = {!!}

kastrol : ∀ {Σ₁ Σ₂ : TyCxt} {κ} → (p : Σ₁ ⊆ Σ₂) →
            ⊆-trans (⊆-skip {x = κ} ⊆-refl) (hd , ⊆-skip p)
            ≡ ⊆-trans p (⊆-skip ⊆-refl)
kastrol p = {!!}
-- kastrol {[]} {[]} tt = refl
-- kastrol {[]} {_ ∷ _} tt = refl
-- kastrol {x ∷ Σ₁} {[]} (() , _)
-- kastrol {y ∷ Σ₁} {.y ∷ Σ₂} (hd , p₂) = cong-× refl {!!}
-- kastrol {x ∷ Σ₁} {y ∷ Σ₂} (tl p₁ , p₂) = cong-× (tl-⊆-skip [] (tl (tl p₁))) {!!}


eixample : ∀ {Σ₁ Σ₂} {κ} → (Γ : List (Type Σ₁ ∗)) →
             (p : Σ₁ ⊆ Σ₂) →
             weakenCxt (weakenCxt Γ (⊆-skip ⊆-refl)) (hd , ⊆-skip p)
             ≡
             weakenCxt (weakenCxt Γ p) (⊆-skip {x = κ} ⊆-refl)
eixample {κ = κ} Γ p
  rewrite weakenCxt-weakenCxt Γ (⊆-skip {x = κ} ⊆-refl) (hd , ⊆-skip p) |
          weakenCxt-weakenCxt Γ p (⊆-skip {x = κ} ⊆-refl) |
          kastrol {κ = κ} p
  = refl



weakenExpr (var i) p = var (weakenVar i p)
weakenExpr (e₁ $ e₂) p = weakenExpr e₁ p $ weakenExpr e₂ p
weakenExpr (_[_] {τ₁ = τ₁} e τ) p
  rewrite weakenType-substTop τ τ₁ p = weakenExpr e p [ weakenType τ p ]
weakenExpr (lam τ e) p = lam (weakenType τ p) (weakenExpr e p)
weakenExpr {Σ₁} {Σ₂} {Γ} (Λ κ {τ} e) p
  = let we : Expr (κ ∷ Σ₂) (weakenCxt (weakenCxt Γ (⊆-skip ⊆-refl)) (hd , ⊆-skip p))
                  (weakenType τ (⊆-keep p))
        we = weakenExpr e (hd , ⊆-skip p)
        cxts : weakenCxt (weakenCxt Γ (⊆-skip ⊆-refl)) (hd , ⊆-skip p)
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

weakenExpr (con dc) p rewrite weakenType-weakenType (dcType dc) tt p = con dc
weakenExpr (lit (flit l)) _ = lit (flit l)
weakenExpr (fvar (fvar m i)) _ = fvar (fvar m i)
weakenExpr (fdict fdict) _ = fdict fdict
weakenExpr {Σ₂ = Σ₂} {Γ} (match {τ₁} adt tyArgs e bs ex) p
  = match adt (weakenTypes tyArgs p)
              (transport (Expr Σ₂ (weakenCxt Γ p))
                         (weakenType-applyTyArgs adt p tyArgs)
                         (weakenExpr e p))
              (map (flip weakenBranch p) bs)
              (Exhaustive-weakenBranch p adt tyArgs Γ τ₁ bs ex)
