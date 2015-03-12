module MkPick where

open import MyPrelude hiding (_≤_; _<_)
open import TypedCore

infix 4 _≤_ _<_

data _≤_ : Nat → Nat → Set where
  z≤n : ∀ {n}                 → zero  ≤ n
  s≤s : ∀ {m n} (m≤n : m ≤ n) → suc m ≤ suc n

_<_ : Nat → Nat → Set
m < n = suc m ≤ n


_∸_ : Nat → Nat → Nat
n ∸ zero = n
zero ∸ n = zero
(suc n) ∸ (suc m) = n ∸ m

≤-refl : (n : Nat) → n ≤ n
≤-refl zero = z≤n
≤-refl (suc n) = s≤s (≤-refl n)

≤-increase : {m n : Nat} → m ≤ n → m ≤ (suc n)
≤-increase z≤n = z≤n
≤-increase (s≤s p) = s≤s (≤-increase p)

subIsLess : (n m : Nat) → (n ∸ m) ≤ n
subIsLess n       zero    = ≤-refl n
subIsLess zero    (suc m) = ≤-refl zero
subIsLess (suc n) (suc m) = ≤-increase (subIsLess n m)

elemInWeakenCxt : ∀ {Σ₁ Σ₂ Γ } → {τ : Type Σ₁ ∗} → {prf : Σ₁ ⊆ Σ₂} → τ ∈ Γ → (weakenType τ prf) ∈ (weakenCxt Γ prf)
elemInWeakenCxt hd     = hd
elemInWeakenCxt (tl p) = tl (elemInWeakenCxt p)

-- mkTyCxt n maakt een typecontext met n keer het kind *
mkTyCxt : Nat → TyCxt
mkTyCxt zero    = []
mkTyCxt (suc n) = ∗ ∷ (mkTyCxt n)

-- mkTypeVarT m n p maakt een verwijzing naar de m-de typevariabele in de typecontext (mkTyCxt n)
mkTypeVarT : (m n : Nat) → m < n → Type (mkTyCxt n) ∗
mkTypeVarT m       zero    ()
mkTypeVarT zero    (suc n) p       = var hd
mkTypeVarT (suc m) (suc n) (s≤s p) = weakenType (mkTypeVarT m n p) (⊆-skip ⊆-refl)

-- mkTypeFun xs t maakt een type van functies door alle types uit de context xs achter elkaar te plaatsten. (vb. mkTypeFun [a,b,c] t = c ⇒ b ⇒ a ⇒ t)
mkTypeFun : {Σ : TyCxt} → Cxt Σ → Type Σ ∗ → Type Σ ∗
mkTypeFun []      τ = τ
mkTypeFun (x ∷ Γ) τ = mkTypeFun Γ (x ⇒ τ)

-- mkTypeAllT xs t plaatst n keer allT voor het type t (met n = lengte van de typecontext xs). Het resultaat is een type in een lege typecontext.
mkTypeAllT : {Σ : TyCxt} → Type Σ ∗ → Type [] ∗
mkTypeAllT {[]}    τ = τ
mkTypeAllT {x ∷ Σ} τ = mkTypeAllT (forAll x τ)

-- mkCxt n maakt een context van lengte n, bestaande uit verwijzingen naar alle typevariabelen in de typecontext (mkTyCxt n)
mkCxt : (n : Nat) → Cxt (mkTyCxt n)
mkCxt zero    = []
mkCxt (suc n) = var hd ∷ weakenCxt (mkCxt n) (⊆-skip ⊆-refl)

-- mkPickTRev m n p maakt het type van de voorstelling van de functie (pick (n-(m+1)) of n)
mkPickTRev : (m n : Nat) → m < n → Type [] ∗
mkPickTRev m .(suc n) (s≤s {.m} {n} p) = mkTypeAllT (mkTypeFun (mkCxt (suc n)) (mkTypeVarT m (suc n) (s≤s p)))

-- mkPickT m n p maakt het type van de voorstelling van de functie (pick (m+1) of n)
mkPickT : (m n : Nat) → m < n → Type [] ∗
mkPickT m .(suc n) (s≤s {.m} {n} p) = mkPickTRev ((suc n) ∸ (suc m)) (suc n) (s≤s (subIsLess n m))

-- mkΛ {xs} t plaatst n keer lamX ∗ voor de term t (met n = lengte van de typecontext xs). Het resultaat is een term in een lege typecontext en lege context.
mkΛ : {Σ : TyCxt} {τ : Type Σ ∗} → Expr Σ [] τ → Expr [] [] (mkTypeAllT τ)
mkΛ {[]}    t = t
mkΛ {x ∷ Σ} t = mkΛ {Σ} (Λ x t)

-- mkLam {xs} {ys} t plaatst n keer (lam ym) voor de term t (met n = de lengte van de context ys, en ym = het m'de element van de context). Het resultaat is een term in een lege context.
mkLam : {Σ : TyCxt} {Γ : Cxt Σ} {τ : Type Σ ∗} → Expr Σ Γ τ → Expr Σ [] (mkTypeFun Γ τ)
mkLam {Σ} {[]}    t = t
mkLam {Σ} {x ∷ Γ} t = mkLam {Σ} {Γ} (lam x t)

-- mkElemCxt m n p geeft een bewijs dat (mkTypeVarT m n p) in (mkCxt n) zit.
mkElemCxt : (m n : Nat) → (p : m < n) → (mkTypeVarT m n p) ∈ (mkCxt n)
mkElemCxt zero    .(suc n) (s≤s {.zero} {n} p)    = hd
mkElemCxt (suc m) .(suc n) (s≤s {.(suc m)} {n} p) = tl (elemInWeakenCxt (mkElemCxt m n p))

-- mkExprVar m n p geeft een verwijzing naar de m-de variabele in de context (mkCxt n).
mkExprVar : (m n : Nat) → (p : m < n) → Expr (mkTyCxt n) (mkCxt n) (mkTypeVarT m n p)
mkExprVar m n p = var (mkElemCxt m n p)

-- mkPickRev m n p  maakt een voorstelling van de functie (pick (n-(m+1)) of n)
mkPickRev : (m n : Nat) → (p : m < n) → Expr [] [] (mkPickTRev m n p)
mkPickRev m .(suc n) (s≤s {.m} {n} p) = mkΛ (mkLam (mkExprVar m (suc n) (s≤s p)))

-- mkPick m n p maakt een voorstelling van de funcite (pick (m+1) of n)
mkPick : (m n : Nat) → (p : m < n) → Expr [] [] (mkPickT m n p)
mkPick m .(suc n) (s≤s {.m} {n} p) = mkPickRev ((suc n) ∸ (suc m)) (suc n) (s≤s (subIsLess n m))


pick1Of3 : Expr [] [] (forAll ∗ (forAll ∗ (forAll ∗
                                   (var (tl (tl hd)) ⇒ var (tl hd) ⇒ var hd ⇒ var (tl hd)))))
pick1Of3 = mkPick 1 3 (s≤s (s≤s z≤n))
