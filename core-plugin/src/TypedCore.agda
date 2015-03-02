module TypedCore where

open import MyPrelude hiding (_$_; [_])
open import UntypedCore
  hiding (module Type; module Expr)
  renaming (Type to UType; Expr to UExpr; TyCon to UTyCon;
            Literal to ULiteral)

Context : Set → Set
Context = List

TyCxt : Set
TyCxt = Context Kind

data TyCon (κ : Kind) : Set where
  tyCon : UTyCon → TyCon κ

unTyCon : ∀ {κ} → TyCon κ → UTyCon
unTyCon (tyCon u) = u

-- TODO remove TyCon?
data ForeignTy (κ : Kind) : Set where
  foreign : NameSpace → String → String → ForeignTy κ


infixr 2 _⇒_

infixl 3 _$_

data Type (Σ : TyCxt) : Kind → Set where
  var     : ∀ {κ} → κ ∈ Σ → Type Σ κ
  con     : ∀ {κ} → TyCon κ → Type Σ κ
  _$_     : ∀ {κ₁ κ₂} → Type Σ (κ₁ ⇒ κ₂) → Type Σ κ₁ → Type Σ κ₂
  _⇒_     : Type Σ ∗ → Type Σ ∗ → Type Σ ∗
  forAll  : ∀ κ → Type (κ ∷ Σ) ∗ → Type Σ ∗
  lit     : TyLit → Type Σ ∗
  foreign : ∀ {κ} → ForeignTy κ → Type Σ κ


Cxt : TyCxt → Set
Cxt Σ = Context (Type Σ ∗)

weakenType : ∀ {Σ₁ Σ₂ κ} → Type Σ₁ κ → Σ₁ ⊆ Σ₂ → Type Σ₂ κ
weakenType (var i)      p = var (∈-over-⊆ p i)
weakenType (con c)      p = con c
weakenType (τ₁ $ τ₂)    p = weakenType τ₁ p $ weakenType τ₂ p
weakenType (τ₁ ⇒ τ₂)    p = weakenType τ₁ p ⇒ weakenType τ₂ p
weakenType (forAll κ τ) p = forAll κ (weakenType τ (⊆-keep p))
weakenType (lit l)      p = lit l
weakenType (foreign f)  p = foreign f

weakenCxt : ∀ {Σ₁ Σ₂} → Cxt Σ₁ → Σ₁ ⊆ Σ₂ → Cxt Σ₂
weakenCxt [] _ = []
weakenCxt (τ :: τs) p = weakenType τ p :: weakenCxt τs p

shift : ∀ {κ κ′ Σ} → Type Σ κ → Type (κ′ ∷ Σ) κ
shift τ = weakenType τ (⊆-skip ⊆-refl)

{-# TERMINATING #-}
substTop : ∀ {Σ κ κ′} → Type Σ κ′ → Type (κ′ ∷ Σ) κ → Type Σ κ
substTop τ (var hd)     = τ
substTop τ (var (tl x)) = var x
substTop τ (con c)      = con c
substTop τ (t₁ $ t₂)    = substTop τ t₁ $ substTop τ t₂
substTop τ (t₁ ⇒ t₂)    = substTop τ t₁ ⇒ substTop τ t₂
substTop τ (forAll κ t) = forAll κ (substTop (weakenType τ (⊆-skip ⊆-refl))
                                             (weakenType t ⊆-swap))
substTop τ (lit l)      = lit l
substTop τ (foreign f)  = foreign f

data Literal (Σ : TyCxt) (τ : Type Σ ∗) : Set where
  lit : ULiteral → Literal Σ τ

unLit : ∀ {Σ} {τ : Type Σ ∗} → Literal Σ τ → ULiteral
unLit (lit u) = u

data ForeignExpr (Σ : TyCxt) (τ : Type Σ ∗) : Set where
  foreign : NameSpace → String → String → ForeignExpr Σ τ

data Expr (Σ : TyCxt) (Γ : Cxt Σ) : Type Σ ∗ → Set where
  var     : ∀ {τ} → τ ∈ Γ → Expr Σ Γ τ
  lit     : ∀ {τ} → Literal Σ τ → Expr Σ Γ τ
  _$_     : ∀ {τ₁ τ₂} → Expr Σ Γ (τ₁ ⇒ τ₂) → Expr Σ Γ τ₁ → Expr Σ Γ τ₂
  _[_]    : ∀ {κ τ₁} → Expr Σ Γ (forAll κ τ₁) → (τ₂ : Type Σ κ) →
            Expr Σ Γ (substTop τ₂ τ₁)
  lam     : ∀ τ₁ {τ₂} → Expr Σ (τ₁ :: Γ) τ₂ → Expr Σ Γ (τ₁ ⇒ τ₂)
  Λ       : ∀ κ {τ} → Expr (κ :: Σ) (weakenCxt Γ (⊆-skip ⊆-refl)) τ →
            Expr Σ Γ (forAll κ τ)
  foreign : ∀ {τ} → ForeignExpr Σ τ → Expr Σ Γ τ


-- ex₁ : ∀ {Σ Γ} → Expr Σ Γ (Int ⇒ Int)
-- ex₁ = lam Int (var hd)

ex₂ : ∀ {Σ Γ} → Expr Σ Γ (forAll ∗ (var hd ⇒ var hd))
ex₂ = Λ ∗ (lam (var hd) (var hd))




pattern ffor ns q s = foreign (foreign ns q s)

eraseτ : ∀ {Σ κ} → Type Σ κ → UType
eraseτ (var k)       = var (∈2i k)
eraseτ (con c)       = con (unTyCon c)
eraseτ (τ₁ $ τ₂)     = eraseτ τ₁ $ eraseτ τ₂
eraseτ (τ₁ ⇒ τ₂)     = eraseτ τ₁ ⇒ eraseτ τ₂
eraseτ (forAll κ τ)  = forAll κ (eraseτ τ)
eraseτ (lit l)       = lit l
eraseτ (ffor ns q s) = foreign ns q s

erase : ∀ {Σ Γ τ} → Expr Σ Γ τ → UExpr
erase (var k)       = var (∈2i k)
erase (lit l)       = lit (unLit l)
erase (e₁ $ e₂)     = erase e₁ $ erase e₂
erase (e [ τ ])     = erase e [ eraseτ τ ]
erase (lam τ e)     = lam (eraseτ τ) (erase e)
erase (Λ κ e)       = Λ κ (erase e)
erase (ffor ns q s) = foreign ns q s

module ToCore where

  {-# IMPORT Find #-}

  open import CoreMonad
  open import CoreSyn
    renaming (Kind to CKind; Type to CType)
    hiding (Expr)

  postulate
    ModGuts       : Set
  {-# COMPILED_TYPE ModGuts GhcPlugins.ModGuts #-}


  DeBruijnEnv : Set
  DeBruijnEnv = List Id

  ToCoreM : Set → Set
  ToCoreM = ReaderT ModGuts (StateT (DeBruijnEnv × DeBruijnEnv) CoreM)

  runToCoreM : ∀ {A : Set} → ModGuts → ToCoreM A → CoreM A
  runToCoreM modGuts m = fst <$> runStateT (runReaderT m modGuts) ([] , [])

  extendΣ : Kind → ToCoreM Var

  extendΓ : ∀ {Σ κ} → Type Σ κ → ToCoreM Var

  postulate
    lookupForeignHs : ModGuts → NameSpace → String → String → CoreM Id
    panic           : ∀ {A : Set} → String → A
    mkAppTy         : CType → CType → CType
  {-# COMPILED lookupForeignHs
      (\guts ns qual s -> Find.findInGuts guts ns qual s) #-}
  {-# COMPILED panic (\_ -> GhcPlugins.panic) #-}
  -- TODO use dependent types to avoid the panic
  {-# COMPILED mkAppTy GhcPlugins.mkAppTy #-}

  lookupForeign : NameSpace → String → String → ToCoreM Id
  lookupForeign ns q s = ask >>= λ guts →
    lift (lift (lookupForeignHs guts ns q s))


  lookupΣ : Nat → ToCoreM Id
  lookupΣ i = lift (gets fst >>= λ Σ →
    maybe (panic "Index out of bounds") return (Σ ! i))

  lookupΓ : Nat → ToCoreM Id
  lookupΓ i = lift (gets snd >>= λ Γ →
    maybe (panic "Index out of bounds") return (Γ ! i))


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

    ToCoreType : ∀ {Σ κ} → ToCore (Type Σ κ) CType
    ToCoreType = record { toCore = tr }
      where
        tr : ∀ {Σ κ} → Type Σ κ → ToCoreM CType
        tr (var k)       = TyVarTy <$> lookupΣ (∈2i k)
        tr (con c)       = pure (TyConApp (unTyCon c) [])
        tr (τ₁ $ τ₂)     = mkAppTy <$> tr τ₁ <*> tr τ₂
        tr (τ₁ ⇒ τ₂)     = FunTy <$> tr τ₁ <*> tr τ₂
        tr (forAll κ τ)  = ForAllTy <$> extendΣ κ <*> tr τ
        tr (lit l)       = pure (LitTy l)
        tr (ffor ns q s) = TyVarTy <$> lookupForeign ns q s

    ToCoreExpr : ∀ {Σ Γ τ} → ToCore (Expr Σ Γ τ) CoreExpr
    ToCoreExpr = record { toCore = tr }
      where
        tr : ∀ {Σ Γ τ} → Expr Σ Γ τ → ToCoreM CoreExpr
        tr (var k)       = Var' <$> lookupΓ (∈2i k)
        tr (lit l)       = pure (Lit (unLit l))
        tr (e₁ $ e₂)     = App <$> tr e₁ <*> tr e₂
        tr (e [ τ ])     = App <$> tr e <*> (Type' <$> toCore τ)
        tr (lam τ e)     = Lam <$> extendΓ τ <*> tr e
        tr (Λ κ e)       = Lam <$> extendΣ κ <*> tr e
        tr (ffor ns q s) = Var' <$> lookupForeign ns q s


  extendΣ κ = toCore κ >>= λ ck →
              lift (lift (mkTyVar "tyvar" ck)) >>= λ id →
              lift (extend id) >>
              return id
    where
      extend : Id → StateT (DeBruijnEnv × DeBruijnEnv) CoreM ⊤
      extend id = modify (λ { (Σ , Γ) → id ∷ Σ , Γ }) >> return tt

  extendΓ τ = toCore τ >>= λ ct →
              lift (lift (mkId "var" ct)) >>= λ id →
              lift (extend id) >>
              return id
    where
      extend : Id → StateT (DeBruijnEnv × DeBruijnEnv) CoreM ⊤
      extend id = modify (λ { (Σ , Γ) → Σ , id ∷ Γ }) >> return tt
