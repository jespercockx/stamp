module ToCore where

{-# IMPORT Find #-}
{-# IMPORT ToCoreM #-}

open import MyPrelude hiding (_$_; [_])
open import Data.Traversable using (mapM)
open import TypedCore
open import CoreMonad
open import CoreSyn
  renaming (Kind to CKind; Type to CType)
  hiding (Expr)


postulate
  ToCoreM         : Set → Set
  toCoreMReturn   : ∀ {A : Set} → A → ToCoreM A
  toCoreMBind     : ∀ {A B : Set} → ToCoreM A → (A → ToCoreM B) → ToCoreM B
  ModGuts         : Set
  runToCoreM      : ∀ {A : Set} → ModGuts → ToCoreM A → CoreM A
  RdrName         : Set
  qname           : NameSpace → String → String → RdrName
  lookupForeign   : RdrName → ToCoreM (Either Id TyCon)
  lookupForeignId : RdrName → ToCoreM Id
  lookupInstance  : CType → ToCoreM Id
  withFreshTyVar  : ∀ {A : Set} → CKind → (TyVar → ToCoreM A) → ToCoreM A
  withFreshVar    : ∀ {A : Set} → CType → (Id → ToCoreM A) → ToCoreM A
  lookupTyVar     : Int → ToCoreM TyVar
  lookupVar       : Int → ToCoreM Id
  mkAppTy         : CType → CType → CType
  dataConWrapId   : DataCon → Id

{-# COMPILED_TYPE ToCoreM ToCoreM.ToCoreM #-}
{-# COMPILED toCoreMReturn (\_ -> return)  #-}
{-# COMPILED toCoreMBind   (\_ _ -> (>>=)) #-}
{-# COMPILED_TYPE ModGuts GhcPlugins.ModGuts #-}
{-# COMPILED runToCoreM (\_ -> ToCoreM.runToCoreM) #-}
{-# COMPILED_TYPE RdrName GhcPlugins.RdrName #-}
{-# COMPILED qname
    (\ns qual str -> GhcPlugins.mkQual ns
                  (GhcPlugins.mkFastString qual,
                   GhcPlugins.mkFastString str)) #-}
{-# COMPILED lookupForeign ToCoreM.lookupForeign #-}
{-# COMPILED lookupForeignId ToCoreM.lookupForeignId #-}
{-# COMPILED lookupInstance ToCoreM.lookupInstance #-}
{-# COMPILED withFreshTyVar (\_ -> ToCoreM.withFreshTyVar) #-}
{-# COMPILED withFreshVar (\_ -> ToCoreM.withFreshVar) #-}
{-# COMPILED lookupTyVar ToCoreM.lookupTyVar #-}
{-# COMPILED lookupVar ToCoreM.lookupVar #-}
{-# COMPILED mkAppTy GhcPlugins.mkAppTy #-}
{-# COMPILED dataConWrapId GhcPlugins.dataConWrapId #-}


instance
  MonadToCoreM : Monad ToCoreM
  MonadToCoreM = record { return = toCoreMReturn ; _>>=_ = toCoreMBind }

  ApplicativeToCoreM : Applicative ToCoreM
  ApplicativeToCoreM = defaultMonadApplicative

  FunctorToCoreM : Functor ToCoreM
  FunctorToCoreM = defaultMonadFunctor


record ToCore (A : Set) (B : Set) : Set where
  field toCore : A → ToCoreM B
open ToCore {{...}} public

instance
  ToCoreKind : ToCore Kind CKind
  ToCoreKind = record { toCore = return ∘ tr }
    where
      tr : Kind → CKind
      tr ∗         = liftedTypeKind
      tr (κ₁ ⇒ κ₂) = mkArrowKind (tr κ₁) (tr κ₂)

  ToCoreType : ∀ {Σ κ} → ToCore (Type Σ κ) CType
  ToCoreType = record { toCore = tr }
    where
      tr : ∀ {Σ κ} → Type Σ κ → ToCoreM CType
      tr (var k)       = TyVarTy <$> lookupTyVar (fromNat (∈2i k))
      tr (τ₁ $ τ₂)     = mkAppTy <$> tr τ₁ <*> tr τ₂
      tr (τ₁ ⇒ τ₂)     = FunTy <$> tr τ₁ <*> tr τ₂
      tr (forAll κ τ)  = toCore κ >>= λ ck →
                         withFreshTyVar ck λ tv →
                         ForAllTy tv <$> tr τ
      tr (foreign f) with f
      ... | lit l      = pure (LitTy l)
      ... | con c      = pure (TyConApp c []) -- TODO remove this one
      ... | var ns q s = lookupForeign (qname ns q s) >>=
                         pure ∘ either TyVarTy (λ c → TyConApp c [])

  ToCoreExpr : ∀ {Σ Γ τ} → ToCore (Expr Σ Γ τ) CoreExpr
  ToCoreExpr = record { toCore = tr }
    where
      tr : ∀ {Σ Γ τ} → Expr Σ Γ τ → ToCoreM CoreExpr
      tr (var k)   = Var' <$> lookupVar (fromNat (∈2i k))
      tr (e₁ $ e₂) = App <$> tr e₁ <*> tr e₂
      tr (e [ τ ]) = App <$> tr e <*> (Type' <$> toCore τ)
      tr (lam τ e) = toCore τ >>= λ ct →
                     withFreshVar ct λ v →
                     Lam v <$> tr e
      tr (Λ κ e)   = toCore κ >>= λ ck →
                     withFreshTyVar ck λ tv →
                     Lam tv <$> tr e
      tr {τ = τ} (foreign f) with f
      ... | lit l      = pure (Lit l)
      ... | con c      = pure (Var' (dataConWrapId c))
      ... | var ns q s = Var' <$> lookupForeignId (qname ns q s)
      ... | dict       = toCore τ >>= λ ct → Var' <$> lookupInstance ct
