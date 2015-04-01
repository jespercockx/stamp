module ToCore where

{-# IMPORT Find #-}
{-# IMPORT ToCoreM #-}

open import MyPrelude hiding (_$_; [_])
open import Data.Traversable using (mapM)
open import TypedCore
open import CoreMonad
open import CoreSyn
  renaming (Kind to CKind; Type to CType; TyCon to CTyCon; DataCon to CDataCon)
  hiding (Expr)


postulate
  ToCoreM              : Set → Set
  toCoreMReturn        : ∀ {A : Set} → A → ToCoreM A
  toCoreMBind          : ∀ {A B : Set} → ToCoreM A → (A → ToCoreM B) → ToCoreM B
  ModGuts              : Set
  runToCoreM           : ∀ {A : Set} → ModGuts → ToCoreM A → CoreM A
  RdrName              : Set
  qname                : NameSpace → String → String → RdrName
  lookupForeignId      : RdrName → ToCoreM Id
  lookupForeignTyCon   : RdrName → ToCoreM CTyCon
  lookupForeignDataCon : RdrName → ToCoreM CDataCon
  lookupInstance       : CType → ToCoreM Id
  withFreshTyVar       : ∀ {A : Set} → CKind → (TyVar → ToCoreM A) → ToCoreM A
  withFreshVar         : ∀ {A : Set} → CType → (Id → ToCoreM A) → ToCoreM A
  lookupTyVar          : Int → ToCoreM TyVar
  lookupVar            : Int → ToCoreM Id
  mkAppTy              : CType → CType → CType
  dataConWrapId        : CDataCon → Id
  mkWildValBinder      : CType → Id

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
{-# COMPILED lookupForeignId ToCoreM.lookupForeignId #-}
{-# COMPILED lookupForeignDataCon ToCoreM.lookupForeignDataCon #-}
{-# COMPILED lookupForeignTyCon ToCoreM.lookupForeignTyCon #-}
{-# COMPILED lookupInstance ToCoreM.lookupInstance #-}
{-# COMPILED withFreshTyVar (\_ -> ToCoreM.withFreshTyVar) #-}
{-# COMPILED withFreshVar (\_ -> ToCoreM.withFreshVar) #-}
{-# COMPILED lookupTyVar ToCoreM.lookupTyVar #-}
{-# COMPILED lookupVar ToCoreM.lookupVar #-}
{-# COMPILED mkAppTy GhcPlugins.mkAppTy #-}
{-# COMPILED dataConWrapId GhcPlugins.dataConWrapId #-}
{-# COMPILED mkWildValBinder GhcPlugins.mkWildValBinder #-}

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

  ToCoreForeignTyCon : ToCore ForeignTyCon CTyCon
  ToCoreForeignTyCon = record { toCore = tr }
    where
      tr : ForeignTyCon → ToCoreM CTyCon
      tr (fcon q s) = lookupForeignTyCon (qname tcNameSpace q s)

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
      tr (con c) with c
      ... | con ftc _ _ = TyConApp <$> toCore ftc <*> pure []
      tr (lit l) = pure (LitTy l)

  ToCoreForeignDataCon : ToCore ForeignDataCon CDataCon
  ToCoreForeignDataCon
    = record { toCore = λ { (fcon q s) →
                            lookupForeignDataCon (qname dataNameSpace q s) } }

  ToCorePat : ∀ {Σ τ} → ToCore (Pat Σ τ) AltCon
  ToCorePat = record { toCore = tr }
    where
      tr : ∀ {Σ τ} → Pat Σ τ → ToCoreM AltCon
      tr ̺                    = pure DEFAULT
      tr (lit l)              = pure (LitAlt l)
      tr (con (con dc _ _ _)) = DataAlt <$> toCore dc

  ToCoreExpr : ∀ {Σ Γ τ} → ToCore (Expr Σ Γ τ) CoreExpr
  {-# TERMINATING #-}

  ToCoreBranch : ∀ {Σ Γ τ₁ τ₂} → ToCore (Branch Σ Γ τ₁ τ₂) CoreAlt
  ToCoreBranch = record { toCore = tr }
    where
      tr : ∀ {Σ Γ τ₁ τ₂} → Branch Σ Γ τ₁ τ₂ → ToCoreM CoreAlt
      tr (alt p e) = triple <$> toCore p <*> pure [] <*> toCore e
      -- TODO replace empty list

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
      tr (con c) with c
      ... | con dc _ _ _   = Var' ∘ dataConWrapId <$> toCore dc
      tr (lit (flit l))    = pure (Lit l)
      tr (fvar (fvar q s)) = Var' <$> lookupForeignId (qname varNameSpace q s)
      tr {τ = τ} (fdict fdict) = toCore τ >>= λ ct → Var' <$> lookupInstance ct
      tr {τ = τ} (match sc bs)
        = toCore (exprType sc) >>= λ scCType →
          toCore τ >>= λ resCType →
          Case <$> toCore sc <*>
                   pure (mkWildValBinder scCType) <*>
                   pure resCType <*>
                   mapM toCore bs
