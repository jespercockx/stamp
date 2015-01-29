module CoreSyn where

{-# IMPORT GhcPlugins #-}

open import CoreMonad

open import Data.Traversable using (mapM)
open import Prelude

postulate
  Var'          : Set
  OccName       : Set
  Tickish       : Set → Set
  DataCon       : Set -- TODO
  Literal       : Set -- TODO
  Type'         : Set -- TODO
  Coercion'     : Set -- TODO
  getOccString  : Var' -> String

{-# COMPILED_TYPE Var' GhcPlugins.Var #-}
{-# COMPILED_TYPE OccName GhcPlugins.OccName #-}
{-# COMPILED_TYPE Tickish GhcPlugins.Tickish #-}
{-# COMPILED_TYPE DataCon GhcPlugins.DataCon #-}
{-# COMPILED_TYPE Literal GhcPlugins.Literal #-}
{-# COMPILED_TYPE Type' GhcPlugins.Type #-}
{-# COMPILED_TYPE Coercion' GhcPlugins.Coercion #-}
{-# COMPILED getOccString GhcPlugins.getOccString #-}


-- Redefine it here because the COMPILED_DATA pragma must be in the
-- defining module.
data Tuple (A B : Set) : Set where
  tuple : (x : A) (y : B) → Tuple A B
{-# COMPILED_DATA Tuple (,) (,) #-}

-- A Triple instead of _ , _ , _ in order to export it
data Triple (a b c : Set) : Set where
  triple : a → b → c → Triple a b c
{-# COMPILED_DATA Triple (,,) (,,) #-}

CoreBndr : Set
CoreBndr = Var'

Id : Set
Id = Var'

data AltCon : Set where
  DataAlt : DataCon → AltCon
  LitAlt  : Literal → AltCon
  DEFAULT : AltCon
{-# COMPILED_DATA AltCon GhcPlugins.AltCon
    GhcPlugins.DataAlt GhcPlugins.LitAlt GhcPlugins.DEFAULT
  #-}


data Expr b : Set
{-# COMPILED_DECLARE_DATA Expr GhcPlugins.Expr #-}

data Bind b : Set
{-# COMPILED_DECLARE_DATA Bind GhcPlugins.Bind #-}

Arg : Set → Set

Alt : Set → Set

data Expr b where
  Var : Id → Expr b
  Lit : Literal → Expr b
  App : Expr b → Arg b → Expr b
  Lam : b → Expr b → Expr b
  Let : Bind b → Expr b → Expr b
  Case : Expr b → b → Type' → List (Alt b) → Expr b
  Cast : Expr b → Coercion' → Expr b
  Tick : Tickish Id → Expr b → Expr b
  Type : Type' → Expr b
  Coercion : Coercion' → Expr b

Arg b = Expr b

Alt b = Triple AltCon (List b) (Expr b)

{-# COMPILED_DATA Expr GhcPlugins.Expr
  GhcPlugins.Var GhcPlugins.Lit GhcPlugins.App GhcPlugins.Lam
  GhcPlugins.Let GhcPlugins.Case GhcPlugins.Cast GhcPlugins.Tick
  GhcPlugins.Type GhcPlugins.Coercion #-}

data Bind b where
  NonRec : b → Expr b → Bind b
  Rec    : List (Tuple b (Expr b)) → Bind b

{-# COMPILED_DATA Bind GhcPlugins.Bind
    GhcPlugins.NonRec GhcPlugins.Rec #-}


CoreBind : Set
CoreBind = Bind CoreBndr

CoreProgram : Set
CoreProgram = List CoreBind

CoreExpr : Set
CoreExpr = Expr CoreBndr

CoreArg : Set
CoreArg = Arg CoreBndr

CoreAlt : Set
CoreAlt = Alt CoreBndr

module Exists where
  open import Prelude.Product public
  open import Agda.Primitive using (_⊔_)

  ∃ : ∀ {a b} {A : Set a} → (A → Set b) → Set (a ⊔ b)
  ∃ = Σ _

  ∃₂ : ∀ {a b c} {A : Set a} {B : A → Set b}
       (C : (x : A) → B x → Set c) → Set (a ⊔ b ⊔ c)
  ∃₂ C = ∃ λ a → ∃ λ b → C a b

open Exists public

data WeakDec {a} (P : Set a) : Set a where
  yes : P → WeakDec P
  no  : WeakDec P

data Identity (a : Set) : Set where
  identity : a → Identity a

runIdentity : {a : Set} → Identity a → a
runIdentity (identity x) = x

instance
  MonadIdentity : Monad Identity
  MonadIdentity = record { return = identity ; _>>=_ = bindI }
    where
      bindI : {a b : Set} → Identity a → (a → Identity b) → Identity b
      bindI m k = k (runIdentity m)

  ApplicativeIdentity : Applicative Identity
  ApplicativeIdentity = defaultMonadApplicative

  FunctorIdentity : Functor Identity
  FunctorIdentity = defaultMonadFunctor


record Transform (core : Set) : Set₁ where
  field transform : ∀ {P : CoreExpr → Set} {F : Set → Set}
                    {{_ : Applicative F}} →
                    (t : (e : CoreExpr) → WeakDec (P e)) →
                    (f : Σ CoreExpr P → F CoreExpr) →
                    core → F core
open Transform {{...}} public

instance
  TransformList : {c : Set} {{_ : Transform c}} → Transform (List c)
  TransformList = record { transform = λ t f → mapM (transform t f) }

  TransformTuple : {c₁ c₂ : Set} {{_ : Transform c₁}} {{_ : Transform c₂}} →
                   Transform (Tuple c₁ c₂)
  TransformTuple = record { transform = λ { t f (tuple c₁ c₂) →
                                          pure tuple <*> transform t f c₁
                                                     <*> transform t f c₂ } }

  TransformTriple : {c₁ c₂ c₃ : Set} {{_ : Transform c₁}}
                    {{_ : Transform c₂}} {{_ : Transform c₃}} →
                   Transform (Triple c₁ c₂ c₃)
  TransformTriple = record { transform = λ { t f (triple c₁ c₂ c₃) →
                                           pure triple <*> transform t f c₁
                                                       <*> transform t f c₂
                                                       <*> transform t f c₃ } }

  TransformCoreBndr : Transform CoreBndr
  TransformCoreBndr = record { transform = λ _ _ bndr → pure bndr }

  TransformAltCon : Transform AltCon
  TransformAltCon = record { transform = λ _ _ altCon → pure altCon }

  {-# TERMINATING #-}
  TransformBind : Transform CoreBind

  TransformCoreExpr : Transform CoreExpr
  TransformCoreExpr = record { transform = go }
    where
      go : ∀ {P : CoreExpr → Set}  {F : Set → Set}
           {{_ : Applicative F}} →
           (t : (e : CoreExpr) → WeakDec (P e)) →
           (f : Σ CoreExpr P → F CoreExpr) →
           CoreExpr → F CoreExpr
      go t f e with t e
      go t f e | yes p = f (e , p)
      go t f (App e₁ e₂) | no = pure App <*> go t f e₁ <*> go t f e₂
      go t f (Lam b e) | no = pure (Lam b) <*> go t f e
      go t f (Let binds e) | no = pure Let <*> transform t f binds <*> go t f e
      go t f (Case e b ty alts) | no = pure Case <*> go t f e <*> pure b <*> pure ty <*> transform t f alts
      go t f (Cast e c) | no = pure Cast <*> go t f e <*> pure c
      go t f (Tick ti e) | no = pure (Tick ti) <*> go t f e
      go t f e | no = pure e -- Var, Lit, Type, Coercion

  TransformBind = record {
    transform = λ { t f (NonRec b e) → pure (NonRec b) <*> transform t f e
                  ; t f (Rec binds)  → pure Rec <*> transform t f binds } }


removeCasts : CoreProgram → CoreProgram
removeCasts prog = runIdentity $ transform t f prog
  where
    t : (e : CoreExpr) → WeakDec (∃₂ λ e′ c → e ≡ Cast e′ c)
    t (Cast e′ c) = yes (e′ , c , refl)
    t _ = no
    f : Σ CoreExpr (λ e → ∃₂ λ e′ c → e ≡ Cast e′ c) → Identity CoreExpr
    f (.(Cast e′ c) , e′ , c , refl) = return e′

{-# IMPORT Debug.Trace #-}

postulate
  trace         : {a : Set} → String → a → a
  mkCoreConApps : DataCon → List CoreExpr → CoreExpr
  trueDataCon   : DataCon
  falseDataCon  : DataCon
  mkId          : String → Type' → CoreM Id

{-# COMPILED trace (\_ -> Debug.Trace.trace) #-}
{-# COMPILED mkCoreConApps GhcPlugins.mkCoreConApps #-}
{-# COMPILED trueDataCon GhcPlugins.trueDataCon #-}
{-# COMPILED falseDataCon GhcPlugins.falseDataCon #-}
{-# COMPILED mkId (\s -> GhcPlugins.mkSysLocalM (GhcPlugins.fsLit s)) #-}


replaceAgdaWith : (Type' → CoreM CoreExpr) → CoreProgram → CoreM CoreProgram
replaceAgdaWith repl = transform t f
  where
    t : (e : CoreExpr) → WeakDec (∃₂ λ id ty → e ≡ App (Var id) (Type ty) × getOccString id ≡ "agda")
    t (App (Var id) (Type ty)) with getOccString id == "agda"
    t (App (Var id) (Type ty)) | yes p = yes (id , ty , refl , p)
    t (App (Var id) (Type ty)) | no _  = no
    t e = no
    f : Σ CoreExpr (λ e → ∃₂ λ id ty → e ≡ App (Var id) (Type ty) × getOccString id ≡ "agda") → CoreM CoreExpr
    f (.(App (Var id) (Type ty)) , id , ty , refl , _) = trace "REPLACING" (repl ty)

replaceAgdaWithTrue : CoreProgram → CoreM CoreProgram
replaceAgdaWithTrue = replaceAgdaWith repl
  where
    repl : Type' → CoreM CoreExpr
    repl ty = mkId "jos" ty >>= λ id → return $ Lam id (mkCoreConApps falseDataCon [])
-- TODO ty is '(a -> Bool)', convert it to 'a'
