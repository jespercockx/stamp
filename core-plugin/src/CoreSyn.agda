module CoreSyn where

{-# IMPORT GhcPlugins #-}
{-# IMPORT OccName #-}
{-# IMPORT TypeRep #-}
{-# IMPORT TysPrim #-}
{-# IMPORT Data.ByteString #-}

open import CoreMonad

open import Data.Traversable using (mapM)
open import MyPrelude

private
  postulate
    todo  : ∀ {a} {A : Set a} → String → A

postulate
  Var          : Set
  OccName      : Set
  Tickish      : Set → Set
  DataCon      : Set -- TODO
  TyCon        : Set -- TODO
  TyLit        : Set -- TODO
  Coercion     : Set -- TODO
  ByteString   : Set
  Integer      : Set
  Rational     : Set
  FastString   : Set
  getOccString : Var → String

{-# COMPILED_TYPE Var GhcPlugins.Var #-}
{-# COMPILED_TYPE OccName GhcPlugins.OccName #-}
{-# COMPILED_TYPE Tickish GhcPlugins.Tickish #-}
{-# COMPILED_TYPE DataCon GhcPlugins.DataCon #-}
{-# COMPILED_TYPE TyCon GhcPlugins.TyCon #-}
{-# COMPILED_TYPE TyLit TypeRep.TyLit #-}
{-# COMPILED_TYPE Coercion GhcPlugins.Coercion #-}
{-# COMPILED_TYPE ByteString Data.ByteString.ByteString  #-}
{-# COMPILED_TYPE Integer Prelude.Integer #-}
{-# COMPILED_TYPE Rational Prelude.Rational #-}
{-# COMPILED_TYPE FastString GhcPlugins.FastString #-}
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

data Type : Set


TyVar : Set
TyVar = Var

Kind : Set
Kind = Type

KindOrType : Set
KindOrType = Type

data Type where
  TyVarTy  : TyVar → Type
  AppTy    : Type → Type → Type
  TyConApp : TyCon → List KindOrType → Type
  FunTy    : Type → Type → Type
  ForAllTy : Var → Type → Type
  LitTy    : TyLit → Type

{-# COMPILED_DATA Type TypeRep.Type
    TypeRep.TyVarTy TypeRep.AppTy TypeRep.TyConApp
    TypeRep.FunTy TypeRep.ForAllTy TypeRep.LitTy #-}

postulate
  liftedTypeKind : Kind
  mkArrowKind    : Kind → Kind → Kind

{-# COMPILED liftedTypeKind GhcPlugins.liftedTypeKind #-}
{-# COMPILED mkArrowKind TysPrim.mkArrowKind #-}

data FunctionOrData : Set where
  IsFunction : FunctionOrData
  IsData     : FunctionOrData

{-# COMPILED_DATA FunctionOrData GhcPlugins.FunctionOrData
    GhcPlugins.IsFunction GhcPlugins.IsData #-}

data Literal : Set where
  MachChar     : Char → Literal
  MachStr      : ByteString → Literal
  MachNullAddr : Literal
  MachInt      : Integer → Literal
  MachInt64    : Integer → Literal
  MachWord     : Integer → Literal
  MachWord64   : Integer → Literal
  MachFloat    : Rational → Literal
  MachDouble   : Rational → Literal
  MachLabel    : FastString → Maybe Int → FunctionOrData → Literal
  LitInteger   : Integer → Type → Literal

{-# COMPILED_DATA Literal GhcPlugins.Literal
    GhcPlugins.MachChar GhcPlugins.MachStr GhcPlugins.MachNullAddr
    GhcPlugins.MachInt GhcPlugins.MachInt64 GhcPlugins.MachWord
    GhcPlugins.MachWord64 GhcPlugins.MachFloat GhcPlugins.MachDouble
    GhcPlugins.MachLabel GhcPlugins.LitInteger #-}

postulate
  mkMachChar   : Char → Literal
  mkMachString : String → Literal
  mkMachInt    : Integer → Literal -- Normally DynFlags → Integer → Literal


{-# COMPILED mkMachChar GhcPlugins.mkMachChar #-}
{-# COMPILED mkMachString GhcPlugins.mkMachString #-}
{-# COMPILED mkMachInt GhcPlugins.MachInt #-}

CoreBndr : Set
CoreBndr = Var

Id : Set
Id = Var

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
  Var'  : Id → Expr b
  Lit   : Literal → Expr b
  App   : Expr b → Arg b → Expr b
  Lam   : b → Expr b → Expr b
  Let   : Bind b → Expr b → Expr b
  Case  : Expr b → b → Type → List (Alt b) → Expr b
  Cast  : Expr b → Coercion → Expr b
  Tick  : Tickish Id → Expr b → Expr b
  Type' : Type → Expr b
  Coercion' : Coercion → Expr b

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
      go t f e | no = pure e -- Var', Lit, Type', Coercion'

  TransformBind = record {
    transform = λ { t f (NonRec b e) → pure (NonRec b) <*> transform t f e
                  ; t f (Rec binds)  → pure Rec <*> transform t f binds } }


{-# IMPORT Debug.Trace #-}

postulate
  trace         : {a : Set} → String → a → a
  mkCoreConApps : DataCon → List CoreExpr → CoreExpr
  trueDataCon   : DataCon
  falseDataCon  : DataCon
  mkId          : String → Type → CoreM Id
  mkTyVar       : String → Kind → CoreM Var
  isTyVar       : Var → Bool
  funResultTy   : Type → Type
  funArgTy      : Type → Type




{-# COMPILED trace (\_ -> Debug.Trace.trace) #-}
{-# COMPILED mkCoreConApps GhcPlugins.mkCoreConApps #-}
{-# COMPILED trueDataCon GhcPlugins.trueDataCon #-}
{-# COMPILED falseDataCon GhcPlugins.falseDataCon #-}
{-# COMPILED mkId (\s -> GhcPlugins.mkSysLocalM (GhcPlugins.fsLit s)) #-}
{-# COMPILED mkTyVar
             (\s k -> do { uniq <- GhcPlugins.getUniqueM
                         ; let { name = GhcPlugins.mkSysTvName uniq
                                        (GhcPlugins.fsLit s) }
                         ; return (GhcPlugins.mkTyVar name k) }) #-}
{-# COMPILED isTyVar GhcPlugins.isTyVar #-}
{-# COMPILED funResultTy GhcPlugins.funResultTy #-}
{-# COMPILED funArgTy GhcPlugins.funArgTy #-}


postulate
  charTyCon : TyCon
  listTyCon : TyCon
  intTyCon  : TyCon
  unitTyCon : TyCon
  boolTyCon : TyCon

{-# COMPILED charTyCon GhcPlugins.charTyCon #-}
{-# COMPILED listTyCon GhcPlugins.listTyCon #-}
{-# COMPILED intTyCon GhcPlugins.intTyCon #-}
{-# COMPILED unitTyCon GhcPlugins.unitTyCon #-}
{-# COMPILED boolTyCon GhcPlugins.boolTyCon #-}


postulate
  NameSpace        : Set
  tcNameSpace      : NameSpace
  clsNameSpace     : NameSpace
  dataNameSpace    : NameSpace
  srcDataNameSpace : NameSpace
  tvNameSpace      : NameSpace
  varNameSpace     : NameSpace

{-# COMPILED_TYPE NameSpace OccName.NameSpace #-}
{-# COMPILED clsNameSpace OccName.clsName #-}
{-# COMPILED tcNameSpace OccName.tcName #-}
{-# COMPILED dataNameSpace OccName.dataName #-}
{-# COMPILED srcDataNameSpace OccName.srcDataName #-}
{-# COMPILED tvNameSpace OccName.tvName #-}
{-# COMPILED varNameSpace OccName.varName #-}


replaceAgdaWith : (List CoreExpr → CoreM CoreExpr) →
                  CoreProgram → CoreM CoreProgram
replaceAgdaWith repl = transform t f
  where
    t : (e : CoreExpr) → WeakDec (List CoreExpr)
    t (Var' id) with getOccString id == "agda"
    ... | yes p  = yes []
    ... | no _   = no
    -- Look through type applications
    t (App e (Type' _)) = t e
    -- Remember the arguments
    t (App e arg) with t e
    ... | yes args = yes (arg ∷ args)
    ... | no       = no
    t (Lam _ e) = t e -- Look through type + dict abstractions
    t _ = no
    f : CoreExpr × List CoreExpr → CoreM CoreExpr
    f (_ , args) = repl args
