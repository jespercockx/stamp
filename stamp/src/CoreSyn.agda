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


postulate
  NameSpace        : Set
  tcNameSpace      : NameSpace
  dataNameSpace    : NameSpace
  varNameSpace     : NameSpace

{-# COMPILED_TYPE NameSpace OccName.NameSpace #-}
{-# COMPILED tcNameSpace OccName.tcName #-}
{-# COMPILED dataNameSpace OccName.dataName #-}
{-# COMPILED varNameSpace OccName.varName #-}
