module CoreSyn where

{-# IMPORT GhcPlugins #-}

open import Prelude.List using (List)
open import Prelude.String using (String)

postulate
  Var'          : Set
  OccName       : Set
  Tickish       : Set → Set
  DataCon       : Set -- TODO
  Literal       : Set -- TODO
  Type'         : Set -- TODO
  Coercion'     : Set -- TODO
  varOccName    : Var' → OccName
  occNameString : OccName → String

{-# COMPILED_TYPE Var' GhcPlugins.Var #-}
{-# COMPILED_TYPE OccName GhcPlugins.OccName #-}
{-# COMPILED_TYPE Tickish GhcPlugins.Tickish #-}
{-# COMPILED_TYPE DataCon GhcPlugins.DataCon #-}
{-# COMPILED_TYPE Literal GhcPlugins.Literal #-}
{-# COMPILED_TYPE Type' GhcPlugins.Type #-}
{-# COMPILED_TYPE Coercion' GhcPlugins.Coercion #-}
{-# COMPILED varOccName GhcPlugins.varOccName #-}
{-# COMPILED occNameString GhcPlugins.occNameString #-}


-- Redefine it here because the COMPILED_DATA pragma must be in the
-- defining module.
infixr 3 _×_
data _×_ (A B : Set) : Set where
  _,_ : (x : A) (y : B) → A × B
{-# COMPILED_DATA _×_ (,) (,) #-}

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

mutual
  data Bind b : Set where
    NonRec : b → Expr b → Bind b
    Rec    : List (b × Expr b) → Bind b

  data Expr b : Set where
    Var : Id → Expr b
    Lit : Literal → Expr b
    App : Expr b → Arg b → Expr b
    Lam : b → Expr b → Expr b
    Let : Bind b → Expr b → Expr b
    Case : Expr b  → b → Type' → List (Alt b) → Expr b
    Cast : Expr b → Coercion' → Expr b
    Tick : Tickish Id → Expr b → Expr b
    Type : Type' → Expr b
    Coercion : Coercion' → Expr b

  Arg : Set → Set
  Arg b = Expr b

  Alt : Set → Set
  Alt b = Triple AltCon (List b) (Expr b)

-- Problem: Expr and Bind are mutually recursively defined.
-- Unfortunately, the COMPILED_DATA pragmas are processed
-- sequentially, not allowing mutual recursion. Thus, when
-- encountering the COMPILED_DATA pragma for Bind, Agda doesn't know
-- how to compile/export the Expr type used in the constructors of
-- Bind, and vice versa.
--
-- This is a known bug:
-- https://code.google.com/p/agda/issues/detail?id=223

{-# COMPILED_DATA Bind GhcPlugins.Bind
    GhcPlugins.NonRec GhcPlugins.Rec #-}
{-# COMPILED_DATA Expr GhcPlugins.Expr
    GhcPlugins.Var GhcPlugins.Lit GhcPlugins.App GhcPlugins.Lam
    GhcPlugins.Let GhcPlugins.Case GhcPlugins.Cast GhcPlugins.Tick
    GhcPlugins.Type GhcPlugins.Coercion #-}


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
