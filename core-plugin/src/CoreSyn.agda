module CoreSyn where

{-# IMPORT GhcPlugins #-}
{-# IMPORT CoreBridge #-}

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

mutual
  data Expr b : Set where
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

  Arg : Set → Set
  Arg b = Expr b

  Alt : Set → Set
  Alt b = Triple AltCon (List b) (Expr b)

  postulate
    Bind   : Set → Set
    NonRec : ∀ {b} → b → Expr b → Bind b
    Rec    : ∀ {b} → List (Tuple b (Expr b)) → Bind b


-- Problem: Expr and Bind are mutually recursively defined.
-- Unfortunately, the COMPILED_DATA pragmas are processed
-- sequentially, not allowing mutual recursion. Thus, when
-- encountering the COMPILED_DATA pragma for Bind, Agda doesn't know
-- how to compile/export the Expr type used in the constructors of
-- Bind, and vice versa.
--
-- This is a known bug:
-- https://code.google.com/p/agda/issues/detail?id=223

  -- data Bind b : Set where
  --   NonRec : b → Expr b → Bind b
  --   Rec    : List (b × Expr b) → Bind b



{-# COMPILED_TYPE Bind GhcPlugins.Bind #-}

{-# COMPILED_DATA Expr GhcPlugins.Expr
    GhcPlugins.Var GhcPlugins.Lit GhcPlugins.App GhcPlugins.Lam
    GhcPlugins.Let GhcPlugins.Case GhcPlugins.Cast GhcPlugins.Tick
    GhcPlugins.Type GhcPlugins.Coercion #-}

{-# COMPILED NonRec (\_ -> GhcPlugins.NonRec) #-}
{-# COMPILED Rec (\_ -> GhcPlugins.Rec) #-}

data Bind' b : Set where
  NonRec' : b → Expr b → Bind' b
  Rec'    : List (Tuple b (Expr b)) → Bind' b

postulate
  elimBind : ∀ {i b} {P : Set i} →
             (nonRec : (bndr : b) → (expr : Expr b) → P)
             (rec : (binds : List (Tuple b (Expr b))) → P)
             (bind : Bind b) → P
-- Non-dependent eliminator, because exporting a dependent one was
-- difficult.

{-# COMPILED elimBind (\_ _ _ -> CoreBridge.elimBind) #-}


bind2bind' : ∀ {b} → Bind b → Bind' b
bind2bind' = elimBind NonRec' Rec'

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
