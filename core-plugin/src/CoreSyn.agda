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
