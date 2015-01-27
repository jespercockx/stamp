module Plugin where

{-# IMPORT GhcPlugins #-}

open import Prelude
open import Data.Traversable using (mapM)


open import CoreMonad
open import CoreSyn

postulate
  CommandLineOption : Set

{-# COMPILED_TYPE CommandLineOption String #-}

record Binders core : Set where
  field binders : core → List CoreBndr

open Binders {{...}} public

instance
  BindersCoreBndr : Binders CoreBndr
  BindersCoreBndr = record { binders = [_] }

  BindersList : {c : Set} {{_ : Binders c}} → Binders (List c)
  BindersList = record { binders = concatMap binders }

  BindersTuple : {c₁ c₂ : Set} {{_ : Binders c₁}} {{_ : Binders c₂}} → Binders (Tuple c₁ c₂)
  BindersTuple = record { binders = λ { (tuple c₁ c₂) → binders c₁ ++ binders c₂ } }

  {-# TERMINATING #-}
  BindersCoreExpr : Binders CoreExpr
  BindersCoreBind : Binders CoreBind

  BindersCoreExpr = record { binders = bndrs }
    where
      bndrs : CoreExpr → List CoreBndr
      bndrs (Var b) = [ b ]
      bndrs (Lit _) = []
      bndrs (App e₁ e₂) = bndrs e₁ ++ bndrs e₂
      bndrs (Lam b e) = b ∷ bndrs e
      bndrs (Let binds e) = binders binds ++ bndrs e
      bndrs (Case e b _ alts) = b ∷ bndrs e
      bndrs (Cast e _) = bndrs e
      bndrs (Tick _ e) = bndrs e
      bndrs (Type _) = []
      bndrs (Coercion _) = []

  BindersCoreBind = record { binders = bndrs }
    where
      bndrs : CoreBind → List CoreBndr
      bndrs bind with bind2bind' bind
      ... | NonRec' b e = b ∷ binders e
      ... | Rec' bexprs = binders bexprs

printBinders : CoreProgram → CoreM Unit
printBinders prog = mapM (putMsgS ∘ getOccString) (binders prog) >>
                    return tt

agdaMetaPass : List CommandLineOption → CoreProgram → CoreM CoreProgram
agdaMetaPass options bindings = printBinders bindings >> return bindings
{-# COMPILED_EXPORT agdaMetaPass agdaMetaPass #-}


-- TODO get rid of this
main : IO Unit
main = ioReturn tt
