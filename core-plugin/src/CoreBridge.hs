-- Module to help bridge the gap between CoreSyn in Haskell and CoreSyn in
-- Agda.
module CoreBridge where

import GhcPlugins (Bind(..), Expr)



elimBind :: (b -> Expr b -> p) -> ([(b, (Expr b))] -> p) -> Bind b -> p
elimBind nonRecP _    (NonRec bndr expr) = nonRecP bndr expr
elimBind _       recP (Rec binds)        = recP binds
