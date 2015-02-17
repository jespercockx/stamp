{-# LANGUAGE StandaloneDeriving #-}
module ShowCore where

import GhcPlugins
import TypeRep
import CostCentre
import Module
import CoAxiom


showCore :: CoreProgram -> CoreM CoreProgram
showCore prog = putMsgS (show prog) >> return prog

instance Show Var where
  show var
    | isTyVar   var = "(TyVar: "   ++ getOccString var ++ ")"
    | isTcTyVar var = "(TcTyVar: " ++ getOccString var ++ ")"
    | isId      var = "(Id: "      ++ getOccString var ++ ")"

instance Show Name where
  show name = "(Name: " ++ getOccString name ++ ")"

instance Show DataCon where
  show dc = "(DataCon: " ++ show (dataConName dc) ++ ")"

instance Show Module where
  show _ = "(Module: ?)"

instance Show TyCon where
  show _ = "(TyCon: ?)"

instance Show CoAxiomRule where
  show _ = "(CoAxiomRule: ?)"

instance Show (CoAxiom b) where
  show _ = "(CoAxiom: ?)"


deriving instance (Show IsCafCC)
deriving instance (Show LeftOrRight)
deriving instance (Show Role)
deriving instance (Show Branched)
deriving instance (Show FunctionOrData)
deriving instance (Show TyLit)
deriving instance (Show CostCentre)
deriving instance (Show Coercion)
deriving instance (Show Literal)
deriving instance (Show Type)
deriving instance (Show AltCon)
deriving instance (Show b) => Show (Tickish b)
deriving instance (Show b) => Show (Expr b)
deriving instance (Show b) => Show (Bind b)
