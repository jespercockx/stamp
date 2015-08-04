{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TupleSections #-}
module Splice
       (
         spliceAgda
       , AgdaCode
       ) where

import           Control.Monad (forM, liftM)
import           Data.Maybe (listToMaybe)

import           Data.Generics.Uniplate.Data
import qualified Data.Text as T
import qualified Data.Text.Encoding as T
import           GhcPlugins

import           ShowCore ()


-- | Try the rewrite at each node before visiting its children.
replaceM :: (Monad m, Uniplate on) => (on -> m on) -> on -> m on
replaceM f x = f x >>= descendM (replaceM f)


class Splicable container spliceElem where
  splice :: Monad m
         => (spliceElem -> m spliceElem)
         -> container -> m container

instance Splicable CoreExpr CoreExpr where
  splice splicer = replaceM f
    where
      -- replaceM takes care that the expressions in Let and Case are also
      -- handled, but we must manually visit the CoreBinds and CoreAlts
      f (Let bind e) = flip Let e `liftM` splice splicer bind
      f (Case e b t alts) = Case e b t `liftM` splice splicer alts
      f e = splicer e

-- AMP will make this much prettier
instance Splicable CoreBind CoreExpr where
  splice splicer (NonRec b e) = NonRec b `liftM` splice splicer e
  splice splicer (Rec bes) =
    Rec `liftM` forM bes (\(b, e) -> (b,) `liftM` splice splicer e)

instance Splicable container CoreExpr
         => Splicable [container] CoreExpr where
  splice splicer = mapM (splice splicer)

instance Splicable CoreAlt CoreExpr where
  splice splicer (ac, bs, e) = (ac, bs,) `liftM` splice splicer e



extractStringArg :: [CoreArg] -> Maybe String
extractStringArg args = listToMaybe args >>= asString
  where
    asString (App (Var _) (Lit (MachStr bs)))
      = Just $ T.unpack $ T.decodeUtf8 bs
    -- The underscore above will be the Id GHC.CString.unpackCString#
    asString _ = Nothing

type AgdaCode = String


spliceAgda :: (AgdaCode -> CoreM CoreExpr) -> CoreProgram -> CoreM CoreProgram
spliceAgda splicer = splice run
  where
    run :: CoreExpr -> CoreM CoreExpr
    run e
      | Just args <- extractArgs e
      = maybe (error "Expected a string as first argument") splicer $
        extractStringArg args
      | otherwise
      = return e

    extractArgs :: CoreExpr -> Maybe [CoreArg]
    extractArgs (Var i) | getOccString i == "agdaSplice" = Just []
    -- Look through type + dict abstractions
    extractArgs (Lam _ e) = extractArgs e
    -- Look through type applications
    extractArgs (App e (Type _)) = extractArgs e
    -- Remember the arguments
    extractArgs (App e arg) = fmap (arg :) (extractArgs e)
    extractArgs _ = Nothing
