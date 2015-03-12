{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DeriveFunctor #-}
module ToCoreM where

import Find
import GhcPlugins
import Panic (panic, panicDoc)

import Data.Functor ((<$>))
import Control.Applicative (Applicative)
import Control.Arrow (first, second)

import Control.Monad.Reader (MonadReader, ReaderT, runReaderT, ask)
import Control.Monad.Trans (lift)
import Control.Monad.State (MonadState, StateT, runStateT, gets, modify)

type Env = ([TyVar], [Id])

emptyEnv :: Env
emptyEnv = ([], [])

-- TODO use TcM?
newtype ToCoreM a = ToCoreM (ReaderT ModGuts (StateT Env CoreM) a)
                  deriving (Functor, Applicative, Monad,
                            MonadReader ModGuts, MonadState Env)


liftCore :: CoreM a -> ToCoreM a
liftCore = ToCoreM . lift . lift

runToCoreM :: ModGuts -> ToCoreM a -> CoreM a
runToCoreM modGuts (ToCoreM m)
  = fst <$> runStateT (runReaderT m modGuts) emptyEnv

lookupForeign :: RdrName -> ToCoreM Named
lookupForeign rdr_name = do
  guts <- ask
  liftCore $ putMsg (text "Looking up:" <+> ppr rdr_name)
  liftCore $ findInGuts guts rdr_name

lookupForeignId :: RdrName -> ToCoreM Id
lookupForeignId rdr_name = do
  n <- lookupForeign rdr_name
  case n of
    Left id -> return id
    Right _ -> panicDoc "Found a TyCon instead of an Id:" (ppr rdr_name)

lookupForeignTyCon :: RdrName -> ToCoreM TyCon
lookupForeignTyCon rdr_name = do
  n <- lookupForeign rdr_name
  case n of
    Left _      -> panicDoc "Found an Id instead of a TyCon:" (ppr rdr_name)
    Right tycon -> return tycon

lookupInstance :: Type -> ToCoreM Id
lookupInstance ty
  | Just (cls, args) <- getClassPredTys_maybe ty
  = do guts <- ask
       liftCore $ findInstance guts cls args
  | otherwise = panicDoc "Not a type-class application" (ppr ty)

withFreshTyVar :: Kind -> (TyVar -> ToCoreM a) -> ToCoreM a
withFreshTyVar k cont = do
  uniq <- liftCore $ getUniqueM
  let name = mkSysTvName uniq (fsLit "tyvar")
      tv   = mkTyVar name k
  modify (first (tv :))
  cont tv

withFreshVar :: Type -> (Id -> ToCoreM a) -> ToCoreM a
withFreshVar t cont = do
  v <- liftCore $ mkSysLocalM (fsLit "var") t
  modify (second (v :))
  cont v


safeIndex :: Int -> [a] -> Maybe a
safeIndex _ []     = Nothing
safeIndex 0 (x:_)  = Just x
safeIndex n (_:xs) = safeIndex (pred n) xs

lookupTyVar :: Int -> ToCoreM TyVar
lookupTyVar i = do
  mbTv <- gets (safeIndex i . fst)
  maybe (panic "Index out of bounds") return mbTv

lookupVar :: Int -> ToCoreM Id
lookupVar i = do
  mbVar <- gets (safeIndex i . snd)
  maybe (panic "Index out of bounds") return mbVar
