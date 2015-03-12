module Find (Named, findInGuts, findInstance) where

import Control.Monad (liftM)
import Data.List (intercalate)
import Data.Functor ((<$>))

import Class (Class)
import ConLike (ConLike(..))
import Finder (findImportedModule, cannotFindModule)
import GhcPlugins
import InstEnv (instanceDFunId)
import LoadIface (loadSysInterface)
import Panic (throwGhcExceptionIO, GhcException(..))
import TcEnv (tcLookupInstance)
import TcRnMonad (initIfaceTcRn)
import TyCon (TyCon)

import Typechecker


type Named = Either Id TyCon



findInstance :: ModGuts -> Class -> [Type] -> CoreM DFunId
findInstance guts cls args = do
  hsc_env <- getHscEnv
  putMsg (text "Finding instance for:" <+> ppr cls <+> ppr args)
  (_, mb_clsInst) <- liftIO $ initTcFromModGuts hsc_env guts HsSrcFile False $
                     tcLookupInstance cls args
  putMsgS "DONE"
  return $ maybe (panic "No instance found") instanceDFunId mb_clsInst

-- Copied from HERMIT
findInGuts :: ModGuts -> RdrName -> CoreM Named
findInGuts guts rdr_name = putMsgS "findInGuts" >> do
  let rdr_env  = mg_rdr_env guts
  case lookupGRE_RdrName rdr_name rdr_env of
        [gre] -> lookupNamed (gre_name gre)
        []    -> findInPackageDB guts rdr_name
        _     -> fail "findInGuts: multiple names returned"

findInPackageDB :: ModGuts -> RdrName -> CoreM Named
findInPackageDB guts rdr_name = putMsgS "findInPackageDB" >> do
  mnm <- lookupName guts rdr_name
  case mnm of
    Nothing -> findNamedBuiltIn rdr_name
    Just n  -> lookupNamed n

lookupNamed :: Name -> CoreM Named
lookupNamed n = do
  tything <- lookupThing n
  case tything of
    AnId id                   -> return $ Left id
    ATyCon tc                 -> return $ Right tc
    AConLike (RealDataCon dc) -> return $ Left $ dataConWrapId dc
    _                         -> fail "Wrong kind of TyThing"

-- | Helper to call lookupRdrNameInModule
lookupName :: ModGuts -> RdrName -> CoreM (Maybe Name)
lookupName guts rdr_name = putMsgS "lookupName" >> case isQual_maybe rdr_name of
  Nothing     -> return Nothing -- we can't use lookupName on the current module
  Just (m, _) -> do
    hsc_env <- getHscEnv
    putMsgS "lookupRdrNameInModule"
    liftIO $ lookupRdrNameInModule hsc_env guts m rdr_name

findNamedBuiltIn :: RdrName -> CoreM Named
findNamedBuiltIn rdr_name
  | isValNameSpace (rdrNameSpace rdr_name)
  = case [ dc | tc <- wiredInTyCons, dc <- tyConDataCons tc
              , cmpRdrName2Name rdr_name (getName dc) ] of
      []   -> fail "name not in scope."
      [dc] -> return $ Left $ dataConWrapId dc
      dcs  -> fail $ "multiple DataCons match: " ++
              intercalate ", " (map unqualifiedName dcs)
  | isTcClsNameSpace (rdrNameSpace rdr_name)
  = putMsgS "AQUI" >> case [ tc | tc <- wiredInTyCons
              , cmpRdrName2Name rdr_name (getName tc) ] of
      []   -> fail "type name not in scope."
      [tc] -> return $ Right tc
      tcs  -> fail $ "multiple TyCons match: " ++
              intercalate ", " (map unqualifiedName tcs)
  | otherwise
  = fail "findNameBuiltIn: unusable NameSpace"

-- | Get the unqualified name from a 'NamedThing'.
unqualifiedName :: NamedThing nm => nm -> String
unqualifiedName = getOccString

cmpRdrName2Name :: RdrName -> Name -> Bool
cmpRdrName2Name rdr_name name
  | Just (m', _) <- isQual_maybe rdr_name
  , Just m <- nameModule_maybe name = (m' == moduleName m) && sameOccName
  | otherwise = sameOccName
  where sameOccName = occName rdr_name == occName name


-- | Finds the 'Name' corresponding to the given 'RdrName' in the context of the 'ModuleName'. Returns @Nothing@ if no
-- such 'Name' could be found. Any other condition results in an exception:
--
-- * If the module could not be found
-- * If we could not determine the imports of the module
--
-- This is adapted from GHC's function called lookupRdrNameInModuleForPlugins,
-- but using initTcFromModGuts instead of initTcInteractive. Also, we ImportBySystem
-- instead of ImportByPlugin, so the EPS gets populated with RULES and instances from
-- the loaded module.
--
-- TODO: consider importing by plugin first, then only importing by system when a name
-- is successfully found... as written we will load RULES/instances if the module loads
-- successfully, even if the name is not found.
lookupRdrNameInModule :: HscEnv -> ModGuts -> ModuleName -> RdrName -> IO (Maybe Name)
lookupRdrNameInModule hsc_env guts mod_name rdr_name = do
    -- First find the package the module resides in by searching exposed packages and home modules
    found_module <- findImportedModule hsc_env mod_name Nothing
    case found_module of
        Found _ mod -> do
            -- Find the exports of the module
            (_, mb_iface) <- initTcFromModGuts hsc_env guts HsSrcFile False $
                             initIfaceTcRn $
                             loadSysInterface doc mod
            case mb_iface of
                Just iface -> do
                    -- Try and find the required name in the exports
                    let decl_spec = ImpDeclSpec { is_mod = mod_name, is_as = mod_name
                                                , is_qual = False, is_dloc = noSrcSpan }
                        provenance = Imported [ImpSpec decl_spec ImpAll]
                        env = mkGlobalRdrEnv (gresFromAvails provenance (mi_exports iface))
                    case lookupGRE_RdrName rdr_name env of
                        [gre] -> return (Just (gre_name gre))
                        []    -> return Nothing
                        _     -> panic "lookupRdrNameInModule"

                Nothing -> throwCmdLineErrorS dflags $ hsep [ptext (sLit "Could not determine the exports of the module"), ppr mod_name]
        err -> throwCmdLineErrorS dflags $ cannotFindModule dflags mod_name err
  where
    dflags = hsc_dflags hsc_env
    doc = ptext (sLit "contains a name used in an invocation of lookupRdrNameInModule")

-- | Also copied from GHC because it is not exposed.
throwCmdLineErrorS :: DynFlags -> SDoc -> IO a
throwCmdLineErrorS dflags = throwCmdLineError . showSDoc dflags

throwCmdLineError :: String -> IO a
throwCmdLineError = throwGhcExceptionIO . CmdLineError
