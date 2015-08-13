{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE NamedFieldPuns #-}
module Plugin
       ( CompilationException
       , plugin
       ) where

import           Control.Exception (Exception, throwIO)
import           Data.Typeable (Typeable)
import           System.Exit (ExitCode(..))
import           System.IO (hPutStrLn, hClose, IOMode(WriteMode), withFile)

import           Data.String.Interpolate (i)
import           GhcPlugins
import           Language.Haskell.Interpreter (setImports, loadModules, interpret)
import           Language.Haskell.Interpreter.Unsafe (unsafeRunInterpreterWithArgs)
import           System.FilePath (dropExtension, replaceExtension, takeFileName, takeDirectory, (</>))
--import           System.IO.Temp (withSystemTempFile, withSystemTempDirectory)
import           System.Process (readProcessWithExitCode)

import           ShowCore (showCore)
import           Splice (AgdaCode, spliceAgda)
import           ToCoreM (ToCoreM, runToCoreM)

-- TODO batch all meta-program calls into one module?


type PassWithGuts = ModGuts -> CoreProgram -> CoreM CoreProgram

data InvocationInfo =
  InvocationInfo
  { pkgDBs :: [PkgConfRef]
    -- ^ Package databases of the current GHC instance.
  , pkgs   :: [PackageId]
    -- ^ Packages laoded by the current GHC instance.
  , agdaIncludeDirs :: [FilePath]
    -- ^ Directories containing Agda code to pass using -i to the Agda
    -- compiler.
  }

getInvocationInfo :: CoreM InvocationInfo
getInvocationInfo = do
  flags <- getDynFlags
  -- TODO why do we need the [] argument here?
  return $ InvocationInfo
    { pkgDBs = extraPkgConfs flags []
    , pkgs = preloadPackages (pkgState flags)
    -- TODO extract the via the [CommandLineOption]
    , agdaIncludeDirs = [
           "/home/thomasw/.cabal-sandboxes/Agda-Core/agda-prelude/src"
         , "/home/thomasw/Dropbox/Core/Agda/stamp/src"
         ]
    }


-- Usually, a monad stack including a ReaderT of InvocationInfo would be used
-- to pass InvocationInfo around, but this becomes unpractical because of all
-- the continuation-passing style functions we're using, i.e.
-- withSystemTempFile, ..., which all take a (_ -> IO _) argument (instead of
-- using MonadIO). Therefore, we pass InvocationInfo around manually.

runMetaProgram :: ModGuts -> AgdaCode -> CoreM CoreExpr
runMetaProgram guts code = do
  info   <- getInvocationInfo
  toCore <- liftIO $ withAgdaFile code $
            flip (withHsFile info) (loadCompiledMetaProgram info)
  runToCoreM guts toCore


withAgdaFile :: AgdaCode -> (FilePath -> IO a) -> IO a
withAgdaFile code f = withSystemTempFile "AgdaSplice.agda" $ \file h -> do
  -- TODO which imports?
  hPutStrLn h [i|
module #{dropExtension (takeFileName file)} where
open import ToCore
open import CoreSyn
open import HelloWorld
open import DeriveEq
metaProg : ToCoreM CoreExpr
metaProg = toCore (#{code})
{-# COMPILED_EXPORT metaProg metaProg #-}
|]
  hClose h
  f file



-- TODO remove this two functions, they're for debugging purposes
withSystemTempFile fileName f = withFile file WriteMode (f file)
  where file = "/tmp" </> fileName

withSystemTempDirectory :: FilePath -> (FilePath -> IO a) -> IO a
withSystemTempDirectory folderName f = f ("/tmp" </> folderName)


withHsFile :: InvocationInfo -> FilePath -> (FilePath -> IO a) -> IO a
withHsFile (InvocationInfo { pkgDBs, agdaIncludeDirs }) agdaFile f
  = withSystemTempDirectory "dist" $ \compileDir -> do
    (code, stdout, stderr)
      <- readProcessWithExitCode "agda" -- This can be overriden using the PATH
         ([ "-c", "--no-main", "--compile-dir=" ++ compileDir
          , "--ghc-flag=-package ghc", "--ghc-flag=-dynamic"
          , "-i", takeDirectory agdaFile, agdaFile ] ++
          concat [ ["-i", dir] | dir <- agdaIncludeDirs ] ++
          [ "--ghc-flag=-package-db=" ++ dbPath
          | PkgConfFile dbPath <- pkgDBs])
         "" -- empty stdin
    case code of
      -- TODO extract this path munging
      ExitSuccess   -> let dir = compileDir </> "MAlonzo" </> "Code"
                           file = replaceExtension (takeFileName agdaFile) ".hs"
                       in f (dir </> file)
      ExitFailure _ -> throwIO (CompilationException stdout stderr)

data CompilationException
  = CompilationException
    { ce_stdout :: String
    , ce_stderr :: String
    } deriving (Typeable)

instance Show CompilationException where
  show ce = "Compilation failed: " ++ ce_stderr ce ++ ce_stdout ce

instance Exception CompilationException

loadCompiledMetaProgram :: InvocationInfo -> FilePath
                        -> IO (ToCoreM CoreExpr)
loadCompiledMetaProgram (InvocationInfo { pkgDBs, pkgs }) hsFile = do
  errMetaProg <- unsafeRunInterpreterWithArgs args $ do
    loadModules [hsFile]
    setImports ["MAlonzo.Code.AgdaSplice", "ToCoreM", "GhcPlugins"]
     -- The undefined below is just a witness for type inference and not
     -- needed because of the top-level type signature
    interpret "metaProg" undefined
  either throwIO return errMetaProg
  where
    args = ("-i" ++ "/tmp/dist/") : -- TODO derive from hsFile
           "-fno-warn-overlapping-patterns" :
           ["-package-db=" ++ dbPath | PkgConfFile dbPath <- pkgDBs] ++
           ["-package " ++ packageIdString pkg | pkg <- pkgs]

-- The steps to splice a meta-program invocation:

-- 1. Agda meta-program invocation as it is mentioned in the splice:
--    `[agda| metaProgCall |]` with type `Expr [] [] τ` for some `τ`.
--
-- 2. Agda meta-program invocation passed to the Agda compiler to compile to
--    Haskell: `toCore metaProgCall` with type `ToCoreM CoreExpr`
--
-- 3. The meta-program invocation that was compiled to Haskell is then
--    executed. Its result is then converted to a value of type `CoreM
--    CoreExpr` with `runToCoreM :: ModGuts -> ToCoreM a -> CoreM a`.
--    The resulting `CoreExpr` is spliced in the Core AST.

agdaMetaPass :: [CommandLineOption] -> ModGuts
             -> CoreProgram -> CoreM CoreProgram
agdaMetaPass _options guts = spliceAgda (runMetaProgram guts)


plugin :: Plugin
plugin = defaultPlugin {
  installCoreToDos = install
}

bindsOnlyPassWithGuts :: PassWithGuts -> ModGuts -> CoreM ModGuts
bindsOnlyPassWithGuts pass guts
  = do { binds' <- pass guts (mg_binds guts)
       ; return (guts { mg_binds = binds' }) }

install :: [CommandLineOption] -> [CoreToDo] -> CoreM [CoreToDo]
install options todo = do
  reinitializeGlobals
  let pass = agdaMetaPass options
  return (CoreDoPluginPass "Show Core" (bindsOnlyPass showCore) :
          CoreDoPluginPass "Agda meta-programming" (bindsOnlyPassWithGuts pass) :
          CoreDoPluginPass "Show Core" (bindsOnlyPass showCore) : todo)
