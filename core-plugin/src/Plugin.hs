{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE RecordWildCards #-}
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
import           System.Directory (createDirectoryIfMissing)
import           System.FilePath ((</>))
import qualified System.FilePath as Path

import           System.Process (readProcessWithExitCode)

import           ShowCore (showCore)
import           Splice (AgdaCode, spliceAgda)
import           ToCoreM (ToCoreM, runToCoreM)

-- TODO batch all meta-program calls into one module?


type PassWithGuts = ModGuts -> CoreProgram -> CoreM CoreProgram

data CompilationException
  = CompilationException
    { ce_stdout :: String
    , ce_stderr :: String
    } deriving (Typeable)

instance Show CompilationException where
  show ce = "Compilation failed: " ++ ce_stderr ce ++ ce_stdout ce

instance Exception CompilationException

data InvocationInfo =
  InvocationInfo
  { pkgDBs :: [PkgConfRef]
    -- ^ Package databases of the current GHC instance.
  , pkgs   :: [PackageId]
    -- ^ Packages laoded by the current GHC instance.
  , agdaIncludeDirs :: [FilePath]
    -- ^ Directories containing Agda code to pass using -i to the Agda
    -- compiler.
  , compileDir :: FilePath
    -- ^ The directory to store the .hs files the Agda code was compiled to.
  }

getIncludeDirsFromOptions :: [CommandLineOption] -> [FilePath]
getIncludeDirsFromOptions = id -- This suffices at the moment


getInvocationInfo :: [CommandLineOption] -> CoreM InvocationInfo
getInvocationInfo options = do
  flags <- getDynFlags
  liftIO $ createDirectoryIfMissing True "/tmp/dist" -- TODO
  -- TODO why do we need the [] argument here?
  return $ InvocationInfo
    { pkgDBs = extraPkgConfs flags []
    , pkgs = preloadPackages (pkgState flags)
    , agdaIncludeDirs = getIncludeDirsFromOptions options
    , compileDir = "/tmp/dist" -- TODO somewhere in the project's dist folder?
    }

runMetaProgram :: InvocationInfo -> ModGuts -> AgdaCode -> CoreM CoreExpr
runMetaProgram info@(InvocationInfo { compileDir }) guts code = do
  let agdaFile = compileDir </> "AgdaSplice.agda"
  toCore <- liftIO $ do
    putStrLn "runMetaProgram"
    generateAgdaFile code agdaFile
    hsFile <- compileAgdaFile info agdaFile
    loadCompiledMetaProgram info hsFile
  runToCoreM guts toCore

generateAgdaFile :: AgdaCode -> FilePath -> IO ()
generateAgdaFile code file = withFile file WriteMode $ \h -> do
  -- TODO which imports?
  hPutStrLn h [i|
module AgdaSplice where
open import ToCore
open import CoreSyn
open import HelloWorld
open import DeriveEq
metaProg : ToCoreM CoreExpr
metaProg = toCore (#{code})
{-# COMPILED_EXPORT metaProg metaProg #-}
|]
  hClose h

compileAgdaFile :: InvocationInfo -> FilePath -> IO FilePath
compileAgdaFile (InvocationInfo {..}) agdaFile = do
  (code, stdout, stderr)
      <- readProcessWithExitCode "agda" -- This can be overriden using the PATH
         ([ "-c", "--no-main", "--compile-dir=" ++ compileDir
          , "--ghc-flag=-package ghc", "--ghc-flag=-dynamic"
          , "-i", Path.takeDirectory agdaFile, agdaFile ] ++
          concat [ ["-i", dir] | dir <- agdaIncludeDirs ] ++
          [ "--ghc-flag=-package-db=" ++ dbPath
          | PkgConfFile dbPath <- pkgDBs])
         "" -- empty stdin
  case code of
    ExitSuccess   ->
      let dir = compileDir </> "MAlonzo" </> "Code"
          file = Path.replaceExtension (Path.takeFileName agdaFile) ".hs"
      in return $ dir </> file
    ExitFailure _ -> throwIO (CompilationException stdout stderr)


loadCompiledMetaProgram :: InvocationInfo -> FilePath
                        -> IO (ToCoreM CoreExpr)
loadCompiledMetaProgram (InvocationInfo {..}) hsFile = do
  errMetaProg <- unsafeRunInterpreterWithArgs args $ do
    loadModules [hsFile]
    setImports ["MAlonzo.Code.AgdaSplice", "ToCoreM", "GhcPlugins"]
     -- The undefined below is just a witness for type inference and not
     -- needed because of the top-level type signature
    interpret "metaProg" undefined
  either throwIO return errMetaProg
  where
    args = ("-i" ++ compileDir) : "-fno-warn-overlapping-patterns" :
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
agdaMetaPass options guts prog = do
  liftIO $ putStrLn "agdaMetaPass"
  info <- getInvocationInfo options
  spliceAgda (runMetaProgram info guts) prog


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
  -- Show Core before and after for debugging
  return (CoreDoPluginPass "Show Core" (bindsOnlyPass showCore) :
          CoreDoPluginPass "Agda meta-programming" (bindsOnlyPassWithGuts pass) :
          CoreDoPluginPass "Show Core" (bindsOnlyPass showCore) : todo)
