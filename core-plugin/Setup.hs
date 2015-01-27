{-# OPTIONS_GHC -Wall -Werror #-}
import Distribution.PackageDescription
import Distribution.Simple
import Distribution.Simple.LocalBuildInfo
import Distribution.Simple.PreProcess
import Distribution.Simple.Program
import System.FilePath (takeDirectory, takeFileName, dropExtension)


main :: IO ()
main = defaultMainWithHooks
       simpleUserHooks { hookedPreProcessors = [("agda", agdaCompiler)]
                       , hookedPrograms = [agdaProgram] }

agdaCompiler :: BuildInfo -> LocalBuildInfo -> PreProcessor
agdaCompiler _bi lbi =
  PreProcessor {
    platformIndependent = True,
    runPreProcessor = mkSimplePreProcessor $ \inFile outFile verbosity ->
    rawSystemProgramConf verbosity agdaProgram (withPrograms lbi)
    ["-c", "--no-main", "--compile-dir=" ++ takeDirectory outFile, "--ghc-flag=-package ghc",
     "-i", "/home/agda/agda-prelude/src", "-i", "src", -- TODO make this configurable
     inFile] >>
    -- Dummy output file
    writeFile outFile ("module " ++ dropExtension (takeFileName inFile) ++ " where\n")
    }


-- Information: https://gist.github.com/23Skidoo/7930870

-- To get cabal to use the Agda to compile *.agda files to *.hs files, we
-- defined the Adga compiler as a preprocessor for the project build (see
-- Setup.hs). We must list `Filename` as an exposed module to get cabal to
-- pick it up as a file to preprocess with Agda. After compiling it with Agda,
-- which generates the file MAlonzo.Code.Filename, cabal still tries to
-- compile the original Filename.hs, so we generate a dummy file with that
-- name.

agdaProgram :: Program
agdaProgram = (simpleProgram "agda") {
  programFindVersion = findProgramVersion "--version" $ \str ->
   case words str of
     (_:_:ver:_) -> ver
     _           -> ""
  }
