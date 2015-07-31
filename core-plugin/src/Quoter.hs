{-# LANGUAGE TemplateHaskell #-}
module Quoter where

import Data.Char (isSpace)
import Data.List (dropWhileEnd)

import Language.Haskell.TH (Q, Exp, appE, litE, stringL)
import Language.Haskell.TH.Quote


agdaSplice :: a
agdaSplice = error "Compiler plugin did not run correctly"
{-# NOINLINE agdaSplice #-}

expr :: String -> Q Exp
expr str = appE [| agdaSplice |] (litE (stringL (trim str)))
  where
    trim = dropWhileEnd isSpace . dropWhile isSpace

agda :: QuasiQuoter
agda = QuasiQuoter
       { quoteExp  = expr
       , quotePat  = error "agda quotePat"
       , quoteDec  = error "agda quoteDec"
       , quoteType = error "agda quoteType"
       }
