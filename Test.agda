module Test where

{-# IMPORT Haskell #-}

open import Prelude.Equality
open import Prelude.Bool
open import Prelude.IO
open import Prelude.Unit

postulate barry : Bool

{-# COMPILED barry Haskell.barry #-}

foo : Bool
foo = barry

main : IO ⊤
main = if foo then putStrLn "Yes" else putStrLn "No"
