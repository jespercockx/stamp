module Main where

agda :: a
agda = error "Compiler plugin did not run correctly"
{-# NOINLINE agda #-}

main :: IO ()
main = putStrLn ("Hello World: " ++ show (barry 3))

barry :: a -> a
barry = agda
