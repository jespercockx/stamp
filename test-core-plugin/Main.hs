module Main where

agda :: a
agda = undefined
{-# NOINLINE agda #-}

main :: IO ()
main = putStrLn ("Hello World: " ++ show (barry 3))

barry :: a -> Bool
barry = const agda
