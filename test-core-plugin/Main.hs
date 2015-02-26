module Main where

agda :: a
agda = error "Compiler plugin did not run correctly"
{-# NOINLINE agda #-}

main :: IO ()
main = agda -- putStrLn ("Hello World: " ++ show (barry 3 True 'x'))

-- barry :: a -> b -> c -> b
-- barry = agda



-- food :: IO ()
-- food = putStrLn "hello"
