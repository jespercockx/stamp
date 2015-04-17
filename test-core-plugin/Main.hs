module Main where

agda :: a
agda = error "Compiler plugin did not run correctly"
{-# NOINLINE agda #-}

main :: IO ()
-- main = agda
main = putStrLn "hello world" -- ("Hello World: " ++ show ((agda :: Bool -> Bool) True))

-- notAgda :: Bool -> Bool
-- notAgda = agda

maybeToList :: Maybe a -> [a]
maybeToList = agda

-- maybeToListBool :: Maybe Bool -> [Bool]
-- maybeToListBool = agda

-- food :: IO ()
-- food = putStrLn "hello"
