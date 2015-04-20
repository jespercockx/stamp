module Main where

import Data

agda :: a
agda = error "Compiler plugin did not run correctly"
{-# NOINLINE agda #-}

main :: IO ()
-- main = agda
-- main = putStrLn "hello world" -- ("Hello World: " ++ show ((agda :: Bool -> Bool) True))
main = putStrLn $ showFoo Barry ++ " " ++ showFoo (Bar True)

-- notAgda :: Bool -> Bool
-- notAgda = agda

-- maybeToList :: Maybe a -> [a]
-- maybeToList = agda

-- maybeToListBool :: Maybe Bool -> [Bool]
-- maybeToListBool = agda


showFoo :: Foo -> String
showFoo = agda
-- showFoo = \foo -> case foo of
--   Barry -> "Barry"
--   Bar b -> "Bar" ++ show b
