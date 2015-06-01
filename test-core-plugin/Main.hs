module Main where

import Data

agda :: a
agda = error "Compiler plugin did not run correctly"
{-# NOINLINE agda #-}

main :: IO ()
main = do
  putStrLn $ "Barry `eqFoo` Barry: " ++ show (Barry `eqFoo` Barry)
  putStrLn $ "Barry `eqFoo` Bar True: " ++ show (Barry `eqFoo` Bar True)
  putStrLn $ "Bar True `eqFoo` Bar True: " ++ show (Bar True `eqFoo` Bar True)
  putStrLn $ "Bar False `eqFoo` Bar True: " ++ show (Bar False `eqFoo` Bar True)
  putStrLn $ "Bar True `eqFoo` Bar False: " ++ show (Bar True `eqFoo` Bar False)
-- main = agda
-- main = putStrLn "hello world" -- ("Hello World: " ++ show ((agda :: Bool -> Bool) True))
-- main = putStrLn $ showFoo Barry ++ " " ++ showFoo (Bar True)

-- notAgda :: Bool -> Bool
-- notAgda = agda

-- maybeToList :: Maybe a -> [a]
-- maybeToList = agda

-- maybeToListBool :: Maybe Bool -> [Bool]
-- maybeToListBool = agda


-- showFoo :: Foo -> String
-- showFoo = agda
-- showFoo = \foo -> case foo of
--   Barry -> "Barry"
--   Bar b -> "Bar" ++ show b


eqFoo :: Foo -> Foo -> Bool
eqFoo = agda
-- eqFoo f1 f2 = case (f1, f2) of
--   (Barry, Barry)   -> True
--   (Bar b1, Bar b2) -> b1 == b2
--   _                -> False
