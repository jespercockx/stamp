module Main where

agda :: a
agda = error "Compiler plugin did not run correctly"
{-# NOINLINE agda #-}

main :: IO ()
-- main = agda
main = putStrLn "hello world" -- ("Hello World: " ++ show ((agda :: Bool -> Bool) True))

notHs = \x -> case x of
  True -> False
  False -> True

notAgda = agda

-- barry :: a -> b -> c -> b
-- barry = agda



-- food :: IO ()
-- food = putStrLn "hello"
