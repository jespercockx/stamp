module Main where


foo a b c d e f g = (g + a)

main :: IO ()
main = putStrLn ("Hello World" ++ show (foo 1 2 3 4 5 6 7))
