module Main where

import Term (evaluate)
import System.IO (hFlush, stdout)

main :: IO ()
main = do
    putStr "REPL> "
    hFlush stdout
    s <- getLine
    putStrLn (evaluate s)
    main