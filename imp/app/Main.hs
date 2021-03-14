module Main where

import System.Environment ( getArgs )   
import Control.Monad (when)


import Parse
import AST
import Checker
import Interpret

main :: IO ()
main = do
    args <- getArgs
    when (null args) (error "Need file to run")
    let (file:_) = args
    pgm <- loadProgramFromFile file
    checkPgm pgm
    (_, st) <- evalPgm pgm
    putStrLn $ showImpState st