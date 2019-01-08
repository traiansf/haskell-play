{-# LANGUAGE GADTs #-}

module Lib
    ( Exp (..)
    , someFunc
    ) where

data Exp eType child where
    Var :: String -> Exp eType child
    Int :: Integer -> Exp Integer child
    Bool :: Integer -> Exp Bool child
    (:+:) :: child Integer -> child Integer -> Exp Integer child
    (:<=:) :: child Integer -> child Integer -> Exp Bool child
    (:=>:) :: String -> child t2 -> Exp (t1 -> t2) child
    (:$:) :: child (t1 -> t2) -> child t1 -> Exp t2 child

infixr 0 :=>:
infixl 9 :$:
infixl 6 :+:
infix 4 :<=:

type HExp eType = Fix (Exp eType)

someFunc :: IO ()
someFunc = putStrLn "someFunc"
