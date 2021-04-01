module Variable (Variable, var, freshVariable) where

import Nice
import Data.Char (isLetter)

data Variable
  = Variable
  { name :: String
  , count :: Int
  }
  deriving (Show, Eq, Ord)

var :: String -> Variable
var x = Variable x 0

instance ShowNice Variable where
    showNice (Variable x 0) = x
    showNice (Variable x cnt) = x <> "_" <> show cnt

instance ReadNice Variable where
    readNice s
      | null x = error $ "expected variable but found " <> s
      | otherwise = (var x, s')
      where
        (x, s') = span isLetter s

freshVariable :: Variable -> [Variable] -> Variable
freshVariable var vars = Variable x (cnt + 1)
  where
    x = name var
    varsWithName = filter ((== x) . name) vars
    Variable _ cnt = maximum (var : varsWithName)
