module Nice where

class ShowNice a where
    showNice :: a -> String

class ReadNice a where
    readNice :: String -> (a, String)