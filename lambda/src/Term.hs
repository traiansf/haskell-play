module Term where

import Variable
import Nice
import Data.List ( nub )

data Term
  = V Variable
  | App Term Term
  | Lam Variable Term
  deriving (Show)

instance ShowNice Term where
    showNice (V var) = showNice var
    showNice (App t1 t2) = "(" <> showNice t1 <> " " <> showNice t2 <> ")"
    showNice (Lam var t) = "(" <> "\\" <> showNice var <> "." <> showNice t <> ")"

instance ReadNice Term where
    readNice [] = error "Nothing to read"
    readNice ('(' : '\\' : s) = (Lam var t, s'')
      where
        (var, '.' : s') = readNice s
        (t, ')' : s'') = readNice s'
    readNice ('(' : s) = (App t1 t2, s'')
      where
        (t1, ' ' : s') = readNice s
        (t2, ')' : s'') = readNice s'
    readNice s = (V var, s')
      where
        (var, s') = readNice s

freeVars :: Term -> [Variable]
freeVars (V var) = [var]
freeVars (App t1 t2) = nub $ freeVars t1 ++ freeVars t2
freeVars (Lam var t) = filter (/= var) (freeVars t)

subst :: Term -> Variable -> Term -> Term
subst (V var') var t = if var == var' then t else V var'
subst (App t1 t2) var t = App (subst t1 var t) (subst t2 var t)
subst (Lam var' t') var t =
    if var' `notElem` fv then Lam var' (subst t' var t)
    else Lam freshV (subst (subst t' var' (V freshV)) var t)
  where
    fv = var : freeVars t
    freshV = freshVariable var' fv

reduce :: Term -> Term -- fully normalizing, bottom-up, may not terminate
reduce (V x) = V x
reduce (App t1 t2)
  | Lam v t <- r1 = reduce (subst t v r2)
  | otherwise = App r1 r2
  where
    r1 = reduce t1
    r2 = reduce t2
reduce (Lam var t) = Lam var (reduce t)

evaluate :: String -> String
evaluate s = showNice (reduce t)
  where
    (t, "") = readNice s