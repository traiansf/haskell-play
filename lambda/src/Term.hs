module Term where

import Variable
import Nice
import Data.List ( nub )

data Term
  = V Variable
  | App Term Term
  | Lam Variable Term
  deriving (Show)

-- alpha-equivalence
aEq :: Term -> Term -> Bool
aEq (V x) (V x') = x == x'
aEq (App t1 t2) (App t1' t2') = aEq t1 t1' && aEq t2 t2'
aEq (Lam x t) (Lam x' t')
  | x == x'   = aEq t t'
  | otherwise = aEq (subst (V y) x t) (subst (V y) x' t')
  where
    fvT = freeVars t
    fvT' = freeVars t'
    allFV = nub ([x, x'] ++ fvT ++ fvT')
    y = freshVariable x allFV
aEq _ _ = False

v :: String -> Term
v x = V (var x)

lam :: String -> Term -> Term
lam x = Lam (var x)

lams :: [String] -> Term -> Term
lams xs t = foldr lam t xs

($$) :: Term -> Term -> Term
($$) = App
infixl 9 $$

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


-- subst u x t defines [u/x]t, i.e.,  substituting u for x in t
-- for example [3/x](x + x) == 3 + 3
-- This substitution avoids variable captures so it is safe to be used when 
-- reducing terms with free variables (e.g., if evaluating inside lambda abstractions)
subst
    :: Term     -- ^ substitution term
    -> Variable -- ^ variable to be substitutes
    -> Term     -- ^ term in which the substitution occurs
    -> Term
subst u x (V y)
  | x == y    = u
  | otherwise = V y
subst u x (App t1 t2) = App (subst u x t1) (subst u x t2)
subst u x (Lam y t)
  | x == y          = Lam y t
  | y `notElem` fvU = Lam y (subst u x t)
  | x `notElem` fvT = Lam y t
  | otherwise       = Lam y' (subst u x (subst (V y') y t))
  where
    fvT = freeVars t
    fvU = freeVars u
    allFV = nub ([x] ++ fvU ++ fvT)
    y' = freshVariable y allFV

-- Strict / Eager evaluation
-- - make sure operands are always evaluated before evaluating expression
-- - evaluates inside lambda abstractions
strictReduce :: Term -> Term
strictReduce (V x) = V x
strictReduce (App t1 t2)
  | Lam v t <- r1 = strictReduce (subst r2 v t)
  | otherwise = App r1 r2
  where
    r1 = strictReduce t1
    r2 = strictReduce t2
strictReduce (Lam var t) = Lam var (strictReduce t)

-- alpha-beta equivalence (for strongly normalizing terms) is obtained by
-- fully evaluating the terms using beta-reduction, then checking their
-- alpha-equivalence.
abEq :: Term -> Term -> Bool
abEq t1 t2 = aEq (strictReduce t1) (strictReduce t2)

-- Call by value
-- - make sure operands are always evaluated before evaluating expression
-- - never reduce under a lambda-abstraction (it's already a value)
callByValueReduce :: Term -> Term
callByValueReduce (V x) = V x
callByValueReduce (App t1 t2)
  | Lam v t <- r1 = callByValueReduce (subst r2 v t)
  | otherwise = App r1 r2
  where
    r1 = callByValueReduce t1
    r2 = callByValueReduce t2
callByValueReduce (Lam var t) = Lam var t

-- Call by name
-- - never evaluate right-hand-side of an application
-- - never reduce under a lambda-abstraction (it's already a value)
callByNameReduce :: Term -> Term
callByNameReduce (V x) = V x
callByNameReduce (App t1 t2)
  | Lam v t <- r1 = callByNameReduce (subst t2 v t)
  | otherwise = App r1 t2
  where
    r1 = callByNameReduce t1
callByNameReduce (Lam var t) = Lam var t

reduce :: Term -> Term
reduce = strictReduce

evaluate :: String -> String
evaluate s = showNice (reduce t)
  where
    (t, "") = readNice s