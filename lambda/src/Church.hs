{-# LANGUAGE RankNTypes #-}
module Church where

import Term
import qualified Data.Function as Function


newtype CBool = CBool {cIf :: forall t. t -> t -> t}

instance Show CBool where
    show b = show $ cIf b True False

churchTrue :: Term
churchTrue = lams ["t", "f"] (v "t")

cTrue :: CBool
cTrue = CBool $ \t f -> t

churchFalse :: Term
churchFalse = lams ["t", "f"] (v "f")

cFalse :: CBool
cFalse = CBool $ \t f -> f

churchIf :: Term
churchIf = lams ["c", "then", "else"] (v "c" $$ v "then" $$ v "else")

churchNot :: Term
churchNot = lam "b" (v "b" $$ churchFalse $$ churchTrue)

cNot :: CBool -> CBool
cNot = \b -> CBool $ \t f -> cIf b f t

churchAnd :: Term
churchAnd = lams ["b1", "b2"] (v "b1" $$ v "b2" $$ churchFalse)

(&&:) :: CBool -> CBool -> CBool
(&&:) = \b1 b2 -> cIf b1 b2 cFalse
infixr 3 &&:

churchOr :: Term
churchOr = lams ["b1", "b2"] (v "b1" $$ churchTrue $$ v "b2")

(||:) :: CBool -> CBool -> CBool
(||:) = \b1 b2 -> cIf b1 cTrue b2
infixr 2 ||:

newtype CNat = CNat { cFor :: forall t. (t -> t) -> t -> t }

instance Show CNat where
    show n = show $ cFor n (1 +) (0 :: Integer)

church0 :: Term
church0 = lams ["s", "z"] (v "z") -- note that it's the same as churchFalse

church1 :: Term
church1 = lams ["s", "z"] (v "s" $$ v "z")

church2 :: Term
church2 = lams ["s", "z"] (v "s" $$ (v "s" $$ v "z"))

churchS :: Term
churchS = lams ["t","s","z"] (v "s" $$ (v "t" $$ v "s" $$ v "z"))

cS :: CNat -> CNat
cS = \t -> CNat $ \s z -> s (cFor t s z)

iterate' :: (Ord t, Num t) => t -> (p -> p) -> p -> p
iterate' n f a = go n
  where
    go n
      | n <= 0 = a
      | otherwise  = f (go (n - 1))

churchNat :: Integer -> Term
churchNat n = lams ["s", "z"] (iterate' n (v "s" $$) (v "z"))

cNat :: (Ord p, Num p) => p -> CNat
cNat n = CNat $ \s z -> (iterate' n (s $) z)

churchPlus :: Term
churchPlus = lams ["n", "m", "s", "z"] (v "n" $$ v "s" $$ (v "m" $$ v "s" $$ v "z"))

(+:) :: CNat -> CNat -> CNat
(+:) = \n m -> CNat $ \s -> cFor n s . cFor m s
infixl 6 +:

churchPlus' :: Term
churchPlus' = lams ["n", "m"] (v "n" $$ churchS $$ v "m")

churchMul :: Term
churchMul = lams ["n", "m", "s"] (v "n" $$ (v "m" $$ v "s"))

(*:) :: CNat -> CNat -> CNat
(*:) = \n m -> CNat $ cFor n . cFor m
infixl 7 *:

churchMul' :: Term
churchMul' = lams ["n", "m"] (v "n" $$ (churchPlus' $$ v "m") $$ church0)

churchPow :: Term
churchPow = lams ["m", "n"] (v "n" $$ v "m")

(^:) :: CNat -> CNat -> CNat
(^:) = \m n -> CNat $ cFor n (cFor m)
infixr 8 ^:

churchPow' :: Term
churchPow' = lams ["m", "n"] (v "n" $$ (churchMul' $$ v "m") $$ church1)

churchIs0 :: Term
churchIs0 = lam "n" (v "n" $$ (churchAnd $$ churchFalse) $$ churchTrue)

cIs0 :: CNat -> CBool
cIs0 = \n -> cFor n (cFalse &&:) cTrue

churchS' :: Term
churchS' = lam "n" (v "n" $$ churchS $$ church1)

churchS'Rev0 :: Term
churchS'Rev0 = lams ["s","z"] church0

churchPred :: Term
churchPred =
    lam "n"
        (churchIf
        $$ (churchIs0 $$ v "n")
        $$ church0
        $$ (v "n" $$ churchS' $$ churchS'Rev0))

churchSub :: Term
churchSub = lams ["m", "n"] (v "n" $$ churchPred $$ v "m")

(-:) :: CNat -> CNat -> CNat
(-:) = \m n -> cFor n cPred m

instance Num CNat where
    (+) = (+:)
    (*) = (*:)
    (-) = (-:)
    abs = id
    signum n = cIf (cIs0 n) 0 1
    fromInteger = cNat

instance Enum CNat where
    toEnum = cNat
    fromEnum n = cFor n succ 0

churchLte :: Term
churchLte = lams ["m", "n"] (churchIs0 $$ (churchSub $$ v "m" $$ v "n"))

(<=:) :: CNat -> CNat -> CBool
(<=:) = \m n -> cIs0 (m - n)
infix 4 <=:

churchGte :: Term
churchGte = lams ["m", "n"] (churchLte $$ v "n" $$ v "m")

(>=:) :: CNat -> CNat -> CBool
(>=:) = \m n -> n <=: m
infix 4 >=:

churchLt :: Term
churchLt = lams ["m", "n"] (churchNot $$ (churchGte $$ v "m" $$ v "n"))

(<:) :: CNat -> CNat -> CBool
(<:) = \m n -> cNot (m >=: n)
infix 4 <:

churchGt :: Term
churchGt = lams ["m", "n"] (churchLt $$ v "n" $$ v "m")

(>:) :: CNat -> CNat -> CBool
(>:) = \m n -> n <: m
infix 4 >:

churchEq :: Term
churchEq = lams ["m", "n"] (churchAnd $$ (churchLte $$ v "m" $$ v "n") $$ (churchLte $$ v "n" $$ v "m"))

(==:) :: CNat -> CNat -> CBool
(==:) = \m n -> m <=: n &&: n <=: m

instance Eq CNat where
    m == n = cIf (m ==: n) True False

instance Ord CNat where
    m <= n = cIf (m <=: n) True False

newtype CPair a b = CPair { cOn :: forall c . (a -> b -> c) -> c }

instance (Show a, Show b) => Show (CPair a b) where
    show p = show $ cOn p (,)

churchPair :: Term
churchPair = lams ["f", "s", "action"] (v "action" $$ v "f" $$ v "s")

cPair :: a -> b -> CPair a b
cPair = \x y -> CPair $ \action -> action x y

churchFst :: Term
churchFst = lam "pair" (v "pair" $$ churchTrue)

cFst :: CPair a b -> a
cFst = \p -> (cOn p $ \x y -> x)

churchSnd :: Term
churchSnd = lam "pair" (v "pair" $$ churchFalse)

cSnd :: CPair a b -> b
cSnd = \p -> (cOn p $ \x y -> y)

churchPred' :: Term
churchPred' = lam "n" (churchFst $$
    (v "n"
    $$ lam "p" (lam "x" (churchPair $$ v "x" $$ (churchS $$ v "x"))
          $$ (churchSnd $$ v "p"))
    $$ (churchPair $$ church0 $$ church0)
    ))

cPred :: CNat -> CNat
cPred = \n -> cFst $
    cFor n (\p -> (\x -> cPair x (cS x)) (cSnd p)) (cPair 0 0)

churchFactorial :: Term
churchFactorial = lam "n" (churchSnd $$
    (v "n"
    $$ lam "p"
        (churchPair
        $$ (churchS $$ (churchFst $$ v "p"))
        $$ (churchMul $$ (churchFst $$ v "p") $$ (churchSnd $$ v "p"))
        )
    $$ (churchPair $$ church1 $$ church1)
    ))

cFactorial :: CNat -> CNat
cFactorial = \n -> cSnd $ cFor n (\p -> cPair (cFst p) (cFst p * cSnd p)) (cPair 1 1)

churchFibonacci :: Term
churchFibonacci = lam "n" (churchFst $$
    (v "n"
    $$ lam "p"
        (churchPair
        $$ (churchSnd $$ v "p")
        $$ (churchPlus $$ (churchFst $$ v "p") $$ (churchSnd $$ v "p"))
        )
    $$ (churchPair $$ church0 $$ church1)
    ))

cFibonacci :: CNat -> CNat
cFibonacci = \n -> cFst $ cFor n (\p -> cPair (cSnd p) (cFst p + cSnd p)) (cPair 0 1)

churchDivMod :: Term
churchDivMod =
    lams ["m", "n"]
        (v "m"
        $$ lam "pair"
          (churchIf
          $$ (churchLte $$ v "n" $$ (churchSnd $$ v "pair"))
          $$ (churchPair
             $$ (churchS $$ (churchFst $$ v "pair"))
             $$ (churchSub
                $$ (churchSnd $$ v "pair")
                $$ v "n"
                )
             )
          $$ v "pair"
          )
        $$ (churchPair $$ church0 $$ v "m")
        )

cDivMod :: CNat -> CNat -> CPair CNat CNat
cDivMod = \m n -> cFor m (\p -> cIf (n <=: cSnd p) (cPair (cS (cFst p)) (cSnd p - n)) p) (cPair 0 m)


newtype CList a = CList { cFoldR :: forall b. (a -> b -> b) -> b -> b }

instance Foldable CList where
    foldr agg init xs = cFoldR xs agg init

churchNil :: Term
churchNil = lams ["agg", "init"] (v "init")

cNil :: CList a
cNil = CList $ \agg init -> init

churchCons :: Term
churchCons = lams ["x","l","agg", "init"]
    (v "agg"
    $$ v "x"
    $$ (v "l" $$ v "agg" $$ v "init")
    )

(.:) :: a -> CList a -> CList a
(.:) = \x xs -> CList $ \agg init -> agg x (cFoldR xs agg init)

churchList :: [Term] -> Term
churchList = foldr (\x l -> churchCons $$ x $$ l) churchNil

cList :: [a] -> CList a
cList = foldr (.:) cNil

churchNatList :: [Integer] -> Term
churchNatList = churchList . map churchNat

cNatList :: [Integer] -> CList CNat
cNatList = cList . map cNat

churchSum :: Term
churchSum = lam "l" (v "l" $$ churchPlus $$ church0)

cSum :: CList CNat -> CNat
cSum = sum -- since CList is an instance of Foldable; otherwise:  \l -> cFoldR l (+) 0

churchIsNil :: Term
churchIsNil = lam "l" (v "l" $$ lams ["x", "a"] churchFalse $$ churchTrue)

cIsNil :: CList a -> CBool
cIsNil = \l -> cFoldR l (\_ _ -> cFalse) cTrue

churchHead :: Term
churchHead = lams ["l", "default"] (v "l" $$ lams ["x", "a"] (v "x") $$ v "default")

cHead :: CList a -> a -> a
cHead = \l d -> cFoldR l (\x _ -> x) d

churchTail :: Term
churchTail = lam "l" (churchFst $$
    (v "l"
    $$ lams ["x","p"] (lam "t" (churchPair $$ v "t" $$ (churchCons $$ v "x" $$ v "t"))
          $$ (churchSnd $$ v "p"))
    $$ (churchPair $$ churchNil $$ churchNil)
    ))

cTail :: CList a -> CList a
cTail = \l -> cFst $ cFoldR l (\x p -> (\t -> cPair t (x .: t)) (cSnd p)) (cPair cNil cNil)

cLength :: CList a -> CNat
cLength = \l -> cFoldR l (\_ n -> cS n) 0

fix :: Term
fix = lam "f" (lam "x" (v "f" $$ (v "x" $$ v "x")) $$ lam "x" (v "f" $$ (v "x" $$ v "x")))

divmod :: (Enum a, Num a, Ord b, Num b) => b -> b -> (a, b)
divmod m n = divmod' (0, 0)
  where
    divmod' (x, y)
      | x' <= m = divmod' (x', succ y)
      | otherwise = (y, m - x)
      where x' = x + n

divmod' m n =
  if n == 0 then (0, m)
  else
    Function.fix
    (\f p -> 
        (\x' ->
            if x' > 0 then f ((,) (succ (fst p)) x')
            else if (<=) n (snd p) then ((,) (succ (fst p)) 0)
            else p)
        ((-) (snd p) n))
    (0, m)

churchDivMod' :: Term
churchDivMod' = lams ["m", "n"]
  (churchIs0 $$ v "n"
  $$ (churchPair $$ church0 $$ v "m")
  $$ (fix
      $$ lams ["f", "p"]
          (lam "x"
              (churchIs0 $$ v "x"
              $$ (churchLte $$ v "n" $$ (churchSnd $$ v "p")
                  $$ (churchPair $$ (churchS $$ (churchFst $$ v "p")) $$ church0)
                  $$ v "p"
                 )
              $$ (v "f" $$ (churchPair $$ (churchS $$ (churchFst $$ v "p")) $$ v "x"))
              )
          $$ (churchSub $$ (churchSnd $$ v "p") $$ v "n")
          )
      $$ (churchPair $$ church0 $$ v "m")
      )
  )

churchSudan :: Term
churchSudan = fix $$ lam "f" (lams ["n", "x", "y"]
    (churchIs0 $$ v "n"
        $$ (churchPlus $$ v "x" $$ v "y")
        $$ (churchIs0 $$ v "y"
            $$ v "x"
            $$ (lam "fnpy"
                (v "f" $$ (churchPred $$ v "n")
                $$ v "fnpy"
                $$ (churchPlus $$ v "fnpy" $$ v "y")
                )
                $$ (v "f" $$ v "n" $$ v "x" $$ (churchPred $$ v "y"))
                )
            )
    ))

churchAckermann :: Term
churchAckermann = fix $$ lam "A" (lams ["m", "n"]
    (churchIs0 $$ v "m"
    $$ (churchS $$ v "n")
    $$ (churchIs0 $$ v "n"
        $$ (v "A" $$ (churchPred $$ v "m") $$ church1)
        $$ (v "A" $$ (churchPred $$ v "m")
            $$ (v "A" $$ v "m" $$ (churchPred $$ v "n")))
        )
    )
    )