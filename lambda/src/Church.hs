module Church where

import Term


churchTrue :: Term
churchTrue = lams ["t", "f"] (v "t")

churchFalse :: Term
churchFalse = lams ["t", "f"] (v "f")

churchIf :: Term
churchIf = lams ["c", "then", "else"] (v "c" $$ v "then" $$ v "else")

churchNot :: Term
churchNot = lam "b" (v "b" $$ churchFalse $$ churchTrue)

churchAnd :: Term
churchAnd = lams ["b1", "b2"] (v "b1" $$ v "b2" $$ churchFalse)

churchOr :: Term
churchOr = lams ["b1", "b2"] (v "b1" $$ churchTrue $$ v "b2")

church0 :: Term
church0 = lams ["s", "z"] (v "z") -- note that it's the same as churchFalse

church1 :: Term
church1 = lams ["s", "z"] (v "s" $$ v "z")

church2 :: Term
church2 = lams ["s", "z"] (v "s" $$ (v "s" $$ v "z"))

churchS :: Term
churchS = lams ["t","s","z"] (v "s" $$ (v "t" $$ v "s" $$ v "z"))

churchNat :: Int -> Term
churchNat n = lams ["s", "z"] (iterate' n (v "s" $$) (v "z"))
  where
    iterate' n f a = foldr (const f) a (replicate n ())

churchPlus :: Term
churchPlus = lams ["n", "m", "s", "z"] (v "n" $$ v "s" $$ (v "m" $$ v "s" $$ v "z"))

churchPlus' :: Term
churchPlus' = lams ["n", "m"] (v "n" $$ churchS $$ v "m")

churchMul :: Term
churchMul = lams ["n", "m", "s"] (v "n" $$ (v "m" $$ v "s"))

churchMul' :: Term
churchMul' = lams ["n", "m"] (v "n" $$ (churchPlus' $$ v "m") $$ church0)

churchPow :: Term
churchPow = lams ["m", "n"] (v "n" $$ v "m")

churchPow' :: Term
churchPow' = lams ["m", "n"] (v "n" $$ (churchMul' $$ v "m") $$ church1)

churchIs0 :: Term
churchIs0 = lam "n" (v "n" $$ (churchAnd $$ churchFalse) $$ churchTrue)

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

churchLte :: Term
churchLte = lams ["m", "n"] (churchIs0 $$ (churchSub $$ v "m" $$ v "n"))

churchGte :: Term
churchGte = lams ["m", "n"] (churchLte $$ v "n" $$ v "m")

churchLt :: Term
churchLt = lams ["m", "n"] (churchNot $$ (churchGte $$ v "m" $$ v "n"))

churchGt :: Term
churchGt = lams ["m", "n"] (churchLt $$ v "n" $$ v "m")

churchEq :: Term
churchEq = lams ["m", "n"] (churchAnd $$ (churchLte $$ v "m" $$ v "n") $$ (churchLte $$ v "n" $$ v "m"))

churchPair :: Term
churchPair = lams ["f", "s", "action"] (v "action" $$ v "f" $$ v "s")

churchFst :: Term
churchFst = lam "pair" (v "pair" $$ churchTrue)

churchSnd :: Term
churchSnd = lam "pair" (v "pair" $$ churchFalse)

churchDivMod :: Term
churchDivMod =
    lams ["m", "n"]
        (v "m"
        $$ lam "pair"
          (churchIf
          $$ (churchGt $$ (churchSnd $$ v "pair") $$ v "n")
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