module Interpret where

import Control.Monad.State.Strict
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map

import AST
import System.IO (stdout, hFlush)

data Value = IVal Integer  | BVal Bool
  deriving (Show, Eq)

data ImpState = ImpState
    { env :: Map String Int
    , store :: Map Int Value
    , nextLoc :: Int
    }
  deriving (Show)

compose :: Ord b => Map b c -> Map a b -> Map a c
compose bc ab
  | null bc = Map.empty
  | otherwise = Map.mapMaybe (bc Map.!?) ab

showImpState :: ImpState -> String
showImpState st = 
    "Final state: " <> show (compose (store st) (env st))

emptyState :: ImpState
emptyState = ImpState Map.empty Map.empty 0

type M = StateT ImpState IO

runM :: M a -> IO (a, ImpState)
runM m = runStateT m emptyState

lookupM :: String -> M Value
lookupM x = do
    Just l <- Map.lookup x <$> gets env
    Just v <- Map.lookup l <$> gets store
    return v

updateM :: String -> Value -> M ()
updateM x v = do
    Just l <- Map.lookup x <$> gets env
    st <- gets store
    let st' = Map.insert l v st
    modify' (\s -> s {store = st'})

aop :: BinAop -> Integer -> Integer -> Integer
aop Add = (+)
aop Sub = (-)
aop Mul = (*)
aop Div = div
aop Mod = mod

cop :: BinCop  -> Integer -> Integer -> Bool
cop Lt = (<)
cop Lte = (<=)
cop Gte = (>=)
cop Gt = (>)

eop :: Eq a => BinEop -> a -> a -> Bool
eop Eq = (==)
eop Neq = (/=)

lop :: BinLop -> Bool -> Bool -> Bool
lop And = (&&)
lop Or = (||)

evalExp :: Exp -> M Value
evalExp (I n) = return (IVal n)
evalExp (B b) = return (BVal b)
evalExp (Id x) = lookupM x
evalExp (UMin e) = do
    IVal i <- evalExp e
    return (IVal $ negate i)
evalExp (BinA op e1 e2) = do
    IVal i1 <- evalExp e1
    IVal i2 <- evalExp e2
    return (IVal $ aop op i1 i2)
evalExp (BinC op e1 e2) = do
    IVal i1 <- evalExp e1
    IVal i2 <- evalExp e2
    return (BVal $ cop op i1 i2)
evalExp (BinE op e1 e2) = do
    v1 <- evalExp e1
    v2 <- evalExp e2
    return (BVal $ eop op v1 v2)
evalExp (BinL op e1 e2) = do
    BVal b1 <- evalExp e1
    BVal b2 <- evalExp e2
    return (BVal $ lop op b1 b2)
evalExp (Not e) = do
    BVal b <- evalExp e
    return (BVal $ not b)

evalStmt :: Stmt -> M ()
evalStmt (Asgn x e) = do
    v <- evalExp e
    updateM x v
evalStmt (If e s1 s2) = do
    BVal b <- evalExp e
    if b then evalStmt s1 else evalStmt s2
evalStmt (While e s) = do
    BVal b <- evalExp e
    when b $ do
        evalStmt s
        evalStmt (While e s)
evalStmt (Read s x) = do
    i <- liftIO (putStr s >> hFlush stdout >> readLn)
    evalStmt(Asgn x (I i))
evalStmt (Print s e) = do
    IVal i <- evalExp e
    liftIO (putStrLn (s <> show i))
evalStmt (Decl x e) = do
    v <- evalExp e
    modify' (declare v)
  where
    declare v st = ImpState env' store' nextLoc'
      where
        l = nextLoc st
        nextLoc' = 1 + nextLoc st
        store' = Map.insert l v (store st)
        env' = Map.insert x l (env st)
evalStmt (Block sts) = do
    oldEnv <- gets env
    mapM_ evalStmt sts
    modify' (\s -> s {env = oldEnv})

evalPgm :: [Stmt] -> IO ((), ImpState)
evalPgm sts = runM $ mapM_ evalStmt sts

pFact= Block [
       Decl "n" (I 0),
       Read "n=" "n",
       Decl "fact" (Id "n"),
       Decl "i" (I 1),
       While (BinE Neq  (Id "n") (Id "i")) 
                (Block [ Asgn "fact" (BinA Mul (Id "fact") (Id "i")),
                       Asgn "i" (BinA Add (Id "i") (I 1))
                       ]),
        Print "fact= " (Id "fact")
              ]