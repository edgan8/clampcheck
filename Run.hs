module Run (
) where

import Pretty
import Util
import Idx
import Types
import ExprU
import qualified Data.Map as M

data RMError = RMString String | RMDone
  deriving (Show,Eq)
instance Error RMError where
  strMsg s = RMString s

type RMState = Int
type RuMonad a = ErrorT RMError (State RMState) a

data RuVal =
    RuLit Lit
  | RuAbs AQual Idx Expr
  | RuWith Expr Expr
  | RuPrim1 PrimOp1 RuVal
  | RuPrim2 PrimOp2 RuVal RuVal
  deriving (Show,Eq)

data RuCont = 
    KApp1 Expr
  | KApp2 RuVal
  | KLet Idx Expr
  | KLetp Idx Idx Expr
  | KMatch Idx Expr Idx Expr
  | KWith1 Expr
  | KWith2 RuVal
  | K1Prim PrimOp1
  | K2Prim1 PrimOp2 Expr
  | K2Prim2 PrimOp2 RuVal
  deriving (Show,Eq)

type RuEnv = M.Map Idx RuVal

type RuStore = M.Map Int (RuVal,Int)

type RuState = (RuStore,[RuCont],Expr)

type LMSet = M.Map Int Int

subBuiltins :: Expr -> Expr
subBuiltins = undefined

isVal :: Expr -> Bool
isVal = undefined

convertVal :: Expr -> RuVal
convertVal = undefined

applyPrim1 :: PrimOp1 -> Expr -> Expr
applyPrim1 = undefined

applyPrim2 :: PrimOp2 -> Expr -> Expr -> Expr
applyPrim2 = undefined

locs :: RuVal -> LMSet
locs = undefined

incr :: LMSet -> RuStore -> RuStore
incr = undefined

decr :: LMSet -> RuStore -> RuStore
decr = undefined

subst :: Expr -> Idx -> Expr -> Expr
subst = undefined

step :: RuState -> RuMonad (RuState)
step (s,k,ExApp e1 e2) = do
  return (s,(KApp1 e2):k,e1)
step (s,k,ExLet i e1 e2) = do
  return (s,(KLet i e2):k,e1)
step (s,k,ExLetp i1 i2 e1 e2) = do
  return (s,(KLetp i1 i2 e2):k,e1)
step (s,k,ExMatch e i1 e1 i2 e2) = do
  return (s,(KMatch i1 e1 i2 e2):k,e)
step (s,k,ExWith e1 e2) = do
  return (s,(KWith1 e2):k,e1)
step (s,k,ExDup es ips e2) = do
  let eips = zip es ips
  return $ (foldl processExp s es,k,
            foldl processBinds e2 eips)
  where 
    processExp k e = 
      incr (locs (convertVal e)) k
    processBinds e2 (e,(i1,i2)) =
      subst (subst e2 i2 e) i1 e
step (s,k,ExDrop es e2) = do
  return $ (foldl processExp s es,k,e2)
  where 
    processExp k e = 
      decr (locs (convertVal e)) k
step (s,k,ExPrim1 p e) = do
  return (s,(K1Prim p):k,e)
step (s,k,ExPrim2 p e1 e2) = do
  return (s,(K2Prim1 p e2):k,e1)
