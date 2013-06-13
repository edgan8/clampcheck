module Run (
) where

import Pretty
import Util
import Idx
import Types
import ExprU
import qualified Data.Map as M

data RMError = RMString String
  deriving (Show,Eq)
instance Error RMError where
  strMsg s = RMString s

type RMState = Int
type RuMonad a = ErrorT RMError (State RMState) a

data RuVal =
    RVLit Lit
  | RVAbs AQual Idx Expr
  | RVWith Expr Expr
  | RVInl RuVal
  | RVInr RuVal
  | RVPair RuVal RuVal
  deriving (Show,Eq)

data RuCont = 
    KApp1 Expr
  | KApp2 RuVal
  | KLet Idx Expr
  | KLetp Idx Idx Expr
  | KMatch Idx Expr Idx Expr
  | K1Prim PrimOp1
  | K2Prim1 PrimOp2 Expr
  | K2Prim2 PrimOp2 RuVal
  deriving (Show,Eq)

type RuEnv = M.Map Idx RuVal

type RuStore = M.Map Int (RuVal,Int)

type RuState = (RuStore,[RuCont],Expr)
type RuFState = (RuStore,RuVal)

type LMSet = M.Map Int Int

subBuiltins :: Expr -> Expr
subBuiltins = id -- TODO

isVal :: Expr -> Bool
isVal (ExLit _) = True
isVal (ExAbs _ _ _) = True
isVal (ExWith _ _) = True
isVal (ExPrim1 (PrInl) v) = isVal v
isVal (ExPrim1 (PrInr) v) = isVal v
isVal (ExPrim2 (PrPair) v1 v2) = isVal v1 && isVal v2
isVal _ = False

convertVal :: Expr -> RuVal
convertVal (ExLit l) = RVLit l
convertVal (ExAbs a i e) = RVAbs a i e
convertVal (ExWith e1 e2) = RVWith e1 e2
convertVal (ExPrim1 (PrInl) v) = RVInl (convertVal v)
convertVal (ExPrim1 (PrInr) v) = RVInr (convertVal v)
convertVal (ExPrim2 (PrPair) v1 v2) = 
  RVPair (convertVal v1) (convertVal v2)

locs :: RuVal -> LMSet
locs = undefined

incr :: LMSet -> RuStore -> RuStore
incr = undefined

decr :: LMSet -> RuStore -> RuStore
decr = undefined

subst :: Expr -> Idx -> RuVal -> Expr
subst = undefined

runRuMonad :: RMState -> RuMonad a -> a
runRuMonad s m = evalState (do
  r <- (runErrorT m)
  case r of
    Left e -> error (show e)
    Right sm -> return sm
  ) s

run :: Expr -> RuFState
run e = runRuMonad 0 (runS (M.empty,[],e))

runS :: RuState -> RuMonad RuFState
runS s = do
  res <- step s
  case res of
    Left s2 -> runS s2
    Right sf -> return sf

step :: RuState -> RuMonad (Either RuState RuFState)
step (s,k,ExApp e1 e2) = do
  return $ Left (s,(KApp1 e2):k,e1)
step (s,k,ExLet i e1 e2) = do
  return $ Left (s,(KLet i e2):k,e1)
step (s,k,ExLetp i1 i2 e1 e2) = do
  return $ Left (s,(KLetp i1 i2 e2):k,e1)
step (s,k,ExMatch e i1 e1 i2 e2) = do
  return $ Left (s,(KMatch i1 e1 i2 e2):k,e)
step (s,k,ExDup es ips e2) = do
  let vs = map convertVal es
  let vips = zip vs ips
  return $ Left $ (foldl processExp s vs,k,
            foldl processBinds e2 vips)
  where 
    processExp k v = 
      incr (locs v) k
    processBinds e2 (v,(i1,i2)) =
      subst (subst e2 i2 v) i1 v
step (s,k,ExDrop es e2) = do
  return $ Left $ (foldl processExp s es,k,e2)
  where 
    processExp k e = 
      decr (locs (convertVal e)) k
step (s,k,ExPrim1 p e) = do
  return $ Left (s,(K1Prim p):k,e)
step (s,k,ExPrim2 p e1 e2) = do
  return $ Left (s,(K2Prim1 p e2):k,e1)
step (s,k,e) = do
  if (isVal e) then
    stepVal (s,k,convertVal e)
  else
    throwError $ strMsg "Not Val --- Unbound Var?"

stepVal :: (RuStore,[RuCont],RuVal) -> RuMonad (Either RuState RuFState)
stepVal (s,(KApp1 e):ktl,v@(RVAbs _ _ _)) = do
  return $ Left (s,(KApp2 v):ktl,e)
stepVal (s,(KApp2 (RVAbs _ i e)):ktl,v) = do
  return $ Left (s,ktl,subst e i v)
stepVal (s,(KLet i e):ktl,v) = do
  return $ Left (s,ktl,subst e i v)
stepVal (s,(KLetp i1 i2 e):ktl,RVPair v1 v2) = do
  return $ Left (s,ktl,subst (subst e i1 v1) i2 v2)
stepVal (s,(KMatch i1 e1 i2 e2):ktl,RVInl v) = do
  return $ Left (s,ktl,subst e1 i1 v)
stepVal (s,(KMatch i1 e1 i2 e2):ktl,RVInr v) = do
  return $ Left (s,ktl,subst e2 i2 v)
stepVal (s,(K1Prim p):ktl,v) = do
  (s2,v2) <- applyPrim1 p (s,v)
  stepVal (s2,ktl,v2)
stepVal (s,(K2Prim1 p e):ktl,v) = do
  return $ Left (s,(K2Prim2 p v):ktl,e)
stepVal (s,(K2Prim2 p v1):ktl,v2) =
  stepVal (s,ktl,applyPrim2 p v1 v2)
stepVal (s,[],v) = do
  return $ Right (s,v)

applyPrim1 :: PrimOp1 -> (RuStore,RuVal) -> RuMonad (RuStore,RuVal)
applyPrim1 PrInl (s,v) =
  return (s,RVInl v)
applyPrim1 PrInr (s,v) =
  return (s,RVInr v)
applyPrim1 PrFst (s,RVPair v1 v2) =
  return (s,v1)
applyPrim1 PrSnd (s,RVPair v1 v2) =
  return (s,v2)
applyPrim1 PrFix _ = undefined
applyPrim1 PrWNew (s,v) = do
  lnum <- lift get
  put (lnum+1)
  return (M.insert lnum (v,1) s,RVLit (LiLab lnum))

applyPrim2 :: PrimOp2 -> RuVal -> RuVal -> RuVal
applyPrim2 PrPair v1 v2 = RVPair v1 v2
applyPrim2 p (RVLit (LiNum i1)) (RVLit (LiNum i2)) =
  (applyNumOp p i1 i2)


mkNum :: Int -> RuVal
mkNum i = RVLit (LiNum i)
mkTrue :: RuVal
mkTrue = RVInl (RVLit (LiUnit))
mkFalse :: RuVal
mkFalse = RVInr (RVLit (LiUnit))

applyNumOp :: PrimOp2 -> Int -> Int -> RuVal
applyNumOp PrPlus i1 i2 = mkNum $ i1 + i2
applyNumOp PrMinus i1 i2 = mkNum $ i1 - i2
applyNumOp PrGt i1 i2 =
  if (i1 > i2) then mkTrue else mkFalse
applyNumOp PrLt i1 i2 =
  if (i1 < i2) then mkTrue else mkFalse
applyNumOp PrEqq i1 i2 =
  if (i1 == i2) then mkTrue else mkFalse
