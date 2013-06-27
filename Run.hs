module Run (
  RMError(..), RMState, RuMonad, RuVal(..), RuStore,
  run,
  isGeneralizable,
  isVal,convertVal,convertExpr
) where

import Pretty
import Util
import Idx
import Types
import ExprU
import Debug.Trace
import Data.Data
import Data.Generics
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

instance Pretty RuVal where
  pretty (RVLit l) = pretty l
  pretty (RVAbs a _ _) = text "\\ _ -"<>pretty a<>text "> _"
  pretty (RVWith e1 e2) = text "[_, _]"
  pretty (RVInl v) = pretty "Left" <+> pretty v
  pretty (RVInr v) = pretty "Right" <+> pretty v
  pretty (RVPair v1 v2) = parens (pretty v1<>comma<+> pretty v2)

data RuCont = 
    KApp1 Expr
  | KApp2 RuVal
  | KLet Idx Expr
  | KLetp Idx Idx Expr
  | KMatch Idx Expr Idx Expr
  | K1Prim PrimOp1
  | K2Prim1 PrimOp2 Expr
  | K2Prim2 PrimOp2 RuVal
  | KDup [RuVal] [Expr] [(Idx,Idx)] Expr
  | KDrop [RuVal] [Expr] Expr
  deriving (Show,Eq)

type RuEnv = M.Map Idx RuVal

type RuStore = M.Map Int (RuVal,Int)

type RuState = (RuStore,[RuCont],Expr)
type RuFState = (RuStore,RuVal)

type LMSet = [Int]

subBuiltins :: Expr -> Expr
subBuiltins e =
  everywhere (mkT subGVar) e
  where
    subGVar (ExGVar gv) 
      | gv == IdS "@lunit" = ExLit LiUnit
      | gv == IdS "@ldispose" = 
        ExAbs AQU (IdS "lddummy") (ExLit LiUnit)
      | otherwise = ExGVar gv
    subGVar e = e

isGeneralizable :: Expr -> Bool
isGeneralizable (ExPrim1 (PrFix) e) = isVal e
isGeneralizable e = isVal e

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
convertVal e = error $ show $ text "bad e:"<+>pretty e

convertExpr :: RuVal -> Expr
convertExpr (RVLit l) = ExLit l
convertExpr (RVAbs a i e) = ExAbs a i e
convertExpr (RVWith e1 e2) = ExWith e1 e2
convertExpr (RVInl v) = ExPrim1 PrInl (convertExpr v)
convertExpr (RVInr v) = ExPrim1 PrInr (convertExpr v)
convertExpr (RVPair v1 v2) = 
  ExPrim2 PrPair (convertExpr v1) (convertExpr v2)

-- TODO

msetplus :: LMSet -> LMSet -> LMSet
msetplus = ( ++ )
msetsing x = [x]
msetempty = []

locsE :: Expr -> LMSet
locsE (ExLit (LiLab l)) = msetsing l
locsE (ExLit _) = msetempty
locsE (ExVar _) = msetempty
locsE (ExGVar _) = msetempty
locsE (ExAbs _ _ e) = locsE e
locsE (ExApp e1 e2) = msetplus (locsE e1) (locsE e2)
locsE (ExLet _ e1 e2) = msetplus (locsE e1) (locsE e2)
locsE (ExLetp _ _ e1 e2) = msetplus (locsE e1) (locsE e2)
locsE (ExMatch e _ e1 _ e2) = msetplus (locsE e) (locsE e1)
locsE (ExDup es _ e2) = foldl msetplus (locsE e2) (map locsE es)
locsE (ExDrop es e2) = foldl msetplus (locsE e2) (map locsE es)
locsE (ExPrim1 _ e) = locsE e
locsE (ExPrim2 _ e1 e2) = msetplus (locsE e1) (locsE e2)

locs :: RuVal -> LMSet
locs = locsE . convertExpr

incr :: LMSet -> RuStore -> RuStore
incr ls s = 
  foldl incrl s ls
  where
    incrl s l =
      M.adjust (\(v,i) -> (v,i+1)) l s

decr :: LMSet -> RuStore -> RuStore
decr ls s =
  foldl decrl s ls
  where
    decrl s l =
      case (M.lookup l s) of
        Just (v,i) -> if (i>1) then
                        M.insert l (v,i-1) s
                      else
                        M.delete l (decr (locs v) s)
        Nothing -> error "lab not found during decr"

{- When we substitute, we're almost always subbing in a value
 - except in the case of fixpoints -}
substV :: Expr -> Idx -> RuVal -> Expr
substV e i v = subst e i (convertExpr v)

runRuMonad :: RMState -> RuMonad a -> a
runRuMonad s m = evalState (do
  r <- (runErrorT m)
  case r of
    Left e -> error (show e)
    Right sm -> return sm
  ) s

run :: Expr -> RuFState
run e = runRuMonad 0 (runS (M.empty,[],subBuiltins e))

runS :: RuState -> RuMonad RuFState
runS s = do
  res <- step s
  case res of
    Left s2 -> 
      let (_,k,e) = s2 in
      {-trace ("---\nk:"++(show k)++"\ne:"++(show $ pretty e)) -}
       (runS s2)
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
  case es of
    ehd:etl -> return $ Left (s,(KDup [] etl ips e2):k,ehd)
    [] -> return $ Left (s,k,e2)
step (s,k,ExDrop es e2) = do
  case es of
    ehd:etl -> return $ Left (s,(KDrop [] etl e2):k,ehd)
    [] -> return $ Left (s,k,e2)
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
  return $ Left (s,ktl,substV e i v)
stepVal (s,(KLet i e):ktl,v) = do
  return $ Left (s,ktl,substV e i v)
stepVal (s,(KLetp i1 i2 e):ktl,RVPair v1 v2) = do
  return $ Left (s,ktl,substV (substV e i1 v1) i2 v2)
stepVal (s,(KMatch i1 e1 i2 e2):ktl,RVInl v) = do
  return $ Left (s,ktl,substV e1 i1 v)
stepVal (s,(KMatch i1 e1 i2 e2):ktl,RVInr v) = do
  return $ Left (s,ktl,substV e2 i2 v)
stepVal (s,(K1Prim p):ktl,v) = do
  (s2,v_or_e) <- applyPrim1 p (s,v)
  case v_or_e of
    Left v2 -> stepVal (s2,ktl,v2)
    Right e2 -> return $ Left (s,ktl,e2)
stepVal (s,(K2Prim1 p e):ktl,v) = do
  return $ Left (s,(K2Prim2 p v):ktl,e)
stepVal (s,(K2Prim2 p v1):ktl,v2) =
  stepVal (s,ktl,applyPrim2 p v1 v2)
stepVal (s,(KDup vs (ehd:etl) ips e2):ktl,v) = 
  return $ Left (s,(KDup (v:vs) etl ips e2):ktl,ehd)
stepVal (s,(KDup vs [] ips e2):ktl,v) = do
  let newvs = v:vs
  let vips = zip newvs ips
  return $ Left $ (foldl processExp s newvs,ktl,
            foldl processBinds e2 vips)
  where 
    processExp k v = 
      incr (locs v) k
    processBinds e2 (v,(i1,i2)) =
      substV (substV e2 i2 v) i1 v
stepVal (s,(KDrop vs (ehd:etl) e2):ktl,v) =
  return $ Left (s,(KDrop (v:vs) etl e2):ktl,ehd)
stepVal (s,(KDrop vs [] e2):ktl,v) = do
  return $ Left $ (foldl processVal s (v:vs),ktl,e2)
  where 
    processVal s v = 
      decr (locs v) s
stepVal (s,[],v) = do
  return $ Right (s,v)

applyPrim1 :: PrimOp1 -> (RuStore,RuVal) -> 
                RuMonad (RuStore,Either RuVal Expr)
applyPrim1 PrInl (s,v) =
  return (s,Left $ RVInl v)
applyPrim1 PrInr (s,v) =
  return (s,Left $ RVInr v)
applyPrim1 PrFst (s,RVWith e1 e2) =
  return (s,Right e1)
applyPrim1 PrSnd (s,RVWith e1 e2) =
  return (s,Right e2)
applyPrim1 PrFix (s,RVAbs q i e1) =
  return (s,Right $ subst e1 i (ExPrim1 PrFix (ExAbs q i e1)))
applyPrim1 PrWNew (s,v) = do
  lnum <- lift get
  put (lnum+1)
  return (M.insert lnum (v,1) s,Left $ RVLit (LiLab lnum))
applyPrim1 PrSNew (s,v) = do
  lnum <- lift get
  put (lnum+1)
  return (M.insert lnum (v,1) s,Left $ RVLit (LiLab lnum))
applyPrim1 PrRelease (s,RVLit (LiLab l)) = do
  case (M.lookup l s) of
    Just (sv,i) -> 
      if (i>1) then
        return (M.insert l (sv,i-1) s,Left $ RVInr (RVLit (LiUnit)))
      else
        return (M.delete l s,Left $ RVInl sv)
    Nothing -> error "bad release"
applyPrim1 PrSRelease (s,RVLit (LiLab l)) = do
  case (M.lookup l s) of
    Just (sv,i) -> 
      if (i>1) then
        error "strong release aliasing"
      else
        return (M.delete l s,Left $ sv)
    Nothing -> error "bad release"
applyPrim1 PrSwap (s,RVPair (RVLit (LiLab l)) v2) = do
  case (M.lookup l s) of
    Just (sv,i) -> 
      return (M.insert l (v2,i) s,Left $ RVPair (RVLit (LiLab l)) sv)
    Nothing -> error "bad swap"
applyPrim1 PrSSwap (s,RVPair (RVLit (LiLab l)) v2) = do
  case (M.lookup l s) of
    Just (sv,i) -> 
      if (i>1) then
        error "strong swap aliasing"
      else
        return (M.insert l (v2,i) s,Left $ RVPair (RVLit (LiLab l)) sv)
    Nothing -> error "bad swap"
  

applyPrim2 :: PrimOp2 -> RuVal -> RuVal -> RuVal
applyPrim2 PrPair v1 v2 = RVPair v1 v2
applyPrim2 p (RVLit (LiNum i1)) (RVLit (LiNum i2)) =
  (applyNumOp p i1 i2)
applyPrim2 PrOr r1 r2 = applyBoolOp PrOr r1 r2
applyPrim2 PrAnd r1 r2 = applyBoolOp PrAnd r1 r2


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

applyBoolOp :: PrimOp2 -> RuVal -> RuVal -> RuVal
applyBoolOp PrOr (RVInl _) _ = mkTrue
applyBoolOp PrOr (RVInr _) (RVInl _) = mkTrue
applyBoolOp PrOr (RVInr _) (RVInr _) = mkFalse
applyBoolOp PrOr _ _ = error "bad boolop application"
applyBoolOp PrAnd (RVInr _) _ = mkFalse
applyBoolOp PrAnd (RVInl _) (RVInr _) = mkFalse
applyBoolOp PrAnd (RVInl _) (RVInl _) = mkTrue
applyBoolOp PrAnd _ _ = error "bad boolop application"
