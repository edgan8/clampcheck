{- Part of the source code in this file was adopted from M.P. Jones,
 - "Typing Haskell in Haskell" -}

module Infer (
  Assump(..),
  elookup,getType,
  Instantiable(..),
  TI(..), initTI, InferRet(..), Infer(..),
  tiLit, tiExpr, split, tiDeclT, tiProgT,
  initAS
) where

import Pretty
import Util
import Idx
import Types
import Classes
import ExprU
import Run
import Debug.Trace

----Type Inference Monad----
data Assump = AMap Idx Scheme
  deriving (Show)

instance Types Assump where
  apply s (AMap i tsc) = AMap i (apply s tsc)
  tv (AMap i tsc) = tv tsc
instance Pretty Assump where
  pretty (AMap i tsc) = pretty i <> text ":" <+> pretty tsc

elookup :: Monad m => Idx -> [Assump] -> m Scheme
elookup (IdS is) [] = fail ("unbound id: "++(is))
elookup i ((AMap curi tsc):as)
  | i==curi = return tsc
  | otherwise = elookup i as

getType :: [Assump] -> Idx -> TI (Qual Type)
getType as i = do
  tsch <- elookup i as
  freshInst tsch

type TI a = State (Subst,Int) a

initTI :: (Subst,Int)
initTI = ([],0)

getSubst :: TI Subst
getSubst = do
  (s,_) <- get
  return s
incCounter :: TI Int
incCounter = do
  (s,i) <- get
  put (s,i+1)
  return i

extSubst :: Subst -> TI ()
extSubst news = modify (\(s,i)->(scomp news s,i))

newTVar :: Kind -> TI Type
newTVar k = do
  i <- incCounter
  return $ TyVar (TVar (IdS ("__v"++(show i))) k)

freshInst :: Scheme -> TI (Qual Type)
freshInst s@(Forall ks qt) = do
  ts <- mapM newTVar ks
  return ((inst ts qt))

unify :: Type -> Type -> TI ()
unify t1 t2 = do
  s <- getSubst
  s2 <- mgu (apply s t1) (apply s t2)
  extSubst s2


-- substitube out TyQuant variables
class Instantiable t where
  inst :: [Type] -> t -> t

instance Instantiable Type where
  inst ts (TyApp l r) = TyApp (inst ts l) (inst ts r)
  inst ts (TyQuant i) = ts!!i
  inst ts t = t

instance Instantiable a => Instantiable [a] where
  inst ts = map (inst ts)

instance Instantiable t => Instantiable (Qual t) where
  inst ts (ps :=> t) = inst ts ps :=> inst ts t

instance Instantiable Pred where
  inst ts (Pred c t) = Pred c (inst ts t)

data InferRet t = InferRet {irpreds :: [Pred], irt :: t}
type Infer e t = ClassEnv -> [Assump] -> e -> TI (InferRet t)

tiLit :: Lit -> InferRet Type
tiLit (LiNum i) = InferRet {irpreds=[], irt=tInt}
tiLit (LiUnit) = InferRet {irpreds=[], irt=tUnit}

retType :: Type -> InferRet Type
retType t = InferRet {irpreds=[], irt=t}

intop :: Type -> Type -> TI Type
intop t1 t2 = do
  unify t1 tInt
  unify t2 tInt
  return tInt

intpred :: Type -> Type -> TI Type
intpred t1 t2 = do
  unify t1 tInt
  unify t2 tInt
  return tBool

boolop :: Type -> Type -> TI Type
boolop t1 t2 = do
  unify t1 tBool
  unify t2 tBool
  return tBool

tiPrim2 :: PrimOp2 -> Type -> Type -> TI Type
tiPrim2 PrPair t1 t2 = return $ mkPair t1 t2
tiPrim2 PrPlus t1 t2 = intop t1 t2
tiPrim2 PrMinus t1 t2 = intop t1 t2
tiPrim2 PrGt t1 t2 = intpred t1 t2
tiPrim2 PrLt t1 t2 = intpred t1 t2
tiPrim2 PrEqq t1 t2 = intpred t1 t2
tiPrim2 PrAnd t1 t2 = boolop t1 t2
tiPrim2 PrOr t1 t2 = boolop t1 t2

tiPrim1 :: PrimOp1 -> Type -> TI (InferRet Type)
tiPrim1 PrInl t = do
  newtv <- newTVar Star
  return $ retType (mkSum t newtv)
tiPrim1 PrInr t = do
  newtv <- newTVar Star
  return $ retType (mkSum newtv t)
tiPrim1 PrFst t = do
  t1 <- newTVar Star
  t2 <- newTVar Star
  unify t (mkChoice t1 t2)
  return $ retType t1
tiPrim1 PrSnd t = do
  t1 <- newTVar Star
  t2 <- newTVar Star
  unify t (mkChoice t1 t2)
  return $ retType t2
tiPrim1 PrFix t = do
  t1 <- newTVar Star
  unify t (mkArrow tUU t1 t1)
  return $ retType t1
tiPrim1 PrSNew t = do
  return $ retType (mkRef tS t)
tiPrim1 PrWNew t = do
  return $ retType (mkRef tW t)
tiPrim1 PrRelease t = do
  rq <- newTVar Star
  t1 <- newTVar Star
  unify t (mkRef rq t1)
  return $ retType (mkSum t1 tUnit)
tiPrim1 PrSRelease t = do
  t1 <- newTVar Star
  unify t (mkRef tS t1)
  return $ retType t1
tiPrim1 PrSwap t = do
  t1 <- newTVar Star
  rq <- newTVar Star
  unify t (mkPair (mkRef rq t1) t1)
  return $ retType t
tiPrim1 PrSSwap t = do
  t1 <- newTVar Star
  t2 <- newTVar Star
  unify t (mkPair (mkRef tS t1) t2)
  return $ retType $ mkPair (mkRef tS t2) t1

tiExpr :: Infer Expr Type

tiExpr ce as (ExLit l) = return $ tiLit l

tiExpr ce as (ExVar i) = do
  sc <- elookup i as
  (ps :=> t) <- freshInst sc
  return $ InferRet {irpreds=ps,irt=t}

tiExpr ce as (ExGVar i) = do
  sc <- elookup i as
  (ps :=> t) <- freshInst sc
  return $ InferRet {irpreds=ps,irt=t}

tiExpr ce as elam@(ExAbs aq i e) = do
  newtv <- newTVar Star
  let newas = AMap i (toScheme newtv)
  InferRet {irpreds=retp, irt=rett} <- tiExpr ce (newas:as) e

  -- Create Closure Type
  let envfvs = fv elam
  envqts <- mapM (getType as) envfvs
  let (envpreds, envts) = sepQuals envqts
  let funpreds = case aq of
                      AQU -> (map mkDup envts)++(map mkDrop envts)
                      AQR -> map mkDup envts
                      AQA -> map mkDrop envts
                      AQL -> []
  return $ InferRet {irpreds=envpreds++retp++funpreds,
                    irt=mkArrow (atqual aq) newtv rett}
  where
    atqual AQU = tUU
    atqual AQR = tRU
    atqual AQA = tAU
    atqual AQL = tLU

tiExpr ce as (ExApp e1 e2) = do
  InferRet {irpreds=e1p, irt=e1t} <- tiExpr ce as e1
  InferRet {irpreds=e2p, irt=e2t} <- tiExpr ce as e2
  rettv <- newTVar Star
  envtv <- newTVar Star
  unify (mkArrow envtv e2t rettv) e1t
  return $ InferRet {irpreds=e1p++e2p, irt=rettv}

tiExpr ce as (ExLet i e1 e2) = do
  InferRet {irpreds=e1p, irt=e1as} <- tiDecl ce as (DcLet i e1)
  InferRet {irpreds=e2p, irt=e2t} <- tiExpr ce (e1as:as) e2
  return $ InferRet {irpreds=e1p++e2p, irt=e2t}

tiExpr ce as (ExLetp i1 i2 e1 e2) = do
  InferRet {irpreds=e1p, irt=e1t} <- tiExpr ce as e1
  newtv1 <- newTVar Star
  newtv2 <- newTVar Star
  let pairt = mkPair newtv1 newtv2
  unify pairt e1t
  let newas = [AMap i1 (toScheme newtv1), AMap i2 (toScheme newtv2)]
  InferRet {irpreds=e2p, irt=e2t} <- tiExpr ce (newas++as) e2
  return $ InferRet {irpreds = e1p++e2p, irt=e2t}

tiExpr ce as (ExMatch e i1 e1 i2 e2) = do
  InferRet {irpreds=ep, irt=et} <- tiExpr ce as e
  newtv1 <- newTVar Star
  newtv2 <- newTVar Star
  let sumt = mkSum newtv1 newtv2
  unify sumt et
  let i1as = AMap i1 (toScheme newtv1)
  let i2as = AMap i2 (toScheme newtv2)
  InferRet {irpreds=e1p, irt=e1t} <- tiExpr ce (i1as:as) e1
  InferRet {irpreds=e2p, irt=e2t} <- tiExpr ce (i2as:as) e2
  unify e1t e2t
  return $ InferRet {irpreds = ep++e1p++e2p, irt=e1t}

tiExpr ce as (ExWith e1 e2) = do
  InferRet {irpreds=e1p, irt=e1t} <- tiExpr ce as e1
  InferRet {irpreds=e2p, irt=e2t} <- tiExpr ce as e2
  return $ InferRet {irpreds=e1p++e2p, irt=mkChoice e1t e2t}

-- First instantiate schemes, then apply dup constraint to type instances
-- but rebind to original schemes, since we don't want to lose polymorphism thorugh
-- a dup, e.g. a dup acts as a let-generalizable location
tiExpr ce as (ExDup dupes newvs e) = do
  let dupvs = map (\(ExVar i) -> i) dupes
  dupvtschs <- mapM (\i -> elookup i as) dupvs
  dupvqts <- mapM freshInst dupvtschs
  let (dupvPrds, dupvTyps) = sepQuals dupvqts
  let duppreds = map mkDup dupvTyps
  let newvtpairs = zip newvs dupvtschs
  let newas = concat $ map (\((i1,i2),t) -> [AMap i1 t, AMap i2 t]) newvtpairs
  InferRet {irpreds=ep, irt=et} <- tiExpr ce (newas++as) e
  return $ InferRet {irpreds=(dupvPrds++duppreds++ep), irt=et}

tiExpr ce as (ExDrop dropes e) = do
  let dropvs = map (\(ExVar i ) -> i) dropes
  dropvtschs <- mapM (\i -> elookup i as) dropvs
  dropvqts <- mapM freshInst dropvtschs
  let (dropvPrds, dropvTyps) = sepQuals dropvqts
  let droppreds = map mkDrop dropvTyps
  InferRet {irpreds=ep, irt=et} <- tiExpr ce as e
  return $ InferRet {irpreds=(dropvPrds++droppreds++ep), irt=et}

tiExpr ce as (ExPrim1 pOp e) = do
  InferRet {irpreds=ep, irt=et} <- tiExpr ce as e
  InferRet{irpreds=opp, irt=opt} <- tiPrim1 pOp et
  return $ InferRet {irpreds=ep++opp, irt=opt}

tiExpr ce as (ExPrim2 pOp e1 e2) = do
  InferRet {irpreds=e1p, irt=e1t} <- tiExpr ce as e1
  InferRet {irpreds=e2p, irt=e2t} <- tiExpr ce as e2
  rett <- tiPrim2 pOp e1t e2t
  return $ InferRet {irpreds=e1p++e2p, irt=rett}

tiExprQT ce as e = do
  InferRet {irpreds=p,irt=t} <- tiExpr ce as e
  return (p,t)
---- Type Generalization ----

split :: Monad m => ClassEnv -> [TypeVar] -> [TypeVar] -> [Pred]
                  -> m ([Pred],[Pred])

split ce fixvs quantvs ps = do
  ps' <- reduce ce ps
  return $ partition testfixedpred ps'
  where
    -- Only include predicates that might be of use, e.g. ones
    -- which have nonfixed variables
    testfixedpred p = all (`elem` fixvs) (tv p)

---- Declaration Inference, used at let binding sites ----
tiDecl :: Infer Decl Assump
tiDecl ce as (DcLet i e) 
  -- Note Value restriction on generalization
  | isGeneralizable e = do
    eir <- tiExpr ce as e
    s <- getSubst
    let epreds = apply s (irpreds eir)
        ety = apply s (irt eir)
        fvs = tv (apply s as)
        quantvs = tv ety \\ fvs
    (dpreds,rpreds) <- {-trace (show "----\ni:"++"ty:"++(show $ pretty ety)++"env:"++(show as)) -}
                          split ce fvs quantvs epreds
    let tsc = quantify quantvs (rpreds :=> ety)
    return $ InferRet {irpreds=dpreds,irt=AMap i tsc}
  | otherwise = do
    InferRet {irpreds=retp,irt=rett} <- tiExpr ce as e
    return $ InferRet {irpreds=retp,irt=AMap i (toScheme rett)}


tiDeclT :: ClassEnv -> [Assump] -> Idx -> Expr -> Assump
tiDeclT ce as i e =
  let (inferret, (subst,counter)) = runState (tiDecl ce as (DcLet i e)) initTI in
  let epreds = apply subst (irpreds inferret)
      eas = apply subst (irt inferret)
      in
  case epreds of
    [] -> eas
    _ -> eas

---- Program Inference ----

tiProgT :: ClassEnv -> [Assump] -> [Decl] -> [Assump]
tiProgT ce as decls =
    foldl addDecl [] decls 
  where 
    addDecl newAs (DcLet i e) = (tiDeclT ce (newAs++as) i e) : newAs

---- Initial Assumption Environment ----

mkQList i = mkList (TyQuant i)

initAS :: [Assump]
initAS = [
          AMap (IdS "@l_nil") 
            (Forall [Star] ([] :=> mkQList 0)),
          AMap (IdS "@l_unfold") 
            (Forall [Star] ([] :=> mkArrow tUU (mkQList 0) (mkSum 
                                    (mkPair (TyQuant 0) (mkQList 0)) 
                                    tUnit)
            )),
          AMap (IdS "@l_cons") 
            (Forall [Star] ([] :=> mkArrow tUU (mkPair (TyQuant 0) (mkQList 0)) (mkQList 0)
            )),
          AMap (IdS "@lunit") 
            (toScheme tLU),
          AMap (IdS "@ldispose") 
            (toScheme (mkArrow tUU tLU tUnit))
          ] 
