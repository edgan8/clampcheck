module Annot(
  annotExpr
) where
import Util
import ExprU
import qualified Data.Map as M


type AnCtx = [Idx]

-- Monad for renaming in generating dups, allows for gensym
type AS = M.Map Idx Int
type AnRename a = State AS a

initAS = M.empty

-- Gensym a name
freshName :: Idx -> AnRename Idx
freshName i = do
  m <- get
  let cnt = M.findWithDefault 0 i m
  put $ M.alter (\_ -> Just (cnt+1)) i m
  return $ mkIdx i cnt

-- Insert possibly empty dups and drops
insertDup :: AnCtx -> [(Idx,Idx)] -> Expr -> Expr
insertDup [] _ e = e
insertDup xs@(x:tl) xps e = ExDup xs xps e

insertDrop :: AnCtx -> Expr -> Expr
insertDrop [] e = e
insertDrop xs@(x:tl) e = ExDrop xs e


annotExpr :: Expr -> Expr
annotExpr e = snd $ evalState (annotExprM e) initAS

-- If we bind i in an expression with fv c, return
-- remaining fv and possible drop context
dropBindCtx :: Idx -> AnCtx -> (AnCtx, AnCtx)
dropBindCtx i c =
  let dropi = not $ i `elem` c in
  if dropi then (c,[i]) else (delete i c,[])

-- If we take the product of two contexts, return
-- combined fv and possible dup context
dupProdCtx :: AnCtx -> AnCtx -> (AnCtx, AnCtx)
dupProdCtx c1 c2 = (c1 `union` c2, c1 `intersect` c2)

-- If we take the sum of two contexts, return
-- combined fv, and two possible drop contexts
dropSumCtxs :: AnCtx -> AnCtx -> (AnCtx, AnCtx, AnCtx)
dropSumCtxs c1 c2 = (c1 `union` c2, c2 \\ c1, c1 \\ c2)

-- given a common set of fvs across two expressions, rename them
renameProd :: AnCtx -> Expr -> Expr -> AnRename ([(Idx,Idx)],Expr,Expr)
renameProd dupc e1 e2 = do
  newCtx1 <- mapM freshName dupc
  newCtx2 <- mapM freshName dupc
  let renE1 = renameIdxs e1 (zip dupc newCtx1)
  let renE2 = renameIdxs e2 (zip dupc newCtx2)
  let dupXs = zip newCtx1 newCtx2
  return (dupXs,renE1,renE2)

-- Return the minimal free environment an expression needs + its annotated form
-- Annotations should NOT change the minimal free env needed, and AnCtx
-- should always contain original uservar names, not gensymd names

annotExprM :: Expr -> AnRename (AnCtx,Expr)

annotExprM e@(ExLit _) = return ([],e)
annotExprM e@(ExVar i) = return ([i],e)
annotExprM e@(ExGVar _) = return ([],e)

annotExprM (ExAbs aq i e1) = do
  (e1Ctx, e1Annot) <- annotExprM e1
  let (retCtx,dropCtx) = dropBindCtx i e1Ctx
  let retExp = ExAbs aq i (insertDrop dropCtx e1Annot)
  return (retCtx, retExp)

annotExprM (ExApp e1 e2) = do
  (e1Ctx, e1Annot) <- annotExprM e1
  (e2Ctx, e2Annot) <- annotExprM e2
  let (retCtx,dupCtx) = dupProdCtx e1Ctx e2Ctx

  (dupXs,renE1Annot,renE2Annot) <- renameProd dupCtx e1Annot e2Annot
  let appExpr = ExApp renE1Annot renE2Annot
  return (retCtx,insertDup dupCtx dupXs appExpr)

-- isomorphic to (\i.e2) * e1
annotExprM (ExLet i e1 e2) = do
  (e1Ctx, e1Annot) <- annotExprM e1
  (e2Ctx, e2Annot) <- annotExprM e2

  let (e2iCtx,e2iDropCtx) = dropBindCtx i e2Ctx
  let e2iAnnot = insertDrop e2iDropCtx e2Annot

  let (retCtx,dupCtx) = dupProdCtx e2iCtx e1Ctx
  (dupXs,renE1Annot,renE2iAnnot) <- renameProd dupCtx e1Annot e2iAnnot
  let letExpr = ExLet i renE1Annot renE2iAnnot
  return (retCtx,insertDup dupCtx dupXs letExpr)

annotExprM (ExLetp i1 i2 e1 e2) = do
  (e1Ctx, e1Annot) <- annotExprM e1
  (e2Ctx, e2Annot) <- annotExprM e2

  let (e2iCtx,e2iDropCtx) = dropBindCtx i1 e2Ctx
  let (e2iiCtx,e2iiDropCtx) = dropBindCtx i2 e2iCtx
  let e2CombinedDropCtx = e2iDropCtx `union` e2iiDropCtx
  let e2iAnnot = insertDrop e2CombinedDropCtx e2Annot

  let (retCtx,dupCtx) = dupProdCtx e2iiCtx e1Ctx
  (dupXs,renE1Annot,renE2iAnnot) <- renameProd dupCtx e1Annot e2iAnnot
  let letpExpr = ExLetp i1 i2 renE1Annot renE2iAnnot
  return (retCtx,insertDup dupCtx dupXs letpExpr)

annotExprM (ExMatch e i1 e1 i2 e2) = do
  (eCtx, eAnnot) <- annotExprM e
  (e1Ctx, e1Annot) <- annotExprM e1
  (e2Ctx, e2Annot) <- annotExprM e2
  let (e1iCtx,e1iDropCtx) = dropBindCtx i1 e1Ctx
      (e2iCtx,e2iDropCtx) = dropBindCtx i2 e2Ctx
      -- Insert drops for binding of individual identifiers
      e1iAnnot = insertDrop e1iDropCtx e1Annot
      e2iAnnot = insertDrop e2iDropCtx e2Annot
      -- Insert drops baesd on branching
      (branchCtx,bDropCtx1,bDropCtx2) = dropSumCtxs e1iCtx e2iCtx
      e1brAnnot = insertDrop bDropCtx1 e1iAnnot
      e2brAnnot = insertDrop bDropCtx2 e2iAnnot
      -- Insert dup based on match expression
      (retCtx,dupCtx) = dupProdCtx eCtx branchCtx
  -- hack: temporarily make branches into with to rename
  (dupXs,eRen,brRen) <- renameProd dupCtx eAnnot (ExWith e1brAnnot e2brAnnot)
  let (ExWith e1BrRen e2BrRen) = brRen
  let matchExpr = ExMatch eRen i1 e1BrRen i2 e2BrRen
  return (retCtx,insertDup dupCtx dupXs matchExpr)

annotExprM (ExWith e1 e2) = do
  (e1Ctx, e1Annot) <- annotExprM e1
  (e2Ctx, e2Annot) <- annotExprM e2

  let (retCtx,dropCtx1,dropCtx2) = dropSumCtxs e1Ctx e2Ctx
  let withExpr = ExWith (insertDrop dropCtx1 e1Annot) (insertDrop dropCtx2 e2Annot)
  return (retCtx,withExpr)

annotExprM (ExPrim1 pOp e) = do
  (eCtx,eAnnot) <- annotExprM e
  return (eCtx,ExPrim1 pOp eAnnot)

annotExprM (ExPrim2 pOp e1 e2) = do
  (e1Ctx, e1Annot) <- annotExprM e1
  (e2Ctx, e2Annot) <- annotExprM e2
  let (retCtx,dupCtx) = dupProdCtx e1Ctx e2Ctx

  (dupXs,renE1Annot,renE2Annot) <- renameProd dupCtx e1Annot e2Annot
  let primExpr = ExPrim2 pOp renE1Annot renE2Annot
  return (retCtx,insertDup dupCtx dupXs primExpr)
