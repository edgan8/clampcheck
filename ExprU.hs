{-# LANGUAGE DeriveDataTypeable #-}

module ExprU(
  module Idx,
  Lit(..), PrimOp1(..), PrimOp2(..), AQual(..), Expr(..), 
  Decl(..),
  subst,
  renameIdxs,
  fv
) where
import Pretty
import Util
import Idx
import Data.Data
import Data.Generics

data Lit = 
    LiNum Int 
  | LiLab Int
  | LiUnit
  deriving (Show,Data,Typeable,Eq)

{- Primitive Operations are CBV builtin functions with
 - no special control properties -}

data PrimOp1 =
    PrInl
  | PrInr
  | PrFst
  | PrSnd
  | PrFix
  | PrWNew
  | PrSNew
  | PrRelease
  | PrSRelease
  | PrSwap
  | PrSSwap
  deriving (Show,Data,Typeable,Eq)

data PrimOp2 =
    PrPair
  | PrPlus
  | PrMinus
  | PrGt
  | PrLt
  | PrEqq
  | PrOr
  | PrAnd
  deriving (Show,Data,Typeable,Eq)

data AQual =
    AQU
  | AQR
  | AQA
  | AQL
  deriving (Show,Data,Typeable,Eq)

data Expr = 
    ExLit Lit
  | ExVar Idx 
  | ExGVar Idx
  | ExAbs AQual Idx Expr 
  | ExApp Expr Expr
  | ExLet Idx Expr Expr 
  | ExLetp Idx Idx Expr Expr
  | ExMatch Expr Idx Expr Idx Expr
  | ExWith Expr Expr
  | ExDup [Expr] [(Idx,Idx)] Expr
  | ExDrop [Expr] Expr
  | ExPrim1 PrimOp1 Expr
  | ExPrim2 PrimOp2 Expr Expr
  deriving (Show,Data,Typeable,Eq)

renameIdxs :: Expr -> [(Idx,Idx)] -> Expr
renameIdxs e ips =
  everywhere (mkT rename1Idx) e
  where
    rename1Idx i1 | (Just i2) <- lookup i1 ips = i2
                  | otherwise = i1

subst :: Expr -> Idx -> Expr -> Expr
subst e@(ExLit _) _ _ = e
subst (ExVar i) x es  
  | i == x = es
  | otherwise = ExVar i
subst e@(ExGVar g) x es
  | g == x = es
  | otherwise = ExGVar g
subst e@(ExAbs a i e1) x es 
  | i == x = e
  | otherwise = ExAbs a i (subst e1 x es)
subst (ExApp e1 e2) x es =
  ExApp (subst e1 x es) (subst e2 x es)
subst (ExLet i e1 e2) x es
  | i == x = ExLet i (subst e1 x es) e2
  | otherwise = ExLet i (subst e1 x es) (subst e2 x es)
subst (ExLetp i1 i2 e1 e2) x es
  | (i1==x || i2==x) = ExLetp i1 i2 (subst e1 x es) e2
  | otherwise = ExLetp i1 i2 (subst e1 x es) (subst e2 x es)
subst (ExMatch e i1 e1 i2 e2) x es
  | (i1==x && i2==x) = ExMatch (subst e x es) i1 e1 i2 e2
  | (i1==x) = ExMatch (subst e x es) i1 e1 i2 (subst e2 x es)
  | (i2==x) = ExMatch (subst e x es) i1 (subst e1 x es) i2 e2
  | otherwise = ExMatch (subst e x es)
                        i1 (subst e1 x es)
                        i2 (subst e2 x es)
subst (ExWith e1 e2) x es =
  ExWith (subst e1 x es) (subst e2 x es)
subst (ExDup el ips e2) x es
  | (any pairmatch ips) = 
    ExDup (map (\e -> subst e x es) el) ips e2
  | otherwise =
    ExDup (map (\e -> subst e x es) el) ips (subst e2 x es)
  where
    pairmatch (i1,i2) = (i1 == x || i2 ==x)
subst (ExDrop el e2) x es = 
  ExDrop (map (\e -> subst e x es) el) (subst e2 x es)
subst (ExPrim1 p e) x es = ExPrim1 p (subst e x es)
subst (ExPrim2 p e1 e2) x es = ExPrim2 p (subst e1 x es) (subst e2 x es)
    


---- Free Var Calculations ----

unioncat :: [[Idx]] -> [Idx]
unioncat ils = foldl union [] ils

-- SET of free variables
fv :: Expr -> [Idx]
fv (ExVar i) = [i]
fv (ExGVar i) = []
fv (ExLit l) = []
fv (ExPrim1 _ e) = fv e
fv (ExPrim2 _ e1 e2) = fv e1 `union` fv e2
fv (ExAbs aq i e) = delete i (fv e)
fv (ExApp e1 e2) = union (fv e1) (fv e2)
fv (ExLet i e1 e2) = union (fv e1) (delete i (fv e2))
fv (ExLetp i1 i2 e1 e2) = union (fv e1) (fv e2 \\ [i1,i2])
fv (ExMatch e i1 e1 i2 e2) = union (fv e) (union (i1 `delete` fv e1) (i2 `delete` fv e2))
fv (ExWith e1 e2) = fv e1 `union` fv e2
fv (ExDup des newvps e) = 
  let newvs = (uncurry union) (unzip newvps) in
  (unioncat (map fv des)) `union` (fv e \\ newvs)
fv (ExDrop des e) = (unioncat (map fv des)) `union` fv e

---- Declarations ----

data Decl = 
    DcLet Idx Expr
  deriving (Show,Data,Typeable,Eq)

---- Pretty Printing ----

-- Primitive Operator Pretty Printing
instance Pretty PrimOp1 where
  pretty (PrInl) = text "Left"
  pretty (PrInr) = text "Right"
  pretty (PrFst) = text "fst"
  pretty (PrSnd) = text "snd"
  pretty (PrFix) = text "fix"
  pretty (PrWNew) = text "wnew"
  pretty (PrSNew) = text "snew"
  pretty (PrRelease) = text "release"
  pretty (PrSRelease) = text "srelease"
  pretty (PrSwap) = text "swap"
  pretty (PrSSwap) = text "sswap"

instance Pretty PrimOp2 where
  pretty (PrPair) = text "pair"
  pretty (PrPlus) = text "+"
  pretty (PrMinus) = text "-"
  pretty (PrGt) = text ">"
  pretty (PrLt) = text "<"
  pretty (PrEqq) = text "=="
  pretty (PrAnd) = text " and "
  pretty (PrOr) = text " or "

instance Pretty AQual where
  pretty (AQU) = text "U"
  pretty (AQR) = text "R"
  pretty (AQA) = text "A"
  pretty (AQL) = text "L"

isInfix :: PrimOp2 -> Bool
isInfix PrPair = False
isInfix _ = True


-- precedences: 0 base level, 1 inside an app

instance Pretty Expr where
  pretty = pprExprPrec 0

pprIdList :: [Idx] -> Doc
pprIdList is = sep $ punctuate comma (map pretty is)
pprExprList :: [Expr] -> Doc
pprExprList es = sep $ punctuate comma (map pretty es)

pprIdPair :: (Idx,Idx) -> Doc
pprIdPair (i1,i2) = parens (pretty i1 <> comma <> pretty i2)
pprIdPairList :: [(Idx,Idx)] -> Doc
pprIdPairList is = sep $ punctuate comma (map pprIdPair is)

tin = text "in"
instance Pretty Lit where
  pretty (LiNum i) = int i
  pretty (LiLab i) = text "l"<>int i
  pretty (LiUnit) = text "()"

pprExprPrec :: Int -> Expr -> Doc
pprExprPrec p (ExLit l) = pretty l
pprExprPrec p (ExVar i) = pretty i
pprExprPrec p (ExGVar i) = pretty i
pprExprPrec p (ExAbs aq i e) = 
  let s = (text "\\")<+>(pretty i)<+>(nest 2 (text "-"<>pretty aq<>text ">"</>(pprExprPrec 0 e))) in
  addParen p 0 s
pprExprPrec p (ExApp e1 e2) = 
  let s = (pprExprPrec 1 e1)<+>(pprExprPrec 1 e2) in
  addParen p 0 s
pprExprPrec p (ExLet i e1 e2) = 
  let s = (text "let")<+>(pretty i)<+>equals<+>(pprExprPrec 0 e1)<+>(text "in")
            </>(pprExprPrec 0 e2) in
  addParen p 0 s
pprExprPrec p (ExLetp i1 i2 e1 e2) =
  let s = text "letp"<+>parens (pretty i1<>comma<>pretty i2)
            <+>equals<+>pprExprPrec 0 e1<+>tin
            </> pprExprPrec 0 e2 in
  addParen p 0 s
pprExprPrec p (ExMatch e i1 e1 i2 e2) =
  let s = text "case" <+> pprExprPrec 0 e<+> text "of" <> (nest 2 (line <>
            text "Left" <+> pretty i1 <+> text "->" <+> pprExprPrec 0 e1 
              <> text ";"</> 
            text "Right" <+> pretty i2 <+> text "->" <+> pprExprPrec 0 e2))
            in
  addParen p 0 s
pprExprPrec p (ExWith e1 e2) =
  brackets $ pprExprPrec 0 e1 <> comma <> pprExprPrec 0 e2
pprExprPrec p (ExDup xs xps e) =
  let s = text "dup" <+> (pprExprList xs) <+> text "as" 
          <+> (pprIdPairList xps) <+> tin </> pprExprPrec 0 e
      in
  addParen p 0 s
pprExprPrec p (ExDrop xs e) =
  let s = text "drop" <+> (pprExprList xs) <+> tin
          </> pprExprPrec 0 e
      in
  addParen p 0 s
pprExprPrec p (ExPrim1 pOp e) =
  let s = pretty pOp <+> pprExprPrec 0 e in
  addParen p 0 s
pprExprPrec p (ExPrim2 pOp e1 e2)
  | pOp == PrPair =
      parens $ (pprExprPrec 0 e1)<>comma<>(pprExprPrec 0 e2)
  | isInfix pOp  =
      let s = (pprExprPrec 0 e1)<>pretty pOp<>(pprExprPrec 0 e2) in
      addParen p 0 s
  | otherwise = 
      let s = pretty pOp <+> (pprExprPrec 1 e1) <+> (pprExprPrec 1 e2) in
      addParen p 0 s


instance Pretty Decl where
  pretty (DcLet i e) = text("let")<+>(pretty i)<+>equals<+>(pretty e)