{-# LANGUAGE DeriveDataTypeable #-}

module ExprU(
  module Idx,
  Lit(..), PrimOp1(..), PrimOp2(..), AQual(..), Expr(..), 
  Decl(..),
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
  | ExDup [Idx] [(Idx,Idx)] Expr
  | ExDrop [Idx] Expr
  | ExPrim1 PrimOp1 Expr
  | ExPrim2 PrimOp2 Expr Expr
  deriving (Show,Data,Typeable,Eq)

renameIdxs :: Expr -> [(Idx,Idx)] -> Expr
renameIdxs e ips =
  everywhere (mkT rename1Idx) e
  where
    rename1Idx i1 | (Just i2) <- lookup i1 ips = i2
                  | otherwise = i1

---- Free Var Calculations ----

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
fv (ExDup dvs newvps e) = 
  let newvs = (uncurry union) (unzip newvps) in
  union dvs (fv e \\ newvs)
fv (ExDrop dvs e) = dvs `union` fv e

---- Declarations ----

data Decl = 
    DcLet Idx Expr
  deriving (Show,Data,Typeable,Eq)

---- Pretty Printing ----

-- Primitive Operator Pretty Printing
instance Pretty PrimOp1 where
  pretty (PrInl) = text "inl"
  pretty (PrInr) = text "inr"
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

pprIdPair :: (Idx,Idx) -> Doc
pprIdPair (i1,i2) = parens (pretty i1 <> comma <> pretty i2)
pprIdPairList :: [(Idx,Idx)] -> Doc
pprIdPairList is = sep $ punctuate comma (map pprIdPair is)

tin = text "in"

pprExprPrec :: Int -> Expr -> Doc
pprExprPrec p (ExLit (LiNum i)) = int i
pprExprPrec p (ExLit (LiUnit)) = text "unit"
pprExprPrec p (ExVar i) = pretty i
pprExprPrec p (ExGVar i) = pretty i
pprExprPrec p (ExAbs aq i e) = 
  let s = (text "fun")<+>(pretty i)<+>(nest 2 (text "-"<>pretty aq<>text ">"</>(pprExprPrec 0 e))) in
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
  let s = text "match" <+> pprExprPrec 0 e<+> text "with" <> (nest 2 (line <>
            text "inl" <+> pretty i1 <+> text "->" <+> pprExprPrec 0 e1 </> 
            text "| inr" <+> pretty i2 <+> text "->" <+> pprExprPrec 0 e2))
            in
  addParen p 0 s
pprExprPrec p (ExWith e1 e2) =
  brackets $ pprExprPrec 0 e1 <> comma <> pprExprPrec 0 e2
pprExprPrec p (ExDup xs xps e) =
  let s = text "dup" <+> (pprIdList xs) <+> text "as" 
          <+> (pprIdPairList xps) <+> tin </> pprExprPrec 0 e
      in
  addParen p 0 s
pprExprPrec p (ExDrop xs e) =
  let s = text "drop" <+> (pprIdList xs) <+> tin
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