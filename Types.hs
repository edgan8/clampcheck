{- Much of the source code in this file was adopted from M.P. Jones,
 - "Typing Haskell in Haskell" -}

module Types (
  Kind(..), Type(..), TypeVar(..), TypeCon,
  HasKind(..),
  Qual(..), Pred(..),Scheme(..),
  quantify,toScheme,sepQuals,

  Subst(..), snull, smap, Types(..), scomp, smerge,

  mgu, mguPred, varBind, match, matchPred,

  -- fake types to support polymorphism
  tUU, tRU, tAU, tLU, tS, tW,
  tInt, tArrow, tPair, tUnit,
  tSum, tChoice, tBool,
  tRef, tList,
  mkArrow, mkPair, mkStarVar,
  mkSum, mkChoice,
  mkDup, mkDrop, mkUnl,
  mkRef, mkList,
  module Idx
) where

import Pretty
import Util
import Idx
import Data.Data
import Data.Generics

-- Basic Type Datatypes

data Kind = Star | KArr Kind Kind
  deriving (Eq,Show)

data Type =
    TyVar TypeVar
  | TyCon TypeCon
  | TyApp Type Type
  | TyQuant Int
  deriving (Eq,Show)

data TypeVar = TVar Idx Kind
  deriving (Eq,Show)
data TypeCon = TCon Idx Kind
  deriving (Eq,Show)

class HasKind t where
  kind :: t -> Kind

instance HasKind TypeVar where
  kind (TVar i k) = k
instance HasKind TypeCon where
  kind (TCon i k) = k
instance HasKind Type where
  kind (TyVar tv) = kind tv
  kind (TyCon tc) = kind tc
  kind (TyApp t1 _) =
    case (kind t1) of
      (KArr _ k2) -> k2

-- Typeclasses and Schemes
data Qual t = [Pred] :=> t
  deriving (Eq,Show)
data Pred = Pred Idx Type
  deriving (Eq,Show)
data Scheme = Forall [Kind] (Qual Type)
  deriving (Eq,Show)

quantify :: [TypeVar] -> Qual Type -> Scheme
quantify vs qt = Forall ks (apply s qt)
  where
  orderedvs = (tv qt) `intersect` vs
  ks = map kind orderedvs
  s = zip orderedvs (map TyQuant [0..])

toScheme :: Type -> Scheme
toScheme t = Forall [] ([] :=> t)

sepQuals :: [Qual Type] -> ([Pred],[Type])
sepQuals qts = 
  let (prdlsts, ts) = unzip $ map (\(a:=>b) -> (a,b)) qts in
  (concat prdlsts, ts)
-- Substitutions

type Subst = [(TypeVar, Type)]

snull :: Subst
snull = []
smap :: TypeVar -> Type -> Subst
smap u t = [(u,t)]

class Types t where
  apply :: Subst -> t -> t
  tv :: t -> [TypeVar]

instance Types Type where
  apply s (TyVar u) 
    | Just t <- lookup u s = t
    | otherwise = TyVar u
  apply s (TyApp l r) = TyApp (apply s l) (apply s r)
  apply s t = t

  tv (TyVar u) = [u]
  tv (TyApp l r ) = union (tv l) (tv r)
  tv _ = []

instance Types Pred where
  apply s (Pred i t) = Pred i (apply s t)
  tv (Pred i t) = tv t
instance Types t => Types (Qual t) where
  apply s (ps :=> t) = (apply s ps) :=> apply s t
  tv (ps :=> t) = tv ps `union` tv t
instance Types Scheme where
  apply s (Forall ks qt) = Forall ks (apply s qt)
  tv (Forall ks qt) = tv qt

instance Types a => Types [a] where
  apply s = map (apply s)
  tv = nub . concat . map tv

scomp :: Subst -> Subst -> Subst
scomp s1 s2  = [ (u, apply s1 t) | (u,t) <- s2 ] ++ s1

smerge :: Monad m => Subst -> Subst -> m Subst
smerge s1 s2 = if agree then return (s1++s2) else fail "merge fails"
 where agree = all (\v -> apply s1 (TyVar v) == apply s2 (TyVar v))
                   (map fst s1 `intersect` map fst s2)

-- Unification

mgu :: Monad m => Type -> Type -> m Subst
mgu (TyApp l r) (TyApp l' r') = do
  s1 <- mgu l l'
  s2 <- mgu (apply s1 r) (apply s1 r')
  return (scomp s2 s1)
mgu (TyVar u) t = varBind u t
mgu t (TyVar u) = varBind u t
mgu (TyCon c1) (TyCon c2)
  | c1==c2 = return snull
mgu t1 t2 = fail $ "types do not unify:"++(myshow t1)++","++(myshow t2)

liftp m (Pred i1 t1) (Pred i2 t2)
  | i1 == i2 = m t1 t2
  | otherwise = fail $ "differring classes:"++(myshow i1)++","++(myshow i2)

mguPred :: Monad m => Pred -> Pred -> m Subst
mguPred = liftp mgu

varBind :: Monad m => TypeVar -> Type -> m Subst
varBind u t =
  if (t == TyVar u) then
    return snull
  else if (kind u /= kind t) then
    fail $ "kinds do not match:"++(myshow u)++","++(myshow t)
  else if (elem u (tv t)) then
    fail "occurs check fails"
  else
    return $ smap u t

match :: Monad m => Type -> Type -> m Subst
match (TyApp l r) (TyApp l' r') = do
  s1 <- match l l'
  s2 <- match r r'
  smerge s1 s2
match (TyVar u) t = varBind u t
match (TyCon tc1) (TyCon tc2)
  | tc1 == tc2 = return snull
match _ _ = fail "match failed"

matchPred :: Monad m => Pred -> Pred -> m Subst
matchPred = liftp match

-- prettyprinting

taqpretty :: Type -> Doc
taqpretty aq = 
    if (aq==tUU) then
      text "U" 
    else if(aq==tRU) then
      text "R"
    else if(aq==tAU) then
      text "A"
    else if(aq==tLU) then
      text "L"
    else
      braces $ pretty aq

instance Pretty TypeVar where
  pretty (TVar i k) = pretty i
instance Pretty TypeCon where
  pretty (TCon i k) = pretty i
instance Pretty Type where
  pretty = pprTypePrec 0
instance Pretty Pred where
  pretty (Pred i t) = pretty i <+> pretty t
pprPList :: [Pred] -> Doc
pprPList ps = sep $ punctuate comma (map pretty ps)
instance Pretty t => Pretty (Qual t) where
  pretty ([] :=> t) = pretty t
  pretty (qs :=> t) = pprPList qs <+> text "=>" <> (nest 2 (line <> pretty t))
instance Pretty Scheme where
  pretty (Forall ks qt) = {-text "forall"<+> pretty ks <+> dot <> -}pretty qt
instance Pretty Kind where
  pretty Star = text "*"
  pretty (KArr k1 k2) = pretty k1 <> text "->" <> pretty k2

pprTypePrec :: Int -> Type -> Doc
pprTypePrec p (TyVar u) = pretty u
pprTypePrec p (TyCon tc) = pretty tc
pprTypePrec p (TyApp t1 t2)
  | (TyApp (TyApp (TyCon (TCon (IdS "arrow") _)) aq ) t11) <- t1 = 
    let s = pprTypePrec 1 t11 
              <+>text "-"<>taqpretty aq<>text ">"
              <+> pprTypePrec 0 t2 in
    addParen p 0 s
  | otherwise = 
    let s = pprTypePrec 0 t1 <+> pprTypePrec 1 t2 in
    addParen p 0 s
pprTypePrec p (TyQuant i) = int i


-- primitive builtins

newTy :: String -> Type
newTy s = TyCon (TCon (IdS s) Star)
newTyCon :: String -> Type
newTyCon s = TyCon (TCon (IdS s) (KArr Star Star))
newTyCon2 :: String -> Type
newTyCon2 s = TyCon (TCon (IdS s) (KArr Star (KArr Star Star)))
newTyCon3 :: String -> Type
newTyCon3 s = TyCon (TCon (IdS s) (KArr Star (KArr Star (KArr Star Star))))

tInt = newTy "int"
tUnit = newTy "unit"

tUU = newTy "UUnit"
tRU = newTy "RUnit"
tAU = newTy "AUnit"
tLU = newTy "LUnit"

tS = newTy "Strong"
tW = newTy "Weak"

-- Arrows take in an environment type as first arg
tArrow = newTyCon3 "arrow"
tPair = newTyCon2 "pair"
tChoice = newTyCon2 "choice"
tSum = newTyCon2 "sum"
tRef = newTyCon2 "ref"
tList = newTyCon "list"

tBool = mkSum tUnit tUnit

appCon :: Type -> Type -> Type
appCon tc t1 = TyApp tc t1
appCon2 :: Type -> Type -> Type -> Type
appCon2 tc t1 t2 = TyApp (TyApp tc t1) t2
appCon3 :: Type -> Type -> Type -> Type -> Type
appCon3 tc t1 t2 t3 = TyApp (TyApp (TyApp tc t1) t2) t3

mkArrow :: Type -> Type -> Type -> Type
mkArrow = appCon3 tArrow
mkPair :: Type -> Type -> Type
mkPair = appCon2 tPair
mkChoice :: Type -> Type -> Type
mkChoice = appCon2 tChoice
mkSum :: Type -> Type -> Type
mkSum = appCon2 tSum
mkRef :: Type -> Type -> Type
mkRef = appCon2 tRef
mkList :: Type -> Type
mkList = appCon tList


mkStarVar :: String -> Type
mkStarVar s = TyVar (TVar (IdS s) Star)

-- Builtin Predicates

mkDup :: Type -> Pred
mkDup t = Pred (IdS "Dup") t
mkDrop :: Type -> Pred
mkDrop t = Pred (IdS "Drop") t
mkUnl :: Type -> [Pred]
mkUnl t = [mkDup t, mkDrop t]

-- test types

t1 = mkPair (mkPair tInt tInt) tInt
t2 = mkPair (mkStarVar "a") tInt

