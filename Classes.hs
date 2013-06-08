{- Much of the source code in this file was adopted from M.P. Jones,
 - "Typing Haskell in Haskell" -}

module Classes(
  Inst, Class, ClassEnv,
  defined, super, insts,
  reduce,
  initialEnv,addCoreInsts,
  coreEnv
) where

import Pretty
import Util
import Idx
import Types
import Control.Arrow

type Inst = Qual Pred
type Class = ([Idx],[Inst])

type ClassEnv = Idx -> Maybe Class
super :: ClassEnv -> Idx -> [Idx]
super ce i
  | Just (supers,instl) <- (ce i) = supers
insts :: ClassEnv -> Idx -> [Inst]
insts ce i
  | Just (supers,instl) <- (ce i) = instl

defined :: Maybe a -> Bool
defined (Just _ ) = True
defined Nothing = False

cmodify :: ClassEnv -> Idx -> Class -> ClassEnv
cmodify ce i c = \j -> 
  if i == j then Just c
    else ce j

initialEnv :: ClassEnv
initialEnv i = fail "class not defined"

type EnvT = Kleisli Maybe ClassEnv ClassEnv

addClass :: String -> [String] -> EnvT
addClass c scs = 
  let i = IdS c in
  let is = map IdS scs in
  Kleisli (\ce ->
  if (defined (ce i)) then
    fail "class already defined"
  else if(any (not . defined . ce) is) then
    fail "superclass not defined"
  else
    return $ cmodify ce i (is, [])
  )

overlap :: Pred -> Pred -> Bool
overlap p q = defined (mguPred p q)

addInst :: [Pred] -> Pred -> EnvT
addInst ps p@(Pred i _) = Kleisli (\ce ->
  let its = insts ce i -- instance declarations concerning the class i
      qs = map (\(_:=>q)->q) its  --instance heads
      c = (super ce i, (ps:=>p):its)
      in
  if (not (defined (ce i))) then
    fail "no class for instance"
  else if (any (overlap p) qs) then
    fail "overlapping instance"
  else
    return (cmodify ce i c)
  )

---- Entailment relations ----

-- return all implications of a given predicate
bySuper :: ClassEnv -> Pred -> [Pred]
bySuper ce p@(Pred i t) =
  p : concat [bySuper ce (Pred i' t) | i' <- super ce i]

-- reduce predicate to new subgoals
byInst :: ClassEnv -> Pred -> Maybe [Pred]
byInst ce p@(Pred i t) =
  msum $ map tryInst (insts ce i)
  where
  tryInst (ps :=> h) = do
    u <- matchPred h p
    Just (map (apply u) ps)

-- Does p follow from ps in the context of ce?
entail :: ClassEnv -> [Pred] -> Pred -> Bool
entail ce ps p = any (elem p) (map (bySuper ce) ps) ||
  case byInst ce p of
    Nothing -> False
    Just qs -> all (entail ce ps) qs

inHnf :: Pred -> Bool
inHnf (Pred c t) = hnf t where
  hnf (TyVar v) = True
  hnf (TyCon _) = False
  hnf (TyApp t _) = hnf t

toHnf :: Monad m => ClassEnv -> Pred -> m [Pred]
toHnf ce p
  | inHnf p = return [p]
  | otherwise = 
    case (byInst ce p) of
      Nothing -> fail ("no instances found during context reduction:\n"++(show $ pretty p))
      Just ps -> toHnfs ce ps

toHnfs :: Monad m => ClassEnv -> [Pred] -> m [Pred]
toHnfs ce ps = do
  pss <- mapM (toHnf ce) ps
  return $ concat pss

simplify :: ClassEnv -> [Pred] -> [Pred]
simplify ce = loop [] where
  loop rs [] = rs
  loop rs (p:ps)
    | entail ce (rs++ps) p = loop rs ps
    | otherwise = loop (p:rs) ps

reduce :: Monad m => ClassEnv -> [Pred] -> m [Pred]
reduce ce ps = do
  qs <- toHnfs ce ps
  return $ simplify ce qs


-- Base Typeclasses

addCoreClasses :: EnvT
addCoreClasses =
      addClass "Dup" []
  >>> addClass "Drop" []
  >>> addClass "Readable" []
  >>> addClass "Writable" []

addBaseType :: Type -> EnvT
addBaseType t = addInst [] (Pred (IdS "Dup") t)
            >>> addInst [] (Pred (IdS "Drop") t)

addBaseDup :: Type -> EnvT
addBaseDup t = addInst [] (Pred (IdS "Dup") t)
addBaseDrop :: Type -> EnvT
addBaseDrop t = addInst [] (Pred (IdS "Drop") t)

addBaseTyCon :: (Type -> Type) -> EnvT
addBaseTyCon tc =
      addInst [Pred (IdS "Dup") (mkStarVar "a")]
               (Pred (IdS "Dup") (tc (mkStarVar "a")))
  >>> addInst [Pred (IdS "Drop") (mkStarVar "a")]
               (Pred (IdS "Drop") (tc (mkStarVar "a")))

addBaseTyCon2 :: (Type -> Type -> Type) -> EnvT
addBaseTyCon2 tc =
      addInst [Pred (IdS "Dup") (mkStarVar "a"),
               Pred (IdS "Dup") (mkStarVar "b")]
               (Pred (IdS "Dup") (tc (mkStarVar "a")
                                      (mkStarVar "b")))
  >>> addInst [Pred (IdS "Drop") (mkStarVar "a"),
               Pred (IdS "Drop") (mkStarVar "b")]
               (Pred (IdS "Drop") (tc (mkStarVar "a")
                                      (mkStarVar "b")))

addCoreInsts :: EnvT
addCoreInsts = 
      addCoreClasses
  >>> addBaseType tInt
  >>> addBaseType tUnit
  >>> addBaseType tUU
  >>> addBaseDup tRU
  >>> addBaseDrop tAU
  >>> addBaseTyCon2 mkPair
  >>> addBaseTyCon2 mkSum
  >>> addBaseTyCon2 mkChoice
  >>> addInst [Pred (IdS "Dup") (mkStarVar "p")]
                (Pred (IdS "Dup") (mkArrow (mkStarVar "p")
                                            (mkStarVar "a")
                                            (mkStarVar "b")))
  >>> addInst [Pred (IdS "Drop") (mkStarVar "p")]
                (Pred (IdS "Drop") (mkArrow (mkStarVar "p")
                                            (mkStarVar "a")
                                            (mkStarVar "b")))
  >>> addBaseDup tW
  >>> addInst [mkDup (mkStarVar "rq")]
                (mkDup (mkRef (mkStarVar "rq") (mkStarVar "a")))
  >>> addInst [mkDrop (mkStarVar "a")] 
                (mkDrop (mkRef (mkStarVar "rq") (mkStarVar "a")))
  >>> addBaseTyCon mkList

Just coreEnv = runKleisli addCoreInsts initialEnv
