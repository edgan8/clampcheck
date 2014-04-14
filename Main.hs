module Main where
import Util
import Pretty
import Idx
import ExprU
import Parser
import Annot
import Types
import Classes
import Infer
import Run
import Control.Arrow

initialAssump = initAS

{-

runTests :: String -> (Assump)
runTests s = 
  let (Right er) = parseStr s in
  let e = annotExpr er in
  tiDeclT coreEnv initialAssump (IdS "test") e

processInput :: String -> String
processInput s =
  case (parseStr s) of
    (Left parseErr) -> "Parse Error: "++parseErr++"\n"
    (Right rawExpr) -> 
      let e = annotExpr rawExpr in
      let et = tiDeclT coreEnv initialAssump (IdS "tsch") e in
      let outdoc =
            text "----Annotated Expression:----"<$>
            pretty e<$>
            text "----Inferred TypeScheme:-----"<$>
            pretty et<$>
            text "----Interpreter Results:-----"<$>
            let (m,v) = run e in
            text ("map: "++show m)<$>
            pretty v<>line
        in
      show outdoc
-}


-- To simplify the interpreter we combine all of the declarations
-- into a single expression
combineDecls :: [Decl] -> Expr
combineDecls =
  foldr addDecl (ExVar (IdS "_"))
  where
    addDecl (DcLet i e1) = ExLet i e1

processProgram :: String -> String
processProgram s =
  case (parseStr s) of
    (Left parseErr) -> "Parse Error: "++parseErr++"\n"
    (Right rawDecls) -> 
      let decls = map annotDecl rawDecls in
      let types = tiProgT coreEnv initialAssump decls in
      let outdoc =
            text "----Annotated Declarations:----"<$>
            pretty decls<$>
            text "----Inferred TypeSchemes:-----"<$>
            pretty (reverse types)<$>
            text "----Interpreter Results:-----"<$>
            let (m,v) = run (combineDecls decls) in
            text ("map: "++show m)<$>
            pretty v<>
            line
        in
      show outdoc

s1 = "(fun x -U> (fun y -U> (y,y)) (x,x))"
s2 = "let f = (fun y -R> y) in (f 1, f unit)"
s2b = "let f = (fun y -A> y) in (f 1, f unit)"
s3 = "(fun f -L> (f 1, f unit)) (fun x -U> x)"
s4 = "let z = 5 in let x = 4 in (fun y -L> (y,(z,x)))"
s5 = "let f = (fun x -L> x) in (fun z -U> f (f z))"
s6 = "(let f = (fun x -L> x) in (fun z -L> f z)) 4"
s7 = "let f = (let z = 5 in let x = 4 in (fun y -U> (y,(z,x)))) in \
        \(f unit, f unit)"
s8 = "fun x -U> (x,[x,1])"
s9 = "fun f -U> (f 1, f 2)"
s10 = "(fun f -U> (f 1, f 2)) (fun x -R> x)"

ref1 = "swap (snew 4,3)"
-- Note that changing one arrow to U makes this only work on weak refs!!
ref2 = "fun r -U> (fun k -L> letp (a,b) = swap (r,k) in (a,b+4))"
ref3 = "fun r -U> letp (r1,k) = sswap (r,4) in sswap (r1,unit)"

-- fibonacci like function with a custom decrement function
fixtest = "fix (fun f -U> (fun g -U> (fun x -U> \
            \ match (x>1) with a -> ((f g) (g x)) + ((f g) (g (g x))) | b -> 1\
            \)))"

main = interact processProgram
