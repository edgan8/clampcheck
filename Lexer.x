{
module Lexer where
}

%wrapper "monad"

$digit = 0-9
$alpha = [a-zA-Z]

tokens :-

  $white+                         { skip }
  "//".*                          { skip }
  "("                             { sAction TkLParen }
  ")"                             { sAction TkRParen }
  
  $digit+                         { strAction $ \s -> TkInt (read s) }
  "unit"                          { sAction TkUnit }

  "fun"                           { sAction TkFun }
  "->"                            { sAction TkArrow }
  "-U>"                           { sAction TkArrowU }
  "-R>"                           { sAction TkArrowR }
  "-A>"                           { sAction TkArrowA }
  "-L>"                           { sAction TkArrowL }
  "let"                           { sAction TkLet }
  "="                             { sAction TkEq }
  "in"                            { sAction TkIn }
  ","                             { sAction TkComma }
  "letp"                          { sAction TkLetp }
  "inl"                           { sAction TkInl }
  "inr"                           { sAction TkInr }
  "match"                         { sAction TkMatch }
  "with"                          { sAction TkWith }
  "|"                             { sAction TkPipe }
  "["                             { sAction TkLBrack }
  "]"                             { sAction TkRBrack }
  "fst"                           { sAction TkFst }
  "snd"                           { sAction TkSnd }
  "-"                             { sAction TkMinus }
  "+"                             { sAction TkPlus }
  ">"                             { sAction TkGt }
  "<"                             { sAction TkLt }
  "=="                            { sAction TkEqq }
  "or"                            { sAction TkOr }
  "and"                           { sAction TkAnd }
  "fix"                           { sAction TkFix }
  "wnew"                          { sAction TkWNew }
  "snew"                          { sAction TkSNew }
  "release"                       { sAction TkRelease }
  "srelease"                      { sAction TkSRelease }
  "swap"                          { sAction TkSwap }
  "sswap"                         { sAction TkSSwap }

  "@" [$alpha $digit \_ \']*      { strAction $ \s -> TkGVar s}
  $alpha [$alpha $digit \_ \']*   { strAction $ \s -> TkVar s }

{

strAction :: (String -> LToken) -> AlexAction LToken
strAction tfun = token (\(pos,_,_,str) len -> tfun (take len str))

sAction :: LToken -> AlexAction LToken
sAction t = strAction (\_ -> t)


data LToken =
    TkLParen
  | TkRParen
  | TkInt Int
  | TkUnit
  | TkFun 
  | TkArrow
  | TkArrowU
  | TkArrowR
  | TkArrowA
  | TkArrowL
  | TkLet
  | TkEq
  | TkIn
  | TkComma
  | TkLetp
  | TkInl
  | TkInr
  | TkMatch
  | TkWith
  | TkPipe
  | TkLBrack
  | TkRBrack
  | TkFst
  | TkSnd
  | TkMinus
  | TkPlus
  | TkGt
  | TkLt
  | TkEqq
  | TkOr
  | TkAnd
  | TkFix
  | TkWNew
  | TkSNew
  | TkRelease
  | TkSRelease
  | TkSwap
  | TkSSwap

  | TkVar String
  | TkGVar String
  | TkEOF
  deriving (Show, Eq)

-- Alex calls this function when it reaches EOF
alexEOF = return TkEOF


-- The Alex monad is just like a reader monad, this is used in the parser
-- for errors

getPos :: Alex AlexPosn
getPos = Alex $ \s -> Right (s,alex_pos s)

showPosn (AlexPn _ line col) = show line ++ ":" ++ show col

-- alexMonadScan scans the next token within the reader monad
scanner :: String -> Either String [LToken]
scanner str = runAlex str $ do
  loop []
  where
    loop ts = do
      tok <- alexMonadScan
      if tok == TkEOF
          then return ts
          else loop $! (tok:ts)

lexer :: (LToken -> Alex a) -> Alex a
lexer cont = do
  t <- alexMonadScan
  cont t
}
