{
module Parser (parseStr) where
import Lexer
import ExprU
}

%name parse expr
%tokentype { LToken }
%error { parseError }
%monad { Alex }
%lexer { lexer } { TkEOF }

%token
  '('       {TkLParen}
  ')'       {TkRParen}
  int       {TkInt $$}
  '()'      {TkUnit}
  fun       {TkFun}
  '->'      {TkArrow}
  '-U>'     {TkArrowU}
  '-R>'     {TkArrowR}
  '-A>'     {TkArrowA}
  '-L>'     {TkArrowL}
  let       {TkLet}
  '='       {TkEq}
  in        {TkIn}
  ','       {TkComma}
  letp      {TkLetp}
  Left      {TkInl}
  Right     {TkInr}
  case      {TkMatch}
  of        {TkWith}
  ';'       {TkSemi}
  '['       {TkLBrack}
  ']'       {TkRBrack}
  fst       {TkFst}
  snd       {TkSnd}
  var       {TkVar $$}
  gvar      {TkGVar $$}
  '+'       {TkPlus}
  '-'       {TkMinus}
  '<'       {TkLt}
  '>'       {TkGt}
  '=='      {TkEqq}
  or        {TkOr}
  and       {TkAnd}
  fix       {TkFix}
  wnew      {TkWNew}
  snew      {TkSNew}
  release   {TkRelease}
  srelease  {TkSRelease}
  swap      {TkSwap}
  sswap     {TkSSwap}

%%

primop1 :: { PrimOp1 }
primop1 :
    Left
      { PrInl }
  | Right
      { PrInr }
  | fst
      { PrFst }
  | snd
      { PrSnd }
  | fix
      { PrFix }
  | wnew
      { PrWNew }
  | snew
      { PrSNew }
  | release
      { PrRelease }
  | srelease
      { PrSRelease }
  | swap
      { PrSwap }
  | sswap
      { PrSSwap }

infixop2 :: { PrimOp2 }
infixop2 :
    '+'
      { PrPlus }
  | '-'
      { PrMinus }
  | '>'
      { PrGt }
  | '<'
      { PrLt }
  | '=='
      { PrEqq }
  | and
      { PrAnd }
  | or
      { PrOr }


expr :: { Expr }
expr : 
    infexp
      { $1 }
  | fun var '-U>' expr
      { ExAbs AQU (IdS $2) $4 }
  | fun var '-R>' expr
      { ExAbs AQR (IdS $2) $4 }
  | fun var '-A>' expr
      { ExAbs AQA (IdS $2) $4 }
  | fun var '-L>' expr
      { ExAbs AQL (IdS $2) $4 }
  | let var '=' expr in expr
      { ExLet (IdS $2) $4 $6 }
  | letp '(' var ',' var ')' '=' expr in expr
      { ExLetp (IdS $3) (IdS $5) $8 $10 }
  | case expr of Left var '->' expr ';' Right var '->' expr
      { ExMatch $2 (IdS $5) $7 (IdS $10) $12 }
  | primop1 expr
      { ExPrim1 $1 $2 }

infexp :: {Expr}
infexp : 
    appexp
      { $1 }
  | infexp infixop2 appexp
      { ExPrim2 $2 $1 $3 }

appexp :: {Expr}
appexp : 
    atexp
      { $1 }
  | appexp atexp
      { ExApp $1 $2 }

atexp :: {Expr}
atexp :
    int
      { ExLit (LiNum $1) }
  | '()'
      { ExLit LiUnit }
  | '(' expr ',' expr ')'
      { ExPrim2 PrPair $2 $4 }
  | '[' expr ',' expr ']'
      { ExWith $2 $4 }
  | var
      { ExVar (IdS $1) }
  | gvar
      { ExGVar (IdS $1) }
  | '(' expr ')'
      { $2 }

{

parseError :: LToken -> Alex a
parseError t = do
  p <- getPos
  alexError (showPosn p ++ ":" ++ (show t))

parseStr :: String -> Either String Expr
parseStr s = runAlex s parse

}
