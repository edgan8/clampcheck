module Pretty (
  addParen,myshow,
  module Text.PrettyPrint.Leijen
) where
import Text.PrettyPrint.Leijen

addParen :: Int -> Int -> Doc -> Doc
addParen p0 p1 d
  | p0 > p1 = parens d
  | otherwise = d

myshow :: Pretty a => a -> String
myshow = show . pretty
