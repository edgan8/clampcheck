all: Main

Main: Parser.hs Lexer.hs
	ghc *.hs

Parser.hs: Parser.y
	happy Parser.y

Lexer.hs: Lexer.x
	alex Lexer.x
