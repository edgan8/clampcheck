clampcheck
==========

Clamp Type Checker and Interpreter, by Edward Gan
with design adapted from Mark Jones "Typing Haskell in Haskell"

The Main executable accepts input expressions from stdin and prints
out the inferred type and output value on stdout. Note that the
current type checker infers all type and accepts no type annotations.

Please see the examples in the tests/ directory for the concrete
syntax!

The [ , ] "with" form (not in lambda-cl) is probably unsound in the
current type checker.
