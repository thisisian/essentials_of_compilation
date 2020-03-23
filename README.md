##Work for Essentials of Compilation book

Run tests with `stack test`

The following tests exist and are performed on the chapters where they are relevant:

* R* parsing is tested by parsing the original string, then printing the AST and comparing for equivalency against the original string.
* Unit tests for R* interpreter.
* Unit tests for typechecking, both passing and failing programs.
* Interpreter and compiler output are tested for equivalency with specific programs using random inputs.
* For chapter 4, arbitrary programs are plugged into the interpreter and compiler and the output is checked for consistency.
