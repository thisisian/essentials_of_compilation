module C1 where

data Arg = Num Int | Var String | T | F
  deriving (Show, Eq)
data Compare = Eq | Lt
  deriving (Show, Eq)
data Expr = Plain Arg | Read | Neg Arg | Plus Arg Arg
          | Not Arg | Cmp Compare Arg Arg
  deriving (Show, Eq)
data Stmt = Assign String Expr
  deriving (Show, Eq)
data Tail = Return Expr | Seq Stmt Tail
          | Goto String | If Compare Arg Arg String String
  deriving (Show, Eq)
data Program a = Pgrm a [(String, Tail)]
  deriving (Show, Eq)
