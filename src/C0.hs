module C0 where

data Arg = Num Int | Var String
  deriving (Show, Eq)
data Expr = Plain Arg | Read | Neg Arg | Plus Arg Arg
  deriving (Show, Eq)
data Assign = Assign String Expr
  deriving (Show, Eq)
data Tail = Return Expr | Seq Assign Tail
  deriving (Show, Eq)
data Program = Pgrm Info [(String, Tail)]
  deriving (Show, Eq)

data Info = Locals [String]
  deriving (Show, Eq)
