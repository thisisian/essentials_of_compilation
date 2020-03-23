module C3 where

data Arg = Num Int | Var String | T | F
  deriving (Show, Eq)

data Compare = Eq | Lt
  deriving (Show, Eq)

data Expr = Plain Arg | Read | Neg Arg | Plus Arg Arg
            | Not Arg | Cmp Compare Arg Arg | Allocate Int Type
            | VectorRef Arg Int | VectorSet Arg Int Arg | GlobalValue String
            | Void | FunRef String | Call Arg [Arg]
  deriving (Show, Eq)

data Stmt = Assign String Expr | Collect Int
  deriving (Show, Eq)

data Tail = Return Expr | Seq Stmt Tail
          | Goto String | If Compare Arg Arg String String
          | TailCall Arg [Arg]
  deriving (Show, Eq)
data Def a = Def String [(String, Type)] Type a [(String, Tail)]
 deriving (Show, Eq)

data Program a b = Pgrm a [Def b]
  deriving (Show, Eq)

data Type = TBool | TNum | TVoid | TVector [Type] | TFunc [Type] Type
  deriving (Show, Eq)
