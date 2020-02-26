module C2 where

import qualified R3

data Arg = Num Int | Var String | T | F
  deriving (Show, Eq)
data Compare = Eq | Lt
  deriving (Show, Eq)
data Expr = Plain Arg | Read | Neg Arg | Plus Arg Arg
            | Not Arg | Cmp Compare Arg Arg | Allocate Int Type
            | VectorRef Arg Int | VectorSet Arg Int Arg | GlobalValue String
            | Void
  deriving (Show, Eq)
data Stmt = Assign String Expr | Collect Int
  deriving (Show, Eq)
data Tail = Return Expr | Seq Stmt Tail
          | Goto String | If Compare Arg Arg String String
  deriving (Show, Eq)
data Program a = Pgrm a [(String, Tail)]
  deriving (Show, Eq)

data Type = TBool | TNum | TVoid | TVector [Type]
  deriving (Show, Eq)
