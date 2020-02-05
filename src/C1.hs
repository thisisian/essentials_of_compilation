module C1 where

import Data.Map (Map)
import qualified Data.Map as M
import Data.Set (Set)

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
data Program = Pgrm Info [(String, Tail)]
  deriving (Show, Eq)
data Info = Info { infoLocals :: [String], infoCFG :: Map String (Set String) }
  deriving (Show, Eq)


emptyInfo :: Info
emptyInfo = Info { infoLocals = [], infoCFG = M.empty }
