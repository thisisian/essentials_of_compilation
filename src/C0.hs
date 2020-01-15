module C0 where

data Arg = Num Int | Var String
data Expr = Plain Arg | Read | Neg Arg | Plus Arg Arg
data Assign = Assign String Expr
data Tail = Return Expr | Seq Assign Tail
data Program = Pgrm Info [(String, Tail)]

data Info = Locals [String]

uncover_locals :: Program -> Program
uncover_locals (Pgrm i [(s, t)]) =
  let locals = Locals (collectLocals t)
  in (Pgrm locals [(s, t)])
uncover_locals (Pgrm _ _) = undefined

collectLocals :: Tail -> [String]
collectLocals (Seq (Assign n _) t) = n : collectLocals t
collectLocals (Return _) = []
