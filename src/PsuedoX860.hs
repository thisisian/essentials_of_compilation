module PsuedoX860 where

data Register = Rsp | Rbp | Rax | Rbx | Rcx | Rdx | Rsi | Rdi
              | R8 | R9 | R10 | R11 | R12 | R13 | R14 | R15
  deriving (Show, Eq)

data Arg = Num Int | Reg Register | Deref Register Int | Var String
  deriving (Show, Eq)

data Instr = Addq Arg Arg | Subq Arg Arg | Movq Arg Arg | Retq
           | Negq Arg | Callq String | Pushq Arg | Popq Arg
           | Jmp String
  deriving (Show, Eq)

data Block = Block BInfo [Instr]
  deriving (Show, Eq)

data Program = Program PInfo [(String, Block)]
  deriving (Show, Eq)

data BInfo = BInfo
  deriving (Show, Eq)

data PInfo = PInfo { pInfoLocals :: [String] }
  deriving (Show, Eq)
