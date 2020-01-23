module X860 where

import Common

data Register = Rsp | Rbp | Rax | Rbx | Rcx | Rdx | Rsi | Rdi
              | R8 | R9 | R10 | R11 | R12 | R13 | R14 | R15

instance PrettyPrint Register where
  prettyPrint Rsp = "%rsp"
  prettyPrint Rbp = "%rbp"
  prettyPrint Rax = "%rax"
  prettyPrint Rbx = "%rbx"
  prettyPrint Rcx = "%rcx"
  prettyPrint Rdx = "%rdx"
  prettyPrint Rsi = "%rsi"
  prettyPrint Rdi = "%rdi"
  prettyPrint R8  = "%r8"
  prettyPrint R9  = "%r9"
  prettyPrint R10 = "%r10"
  prettyPrint R11 = "%r11"
  prettyPrint R12 = "%r12"
  prettyPrint R13 = "%r13"
  prettyPrint R14 = "%r14"
  prettyPrint R15 = "%r15"

data Arg = Num Int | Reg Register | Deref Register Int

instance PrettyPrint Arg where
  prettyPrint (Num x) = '$': show x
  prettyPrint (Reg r) = prettyPrint r
  prettyPrint (Deref r off) =
    show off ++ "(" ++ prettyPrint r ++ ")"

data Instr = Addq Arg Arg | Subq Arg Arg | Movq Arg Arg | Retq
           | Negq Arg | Callq String | Pushq Arg | Popq Arg
           | Jmp String

instance PrettyPrint Instr where
  prettyPrint (Addq aL aR) =
    "addq  " ++ prettyPrint aL ++ ", " ++ prettyPrint aR ++ "\n"
  prettyPrint (Subq aL aR) =
    "subq  " ++ prettyPrint aL ++ ", " ++ prettyPrint aR ++ "\n"
  prettyPrint (Movq aL aR) =
    "movq  " ++ prettyPrint aL ++ ", " ++ prettyPrint aR ++ "\n"
  prettyPrint (Negq a)     = "negq  " ++ prettyPrint a ++ "\n"
  prettyPrint Retq         = "retq\n"
  prettyPrint (Callq s)    = "callq " ++ s ++ "\n"
  prettyPrint (Pushq a)    = "pushq " ++ prettyPrint a ++ "\n"
  prettyPrint (Popq a)     = "popq  " ++ prettyPrint a ++ "\n"
  prettyPrint (Jmp s)      = "jmp " ++ s ++ "\n"


data Block = Block BInfo [Instr]

instance PrettyPrint Block where
  prettyPrint (Block _ instrs) = concatMap (("\t" ++) . prettyPrint) instrs

data Program = Program PInfo [(String, Block)]

instance PrettyPrint Program where
  prettyPrint (Program _ bs) = concatMap printBlock bs
   where
     printBlock ("main", block) =
       "\n\t.globl main\n" ++ "main:\n" ++ prettyPrint block
     printBlock (label, block) =
       label ++ ":\n" ++ prettyPrint block

data PInfo = PInfo { frameSize :: Int }

data BInfo = BInfo
