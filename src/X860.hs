module X860 where

import Common

data Arg = Num Int | Reg Register | Deref Register Int
  deriving (Eq, Ord)

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
  prettyPrint (Callq s)    = "callq " ++ (globalize s) ++ "\n" 
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
       "\n\t.globl " ++ (globalize "main") ++ "\n" ++ (globalize "main") ++ ":\n" ++ prettyPrint block  
     printBlock (label, block) =
       label ++ ":\n" ++ prettyPrint block

newtype PInfo = PInfo { frameSize :: Int }

data BInfo = BInfo
