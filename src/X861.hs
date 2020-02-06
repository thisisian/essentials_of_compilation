module X861 where

import Common
import Data.Map (Map)
import qualified Data.Map as M
import Data.Set (Set)
import qualified Data.Set as S

data Program = Program PInfo [(String, Block)]
  deriving (Show)

data PInfo = PInfo { pInfoLocals :: [String]
                   , pInfoCFG :: Map String (Set String)
                   , pInfoConflicts :: Map Arg (Set Arg)
                   , pLocMap :: Map String StoreLoc
                   , pInfoFrameSize :: Int }
  deriving (Show, Eq)

emptyPInfo :: PInfo
emptyPInfo = PInfo { pInfoLocals = []
                   , pInfoCFG = M.empty
                   , pInfoConflicts = M.empty
                   , pLocMap = M.empty
                   , pInfoFrameSize = -1 }

data Block = Block BInfo [Instr]
  deriving (Show)

data BInfo = BInfo { bInfoLiveAfterSets :: [Set Arg]
                   , bInfoConflicts     :: Map Arg (Set Arg)
                   , bInfoMoveRelated   :: Map Arg (Set Arg) }
  deriving (Show, Eq)

emptyBInfo :: BInfo
emptyBInfo = BInfo [] M.empty M.empty

data Instr = Addq Arg Arg | Subq Arg Arg | Movq Arg Arg | Retq
           | Negq Arg | Callq String | Pushq Arg | Popq Arg
           | Jmp String | Xorq Arg Arg | Cmpq Arg Arg | Set CC Arg
           | Movzbq Arg Arg | JmpIf CC String
           | Label String
  deriving (Show)

data Arg = Num Int
         | Reg Register
         | Deref Register Int
         | Var String
         | ByteReg Register
  deriving (Show, Eq, Ord)

data CC = CCEq | CCL | CCLe | CCG | CCGe
  deriving (Show)

data StoreLoc = RegLoc Register | Stack Int
  deriving (Show, Eq)

instance PrettyPrint Arg where
  prettyPrint (Num x) = '$': show x
  prettyPrint (Reg r) = prettyPrint r
  prettyPrint (Deref r off) =
    show off ++ "(" ++ prettyPrint r ++ ")"
  prettyPrint (Var _) = error $ "Attempted to prettyPrint a variable"
  prettyPrint (ByteReg r) = prettyPrint r

instance PrettyPrint CC where
  prettyPrint CCEq = "e"
  prettyPrint CCL  = "l"
  prettyPrint CCLe = "le"
  prettyPrint CCG  = "g"
  prettyPrint CCGe = "ge"

instance PrettyPrint Instr where
  prettyPrint (Addq aL aR)   = prettyPrintBinOp "addq" aL aR
  prettyPrint (Subq aL aR)   = prettyPrintBinOp "subq" aL aR
  prettyPrint (Movq aL aR)   = prettyPrintBinOp "movq" aL aR
  prettyPrint (Negq a)       = "negq  " ++ prettyPrint a ++ "\n"
  prettyPrint Retq           = "retq\n"
  prettyPrint (Callq s)      = "callq " ++ s ++ "\n"
  prettyPrint (Pushq a)      = "pushq " ++ prettyPrint a ++ "\n"
  prettyPrint (Popq a)       = "popq  " ++ prettyPrint a ++ "\n"
  prettyPrint (Jmp s)        = "jmp " ++ s ++ "\n"
  prettyPrint (Xorq aL aR)   = prettyPrintBinOp "xorq" aL aR
  prettyPrint (Cmpq aL aR)   = prettyPrintBinOp "cmpq" aL aR
  prettyPrint (Set cc a)     = "set" ++ prettyPrint cc ++ " " ++ prettyPrint a ++ "\n"
  prettyPrint (Movzbq aL aR) = prettyPrintBinOp "movzbq" aL aR
  prettyPrint (JmpIf cc s)   = "j" ++ prettyPrint cc ++ " " ++ s ++ "\n"
  prettyPrint (Label _)      = undefined

prettyPrintBinOp :: (PrettyPrint a, PrettyPrint b) =>
  String -> a -> b -> String
prettyPrintBinOp op randL randR =
  op ++ " " ++ prettyPrint randL ++ ", " ++ prettyPrint randR ++ "\n"


instance PrettyPrint Block where
  prettyPrint (Block _ instrs) = concatMap (("\t" ++) . prettyPrint) instrs


instance PrettyPrint Program where
  prettyPrint (Program _ bs) = concatMap printBlock bs
   where
     printBlock ("main", block) =
       "\n\t.globl main\n" ++ "main:\n" ++ prettyPrint block
     printBlock (label, block) =
       label ++ ":\n" ++ prettyPrint block

isVar :: Arg -> Bool
isVar (Var _) = True
isVar _ = False

isReg :: Arg -> Bool
isReg (Reg _) = True
isReg _       = False

writeArgs :: Instr -> Maybe (Set Arg)
writeArgs (Addq _ a)   = Just (S.singleton a)
writeArgs (Subq _ a)   = Just (S.singleton a)
writeArgs (Movq _ a)   = Just (S.singleton a)
writeArgs (Negq a)     = Just (S.singleton a)
writeArgs (Popq a)     = Just (S.singleton a)
writeArgs (Xorq _ a)   = Just (S.singleton a)
writeArgs (Movzbq _ a) = Just (S.singleton a)
writeArgs (Pushq _)    = Nothing
writeArgs (Retq)       = Nothing
writeArgs (Callq _)    = Nothing
writeArgs (Jmp _)      = Nothing
writeArgs (Cmpq _ _)   = Nothing
writeArgs (Set _ _ )   = Nothing
writeArgs (JmpIf _ _)  = Nothing
writeArgs (Label _)    = Nothing

readArgs :: Instr -> Maybe (Set Arg)
readArgs (Addq aL aR) = Just (S.fromList [aL, aR])
readArgs (Subq aL aR) = Just (S.fromList [aL, aR])
readArgs (Movq a _)   = Just (S.singleton a)
readArgs (Negq a)     = Just (S.singleton a)
readArgs (Pushq a)    = Just (S.singleton a)
readArgs (Xorq _ a)   = Just (S.singleton a)
readArgs (Movzbq _ a) = Just (S.singleton a)
readArgs (Cmpq aL aR) = Just (S.fromList [aL, aR])
readArgs (Set _ _)    = Nothing
readArgs (Popq _)     = Nothing
readArgs (Callq _)    = Nothing
readArgs (Jmp _)      = Nothing
readArgs (JmpIf _ _)  = Nothing
readArgs (Label _)    = Nothing
