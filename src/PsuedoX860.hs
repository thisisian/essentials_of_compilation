module PsuedoX860 where

import Data.Set (Set)
import qualified Data.Set as S
import qualified Data.Map as M
import qualified X860 as X

data Register = Rsp | Rbp | Rax | Rbx | Rcx | Rdx | Rsi | Rdi
              | R8 | R9 | R10 | R11 | R12 | R13 | R14 | R15
  deriving (Show, Eq, Ord)

data Arg = Num Int | Reg Register | Deref Register Int | Var String
  deriving (Show, Eq, Ord)

data Instr = Addq Arg Arg | Subq Arg Arg | Movq Arg Arg | Retq
           | Negq Arg | Callq String | Pushq Arg | Popq Arg
           | Jmp String
  deriving (Show, Eq)

data Block = Block BInfo [Instr]
  deriving (Show, Eq)

data Program = Program PInfo [(String, Block)]
  deriving (Show, Eq)

data BInfo = BInfo { bInfoLiveAfterSets :: [Set Arg]
                   , bInfoConflicts     :: M.Map Arg (Set Arg) }
  deriving (Show, Eq)

emptyBInfo :: BInfo
emptyBInfo = BInfo [] M.empty

data PInfo = PInfo { pInfoLocals :: [String] }
  deriving (Show, Eq)

callerSaved :: Set Register
callerSaved = S.fromList [Rax, Rdx, Rcx, Rdi, R8, R9, R10, R11]

writeArgs :: Instr -> Maybe (Set Arg)
writeArgs (Addq aL aR) = Just (S.fromList [aL, aR])
writeArgs (Subq aL aR) = Just (S.fromList [aL, aR])
writeArgs (Movq _ a)   = Just (S.singleton a)
writeArgs (Negq a)     = Just (S.singleton a)
writeArgs (Pushq _)    = Nothing
writeArgs (Popq a)     = Just (S.singleton a)
writeArgs _            = Nothing

readArgs :: Instr -> Maybe (Set Arg)
readArgs (Addq aL aR) = Just (S.fromList [aL, aR])
readArgs (Subq aL aR) = Just (S.fromList [aL, aR])
readArgs (Movq a _)   = Just (S.singleton a)
readArgs (Negq a)     = Just (S.singleton a)
readArgs (Pushq a)    = Just (S.singleton a)
readArgs (Popq _)     = Nothing
readArgs _            = Nothing

isArithOp :: Instr -> Bool
isArithOp (Addq _ _) = True
isArithOp (Subq _ _) = True
isArithOp (Negq _)   = True
isArithOp _          = False

toX860 :: Register -> X.Register
toX860 Rsp = X.Rsp
toX860 Rbp = X.Rbp
toX860 Rax = X.Rax
toX860 Rbx = X.Rbx
toX860 Rcx = X.Rcx
toX860 Rdx = X.Rdx
toX860 Rsi = X.Rsi
toX860 Rdi = X.Rdi
toX860 R8  = X.R8
toX860 R9  = X.R9
toX860 R10 = X.R10
toX860 R11 = X.R11
toX860 R12 = X.R12
toX860 R13 = X.R13
toX860 R14 = X.R14
toX860 R15 = X.R15

isVar :: Arg -> Bool
isVar (Var _) = True
isVar _ = False

-- Incorrect -- kept cos I need it to compile
writeArg :: Instr -> Maybe Arg
writeArg _ = error $ "To remove"
