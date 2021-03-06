module PsuedoX860 where

import Data.Set (Set)
import qualified Data.Set as S
import qualified Data.Map as M

import Common
import qualified X860 as X

data StoreLoc = RegLoc Register | Stack Int
  deriving (Show)

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
                   , bInfoConflicts     :: M.Map Arg (Set Arg)
                   , bInfoMoveRelated   :: M.Map Arg (Set Arg) }
  deriving (Show, Eq)

emptyBInfo :: BInfo
emptyBInfo = BInfo [] M.empty M.empty

newtype PInfo = PInfo { pInfoLocals :: [String] }
  deriving (Show, Eq)

callerSaved :: Set Register
callerSaved = S.fromList [Rax, Rdx, Rcx, Rdi, R8, R9, R10, R11]

writeArgs :: Instr -> Maybe (Set Arg)
writeArgs (Addq _ a)   = Just (S.singleton a)
writeArgs (Subq _ a)   = Just (S.singleton a)
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
isArithOp (Addq _ _)  = True
isArithOp (Subq _ _)  = True
isArithOp (Negq _)    = True
isArithOp _           = False

toX860Arg :: Arg -> X.Arg
toX860Arg (Num x)     = X.Num x
toX860Arg (Reg r)     = X.Reg r
toX860Arg (Deref r x) = X.Deref r x
toX860Arg (Var _)     = error "toX86: called with Var"

isVar :: Arg -> Bool
isVar (Var _) = True
isVar _ = False

isReg :: Arg -> Bool
isReg (Reg _) = True
isReg _       = False
