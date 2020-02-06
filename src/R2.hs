{-# OPTIONS_GHC -fno-warn-missing-signatures #-}

module R2 where

import Control.Applicative
import Control.Exception (TypeError(..))
import Control.Monad
import Control.Monad.State
import qualified Data.Map as M
import Text.Parsec.Token
import Text.Parsec.Language
import Text.Parsec (oneOf, letter, alphaNum, try)
import qualified Text.Parsec as Parsec (parse)

import Common

data Expr
  = Num Int
  | Read
  | Neg Expr
  | Add Expr Expr
  | Sub Expr Expr
  | Var String
  | Let String Expr Expr
  | T
  | F
  | And Expr Expr
  | Or Expr Expr
  | Not Expr
  | Cmp Compare Expr Expr
  | If Expr Expr Expr

data Compare = Eq | Lt | Le | Gt | Ge
  deriving Eq

instance Show Expr where
  show (Num x) = show x
  show Read = "(read)"
  show (Neg e) = "(- " ++ show e ++ ")"
  show (Add eL eR) =
    "(+ " ++ show eL ++ " " ++ show eR ++ ")"
  show (Sub eL eR) =
    "(- " ++ show eL ++ " " ++ show eR ++ ")"
  show (Var v) = v
  show (Let v be e) =
    "(let ([" ++ v ++ " " ++ show be ++ "]) " ++ show e ++ ")"
  show T = "#t"
  show F = "#f"
  show (And eL eR) = "(and " ++ show eL ++ " " ++ show eR ++ ")"
  show (Or eL eR) = "(or " ++ show eL ++ " " ++ show eR ++ ")"
  show (Not e) = "(not " ++ show e ++ ")"
  show (Cmp c eL eR) = "(cmp " ++ show c ++ " " ++ show eL ++ " " ++
    show eR ++ ")"
  show (If e eT eF) = "(if " ++ show e ++ " " ++ show eT ++ " " ++ show eF ++ ")"

instance Show Compare where
  show Eq = "eq?"
  show Lt = "<"
  show Le = "<="
  show Gt = ">"
  show Ge = ">="

data Program = Program Info Expr

instance Show Program where
  show (Program _ e) = show e

data Info = Info

instance Show Info where
  show Info = "()"

{- Parser -}
parse :: Parser Program
parse = Parsec.parse pProgram ""

parseError :: String -> Program
parseError s = case Parsec.parse pProgram "" s of
  Left e -> error $ show e
  Right s -> s

pProgram = Program Info <$> pExpr

pExpr = pNum <|> pVar <|> pTrue <|> pFalse <|> pParens pExpr'
 where
  pExpr' = (pReserved "read" *> return Read)
      <|> pLet
      <|> try (pReservedOp "-" *> (Sub <$> pExpr <*> pExpr))
      <|> pReservedOp "-" *> (Neg <$> pExpr)
      <|> pReservedOp "+" *> (Add <$> pExpr <*> pExpr)
      <|> pReserved "and" *> (And <$> pExpr <*> pExpr)
      <|> pReserved "or" *> (Or <$> pExpr <*> pExpr)
      <|> pReserved "not" *> (Not <$> pExpr)
      <|> pReserved "cmp" *> (Cmp <$> pCmp <*> pExpr <*> pExpr)
      <|> pReserved "if" *> (If <$> pExpr <*> pExpr <*> pExpr)

pCmp = pReservedOp "eq?" *> return Eq
     <|> pReservedOp "<" *> return Lt
     <|> pReservedOp "<=" *> return Le
     <|> pReservedOp ">" *> return Gt
     <|> pReservedOp ">=" *> return Ge


pVar = Var <$> pIdent

pTrue = pReserved "#t" *> return T

pFalse = pReserved "#f" *> return F

pLet = do
  pReserved "let"
  (v, be) <- pBinding
  Let v be <$> pExpr

pBinding =
  pParens (pBrackets (do v <- pIdent; e <- pExpr ; return (v, e)))

pNum = do
  int <- pInteger
  return (Num . fromIntegral $ int)

TokenParser { parens = pParens
            , brackets = pBrackets
            , identifier = pIdent
            , reservedOp = pReservedOp
            , reserved = pReserved
            , integer = pInteger
            , whiteSpace = pWhiteSpace } = makeTokenParser def

def = emptyDef { commentLine = ";;"
               , identStart = letter
               , identLetter = alphaNum
               , opStart = oneOf "+-<>e"
               , opLetter = oneOf "+-<>=eq?"
               , reservedNames = ["read", "let", "#t", "#f"]
               , reservedOpNames = ["+", "-", "<", ">", "<=", ">=", "eq?"]
               }

{- Interpreter -}

-- Should I use a 'Val' type? Or implement boolean with integers?
-- I'm going to implement with integers, where F->0, T->(not 0)
-- since the expressions will be typechecked anyway, perhaps this won't
-- have any issues?

type Env = M.Map String Int

interp :: [Int] -> Program -> Int
interp inputs (Program _ e) = evalState (interpExpr M.empty e) inputs

interpExpr :: Env -> Expr -> State [Int] Int
interpExpr _ (Num x) = return x
interpExpr _ Read = nextInput
interpExpr env (Neg e) = (0 -) <$> interpExpr env e
interpExpr env (Add eL eR) = interpBinOp env (+) eL eR
interpExpr env (Sub eL eR) = interpBinOp env (-) eL eR
interpExpr env (Let v be e) = do
  val <- interpExpr env be
  let newEnv = M.insert v val env
  interpExpr newEnv e
interpExpr env (Var v) = case M.lookup v env of
  Just e -> return e
  Nothing -> error $ "Variable " ++ v ++ " not found in env"
interpExpr _ T = return 1
interpExpr _ F = return 0
interpExpr env (And eL eR) = do
  vL <- interpExpr env eL
  if vL == 0
    then return 0
    else interpExpr env eR
interpExpr env (Or eL eR) = do
  vL <- interpExpr env eL
  if vL /= 0
    then return 1
    else interpExpr env eR
interpExpr env (Not e) = do
  v <- interpExpr env e
  if v == 0 then return 1 else return 0
interpExpr env (Cmp Eq eL eR) = interpBinBoolOp env (==) eL eR
interpExpr env (Cmp Lt eL eR) = interpBinBoolOp env (<) eL eR
interpExpr env (Cmp Le eL eR) = interpBinBoolOp env (<=) eL eR
interpExpr env (Cmp Gt eL eR) = interpBinBoolOp env (>) eL eR
interpExpr env (Cmp Ge eL eR) = interpBinBoolOp env (>=) eL eR
interpExpr env (If e eT eF) = do
  v <- interpExpr env e
  if v == 0
    then interpExpr env eF
    else interpExpr env eT

interpBinOp
  :: Env
  -> (Int -> Int -> Int)
  -> Expr
  -> Expr
  -> State [Int] Int
interpBinOp env op eL eR = do
  return op `ap` interpExpr env eL `ap` interpExpr env eR

interpBinBoolOp
  :: Env
  -> (Int -> Int -> Bool)
  -> Expr
  -> Expr
  -> State [Int] Int
interpBinBoolOp env op eL eR = do
  vL <- interpExpr env eL
  vR <- interpExpr env eR
  if vL `op` vR
    then return 1
    else return 0

nextInput :: State [Int] Int
nextInput = do
  is' <- get
  case is' of
    (i:is) -> do
      put is
      return i
    _ -> error "Read was called, but no more inputs remain"


{- Type Checker -}

data Type = TBool | TNum
  deriving Eq

instance Show Type where
  show TBool = "Bool"
  show TNum  = "Num"

typeCheck :: Program -> Either TypeError Type
typeCheck (Program _ e) = typeChkExpr M.empty e

typeChkExpr :: (M.Map String Type) -> Expr -> Either TypeError Type
typeChkExpr _ (Num _) = Right TNum
typeChkExpr _ (Read)  = Right TNum
typeChkExpr env (Neg e) = typeChkUniOp TNum TNum env e
typeChkExpr env (Add eL eR) = typeChkBinOp TNum TNum env eL eR
typeChkExpr env (Sub eL eR) = typeChkBinOp TNum TNum env eL eR
typeChkExpr env (Var s) = case M.lookup s env of
  Just t -> Right t
  Nothing -> Left . TypeError $ "Failed to find binding for " ++ s
typeChkExpr env (Let s bE e) = do
  bTy <- typeChkExpr env bE
  typeChkExpr (M.insert s bTy env) e
typeChkExpr _ T = Right TBool
typeChkExpr _ F = Right TBool
typeChkExpr env (And eL eR) = typeChkBinOp TBool TBool env eL eR
typeChkExpr env (Or eL eR) = typeChkBinOp TBool TBool env eL eR
typeChkExpr env (Not e) = typeChkUniOp TBool TBool env e
typeChkExpr env (Cmp _ eL eR) = typeChkBinOp TNum TBool env eL eR
typeChkExpr env (If e eT eF) = do
  testTy <- typeChkExpr env e
  case testTy of
    TBool -> do
      truTy <- typeChkExpr env eT
      falTy <- typeChkExpr env eF
      if truTy == falTy
        then Right truTy
        else Left . TypeError $ "Branches of If expression don't match. Got " ++
          show truTy ++ " and " ++ show falTy
    t -> Left . TypeError  $ "Test of If expression is of type " ++ show t

typeChkUniOp argTy retTy env e = do
  t <- typeChkExpr env e
  if t == argTy
    then Right retTy
    else Left . TypeError $ "Unary op expected " ++ show argTy ++
      " but got " ++ show t

typeChkBinOp argTy retTy env eL eR = do
  tL <- typeChkExpr env eL
  tR <- typeChkExpr env eR
  if (tL, tR) == (argTy, argTy)
    then Right retTy
    else Left . TypeError $ "BinOp expected " ++ show argTy ++ " and " ++
      show argTy ++ " but got " ++ show tL ++ " and " ++ show tR
