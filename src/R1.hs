{-# OPTIONS_GHC -fno-warn-missing-signatures #-}

module R1 where

import Common

import Control.Applicative
import Control.Monad
import Control.Monad.State

import Text.Parsec.Token
import Text.Parsec.Language
import Text.Parsec (oneOf, letter, alphaNum)
import qualified Text.Parsec as Parsec (parse)

import qualified Data.Map as M

data Expr
  = Num Int
  | Read
  | Neg Expr
  | Add Expr Expr
  | Var String
  | Let String Expr Expr

instance Show Expr where
  show (Num x) = show x
  show Read = "(read)"
  show (Neg e) = "(- " ++ show e ++ ")"
  show (Add eL eR) =
    "(+ " ++ show eL ++ " " ++ show eR ++ ")"
  show (Var v) = v
  show (Let v be e) =
    "(let ([" ++ v ++ " " ++ show be ++ "]) " ++ show e ++ ")"

data Program = Pgrm Info Expr

instance Show Program where
  show (Pgrm _ e) = show e

data Info = Info

instance Show Info where
  show Info = "()"

{- Parser -}
parse :: Parser Program
parse = Parsec.parse pProgram ""

pProgram = Pgrm Info <$> pExpr

pExpr = pNum <|> pVar <|> pParens pExpr'
 where
  pExpr' = (pReserved "read" *> return Read)
      <|> pLet
      <|> pReservedOp "-" *> (Neg <$> pExpr)
      <|> pReservedOp "+" *> (Add <$> pExpr <*> pExpr)

pVar = Var <$> pIdent

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
               , opStart = oneOf "+-"
               , opLetter = oneOf "+-"
               , reservedNames = ["read", "let"]
               , reservedOpNames = ["+", "-"]
               }

{- Interpreter -}

type Env = M.Map String Int

interp :: [Int] -> Program -> Int
interp inputs (Pgrm _ e) = evalState (interpExpr M.empty e) inputs

interpExpr :: Env -> Expr -> State [Int] Int
interpExpr _ (Num x) = return x
interpExpr _ Read = nextInput
interpExpr env (Neg e) = (0 -) <$> interpExpr env e
interpExpr env (Add eL eR) =
  return (+) `ap` interpExpr env eL `ap` interpExpr env eR
interpExpr env (Let v be e) = do
  val <- interpExpr env be
  let newEnv = M.insert v val env
  interpExpr newEnv e
interpExpr env (Var v) = case M.lookup v env of
  Just e -> return e
  Nothing -> error $ "Variable " ++ v ++ " not found in env"

nextInput :: State [Int] Int
nextInput = do
  is' <- get
  case is' of
    (i:is) -> do
      put is
      return i
    _ -> error "Read was called, but no more inputs remain"
