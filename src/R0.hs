{-# OPTIONS_GHC -fno-warn-missing-signatures #-}

module R0 where

import Control.Monad

import Text.Parsec.Token
import Text.Parsec.Language
import Text.Parsec.Char
import Text.Parsec hiding (parse)
import qualified Text.Parsec as Parsec (parse)

import Common

data Expr = Num Int | Read | Neg Expr | Add Expr Expr

instance Show Expr where
  show (Num x) = show x
  show Read = "(read)"
  show (Neg e) = "(- " ++ show e ++ ")"
  show (Add eL eR) =
    "(+ " ++ show eL ++ " " ++ show eR ++ ")"

newtype Program = Pgrm Expr

instance Show Program where
  show (Pgrm e) = show e

{- Parser -}

parse :: Parser Program
parse = Parsec.parse pProgram ""

doParse :: String -> Program
doParse s = case Parsec.parse pProgram "" s of
  Left err -> error $ show err
  Right p  -> p

pProgram = Pgrm <$> pExpr

pExpr = pNum <|> pParens pExpr'
 where
  pExpr' = (pReserved "read" *> return Read)
      <|> pReservedOp "-" *> (Neg <$> pExpr)
      <|> pReservedOp "+" *> (Add <$> pExpr <*> pExpr)

pNum = do
  int <- pInteger
  return (Num . fromIntegral $ int)

TokenParser { parens = pParens
            , reservedOp = pReservedOp
            , reserved = pReserved
            , integer = pInteger
            , whiteSpace = pWhiteSpace } = makeTokenParser def

def = emptyDef { commentLine = ";;"
               , opStart = oneOf "+-"
               , opLetter = oneOf "+-"
               , reservedNames = ["read"]
               , reservedOpNames = ["+", "-"]
               }

{- Interpreter -}
interp :: Program -> IO Int
interp (Pgrm e) = interpExpr e

interpExpr :: Expr -> IO Int
interpExpr (Num x) = return x
interpExpr Read = do
  putStrLn "Enter an integer: "
  read <$> getLine
interpExpr (Neg e) = (0 -) <$> interpExpr e
interpExpr (Add eL eR) =
  return (+) `ap` interpExpr eL `ap` interpExpr eR

{- Partial evaluator -}

testPE :: String -> String
testPE s = show . pe . doParse $ s

pe :: Program -> Program
pe (Pgrm e) = Pgrm $ peExpr e

--peExpr2 :: Expr -> Expr
--peExpr2 (Neg (Num n)) = Num (0 - n)
--peExpr2 (Neg (Add eL eR)) = peExpr2 (Add (Neg eL) (Neg eR))
--peExpr2 (Neg (Neg x)) = peExpr2 x
--peExpr2 (Add eL eR) =
--  case (peExpr2 eL, peExpr2 eR) of
--    ((Num x), (Num y)) ->
--      (Num (x + y))
--    ((Num x), (Add (Num y) eR2)) ->
--      peExpr2 ((Add (Num (x+y)) eR2))
--    ((Add a b), (Add c d)) ->
--      peExpr2 (Add a (Add b (Add c d)))
--    ((Num 0), eR2) -> eR2
--    (eL2, (Add (Num x) eR2)) ->
--      peExpr2 (Add (Num x) (Add eL2 eR2))
--    (eL2@(Add _ _), eR2) ->
--      peExpr2 (Add eR2 eL2)
--    (eL2 , (Num x)) ->
--      peExpr2 (Add (Num x) eL2)
--    (eL2, eR2) -> (Add eL2 eR2)
peExpr :: Expr -> Expr
peExpr (Neg (Num n)) = Num (negate n)
peExpr (Neg (Add eL eR)) = peExpr (Add (Neg eL) (Neg eR))
peExpr (Neg (Neg x)) = peExpr x
peExpr (Add (Num x) (Num y)) = Num (x+y)
peExpr (Add (Num 0) e) = peExpr e
peExpr (Add (Num x) (Add (Num y) e)) = peExpr (Add (Num (x+y)) e)
peExpr (Add (Add a b) (Add c d)) = peExpr (Add a (Add b (Add c d)))
peExpr (Add e (Num x)) = peExpr (Add (Num x) e)
peExpr (Add e1 (Add (Num x) e2)) = peExpr (Add (Num x) (Add e1 e2))
peExpr (Add e1@(Add _ _) e2) = peExpr (Add e2 e1)
peExpr (Add eL eR) =
  case (peExpr eL, peExpr eR) of
    (eL2, Add (Num x) eR2) ->
      peExpr (Add (Num x) (Add eL2 eR2))
    (eL2, eR2) -> Add eL2 eR2
peExpr e = e
