{-# OPTIONS_GHC -fno-warn-missing-signatures #-}

module R0 where

import Control.Monad

import Text.Parsec.Token
import Text.Parsec.Language
import Text.Parsec.Char
import Text.Parsec

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
testParse :: String -> IO ()
testParse s = case parse pProgram "" s of
 Left er -> print er
 Right p -> print p

doParse :: String -> Program
doParse s = case parse pProgram "" s of
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

pe :: Program -> Program
pe (Pgrm e) = Pgrm $ peExpr e

peExpr :: Expr -> Expr
peExpr (Neg (Num x)) = Num (0 - x)
peExpr (Add (Num l) (Num r)) = Num (l+r)
peExpr e = e

{- Exercise 1 -}

testPE :: String -> String
testPE s = show . pe2 . doParse $ s

pe2 :: Program -> Program
pe2 (Pgrm e) = Pgrm $ peExpr2 e

peExpr2 :: Expr -> Expr
peExpr2 (Neg e1) = case peExpr2 e1 of
  (Num n)  -> Num (0 - n)
  (Neg x)  -> peExpr2 x
  (Add eL eR) -> peExpr2 (Add (Neg eL) (Neg eR))
  e2       -> (Neg e2)
peExpr2 (Add eL eR) =
  case (peExpr2 eL, peExpr2 eR) of
    ((Num x), (Num y)) ->
      (Num (x + y))
    ((Num x), (Add (Num y) eR2)) ->
      peExpr2 ((Add (Num (x+y)) eR2))
    ((Add a b), (Add c d)) ->
      peExpr2 (Add a (Add b (Add c d)))
    ((Num 0), eR2) -> eR2
    (eL2, (Add (Num x) eR2)) ->
      peExpr2 (Add (Num x) (Add eL2 eR2))
    (eL2@(Add _ _), eR2) ->
      peExpr2 (Add eR2 eL2)
    (eL2 , (Num x)) ->
      peExpr2 (Add (Num x) eL2)
    (eL2, eR2) -> (Add eL2 eR2)



--peExpr2 (Add eL eR) =
--  case peExpr2 eL of
--    (Num x) ->
--      case peExpr2 eR of
--        (Num y)         -> (Num (x+y))
--        (Add (Num y) e) -> (Add (Num (x+y)) (peExpr2 e))
--        eR2             -> (Add (Num x) eR2)
--
--    (Add eL2 eR2) -> case peExpr2 eL2 of
--      (Num x) ->
--
--    eL2     ->
--      case peExpr eR of
--        eR2@(Num _)   -> peExpr2 (Add eR2 eL2)
--        eR2@(Add _ _) -> peEXpr (Add eR2 eL2)
--        eR2           -> (Add eL2 eR2)

peExpr2 (Num x) = (Num x)
peExpr2 Read = Read
