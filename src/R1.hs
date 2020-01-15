{-# OPTIONS_GHC -fno-warn-missing-signatures #-}

module R1 where

import Control.Applicative
import Control.Monad
import Control.Monad.State

import qualified C0 as C0

import Text.Parsec.Token
import Text.Parsec.Language
import Text.Parsec (oneOf, parse, letter, alphaNum)

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
testParse :: String -> IO ()
testParse s = case parse pProgram "" s of
 Left er -> print er
 Right p -> print p

doParse :: String -> Program
doParse s = case parse pProgram "" s of
  Left err -> error $ show err
  Right p  -> p

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
  e <- pExpr
  return (Let v be e)

pBinding = do
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

{- Partial evaluator -}

testPE :: String -> String
testPE s = show . pe . doParse $ s

pe :: Program -> Program
pe (Pgrm i e) = Pgrm i $ peExpr e

peExpr :: Expr -> Expr
peExpr (Neg (Num n)) = Num (0 - n)
peExpr (Neg (Add eL eR)) = peExpr (Add (Neg eL) (Neg eR))
peExpr (Neg (Neg x)) = peExpr x
peExpr (Add (Num x) (Num y)) = (Num (x+y))
peExpr (Add (Num 0) e) = peExpr e
peExpr (Add (Num x) (Add (Num y) e)) = peExpr (Add (Num (x+y)) e)
peExpr (Add (Add a b) (Add c d)) = peExpr (Add a (Add b (Add c d)))
peExpr (Add e (Num x)) = peExpr (Add (Num x) e)
peExpr (Add e1 (Add (Num x) e2)) = peExpr (Add (Num x) (Add e1 e2))
peExpr (Add e1@(Add _ _) e2) = peExpr (Add e2 e1)
peExpr (Add eL eR) =
  case (peExpr eL, peExpr eR) of
    (eL2, (Add (Num x) eR2)) ->
      peExpr (Add (Num x) (Add eL2 eR2))
    (eL2, eR2) -> (Add eL2 eR2)
peExpr e = e

{- Uniqify Variables -}

type SymbolTable = M.Map String String

uniquify :: Program -> Program
uniquify (Pgrm i e) = Pgrm i $ evalState (uniquifyExpr M.empty e) 0

uniquifyExpr :: SymbolTable -> Expr -> State Int Expr
uniquifyExpr st (Neg e) = Neg <$> uniquifyExpr st e
uniquifyExpr st (Add eL eR) =
  return Add `ap` (uniquifyExpr st eL) `ap` (uniquifyExpr st eR)
uniquifyExpr st (Var name) =
  case M.lookup name st of
    Just name' -> return (Var name')
    Nothing -> error $ "Symbol " ++ name ++ " not found in symbol table"
uniquifyExpr st (Let name be e) = do
  name' <- fresh
  let st' = M.insert name name' st
  be' <- uniquifyExpr st be
  e' <- uniquifyExpr st' e
  return (Let name' be' e')
uniquifyExpr _ e = return e

fresh :: State Int String
fresh = do
  i <- get
  put (i+1)
  return ("_x"++show i)

{- Remove Complex Operators and Operands -}

rco :: Program -> Program
rco (Pgrm i e) = Pgrm i $ evalState (rcoExpr e) 0

freshTemp :: State Int String
freshTemp = do
  i <- get
  put (i+1)
  return ("_temp"++show i)

rcoExpr :: Expr -> State Int Expr
rcoExpr (Num x) = return (Num x)
rcoExpr Read = return Read
rcoExpr (Var name) = return (Var name)
rcoExpr (Neg e) = do
  (bindings, e') <- rcoArg e
  return (makeBindings bindings (Neg e'))
rcoExpr (Add eL eR) = do
  (bindingsL, eL') <- rcoArg eL
  (bindingsR, eR') <- rcoArg eR
  return (makeBindings (bindingsL++bindingsR) (Add eL' eR'))
rcoExpr (Let name be e) = do
  e' <- rcoExpr e
  return (Let name be e')

rcoArg :: Expr -> State Int ([(String, Expr)], Expr)
rcoArg (Num x) = return ([], (Num x))
rcoArg (Var name) = return ([], (Var name))
rcoArg (Read) = return ([], Read)
rcoArg (Neg e) = do
  (bindings, e') <- rcoArg e
  n <- freshTemp
  return $ (bindings ++ [(n, (Neg e'))]
           , Var n)
rcoArg (Add eL eR) = do
  (bindingsL, eL') <- rcoArg eL
  (bindingsR, eR') <- rcoArg eR
  n <- freshTemp
  return $ (bindingsL ++ bindingsR ++ [(n, (Add eL' eR'))]
           , Var n)
rcoArg (Let n be e) = do
  (bindingsBE, be') <- rcoArg be
  (bindings, e') <- rcoArg e
  return ((n, be') : (bindings ++ bindingsBE), e')

makeBindings :: [(String, Expr)] -> Expr -> Expr
makeBindings ((b, be):bs) e =
  (Let b be (makeBindings bs e))
makeBindings [] e = e

--test :: String -> IO ()
--test s = do
--  putStrLn $ show . rco . doParse $ s
--  putStrLn $ "Eval: " ++ show ref
--  putStrLn $ "Eval':" ++ show act
-- where
--  parsed = doParse s
--  ref = interp [0,5..] parsed
--  act = interp [0,5..] . rco . uniquify $ parsed
--
--
--
--test1 = "(- (let ([y 1]) (- (- y))))"

explicateControl :: Program -> C0.Program
explicateControl (Pgrm _ e) = C0.Pgrm (C0.Locals []) $ [("start", ecTail e)]

ecTail :: Expr -> C0.Tail
ecTail (Let n be e) = C0.Seq (C0.Assign n (ecExpr be)) (ecTail e)
ecTail e = C0.Return (ecExpr e)

ecExpr :: Expr -> C0.Expr
ecExpr Read = C0.Read
ecExpr (Add eL eR) = C0.Plus (ecArg eL) (ecArg eR)
ecExpr (Neg e) = C0.Neg (ecArg e)
ecExpr e = (C0.Plain (ecArg e))

ecArg :: Expr -> C0.Arg
ecArg (Num x) = C0.Num x
ecArg (Var x) = C0.Var x
ecArg e = error $ "Called ecArg on " ++ show e
