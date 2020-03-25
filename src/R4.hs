{-# OPTIONS_GHC -fno-warn-missing-signatures #-}

module R4 where

import Control.Applicative
import Control.Exception (TypeError(..))
import Control.Monad.State
import Data.Map (Map)
import qualified Data.Map as M
import qualified Data.Vector.Mutable as MV
import Data.Foldable
import Data.List
import Text.Parsec.Token
import Text.Parsec.Language
import Text.Parsec (oneOf, letter, alphaNum, parseTest)

import Test.Tasty.QuickCheck

import Text.Parsec (try, many1)
import qualified Text.Parsec as Parsec (parse)

import Common

type Env a = Map String (Val a)

data Program b a c = Program b [Def a c] (Expr a)

data Expr a
  = Num Int
  | Read
  | Neg (Expr a)
  | Add (Expr a) (Expr a)
  | Sub (Expr a) (Expr a)
  | Var a String
  | Let a String (Expr a) (Expr a)
  | T
  | F
  | And (Expr a) (Expr a)
  | Or (Expr a) (Expr a)
  | Not (Expr a)
  | Cmp Compare (Expr a) (Expr a)
  | If a (Expr a) (Expr a) (Expr a)
  | Vector a [Expr a]
  | VectorRef a (Expr a) Int
  | VectorSet (Expr a) Int (Expr a)
  | Void
  | Collect Int
  | Allocate Int Type
  | GlobalValue String
  | App a (Expr a) [Expr a]
  | FunRef a String

data Def a b = Define String [(String, Type)] Type b (Expr a)

data Compare = Eq | Lt | Le | Gt | Ge
  deriving Eq

data Type = TBool | TNum | TVector [Type] | TVoid | TFunc [Type] Type
  deriving Eq

data Val a = VBool Bool | VNum Int | VVector (MV.IOVector (Val a)) | VVoid
           | VLambda [String] (Expr a) (Env a)

instance Eq (Val a) where
  (==) (VBool b1) (VBool b2) = b1 == b2
  (==) (VNum x) (VNum y) = x == y
  (==) VVoid VVoid = True
  (==) _ _ = False

instance Show (Val a) where
  show (VBool b) = show b
  show (VNum x) = show x
  show (VVector _) = "[Vector]"
  show (VVoid) = "void"
  show (VLambda args body env) = "lambda args:" ++ show args ++ " body: " ++
    show body ++ " env: " ++ show env

{----- Show Instances -----}

instance (Show b) => Show (Program b a c) where
  show (Program i d e) = intercalate " " (map show d) ++ " " ++ show e
--"(program " ++ show i ++ "\n" ++ show d ++ "\n" ++ show e ++ ")"

instance Show (Expr a) where
  show (Num x) = show x
  show Read = "(read)"
  show (Neg e) = "(- " ++ show e ++ ")"
  show (Add eL eR) =
    "(+ " ++ show eL ++ " " ++ show eR ++ ")"
  show (Sub eL eR) =
    "(- " ++ show eL ++ " " ++ show eR ++ ")"
  show (Var _ s) = s
  show (Let _ v be e) =
    "(let ([" ++ v ++ " " ++ show be ++ "]) " ++ show e ++ ")"
  show T = "#t"
  show F = "#f"
  show (And eL eR) = "(and " ++ show eL ++ " " ++ show eR ++ ")"
  show (Or eL eR) = "(or " ++ show eL ++ " " ++ show eR ++ ")"
  show (Not e) = "(not " ++ show e ++ ")"
  show (Cmp c eL eR) =
    "(cmp " ++ show c ++ " " ++ show eL ++ " " ++ show eR ++ ")"
  show (If _ e eT eF) =
    "(if " ++ show e ++ " " ++ show eT ++ " " ++ show eF ++ ")"
  show (Vector _ es) = "(vector " ++ unwords (map show es) ++ ")"
  show (VectorRef _ e idx) =
    "(vector-ref " ++ show e ++ " " ++ show idx ++ ")"
  show (VectorSet e1 idx e2) =
    "(vector-set! " ++ show e1 ++ " " ++ show idx ++ " " ++ show e2 ++ ")"
  show (Void) = "(void)"
  show (Collect x) = "(collect " ++ show x ++ ")"
  show (Allocate x ty) = "(allocate " ++ show x ++ " " ++ show ty ++ ")"
  show (GlobalValue s) = "(global-value " ++ s ++ ")"
  show (App _ e eArgs) = "(" ++ show e ++ " " ++ (intercalate " " (map show eArgs)) ++ ")"

instance Show Compare where
  show Eq = "eq?"
  show Lt = "<"
  show Le = "<="
  show Gt = ">"
  show Ge = ">="

instance Show Type where
  show TBool = "Bool"
  show TNum  = "Integer"
  show (TVector tys) = "(" ++  intercalate " " (["Vector"] ++ map show tys) ++ ")"
  show TVoid = "Void"
  show (TFunc argTys retTy) =
    "(" ++ intercalate " " (map show argTys) ++ " -> " ++ show retTy ++ ")"

instance Show (Def a b) where
  show (Define fname varTys retTy _ e) = "(define (" ++ fname ++ " " ++ showVT varTys ++ ") : " ++ show retTy ++ " " ++ show e ++ ")"
   where
    showVT ts =
      intercalate " " (map (\(s, ty) -> "[" ++ s ++ " : " ++ show ty ++ "]") ts)
    showVT [] = []


{----- Parser -----}

parse = Parsec.parse pProgram ""

parseError :: String -> (Program () () ())
parseError s = case Parsec.parse pProgram "" s of
  Left e -> error $ show e
  Right s' -> s'

pProgram = Program () <$> many (try pDef) <*> pExpr

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
      <|> pReserved "if" *> (If () <$> pExpr <*> pExpr <*> pExpr)
      <|> pReserved "vector-ref" *> (VectorRef () <$> pExpr <*> pInt )
      <|> pReserved "vector-set!" *> (VectorSet <$> pExpr <*> pInt <*> pExpr)
      <|> pReserved "vector" *> (Vector () <$> many pExpr)
      <|> pReserved "void" *> return Void
      <|> App () <$> pExpr <*> many1 pExpr

pCmp = pReservedOp "eq?" *> return Eq
     <|> pReservedOp "<" *> return Lt
     <|> pReservedOp "<=" *> return Le
     <|> pReservedOp ">" *> return Gt
     <|> pReservedOp ">=" *> return Ge

pVar = Var <$> return() <*> pIdent

pType =
      pReserved "Integer" *> return TNum
      <|> pReserved "Boolean" *> return TBool
      <|> pReserved "Void" *> return TVoid
      <|> try (pParens (pReserved "Vector" *> (TVector <$> many1 pType)))
      <|> (pParens (do
                       argTys <- many pType
                       pReservedOp "->"
                       retTy <- pType
                       return $ TFunc argTys retTy))

pDef =
  pParens $ do
    pReserved "define"
    (fname, varTys) <- pParens (do
                                   fname <- pIdent
                                   varTys <- many (varTypeBind)
                                   return (fname, varTys))
    pReservedOp ":"
    retTy <- pType
    expr <- pExpr
    return $ Define fname varTys retTy () expr

 where
  varTypeBind =
    pBrackets $ do
      s <- pIdent
      pReservedOp ":"
      ty <- pType
      return (s, ty)

pTrue = pReserved "#t" *> return T

pFalse = pReserved "#f" *> return F

pLet = do
  pReserved "let"
  (v, be) <- pBinding
  Let () v be <$> pExpr

pBinding =
  pParens (pBrackets (do v <- pIdent; e <- pExpr ; return (v, e)))

pNum = Num <$> pInt

pInt = do
  int <- pInteger
  return (fromIntegral $ int)

TokenParser { parens = pParens
            , brackets = pBrackets
            , identifier = pIdent
            , reservedOp = pReservedOp
            , reserved = pReserved
            , integer = pInteger
            , whiteSpace = pWhiteSpace } = makeTokenParser def

def = emptyDef { commentLine = ";;"
               , identStart = letter
               , identLetter = alphaNum <|> oneOf "-'"
               , opStart = oneOf "+-<>e:"
               , opLetter = oneOf "+-<>=eq?:"
               , reservedNames = ["read", "let", "#t", "#f"
                                 , "not", "and", "or", "cmp", "if"
                                 , "vector", "vector-set!", "vector-ref"
                                 , "void", "define"]
               , reservedOpNames = [ "+" , "-" , "<", ">"
                                   , "<=", ">=", "eq?" ]
               }

{----- Interpreter -----}

interp :: [Int] -> (Program b a c) -> IO (Val a)
interp inputs (Program _ ds e) = evalStateT (interpExpr topLevelEnv e) inputs
 where topLevelEnv =
         M.map (\(VLambda args body _) -> VLambda args body topLevelEnv')
         topLevelEnv'

        where topLevelEnv' =
                M.fromList
                . map (\(Define s args _ _ body) ->
                       (s, VLambda (map fst args) body M.empty))
                $ ds
-- APT: Although this is what the book said to do, it seems unnecessarily awkward to me for this language.
-- (I guess it will make more sense for the next chapter, where functions can be defined locally.)
-- A more standard solution is to build the topLevelEnv and then simply pass it as an additional
-- (unhanging) parameter to the interpreter, to be consulted in the Var case if the usual
-- local envrionment doesn't have a binding. 

interpExpr :: (Env a) -> (Expr a) -> StateT [Int] IO (Val a)
interpExpr _ (Num x) = return $ VNum x
interpExpr _ Read = do
  x <- nextInput
  return $ VNum x
interpExpr env (Neg e) = do
  ~(VNum x) <- interpExpr env e
  return $ VNum (negate x)
interpExpr env (Add eL eR) = interpBinArithOp env (+) eL eR
interpExpr env (Sub eL eR) = interpBinArithOp env (-) eL eR
interpExpr env (Let _ v be e) = do
  val <- interpExpr env be
  let newEnv = M.insert v val env
  interpExpr newEnv e
interpExpr env (Var _ v) = case M.lookup v env of
  Just e -> return e
  Nothing -> error $ "Variable " ++ v ++ " not found in env"
interpExpr _ T = return $ VBool True
interpExpr _ F = return $ VBool False
interpExpr env (And eL eR) = do
  ~(VBool vL) <- interpExpr env eL
  if vL == False
    then return $ VBool False
    else interpExpr env eR
interpExpr env (Or eL eR) = do
  ~(VBool vL) <- interpExpr env eL
  if vL == True
    then return $ VBool True
    else interpExpr env eR
interpExpr env (Not e) = do
  ~(VBool v) <- interpExpr env e
  if v == True then return (VBool False) else return (VBool True)
interpExpr env (Cmp Eq eL eR) = interpBinCmpOp env (==) eL eR
interpExpr env (Cmp Lt eL eR) = interpBinCmpOp env (<) eL eR
interpExpr env (Cmp Le eL eR) = interpBinCmpOp env (<=) eL eR
interpExpr env (Cmp Gt eL eR) = interpBinCmpOp env (>) eL eR
interpExpr env (Cmp Ge eL eR) = interpBinCmpOp env (>=) eL eR
interpExpr env (If _ e eT eF) = do
  ~(VBool v) <- interpExpr env e
  if v == True
    then interpExpr env eT
    else interpExpr env eF
interpExpr env (Vector _ es) = do
  es' <- mapM (interpExpr env) es
  mV <- liftIO (mkNewVector es')
  return $ VVector mV
interpExpr env (VectorRef _ vec idx) = do
  ~(VVector refVs) <- interpExpr env vec
  liftIO (MV.read refVs idx)
interpExpr env (VectorSet vec idx val) = do
  ~(VVector refVs) <- interpExpr env vec
  val' <- interpExpr env val
  liftIO (MV.write refVs idx val')
  return (VVoid)
interpExpr _ (Void) = return (VVoid)
interpExpr env (App _ e es) = do
  ~(VLambda args body lEnv) <- interpExpr env e
  argEnv <- M.fromList . zip args <$> mapM (interpExpr env) es
  let env' = M.union argEnv (M.union lEnv env)
  interpExpr env' body
interpExpr _ _ = undefined

interpBinArithOp
  :: (Env a)
  -> (Int -> Int -> Int)
  -> Expr a
  -> Expr a
  -> StateT [Int] IO (Val a)
interpBinArithOp env op eL eR = do
  ~(VNum x) <- interpExpr env eL
  ~(VNum y) <- interpExpr env eR
  return $ VNum (x `op` y)

interpBinCmpOp
  :: (Env a)
  -> (Int -> Int -> Bool)
  -> Expr a
  -> Expr a
  -> StateT [Int] IO (Val a)
interpBinCmpOp env op eL eR = do
  ~(VNum vL) <- interpExpr env eL
  ~(VNum vR) <- interpExpr env eR
  if vL `op` vR
    then return $ VBool True
    else return $ VBool False

nextInput :: StateT [Int] IO Int
nextInput = do
  is' <- get
  case is' of
    (i:is) -> do
      put is
      return i
    _ -> error "Read was called, but no more inputs remain"


mkNewVector :: [a] -> IO (MV.IOVector a)
mkNewVector as = do
  newMv <- MV.new (length as)
  mV' <- copy newMv (zip [0..] as)
  return mV'
 where
  copy mV as' = do
   traverse_ (\(i, a) -> MV.write mV i a) as'
   return mV

--{----- Type Checker -----} --
getType :: Expr Type -> Type
getType (Num _) = TNum
getType Read = TNum
getType (Neg _) = TNum
getType (Add _ _) = TNum
getType (Sub _ _) = TNum
getType (Var t _) = t
getType (Let t _ _ _) = t
getType T = TBool
getType F = TBool
getType (And _ _) = TBool
getType (Or _ _) = TBool
getType (Not _) = TBool
getType (Cmp _ _ _) = TBool
getType (If t _ _ _) = t
getType (Vector t _) = t
getType (VectorRef t _ _) = t
getType (VectorSet _ _ _) = TVoid
getType Void = TVoid
getType (Collect _) = TVoid
getType (Allocate _ _) = TVoid
getType (GlobalValue _) = TNum
getType (App t _ _) = t
getType (FunRef t _) = t


typeCheck :: Program () () () -> Either TypeError (Program () Type ())
typeCheck (Program _ ds e) = do
  ds' <- traverse (typeChkDef topLevel) ds
  Program () ds' <$> typeChkExpr topLevel e
 where topLevel = M.fromList . map (\(Define s argTys retTy _ _) ->
                                      (s, TFunc (map snd argTys) retTy)) $ ds

typeChkDef :: Map String Type -> Def () () -> Either TypeError (Def Type ())
typeChkDef env (Define s argTys retTy () e) = do
  e' <- typeChkExpr (M.union (M.fromList argTys) env) e
  let ty = getType e'
  if ty == retTy
    then Right (Define s argTys retTy () e')
    else Left (TypeError $ "Typecheck of function " ++ s ++
               " failed. Expected " ++ show retTy ++ " but got " ++
               show ty)

typeChkExpr :: Map String Type -> Expr () -> Either TypeError (Expr Type)
typeChkExpr _ (Num x) = return (Num x)
typeChkExpr _ Read  = return Read
typeChkExpr env (Neg e) = do
  e' <- typeChkUniOp TNum env e
  return $ Neg e'
typeChkExpr env (Add eL eR) = do
  (eL', eR') <- typeChkBinOp TNum env eL eR
  return $ Add eL' eR'
typeChkExpr env (Sub eL eR) = do
  (eL', eR') <- typeChkBinOp TNum env eL eR
  return $ Sub eL' eR'
typeChkExpr env (Var _ s) = case M.lookup s env of
  Just t -> Right (Var t s)
  Nothing -> Left . TypeError $ "Failed to find binding for " ++ s ++ "\n" ++ show env
typeChkExpr env (Let _ s bE e) = do
  bE' <- typeChkExpr env bE
  let env' = M.insert s (getType bE') env
  e' <- typeChkExpr env' e
  return $ Let (getType e') s bE' e'
typeChkExpr _ T = return T
typeChkExpr _ F = return F
typeChkExpr env (And eL eR) = do
  (eL', eR') <- typeChkBinOp TBool env eL eR
  return $ And eL' eR'
typeChkExpr env (Or eL eR) = do
  (eL', eR') <- typeChkBinOp TBool env eL eR
  return $ Or eL' eR'
typeChkExpr env (Not e) = do
  e' <- typeChkUniOp TBool env e
  return $ Not e'
typeChkExpr env (Cmp c eL eR) = do
  (eL', eR') <- typeChkBinOp TNum env eL eR
  return $ (Cmp c eL' eR')
typeChkExpr env (If _ cond eT eF) = do
  cond' <- typeChkExpr env cond
  case getType cond' of
    TBool -> do
      eT' <- typeChkExpr env eT
      eF' <- typeChkExpr env eF
      let truTy = getType eT'
          falTy = getType eF'
      if truTy == falTy
        then Right (If truTy cond' eT' eF')
        else Left . TypeError $ "Branches of If expression don't match. Got " ++
          show truTy ++ " and " ++ show falTy
    t -> Left . TypeError  $ "Test of If expression is of type " ++ show t
typeChkExpr env (Vector _ es) = do
  es' <- mapM (typeChkExpr env) es
  let tys = map getType es'
  return $ Vector (TVector tys) es'
typeChkExpr env (VectorRef _ e idx) = do
  e' <- typeChkExpr env e
  case getType e' of
    TVector ts ->
      let ty = ts !! idx
      in return $ (VectorRef ty e' idx)
    ty -> Left . TypeError $ "TypeRef expects a vector type, but got " ++ show ty
typeChkExpr env (VectorSet eV idx eSet) =do
  eV' <- typeChkExpr env eV
  case getType eV' of
    TVector ts -> do
      let ty = ts !! idx
      eSet' <- typeChkExpr env eSet
      let setTy = getType eSet'
      if setTy == ty
        then return $ VectorSet eV' idx eSet'
        else Left . TypeError $ "VectorSet expected type " ++ show ty ++
             " but got " ++ show setTy
    ty -> Left . TypeError $ "VectorSet expects vector type, but got " ++ show ty
typeChkExpr env (App _ fe args) = do
  fe' <- typeChkExpr env fe
  case getType fe' of
    (TFunc argTys retTy) -> do
      args' <- mapM (typeChkExpr env) args
      let arg'Tys = map getType args'
      if arg'Tys == argTys
        then Right (App retTy fe' args')
        else Left . TypeError $ "Failed to typecheck App"
    _ -> Left . TypeError $ "Argument to App is not a function type"

typeChkExpr _ Void = return Void
typeChkExpr _ (Collect a) = return (Collect a)
typeChkExpr _ (Allocate a b) = return (Allocate a b)
typeChkExpr _ (GlobalValue a) = return (GlobalValue a)

typeChkUniOp :: Type -> Map String Type
             -> Expr () -> Either TypeError (Expr Type)
typeChkUniOp argTy env e = do
  e' <- typeChkExpr env e
  let ty = getType e'
  if ty == argTy
   then Right $ e'
   else Left . TypeError $ "Unary op expected " ++ show argTy ++
         " but got " ++ show ty

typeChkBinOp :: Type -> Map String Type -> Expr () -> Expr ()
             -> Either TypeError (Expr Type, Expr Type)
typeChkBinOp argTy env eL eR = do
  eL' <- typeChkExpr env eL
  eR' <- typeChkExpr env eR
  let (tL, tR) = (getType eL', getType eR')
  if (tL, tR) == (argTy, argTy)
    then Right (eL', eR')
    else Left . TypeError $ "BinOp expected " ++ show argTy ++ " and " ++
      show argTy ++ " but got " ++ show tL ++
      " and " ++ show tR
