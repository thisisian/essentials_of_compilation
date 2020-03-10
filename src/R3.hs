{-# OPTIONS_GHC -fno-warn-missing-signatures #-}

module R3 where

import Control.Applicative
import Control.Exception (TypeError(..))
import Control.Monad.State
import Data.Map (Map)
import qualified Data.Map as M
import qualified Data.Vector.Mutable as MV
import Data.Foldable
import Text.Parsec.Token
import Text.Parsec.Language
import Text.Parsec (oneOf, letter, alphaNum, try)

import Test.Tasty.QuickCheck

import qualified Text.Parsec as Parsec (parse)

import Common

data Program b a = Program b (Expr a)

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

data Compare = Eq | Lt | Le | Gt | Ge
  deriving Eq

data Type = TBool | TNum | TVector [Type] | TVoid
  deriving Eq

data Val = VBool Bool | VNum Int | VVector (MV.IOVector Val) | VVoid

instance Eq Val where
  (==) (VBool b1) (VBool b2) = b1 == b2
  (==) (VNum x) (VNum y) = x == y
  (==) VVoid VVoid = True
  (==) _ _ = False

instance Show Val where
  show (VBool b) = show b
  show (VNum x) = show x
  show (VVector _) = "[Vector]"
  show (VVoid) = "void"

{----- Show Instances -----}

instance (Show b) => Show (Program b a) where
  show (Program i e) = "(program " ++ show i ++ "\n" ++ show e ++ ")"

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

instance Show Compare where
  show Eq = "eq?"
  show Lt = "<"
  show Le = "<="
  show Gt = ">"
  show Ge = ">="

instance Show Type where
  show TBool = "Bool"
  show TNum  = "Num"
  show (TVector tys) = "Vector " ++ show tys
  show TVoid = "Void"

{----- Parser -----}

parse :: Parser (Program () ())
parse = Parsec.parse pProgram ""

parseError :: String -> (Program () ())
parseError s = case Parsec.parse pProgram "" s of
  Left e -> error $ show e
  Right s' -> s'

pProgram = Program () <$> pExpr

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

pCmp = pReservedOp "eq?" *> return Eq
     <|> pReservedOp "<" *> return Lt
     <|> pReservedOp "<=" *> return Le
     <|> pReservedOp ">" *> return Gt
     <|> pReservedOp ">=" *> return Ge

pVar = Var <$> return() <*> pIdent

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
               , identLetter = alphaNum
               , opStart = oneOf "+-<>e"
               , opLetter = oneOf "+-<>=eq?"
               , reservedNames = ["read", "let", "#t", "#f"
                                 , "not", "and", "or", "cmp", "if"
                                 , "vector", "vector-set!", "vector-ref"
                                 , "void" ]
               , reservedOpNames = ["+", "-", "<", ">", "<=", ">=", "eq?"]
               }

{----- Interpreter -----}


type Env = Map String Val

interp :: [Int] -> (Program b a) -> IO (Val)
interp inputs (Program _ e) = evalStateT (interpExpr M.empty e) inputs

interpExpr :: Env -> (Expr a) -> StateT [Int] IO Val
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
interpExpr _ (Collect _) = undefined
interpExpr _ (Allocate _ _) = undefined
interpExpr _ (GlobalValue _) = undefined

interpBinArithOp
  :: Env
  -> (Int -> Int -> Int)
  -> Expr a
  -> Expr a
  -> StateT [Int] IO Val
interpBinArithOp env op eL eR = do
  ~(VNum x) <- interpExpr env eL
  ~(VNum y) <- interpExpr env eR
  return $ VNum (x `op` y)

interpBinCmpOp
  :: Env
  -> (Int -> Int -> Bool)
  -> Expr a
  -> Expr a
  -> StateT [Int] IO Val
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

{----- Type Checker -----}

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

typeCheck :: Program () () -> Either TypeError (Program () Type)
typeCheck (Program _ e) = Program () <$> typeChkExpr M.empty e

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
  Nothing -> Left . TypeError $ "Failed to find binding for " ++ s
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

{----- Arbitrary Instances -----}

testArbitrary = sample (arbitrary :: Gen (Program () ()))

instance Arbitrary (Program () ()) where
  arbitrary = Program () <$> arbitrary

instance Arbitrary (Expr ()) where
  arbitrary = genExpr M.empty Nothing
  shrink (Neg e) = [Num 0, e] ++ [ Neg e' | e' <- shrink e ]
  shrink (Add eL eR) =
    [Num 0, eL, eR] ++ [ Add eL' eR' | (eL', eR') <- shrink (eL, eR) ]
  shrink (Sub eL eR) =
    [Num 0, eL, eR] ++ [ Sub eL' eR' | (eL', eR') <- shrink (eL, eR) ]
  shrink (And eL eR) =
    [T, F, eL, eR] ++ [ And eL' eR' | (eL', eR') <- shrink (eL, eR) ]
  shrink (Or eL eR) =
    [T, F, eL, eR] ++ [ Or eL' eR' | (eL', eR') <- shrink (eL, eR) ]
  shrink (Not e) = [T, F, e] ++ [ Not e' | e' <- shrink e ]
  shrink (Cmp c eL eR) =
    [T, F, eL, eR] ++ [ Cmp c eL' eR' | (eL', eR') <- shrink (eR, eR) ]
  shrink (If _ e eT eF) =
    [eT, eF] ++ [ If () e' eT' eF' | (e', eT', eF') <- shrink (e, eT, eF) ]
  shrink Read = [Num 0]


genExpr :: Map String Type -> Maybe Type -> Gen (Expr ())
genExpr env ty = sized $ \n -> do
  let n' = if n <= 0 then 0 else n-1
  resize n' (nextGen n)

 where
   nextGen n =
     if (n == 0) then
       case ty of
         Nothing ->
           if M.null env then oneof [ boolVals, numVals ]
           else oneof [ boolVals, numVals, varVals ]
         Just TBool ->
           if M.null . M.filter (== TBool) $ env then boolVals
           else oneof [ boolVals, varVals ]
         Just TNum ->
           if M.null . M.filter (== TNum) $ env then numVals
           else oneof [ numVals, varVals ]
     else do
       case ty of
         Nothing ->
           if M.null env then
             oneof
               [ boolVals, numVals,  binOps, arithOps, letExpr, ifExpr ]
           else
             oneof
               [ boolVals, numVals, varVals, binOps, arithOps, letExpr, ifExpr ]
         Just TBool ->
           if M.null . M.filter (== TBool) $ env then
             oneof
               [ boolVals, binOps, letExpr, ifExpr ]
           else
             oneof
               [ boolVals, varVals, binOps , letExpr, ifExpr ]
         Just TNum ->
           if M.null . M.filter (== TNum) $ env then
             oneof
               [ numVals, arithOps, letExpr, ifExpr ]
           else
             oneof
               [ varVals, numVals, arithOps, letExpr, ifExpr ]

   boolVals :: Gen (Expr ())
   boolVals = oneof [return T, return F]

   numVals :: Gen (Expr ())
   numVals = frequency
     [ (5, Num <$> arbitrary)
     , (1, return Read) ]

   varVals :: Gen (Expr ())
   varVals = oneof $
       map (return . Var ())
       . M.keys
       . M.filter (\t -> case ty of
                     Nothing -> True
                     Just TBool -> t == TBool
                     Just TNum -> t == TNum)
       $ env

   arithOps :: Gen (Expr ())
   arithOps = oneof
     [ Neg <$> genExpr env (Just TNum)
     , Add <$> genExpr env (Just TNum) <*> genExpr env (Just TNum)
     , Sub <$> genExpr env (Just TNum) <*> genExpr env (Just TNum) ]

   binOps :: Gen (Expr ())
   binOps = oneof
     [ Not <$> genExpr env (Just TBool)
     , Cmp <$> arbitrary <*> genExpr env (Just TNum) <*> genExpr env (Just TNum)
     , Or <$> genExpr env (Just TBool) <*> genExpr env (Just TBool)
     , And <$> genExpr env (Just TBool) <*> genExpr env (Just TBool)
     ]

   ifExpr :: Gen (Expr ())
   ifExpr = do
     tyChoice <- oneof [return (Just TBool), return (Just TNum)]
     let ty' = if ty == Nothing then tyChoice else ty
     If () <$> genExpr env (Just TBool) <*> genExpr env ty' <*> genExpr env ty'

   letExpr :: Gen (Expr ())
   letExpr = do
     name <- growingElements (map (:[]) ['a' .. 'z'])
     ty' <- oneof [return TNum, return TBool]
     let env' = M.insert name ty' env
     Let () name <$> genExpr env (Just ty') <*> genExpr env' ty

instance Arbitrary Compare where
  arbitrary = elements [Eq, Lt, Gt, Le, Ge]
