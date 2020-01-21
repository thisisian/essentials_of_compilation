module Chapter2 where

import qualified Data.Map as M

import Control.Monad
import Control.Monad.State

import qualified R1
import qualified C0
import qualified PsuedoX860 as PX
import qualified X860 as X

import Common

compile :: R1.Program -> String
compile =
  prettyPrint
  . patchInstructions
  . assignHomes
  . selectInstructions
  . uncoverLocals
  . explicateControl
  . rco
  . uniquify

{- Uniqify Variables -}

type SymbolTable = M.Map String String

uniquify :: R1.Program -> R1.Program
uniquify (R1.Pgrm i e) = R1.Pgrm i $ evalState (uniquifyExpr M.empty e) 0

uniquifyExpr :: SymbolTable -> R1.Expr -> State Int R1.Expr
uniquifyExpr st (R1.Neg e) = R1.Neg <$> uniquifyExpr st e
uniquifyExpr st (R1.Add eL eR) =
  return R1.Add `ap` uniquifyExpr st eL `ap` uniquifyExpr st eR
uniquifyExpr st (R1.Var name) =
  case M.lookup name st of
    Just name' -> return (R1.Var name')
    Nothing -> error $ "Symbol " ++ name ++ " not found in symbol table"
uniquifyExpr st (R1.Let name be e) = do
  name' <- fresh
  let st' = M.insert name name' st
  be' <- uniquifyExpr st be
  e' <- uniquifyExpr st' e
  return (R1.Let name' be' e')
uniquifyExpr _ e = return e

fresh :: State Int String
fresh = do
  i <- get
  put (i+1)
  return ("_x"++show i)

{- Remove Complex Operators and Operands -}

rco :: R1.Program -> R1.Program
rco (R1.Pgrm i e) = R1.Pgrm i $ evalState (rcoExpr e) 0

freshTemp :: State Int String
freshTemp = do
  i <- get
  put (i+1)
  return ("_temp"++show i)

rcoExpr :: R1.Expr -> State Int R1.Expr
rcoExpr (R1.Num x) = return (R1.Num x)
rcoExpr R1.Read = return R1.Read
rcoExpr (R1.Var name) = return (R1.Var name)
rcoExpr (R1.Neg e) = do
  (bindings, e') <- rcoArg e
  return (makeBindings bindings (R1.Neg e'))
rcoExpr (R1.Add eL eR) = do
  (bindingsL, eL') <- rcoArg eL
  (bindingsR, eR') <- rcoArg eR
  return (makeBindings (bindingsL++bindingsR) (R1.Add eL' eR'))
rcoExpr (R1.Let name be e) = do
  (bindingsBE, be') <- rcoArg be
  e' <- rcoExpr e
  return (makeBindings bindingsBE (R1.Let name be' e'))

rcoArg :: R1.Expr -> State Int ([(String, R1.Expr)], R1.Expr)
rcoArg (R1.Num x) = return ([], R1.Num x)
rcoArg (R1.Var name) = return ([], R1.Var name)
--rcoArg (R1.Read) = return ([], R1.Read)
rcoArg R1.Read = do
  n <- freshTemp
  return ([(n , R1.Read)] , R1.Var n)
rcoArg (R1.Neg e) = do
  (bindings, e') <- rcoArg e
  n <- freshTemp
  return (bindings ++ [(n, R1.Neg e')]
         , R1.Var n)
rcoArg (R1.Add eL eR) = do
  (bindingsL, eL') <- rcoArg eL
  (bindingsR, eR') <- rcoArg eR
  n <- freshTemp
  return (bindingsL ++ bindingsR ++ [(n, R1.Add eL' eR')]
         , R1.Var n)
rcoArg (R1.Let n be e) = do
  (bindingsBE, be') <- rcoArg be
  (bindings, e') <- rcoArg e
  return (bindingsBE ++ [(n, be')] ++ bindings, e')

makeBindings :: [(String, R1.Expr)] -> R1.Expr -> R1.Expr
makeBindings ((b, be):bs) e =
  R1.Let b be (makeBindings bs e)
makeBindings [] e = e

{- Explicate Control -}

explicateControl :: R1.Program -> C0.Program
explicateControl (R1.Pgrm _ e) =
  C0.Pgrm (C0.Locals []) [("start", ecTail e)]

ecTail :: R1.Expr -> C0.Tail
ecTail (R1.Let n be e) = C0.Seq (C0.Assign n (ecExpr be)) (ecTail e)
ecTail e = C0.Return (ecExpr e)

ecExpr :: R1.Expr -> C0.Expr
ecExpr R1.Read = C0.Read
ecExpr (R1.Add eL eR) = C0.Plus (ecArg eL) (ecArg eR)
ecExpr (R1.Neg e) = C0.Neg (ecArg e)
ecExpr e = C0.Plain (ecArg e)

ecArg :: R1.Expr -> C0.Arg
ecArg (R1.Num x) = C0.Num x
ecArg (R1.Var x) = C0.Var x
ecArg e = error $ "Called ecArg on " ++ show e

{- Uncover locals -}

uncoverLocals :: C0.Program -> C0.Program
uncoverLocals (C0.Pgrm _ [(s, t)]) =
  let locals = C0.Locals (collectLocals t)
  in C0.Pgrm locals [(s, t)]
uncoverLocals (C0.Pgrm _ _) = error "Expected only one label"

collectLocals :: C0.Tail -> [String]
collectLocals (C0.Seq (C0.Assign n _) t) = n : collectLocals t
collectLocals (C0.Return _) = []

{- Select Instructions -}

selectInstructions :: C0.Program -> PX.Program
selectInstructions (C0.Pgrm (C0.Locals vs) [(l, t)]) =
  PX.Program
    (PX.PInfo { PX.pInfoLocals = vs })
    [(l, PX.Block PX.BInfo (siTail t))]
selectInstructions (C0.Pgrm _ _) = error "Expected only one label"

siTail :: C0.Tail -> [PX.Instr]
siTail (C0.Return (C0.Plain a))    =
  [ PX.Movq (siArg a) (PX.Reg PX.Rax)
  , PX.Jmp "conclusion" ]
siTail (C0.Return C0.Read)         =
  [ PX.Callq "read_int"
  , PX.Jmp "conclusion" ]
siTail (C0.Return (C0.Neg a))      =
  [ PX.Movq (siArg a) (PX.Reg PX.Rax)
  , PX.Negq (PX.Reg PX.Rax)
  , PX.Jmp "conclusion" ]
siTail (C0.Return (C0.Plus aL aR)) =
  [ PX.Movq (siArg aL) (PX.Reg PX.Rax)
  , PX.Addq (siArg aR) (PX.Reg PX.Rax)
  , PX.Jmp "conclusion" ]
siTail (C0.Seq assign t) = siAssign assign ++ siTail t

siAssign :: C0.Assign -> [PX.Instr]
siAssign (C0.Assign s (C0.Plain a))    =
  [ PX.Movq (siArg a) (PX.Var s) ]
siAssign (C0.Assign s C0.Read)       =
  [ PX.Callq "read_int"
  , PX.Movq (PX.Reg PX.Rax) (PX.Var s) ]
siAssign (C0.Assign s (C0.Neg a))
  | a == C0.Var s =
    [ PX.Negq (PX.Var s) ]
  | otherwise    =
    [ PX.Movq (siArg a) (PX.Var s)
    , PX.Negq (PX.Var s) ]
siAssign (C0.Assign s (C0.Plus aL aR))
  | aL == C0.Var s =
    [ PX.Addq (siArg aR) (PX.Var s) ]
  | aR == C0.Var s =
    [ PX.Addq (siArg aL) (PX.Var s) ]
  | otherwise     =
    [ PX.Movq (siArg aL) (PX.Var s)
    , PX.Addq (siArg aR) (PX.Var s) ]

siArg :: C0.Arg -> PX.Arg
siArg (C0.Num x) = PX.Num x
siArg (C0.Var s) = PX.Var s

{- Assign Homes -}

assignHomes :: PX.Program -> X.Program
assignHomes (PX.Program info' bs') =
  X.Program info bs
 where
  info = X.PInfo (frameSize info')
  bs = map (\(l, b) -> (l, ahBlock locMap b)) bs'
  locMap = buildLocMap info'

ahBlock :: M.Map String Int -> PX.Block -> X.Block
ahBlock m (PX.Block _ instrs) =
  X.Block X.BInfo (map (ahInstr m) instrs)

ahInstr :: M.Map String Int -> PX.Instr -> X.Instr
ahInstr m (PX.Addq aL aR) = X.Addq (ahArg m aL) (ahArg m aR)
ahInstr m (PX.Movq aL aR) = X.Movq (ahArg m aL) (ahArg m aR)
ahInstr _ PX.Retq       = X.Retq
ahInstr m (PX.Negq a)     = X.Negq (ahArg m a)
ahInstr _ (PX.Callq s)    = X.Callq s
ahInstr _ (PX.Jmp s)    =   X.Jmp s
ahInstr _ i = error $ "Unimplemented: " ++ show i

ahArg :: M.Map String Int -> PX.Arg -> X.Arg
ahArg _ (PX.Num x) = X.Num x
ahArg m (PX.Var s) = case M.lookup s m of
  Nothing -> error $ "Assign homes: Variable " ++ s ++ " not found in map."
  Just n  -> X.Deref X.Rbp n
ahArg _ (PX.Reg PX.Rax) = X.Reg X.Rax
ahArg _ _ = undefined

buildLocMap :: PX.PInfo -> M.Map String Int
buildLocMap pInfo = M.fromList (zip locals [-8,-16..])
 where locals = PX.pInfoLocals pInfo

frameSize :: PX.PInfo -> Int
frameSize pInfo =
  if nBytes `mod` 16 == 0
  then nBytes
  else 16 * ((nBytes `div` 16) + 1)
 where nBytes = 8 * length locals
       locals = PX.pInfoLocals pInfo

{- Patch Instructions -}

patchInstructions :: X.Program -> X.Program
patchInstructions (X.Program info [(label, bl)]) =
  X.Program info [(label, pBlock bl), intro fSize,  conclusion fSize ]
 where
  fSize = X.frameSize info
patchInstructions _ = undefined

intro :: Int -> (String, X.Block)
intro fSize
  | fSize == 0 = ( "main",
  X.Block X.BInfo
    [ X.Pushq (X.Reg X.Rbp)
    , X.Movq (X.Reg X.Rsp) (X.Reg X.Rbp)
    , X.Jmp "start" ] )
  | otherwise  = ( "main",
  X.Block X.BInfo
    [ X.Pushq (X.Reg X.Rbp)
    , X.Movq (X.Reg X.Rsp) (X.Reg X.Rbp)
    , X.Subq (X.Num fSize) (X.Reg X.Rsp)
    , X.Jmp "start" ] )


conclusion :: Int -> (String, X.Block)
conclusion fSize
  | fSize == 0 =
    ( "conclusion", X.Block X.BInfo
      [ X.Popq (X.Reg X.Rbp)
      , X.Retq ] )
  | otherwise  =
    ( "conclusion", X.Block X.BInfo
      [ X.Addq (X.Num fSize) (X.Reg X.Rsp)
      , X.Popq (X.Reg X.Rbp)
      , X.Retq ] )

pBlock :: X.Block -> X.Block
pBlock (X.Block info instrs) = X.Block info (concatMap pInstrs instrs)

pInstrs :: X.Instr -> [X.Instr]
pInstrs (X.Movq (X.Deref regL offL) (X.Deref regR offR)) =
  [ X.Movq (X.Deref regL offL) (X.Reg X.Rax)
  , X.Movq (X.Reg X.Rax) (X.Deref regR offR) ]
pInstrs (X.Addq (X.Deref regL offL) (X.Deref regR offR)) =
  [ X.Movq (X.Deref regL offL) (X.Reg X.Rax)
  , X.Addq (X.Reg X.Rax) (X.Deref regR offR) ]
pInstrs (X.Subq (X.Deref regL offL) (X.Deref regR offR)) =
  [ X.Movq (X.Deref regL offL) (X.Reg X.Rax)
  , X.Subq (X.Reg X.Rax) (X.Deref regR offR) ]
pInstrs i = [i]