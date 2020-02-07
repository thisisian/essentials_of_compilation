module Chapter4 where

import qualified R2
import qualified C1
import qualified X861 as X1

import Control.Monad
import Control.Monad.State.Strict
import Data.Graph
import Data.Maybe
import Data.Map (Map)
import qualified Data.Map as M
import Data.List
import Data.Set (Set)
import Data.Tuple
import qualified Data.Set as S

import Common
import Color

compile :: R2.Program -> String
compile =
  prettyPrint
  . patchInstructions
  . assignHomes
  . allocateRegisters -- :: X1.Program IGraph -> X1.Program LocMap
  . buildInterference -- :: X1.Program (CFG, Locals, LiveSets) -> X1.Program IGraph
  . uncoverLive--  :: X1.Program (CFG, Locals) -> (X1.Program (CFG, Locals, LiveSets)
  . selectInstructions -- :: C1.Program (CFG, Locals) -> X1.Program (CFG, Locals)
  . buildCFG --  :: C1.Program () -> C1.Program CFG
  . explicateControl  -- :: R2.Program -> C1.Program ()
  . rco -- :: R2.Program -> R2.Program
  . uniquify -- :: R2.Program -> R2.Program
  . shrink -- :: R2.Program -> R2.Program

{----- Shrink -----}

shrink :: R2.Program -> R2.Program
shrink (R2.Program e) = (R2.Program (shrinkExpr e))

-- Subtract, and, or, <=, >, >=
shrinkExpr :: R2.Expr -> R2.Expr
shrinkExpr (R2.Num x) = R2.Num x
shrinkExpr (R2.Read) = R2.Read
shrinkExpr (R2.Neg e) = (R2.Neg (shrinkExpr e))
shrinkExpr (R2.Add eL eR) = (R2.Add (shrinkExpr eL) (shrinkExpr eR))
shrinkExpr (R2.Sub eL eR) = (R2.Add (shrinkExpr eL) (R2.Neg (shrinkExpr eR)))
shrinkExpr (R2.Var s) = R2.Var s
shrinkExpr (R2.Let s eB e) = (R2.Let s (shrinkExpr eB) (shrinkExpr e))
shrinkExpr R2.T = R2.T
shrinkExpr R2.F = R2.F
shrinkExpr (R2.And eL eR) = (R2.If (shrinkExpr eL) (shrinkExpr eR) R2.F)
shrinkExpr (R2.Or eL eR) = (R2.If (shrinkExpr eL) R2.T (shrinkExpr eR))
shrinkExpr (R2.Not e) = (R2.Not (shrinkExpr e))
shrinkExpr (R2.Cmp R2.Eq eL eR) =
  (R2.Cmp R2.Eq (shrinkExpr eL) (shrinkExpr eR))
shrinkExpr (R2.Cmp R2.Lt eL eR) =
  (R2.Cmp R2.Lt (shrinkExpr eL) (shrinkExpr eR))
shrinkExpr (R2.Cmp R2.Le eL eR) =
  (R2.Not (R2.Cmp R2.Lt (shrinkExpr eR) (shrinkExpr eL)))
shrinkExpr (R2.Cmp R2.Gt eL eR) =
  (R2.Cmp R2.Lt (shrinkExpr eR) (shrinkExpr eL))
shrinkExpr (R2.Cmp R2.Ge eL eR) =
  (R2.Not (R2.Cmp R2.Lt (shrinkExpr eL) (shrinkExpr eR)))
shrinkExpr (R2.If cond eT eF) =
  (R2.If (shrinkExpr cond) (shrinkExpr eT) (shrinkExpr eF))

{----- Uniquify -----}

type SymbolTable = Map String String

uniquify :: R2.Program -> R2.Program
uniquify (R2.Program e) = R2.Program $
  runFreshEnv "_uni" (uniquifyExpr M.empty e)

uniquifyExpr :: SymbolTable -> R2.Expr -> FreshEnv R2.Expr
uniquifyExpr _ (R2.Num x) = return $ R2.Num x
uniquifyExpr _ R2.Read = return $ R2.Read
uniquifyExpr st (R2.Neg e) = R2.Neg <$> uniquifyExpr st e
uniquifyExpr st (R2.Add eL eR) =
  return R2.Add `ap` uniquifyExpr st eL `ap` uniquifyExpr st eR
uniquifyExpr _ (R2.Sub _ _) = error "Found Sub in uniquify step"
uniquifyExpr st (R2.Var name) =
  case M.lookup name st of
    Just name' -> return (R2.Var name')
    Nothing -> error $ "Symbol " ++ name ++ " not found in symbol table"
uniquifyExpr st (R2.Let name be e) = do
  name' <- fresh
  let st' = M.insert name name' st
  be' <- uniquifyExpr st be
  e' <- uniquifyExpr st' e
  return (R2.Let name' be' e')
uniquifyExpr _ R2.T = return $ R2.T
uniquifyExpr _ R2.F = return $ R2.F
uniquifyExpr _ (R2.And _ _) = error "Found And in uniquify step"
uniquifyExpr _ (R2.Or _ _) = error "Found Or in uniquify step"
uniquifyExpr st (R2.Not e) = R2.Not <$> uniquifyExpr st e
uniquifyExpr st (R2.Cmp cmp eL eR)
  | cmp == R2.Eq || cmp == R2.Lt =
      return (R2.Cmp cmp) `ap` uniquifyExpr st eL `ap` uniquifyExpr st eR
  | otherwise = error $ "Found " ++ show cmp ++ " in uniquify step"
uniquifyExpr st (R2.If cond eT eF) =
  return R2.If
    `ap` uniquifyExpr st cond
    `ap` uniquifyExpr st eT
    `ap` uniquifyExpr st eF

{----- Remove Complex Operations and Operands -----}

rco :: R2.Program -> R2.Program
rco (R2.Program e) = R2.Program $ runFreshEnv "_rco" (rcoExpr e)

rcoExpr :: R2.Expr -> FreshEnv R2.Expr
rcoExpr (R2.Num x) = return $ R2.Num x
rcoExpr e@R2.Read = do
  (bindings, e') <- rcoArg e
  return $ makeBindings bindings e'
rcoExpr (R2.Neg e) = do
  (bindings, e') <- rcoArg e
  return $ makeBindings bindings (R2.Neg e')
rcoExpr (R2.Add eL eR) = do
  (bindingsL, eL') <- rcoArg eL
  (bindingsR, eR') <- rcoArg eR
  return $ makeBindings (bindingsL++bindingsR) (R2.Add eL' eR')
rcoExpr (R2.Sub _ _ ) = error "Found Sub in RCO step"
rcoExpr (R2.Var name) = return $ R2.Var name
rcoExpr (R2.Let name be e) = do
  (bindingsBE, be') <- rcoArg be
  e' <- rcoExpr e
  return $ makeBindings bindingsBE (R2.Let name be' e')
rcoExpr R2.T = return R2.T
rcoExpr R2.F = return R2.F
rcoExpr (R2.And _ _) = error "Found Add in RCO step"
rcoExpr (R2.Or _ _) = error "Found Or in RCO step"
rcoExpr (R2.Not e) = do
  (bindings, e') <- rcoArg e
  return $ makeBindings bindings (R2.Not e')
rcoExpr (R2.Cmp cmp eL eR)
  | cmp == R2.Eq || cmp == R2.Lt = do
      (bindingsL, eL') <- rcoArg eL
      (bindingsR, eR') <- rcoArg eR
      return $ makeBindings (bindingsL++bindingsR) (R2.Cmp cmp eL' eR')
  | otherwise = error $ "Found " ++ show cmp ++ "in RCO step."
rcoExpr (R2.If cond eT eF) = do
  cond' <- rcoExpr cond
  eT' <- rcoExpr eT
  eF' <- rcoExpr eF
  return $ (R2.If cond' eT' eF')


rcoArg :: R2.Expr -> FreshEnv ([(String, R2.Expr)], R2.Expr)
rcoArg (R2.Num x) = return ([], R2.Num x)
rcoArg R2.Read = do
  n <- fresh
  return ([(n , R2.Read)] , R2.Var n)
rcoArg (R2.Neg e) = do
  (bindings, e') <- rcoArg e
  n <- fresh
  return (bindings ++ [(n, R2.Neg e')]
         , R2.Var n)
rcoArg (R2.Add eL eR) = do
  (bindingsL, eL') <- rcoArg eL
  (bindingsR, eR') <- rcoArg eR
  n <- fresh
  return (bindingsL ++ bindingsR ++ [(n, R2.Add eL' eR')]
         , R2.Var n)
rcoArg (R2.Sub _ _) = error $ "Found Sub in RCO step"
rcoArg (R2.Var name) = return ([], R2.Var name)
rcoArg (R2.Let n be e) = do
  (bindingsBE, be') <- rcoArg be
  (bindings, e') <- rcoArg e
  return (bindingsBE ++ [(n, be')] ++ bindings, e')
rcoArg R2.T = return ([], R2.T)
rcoArg R2.F = return ([], R2.F)
rcoArg (R2.And _ _) = error $ "Found And in RCO step"
rcoArg (R2.Or _ _) = error $ "Found Or in RCO step"
rcoArg (R2.Not e) = do
  (bindings, e') <- rcoArg e
  n <- fresh
  return (bindings ++ [(n, R2.Not e')], R2.Var n)
rcoArg (R2.Cmp cmp eL eR)
  | cmp == R2.Eq || cmp == R2.Lt = do
      (bindingsL, eL') <- rcoArg eL
      (bindingsR, eR') <- rcoArg eR
      n <- fresh
      return $ ( bindingsL ++ bindingsR ++ [(n, R2.Cmp cmp eL' eR')]
               , R2.Var n)
  | otherwise = error $ "Found " ++ show cmp ++ "in RCO step."
rcoArg (R2.If cond eT eF) = do
  cond' <- rcoExpr cond
  eT' <- rcoExpr eT
  eF' <- rcoExpr eF
  n <- fresh
  return $ ([(n, R2.If cond' eT' eF')], R2.Var n)

makeBindings :: [(String, R2.Expr)] -> R2.Expr -> R2.Expr
makeBindings ((b, be):bs) e =
  R2.Let b be (makeBindings bs e)
makeBindings [] e = e

{----- Explicate Control -----}

explicateControl :: R2.Program -> C1.Program ()
explicateControl (R2.Program e) =
  C1.Pgrm () (("start", startBlock):M.toList blocks)
 where (startBlock, blocks) = runEcState e

ecTail :: R2.Expr -> State EcS C1.Tail
ecTail (R2.Let s be e) = do
  e' <- ecTail e
  ecAssign be s e'
ecTail (R2.If eCmp eT eF ) = do
  eT' <- ecTail eT
  eF' <- ecTail eF
  ecPred eCmp eT' eF'
ecTail (R2.Num x) = return $ C1.Return (C1.Plain (C1.Num x))
ecTail (R2.Read) = error $ "ecTail: Found read in tail position"
ecTail (R2.Neg e) = return $ C1.Return (C1.Neg (ecArg e))
ecTail (R2.Add eL eR) = return $ C1.Return (C1.Plus (ecArg eL) (ecArg eR))
ecTail (R2.Var s) = return $ (C1.Return (C1.Plain (C1.Var s)))
ecTail R2.T = return $ C1.Return (C1.Plain (C1.T))
ecTail R2.F = return $ C1.Return (C1.Plain (C1.F))
ecTail (R2.And _ _) = error $ "ecTail: Found And"
ecTail (R2.Or _ _) = error $ "ecTail: Found Or"
ecTail (R2.Sub _ _) = error $ "ecTail: Found Sub"
ecTail (R2.Not e) = return $ C1.Return (C1.Not (ecArg e))
ecTail (R2.Cmp cmp eL eR) =
  return $ C1.Return (C1.Cmp (ecCmp cmp) (ecArg eL) (ecArg eR))

ecPred :: R2.Expr -> C1.Tail -> C1.Tail -> State EcS C1.Tail
ecPred (R2.T) t1 _ = return $ t1
ecPred (R2.F) _ t2 = return $ t2
ecPred (R2.Not e) t1 t2 = do
  l1 <- newBlock t1
  l2 <- newBlock t2
  return $ C1.If C1.Eq (ecArg e) C1.F l1 l2
ecPred (R2.If cond eT eF) t1 t2 = do
  l1 <- newBlock t1
  l2 <- newBlock t2
  eT' <- ecPred eT (C1.Goto l1) (C1.Goto l2)
  eF' <- ecPred eF (C1.Goto l1) (C1.Goto l2)
  ecPred cond eT' eF'
ecPred (R2.Cmp cmp eL eR) t1 t2 = do
  l1 <- newBlock t1
  l2 <- newBlock t2
  return $ C1.If (ecCmp cmp) (ecArg eL) (ecArg eR) l1 l2
-- Unsure about this - IJW
ecPred (R2.Let s eB e) t1 t2 = do
  e' <- ecPred e t1 t2
  ecAssign eB s e'

ecPred e _ _ = error $ "ecPred: " ++ show e

ecAssign :: R2.Expr -> String -> C1.Tail -> State EcS C1.Tail
ecAssign R2.Read s t = return $ (C1.Seq (C1.Assign s C1.Read) t)
ecAssign (R2.Add eL eR) s t =
  return $ (C1.Seq (C1.Assign s (C1.Plus (ecArg eL) (ecArg eR))) t)
ecAssign (R2.Neg e) s t =
  return $ (C1.Seq (C1.Assign s (C1.Neg (ecArg e))) t)
ecAssign (R2.Not e) s t =
  return $ (C1.Seq (C1.Assign s (C1.Not (ecArg e))) t)
ecAssign (R2.Cmp cmp eL eR) s t =
  return $ (C1.Seq (C1.Assign s (C1.Cmp (ecCmp cmp) (ecArg eL) (ecArg eR))) t)
ecAssign e@(R2.Num _) s t =
  return $ (C1.Seq (C1.Assign s (C1.Plain (ecArg e))) t)
ecAssign e@(R2.Var _) s t =
  return $ (C1.Seq (C1.Assign s (C1.Plain (ecArg e))) t)
ecAssign R2.T s t =
  return $ (C1.Seq (C1.Assign s (C1.Plain (C1.T))) t)
ecAssign R2.F s t =
  return $ (C1.Seq (C1.Assign s (C1.Plain (C1.F))) t)
ecAssign (R2.If cond eT eF) s t = do
  lbl <- newBlock t
  eT' <- ecAssign eT s (C1.Goto lbl)
  eF' <- ecAssign eF s (C1.Goto lbl)
  ecPred cond eT' eF'
ecAssign e _ _ = error $ "Called ecAssign on " ++ show e

ecArg :: R2.Expr -> C1.Arg
ecArg (R2.Num x) = C1.Num x
ecArg (R2.Var x) = C1.Var x
ecArg (R2.T) = C1.T
ecArg (R2.F) = C1.F
ecArg e = error $ "Called ecArg on " ++ show e

ecCmp :: R2.Compare -> C1.Compare
ecCmp R2.Eq = C1.Eq
ecCmp R2.Lt = C1.Lt
ecCmp c = error $ "Called ecCmp on " ++ show c

{- A monad for explicate control -}
data EcS = EcS { ecsBlocks :: Map String C1.Tail, freshBlockNum :: Int }

runEcState :: R2.Expr -> (C1.Tail, Map String C1.Tail)
runEcState e =
  let (startBlock, ecsState) = runState (ecTail e) (EcS M.empty 0)
  in (startBlock, ecsBlocks ecsState)

newBlock :: C1.Tail -> State EcS (String)
newBlock t = do
  (EcS blocks x) <- get
  let lbl = "block"++show x
  put (EcS (M.insert lbl t blocks) (x+1))
  return lbl

{----- Build CFG -----}

type CFG = Map String (Set String)

buildCFG :: C1.Program () -> C1.Program CFG
buildCFG (C1.Pgrm () bs) = C1.Pgrm cfg bs
 where cfg = mkCFG bs M.empty

mkCFG :: [(String, C1.Tail)]
      -> Map String (Set String)
      -> Map String (Set String)
mkCFG ((s, b):bs) m = case b of
  C1.Seq _ t  -> mkCFG ((s, t):bs) m
  C1.Return _ ->
    let m' = M.insert s S.empty m
    in mkCFG bs m' -- Should have it add empty set -- IJW
  C1.Goto b'   ->
    let m' = M.insert s (S.singleton b') m
    in mkCFG bs m'
  C1.If _ _ _ b1 b2 ->
    let m' = M.insert s (S.fromList [b1, b2]) m
    in mkCFG bs m'

mkCFG [] m = m

{----- Select Instructions -----}

selectInstructions :: C1.Program CFG -> X1.Program CFG
selectInstructions (C1.Pgrm cfg bs) =
  (X1.Program cfg
    bs')
 where
  bs' = map (\(l, b) -> (l, mkBlock . siTail $ b)) bs
  mkBlock is = X1.Block is


siTail :: C1.Tail -> [X1.Instr]
siTail (C1.Return (C1.Plain a))    =
  [ X1.Movq (siArg a) (X1.Reg Rax)
  , X1.Jmp "conclusion" ]
siTail (C1.Return C1.Read)         =
  [ X1.Callq "read_int"
  , X1.Jmp "conclusion" ]
siTail (C1.Return (C1.Neg a))      =
  [ X1.Movq (siArg a) (X1.Reg Rax)
  , X1.Negq (X1.Reg Rax)
  , X1.Jmp "conclusion" ]
siTail (C1.Return (C1.Plus aL aR)) =
  [ X1.Movq (siArg aL) (X1.Reg Rax)
  , X1.Addq (siArg aR) (X1.Reg Rax)
  , X1.Jmp "conclusion" ]
siTail (C1.Return (C1.Not a)) =
  [ X1.Movq (siArg a) (X1.Reg Rax)
  , X1.Xorq (X1.Num 1) (X1.Reg Rax)
  , X1.Jmp "conclusion" ]
siTail (C1.Return (C1.Cmp cmp aL aR)) =
  [ X1.Cmpq (siArg aR) (siArg aL)
  , X1.Set (siCompare cmp) (X1.ByteReg Al)
  , X1.Movzbq (X1.ByteReg Al) (X1.Reg Rax)
  , X1.Jmp "conclusion" ]
siTail (C1.Seq assign t) = siStmt assign ++ siTail t
siTail (C1.Goto s) = [X1.Jmp s]
siTail (C1.If cmp aT aF gT gF) =
  [ X1.Cmpq (siArg aF) (siArg aT)
  , X1.JmpIf (siCompare cmp) gT
  , X1.Jmp gF ]

siStmt :: C1.Stmt -> [X1.Instr]
siStmt (C1.Assign s (C1.Plain a))    =
  [ X1.Movq (siArg a) (X1.Var s) ]
siStmt (C1.Assign s C1.Read)       =
  [ X1.Callq "read_int"
  , X1.Movq (X1.Reg Rax) (X1.Var s) ]
siStmt (C1.Assign s (C1.Neg a))
  | a == C1.Var s =
    [ X1.Negq (X1.Var s) ]
  | otherwise    =
    [ X1.Movq (siArg a) (X1.Var s)
    , X1.Negq (X1.Var s) ]
siStmt (C1.Assign s (C1.Plus aL aR))
  | aL == C1.Var s =
    [ X1.Addq (siArg aR) (X1.Var s) ]
  | aR == C1.Var s =
    [ X1.Addq (siArg aL) (X1.Var s) ]
  | otherwise     =
    [ X1.Movq (siArg aL) (X1.Var s)
    , X1.Addq (siArg aR) (X1.Var s) ]
siStmt (C1.Assign s (C1.Not a))
  | a == C1.Var s =
    [ X1.Xorq (X1.Num 1) (siArg a) ]
  | otherwise =
    [ X1.Movq (siArg a) (X1.Var s)
    , X1.Xorq (X1.Num 1) (X1.Var s) ]
siStmt (C1.Assign s (C1.Cmp cmp aL aR)) =
  [ X1.Cmpq (siArg aR) (siArg aL)
  , X1.Set (siCompare cmp) (X1.ByteReg Al)
  , X1.Movzbq (X1.ByteReg Al) (X1.Var s) ]

siArg :: C1.Arg -> X1.Arg
siArg (C1.Num x) = X1.Num x
siArg (C1.Var s) = X1.Var s
siArg (C1.T) = X1.Num 1
siArg (C1.F) = X1.Num 0

siCompare :: C1.Compare -> X1.CC
siCompare (C1.Eq) = X1.CCEq
siCompare (C1.Lt) = X1.CCL

{----- Uncover Live -----}

type LiveSets = [Set X1.Arg]

uncoverLive :: X1.Program CFG -> X1.Program LiveSets
uncoverLive (X1.Program cfg bs) =
  X1.Program liveSets bs

 where
   liveSets = concatMap (\(l, _) -> fromJust $ M.lookup l liveSets') bs
     where liveSets' = ulBlocks2 bs cfg trav M.empty

   trav =
     map (\v -> fromJust $ M.lookup v v2s)
     . topSort . transposeG $ g

   (g, v2s, _) = mapSetToGraph cfg

ulBlocks2 :: [(String, X1.Block)]
         -> Map String (Set String)
         -> [String]
         -> Map String [Set X1.Arg]
         -> Map String [Set X1.Arg]
ulBlocks2 bs cfg (s:ss) m = case M.lookup s cfg of
  Nothing -> error $ s ++ " is not in CFG"
  Just succs ->
    if null succs then
      let (X1.Block is) = fromMaybe
            (error $ "ulBocks:Find to find " ++ show s ++ " in CFG")
            $ lookup s bs
          m' = M.insert s (mkLiveAfterSets is S.empty) m
      in ulBlocks2 bs cfg ss m'
    else
      let init' =
            foldr S.union S.empty
            . head
            . map (\s' ->
                     (fromMaybe
                        (error $ "ulBlocks: Failed to find " ++ show s' ++
                         " in liveAfterSets map") $ M.lookup s' m))
            . S.toList
            $ succs
          (X1.Block is) = fromJust $ lookup s bs
          m' = M.insert s (mkLiveAfterSets is init') m
       in ulBlocks2 bs cfg ss m'
ulBlocks2 _ _ [] m = m

mkLiveAfterSets :: [X1.Instr] -> Set X1.Arg -> [S.Set X1.Arg]
mkLiveAfterSets is init' = reverse $ mkSets init' (reverse is)

mkSets :: S.Set X1.Arg -> [X1.Instr] -> [S.Set X1.Arg]
mkSets set (i:is) = set : (mkSets set' is)
 where
   set' =
     S.filter (X1.isVar) $ (set S.\\ w i) `S.union` r i

   w instr =
     case X1.writeArgs instr of
       Just s   -> s
       _        -> S.empty

   r instr =
     case X1.readArgs instr of
       Just s -> s
       _      -> S.empty

mkSets _ [] = []

{----- Build Interference -----}

type IGraph = Map X1.Arg (Set X1.Arg)

buildInterference :: X1.Program LiveSets
                  -> X1.Program IGraph
buildInterference (X1.Program liveSets bs) =
  X1.Program iGraph bs
 where
   iGraph = buildInterfere sets insts
   sets = liveSets
   insts = concatMap (\(_, (X1.Block is)) -> is) bs

buildInterfere
  :: [S.Set X1.Arg]
  -> [X1.Instr]
  -> Map X1.Arg (Set X1.Arg)
buildInterfere s i = execState (buildInterfere' s i) M.empty

buildInterfere'
  :: [S.Set X1.Arg]
  -> [X1.Instr]
  -> State (Map X1.Arg (S.Set X1.Arg)) ()
buildInterfere' (la:las) (i:is) =
  case i of
    (X1.Addq _ s@(X1.Var _)) -> do
      addEdges s . S.filter (/= s) $ la
      buildInterfere' las is
    (X1.Subq _ s@(X1.Var _)) -> do
      addEdges s . S.filter (/= s) $ la
      buildInterfere' las is
    (X1.Negq s@(X1.Var _))   -> do
      addEdges s . S.filter (/= s) $ la
      buildInterfere' las is
    (X1.Xorq _ s@(X1.Var _)) -> do
      addEdges s . S.filter (/= s) $ la
      buildInterfere' las is
    (X1.Cmpq _ s@(X1.Var _)) -> do
      addEdges s . S.filter (/= s) $ la
      buildInterfere' las is
    (X1.Callq _)  -> do
      addRegisters la
      buildInterfere' las is
    (X1.Movq s d@(X1.Var _)) -> do
      addEdges d . S.filter (\k -> k /= s && k /= d) $ la
      buildInterfere' las is
    (X1.Movzbq s d@(X1.Var _)) -> do
      addEdges d . S.filter (\k -> k /= s && k /= d) $ la
      buildInterfere' las is
    _             -> buildInterfere' las is

 where
  addEdges
    :: X1.Arg
    -> S.Set X1.Arg -> State (M.Map X1.Arg (S.Set X1.Arg)) ()
  addEdges s la' = do
    modify $ M.insertWith (S.union) s la'
    mapM_ (addEdge s) la'
    return ()

  addEdge :: X1.Arg -> X1.Arg -> State (M.Map X1.Arg (S.Set X1.Arg)) ()
  addEdge a1 a2 = do
    modify $ M.insertWith (S.union) a2 (S.singleton a1)
    return ()

  addRegisters la' = do
    let rs = S.map X1.Reg (S.fromList callerSaved)
    mapM_ (\s -> addEdges s rs) la'

buildInterfere' [] [] = return ()
buildInterfere' _ _ = error "buildInterfere: Mismatch between args and live after sets"

{----- Allocate Registers -----}

type LocMap = Map String X1.StoreLoc

allocateRegisters :: X1.Program IGraph -> X1.Program LocMap
allocateRegisters (X1.Program iGraph bs) =
  (X1.Program locMap bs)
 where
   locMap = colorGraph (iGraph) (M.empty)

-- Returns list of Strings to X1.StoreLocs and frameSize
colorGraph
  :: (Map X1.Arg (Set X1.Arg))
  -> (Map X1.Arg (Set X1.Arg))
  -> (Map String X1.StoreLoc)
colorGraph iList mvBList  =
  let
    (g', nodeFromVertex, vertexFromNode) = toGraph iList

    vertexAssoc =
      map (\v -> let (_, a, _) = nodeFromVertex v in (v, a))
      . vertices
      $ g'

    regVerts :: [(Vertex, X1.Arg)]
    regVerts = filter (\(_, a) -> X1.isReg a) vertexAssoc

    varVerts = (vertexAssoc \\ regVerts)

    needColors :: S.Set Vertex
    needColors = S.fromList . map fst $ varVerts

    alreadyColored :: (M.Map Vertex Color)
    alreadyColored =
      M.fromList
      . mapMaybe
          (\(v, a) -> case a of
              (X1.Reg r) -> case colorFromReg r of
                Nothing -> Nothing
                Just n  -> Just (v, n)
              _ -> error $ "colorGraph: Don't expect " ++ show a ++
                   " in the regVerts list.")
      $ regVerts

    preferMap' :: (M.Map Vertex (Set Vertex))
    preferMap' =
      M.fromList
      . map
          (\(var1, vs) -> case vertexFromNode var1 of
              Nothing ->
                error $ "Could not find " ++ show var1 ++ " in graph"
              Just v ->
                let
                  vs' = S.map (fromJust . vertexFromNode) vs :: Set Vertex
                in (v, vs'))
      . M.toList
      $ mvBList

    coloring :: M.Map Vertex Color
    coloring = color g' preferMap' needColors alreadyColored
  in
    M.fromList
    . mapMaybe
        (\(v, c) -> case lookup v vertexAssoc of
            Just (X1.Reg _) -> Nothing
            Just (X1.Var s) -> Just (s, storeLocFromColor c)
            Nothing         -> Nothing
            _               -> error $ "Found " ++ show v ++ "in vertexAssoc")
    . M.toList
    $ coloring

toGraph
  :: M.Map X1.Arg (S.Set X1.Arg)
  -> (Graph, Vertex -> ((), X1.Arg, [X1.Arg]), X1.Arg -> Maybe Vertex)
toGraph conflicts = graphFromEdges .
  map (\(k, ks) -> ((), k, ks)) . M.toList . M.map (S.toList) $ conflicts

regsToUse :: [Register]
regsToUse = tail $ callerSaved

regIntAssoc :: [(Int, Register)]
regIntAssoc = zip [0..] regsToUse

storeLocFromColor :: Int -> X1.StoreLoc
storeLocFromColor n = case lookup n regIntAssoc of
  Just r -> X1.RegLoc r
  Nothing -> X1.Stack $ negate $ 8 * (n - (length regIntAssoc))

colorFromReg :: Register -> Maybe Int
colorFromReg r = lookup r (map swap regIntAssoc)

{----- Assign Homes -----}

type FrameSize = Int

assignHomes
  :: X1.Program (LocMap)
  -> X1.Program (FrameSize)
assignHomes (X1.Program locMap bs) =
  X1.Program (frameSize locMap) bs'
 where
  bs' = map (\(l, b) -> (l, ahBlock locMap b)) bs

ahBlock :: M.Map String X1.StoreLoc -> X1.Block -> X1.Block
ahBlock m (X1.Block instrs) =
  X1.Block (map (ahInstr m) instrs)

ahInstr :: M.Map String X1.StoreLoc -> X1.Instr -> X1.Instr
ahInstr m (X1.Addq aL aR)   = X1.Addq (ahArg m aL) (ahArg m aR)
ahInstr m (X1.Subq aL aR)   = X1.Subq (ahArg m aL) (ahArg m aR)
ahInstr m (X1.Movq aL aR)   = X1.Movq (ahArg m aL) (ahArg m aR)
ahInstr m (X1.Movzbq aL aR) = X1.Movzbq (ahArg m aL) (ahArg m aR)
ahInstr _ X1.Retq           = X1.Retq
ahInstr m (X1.Negq a)       = X1.Negq (ahArg m a)
ahInstr _ i@(X1.Callq _)    = i
ahInstr _ i@(X1.Jmp _)      = i
ahInstr _ i@(X1.Pushq _)    = i
ahInstr m (X1.Xorq aL aR)   = X1.Xorq (ahArg m aL) (ahArg m aR)
ahInstr m (X1.Cmpq aL aR)   = X1.Cmpq (ahArg m aL) (ahArg m aR)
ahInstr m (X1.Set cc a)     = X1.Set cc (ahArg m a)
ahInstr _ i@(X1.JmpIf _ _)  = i
ahInstr _ i@(X1.Label _)    = i
ahInstr _ i@(X1.Popq _)     = i

ahArg :: M.Map String X1.StoreLoc -> X1.Arg -> X1.Arg
ahArg _ a@(X1.Num _) = a
ahArg m (X1.Var s) = case M.lookup s m of
  Nothing -> error $ "Assign homes: Variable " ++ s ++ " not found in map."
  Just (X1.RegLoc r) -> X1.Reg r
  Just (X1.Stack n)  -> X1.Deref Rbp n
ahArg _ a@(X1.Reg _) = a
ahArg _ a@(X1.Deref _ _) = a
ahArg _ a@(X1.ByteReg _) = a

frameSize :: M.Map String X1.StoreLoc -> Int
frameSize locMap =
  if nBytes `mod` 16 == 0
  then nBytes
  else 16 * ((nBytes `div` 16) + 1)
 where
   nBytes =  negate
             . foldr (\n acc -> if n < acc then n else acc) 0
             . mapMaybe (\x -> case x of
                          (X1.Stack n) -> Just n
                          _            -> Nothing)
             . M.elems
             $ locMap

{----- Patch Instructions -----}

patchInstructions :: X1.Program (FrameSize) -> X1.Program ()
patchInstructions (X1.Program fSize bs) = X1.Program () bs'

 where
  bs' = intro fSize : conclusion fSize : map (\(l, b) -> (l, pBlock b)) bs

intro :: Int -> (String, X1.Block)
intro fSize
  | fSize == 0 = ( "main",
  X1.Block
    [ X1.Pushq (X1.Reg Rbp)
    , X1.Movq (X1.Reg Rsp) (X1.Reg Rbp)
    , X1.Jmp "start" ] )
  | otherwise  = ( "main",
  X1.Block
    [ X1.Pushq (X1.Reg Rbp)
    , X1.Movq (X1.Reg Rsp) (X1.Reg Rbp)
    , X1.Subq (X1.Num fSize) (X1.Reg Rsp)
    , X1.Jmp "start" ] )

conclusion :: Int -> (String, X1.Block)
conclusion fSize
  | fSize == 0 =
    ( "conclusion", X1.Block
      [ X1.Popq (X1.Reg Rbp)
      , X1.Retq ] )
  | otherwise  =
    ( "conclusion", X1.Block
      [ X1.Addq (X1.Num fSize) (X1.Reg Rsp)
      , X1.Popq (X1.Reg Rbp)
      , X1.Retq ] )

pBlock :: X1.Block -> X1.Block
pBlock (X1.Block instrs) = X1.Block (concatMap pInstrs instrs)

pInstrs :: X1.Instr -> [X1.Instr]
pInstrs (X1.Movq (X1.Deref regL offL) (X1.Deref regR offR)) =
  [ X1.Movq (X1.Deref regL offL) (X1.Reg Rax)
  , X1.Movq (X1.Reg Rax) (X1.Deref regR offR) ]
pInstrs (X1.Addq (X1.Deref regL offL) (X1.Deref regR offR)) =
  [ X1.Movq (X1.Deref regL offL) (X1.Reg Rax)
  , X1.Addq (X1.Reg Rax) (X1.Deref regR offR) ]
pInstrs (X1.Subq (X1.Deref regL offL) (X1.Deref regR offR)) =
  [ X1.Movq (X1.Deref regL offL) (X1.Reg Rax)
  , X1.Subq (X1.Reg Rax) (X1.Deref regR offR) ]
pInstrs (X1.Xorq (X1.Deref regL offL) (X1.Deref regR offR)) =
  [ X1.Movq (X1.Deref regL offL) (X1.Reg Rax)
  , X1.Xorq (X1.Reg Rax) (X1.Deref regR offR) ]
pInstrs (X1.Cmpq l@(X1.Deref _ _) r@(X1.Deref _ _)) =
  [ X1.Movq l (X1.Reg Rax)
  , X1.Cmpq (X1.Reg Rax) r ]
pInstrs (X1.Cmpq l r@(X1.Num _)) =
  [ X1.Movq r (X1.Reg Rax)
  , X1.Cmpq l (X1.Reg Rax) ]
pInstrs (X1.Movzbq l d@(X1.Deref _ _)) =
  [ X1.Movzbq l (X1.Reg Rax)
  , X1.Movq (X1.Reg Rax) d ]

pInstrs i@(X1.Movq a1 a2) = [i | not $ a1 == a2]
pInstrs i = [i]

{- End -}

--testProg = "(if (if (cmp eq? (read) 1) (cmp eq? (read) 0) (cmp eq? (read) 2)) (+ 10 32) (+ 700 77))"


testProg = "(let ([x (read)]) (if (cmp >= 5 3) #t #f))"

--ch4Test = putStrLn (show $ rco testProg)

compileTest =
  compileToFile R2.parse compile testProg "./test/ch4test"
