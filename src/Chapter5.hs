module Chapter5 where

import Control.Monad
import Control.Monad.State.Strict
import Data.Graph
import Data.Map (Map)
import qualified Data.Map as M
import Data.Maybe
import Data.List
import Data.Set (Set)
import qualified Data.Set as S
import Data.Tuple

import Debug.Trace

import qualified R3
import qualified C1
import qualified X861 as X1

import Common
import Color

--compile :: R3.Program R3.Type -> String
--compile =
--  prettyPrint
--  . patchInstructions
--  . assignHomes
--  . allocateRegisters
--  . buildInterference
--  . uncoverLive
--  . selectInstructions
--  . removeUnreachable
--  . buildCFG
--  . explicateControl
--  . rco
--  . uniquify
--  . shrink

{----- Shrink -----}
--
shrink :: R3.Program R3.Type -> R3.Program R3.Type
shrink (R3.Program e) = R3.Program (shrinkExpr e)

shrinkExpr :: R3.Expr R3.Type -> R3.Expr R3.Type
shrinkExpr e@(R3.Num _) = e
shrinkExpr e@R3.Read = e
shrinkExpr (R3.Neg e) = R3.Neg (shrinkExpr e)
shrinkExpr (R3.Add eL eR) =
  R3.Add (shrinkExpr eL) (shrinkExpr eR)
shrinkExpr (R3.Sub eL eR) =
  R3.Add (shrinkExpr eL) (R3.Neg (shrinkExpr eR))
shrinkExpr (R3.Var t s) = R3.Var t s
shrinkExpr (R3.Let t s eB e) = R3.Let t s (shrinkExpr eB) (shrinkExpr e)
shrinkExpr e@R3.T = e
shrinkExpr e@R3.F = e
shrinkExpr (R3.And eL eR) =
  R3.If R3.TBool (shrinkExpr eL) (shrinkExpr eR) (R3.F)
shrinkExpr (R3.Or eL eR) =
  R3.If R3.TBool (shrinkExpr eL) R3.T (shrinkExpr eR)
shrinkExpr (R3.Not e) = R3.Not (shrinkExpr e)
shrinkExpr (R3.Cmp R3.Eq eL eR) =
  R3.Cmp R3.Eq (shrinkExpr eL) (shrinkExpr eR)
shrinkExpr (R3.Cmp R3.Lt eL eR) =
  R3.Cmp R3.Lt (shrinkExpr eL) (shrinkExpr eR)
shrinkExpr (R3.Cmp R3.Le eL eR) =
  R3.Let R3.TBool "_shrnk"
    (shrinkExpr eL)
    (R3.Not (R3.Cmp R3.Lt (shrinkExpr eR) (R3.Var R3.TNum "_shrnk")))
shrinkExpr (R3.Cmp R3.Gt eL eR) =
  R3.Let R3.TBool "_shrnk"
    (shrinkExpr eL)
    (R3.Cmp R3.Lt (shrinkExpr eR) (R3.Var R3.TNum "_shrnk"))
shrinkExpr (R3.Cmp R3.Ge eL eR) =
  R3.Not (R3.Cmp R3.Lt (shrinkExpr eL) (shrinkExpr eR))
shrinkExpr (R3.If t cond eT eF) =
  R3.If t (shrinkExpr cond) (shrinkExpr eT) (shrinkExpr eF)
shrinkExpr (R3.Vector t elems)  =
  R3.Vector t (map shrinkExpr elems)
shrinkExpr (R3.VectorRef t vec idx) =
  R3.VectorRef t (shrinkExpr vec) idx
shrinkExpr (R3.VectorSet vec idx set) =
  R3.VectorSet (shrinkExpr vec) idx (shrinkExpr set)
shrinkExpr e@R3.Void = e
shrinkExpr (R3.Collect _) = undefined
shrinkExpr (R3.Allocate _ _) = undefined
shrinkExpr (R3.GlobalValue _) = undefined

{----- Uniquify -----}

type SymbolTable = Map String String

uniquify :: R3.Program R3.Type -> R3.Program R3.Type
uniquify (R3.Program e) = R3.Program $
  runFreshEnv "_uni" (uniquifyExpr M.empty e)

uniquifyExpr :: SymbolTable -> R3.Expr R3.Type -> FreshEnv (R3.Expr R3.Type)
uniquifyExpr _ e@(R3.Num _) =
  return e
uniquifyExpr _ e@R3.Read =
  return e
uniquifyExpr st (R3.Neg e) =
  R3.Neg <$> uniquifyExpr st e
uniquifyExpr st (R3.Add eL eR) =
  return R3.Add `ap` uniquifyExpr st eL `ap` uniquifyExpr st eR
uniquifyExpr _ (R3.Sub _ _) = error "Found Sub in uniquify step"
uniquifyExpr st (R3.Var t name) =
  case M.lookup name st of
    Just name' -> return (R3.Var t name')
    Nothing -> error $ "Symbol " ++ name ++ " not found in symbol table"
uniquifyExpr st (R3.Let t name be e) = do
  name' <- fresh
  let st' = M.insert name name' st
  be' <- uniquifyExpr st be
  e' <- uniquifyExpr st' e
  return (R3.Let t name' be' e')
uniquifyExpr _ e@R3.T = return e
uniquifyExpr _ e@R3.F = return e
uniquifyExpr _ (R3.And _ _) = error "Found And in uniquify step"
uniquifyExpr _ (R3.Or _ _) = error "Found Or in uniquify step"
uniquifyExpr st (R3.Not e) =
  R3.Not <$> uniquifyExpr st e
uniquifyExpr st (R3.Cmp cmp eL eR)
  | cmp == R3.Eq || cmp == R3.Lt =
      return (R3.Cmp cmp) `ap` uniquifyExpr st eL `ap` uniquifyExpr st eR
  | otherwise = error $ "Found " ++ show cmp ++ " in uniquify step"
uniquifyExpr st (R3.If t cond eT eF) =
  return (R3.If t)
    `ap` uniquifyExpr st cond
    `ap` uniquifyExpr st eT
    `ap` uniquifyExpr st eF
uniquifyExpr st (R3.Vector t elems) = do
  elems' <- mapM (uniquifyExpr st) elems
  return $ R3.Vector t elems'
uniquifyExpr st (R3.VectorRef t v idx) = do
  v' <- uniquifyExpr st v
  return $ R3.VectorRef t v' idx
uniquifyExpr st (R3.VectorSet v idx set) = do
  v' <- uniquifyExpr st v
  set' <- uniquifyExpr st set
  return $ R3.VectorSet v' idx set'
uniquifyExpr _ e@R3.Void = return e
uniquifyExpr _ (R3.Collect _) = undefined
uniquifyExpr _ (R3.Allocate _ _) = undefined
uniquifyExpr _ (R3.GlobalValue _) = undefined

{----- Expose Allocation -----}

exposeAllocation :: R3.Program R3.Type -> R3.Program R3.Type
exposeAllocation (R3.Program e) = R3.Program $ runFreshEnv "" (eaExpr e)

eaExpr :: R3.Expr R3.Type -> FreshEnv (R3.Expr R3.Type)
eaExpr e@(R3.Num _) = return e
eaExpr e@R3.Read = return e
eaExpr (R3.Neg e) = do
  e' <- eaExpr e
  return $ R3.Neg e'
eaExpr (R3.Add eL eR) = do
  eL' <- eaExpr eL
  eR' <- eaExpr eR
  return $ R3.Add eL' eR'
eaExpr (R3.Sub _ _) = error "Found Sub in exposeAllocation step"
eaExpr e@(R3.Var _ _) = return e
eaExpr (R3.Let t s bE e) = do
  bE' <- eaExpr bE
  e' <- eaExpr e
  return $ R3.Let t s bE' e'
eaExpr e@R3.T = return e
eaExpr e@R3.F = return e
eaExpr (R3.And _ _) = error "Found And in exposeAllocation step"
eaExpr (R3.Or _ _) = error "Found Or in exposeAllocation step"
eaExpr (R3.Not e) = do
  e' <- eaExpr e
  return $ R3.Not e'
eaExpr (R3.Cmp cmp eL eR) = do
  eL' <- eaExpr eL
  eR' <- eaExpr eR
  return $ R3.Cmp cmp eL' eR'
eaExpr (R3.If t cond eT eF) = do
  cond' <- eaExpr cond
  eT' <- eaExpr eT
  eF' <- eaExpr eF
  return $ R3.If t cond' eT' eF'
eaExpr (R3.Vector t elems) = do
  let len = length elems
      bytes = 8+(8*len)
  elemBinds <- mapM (\e -> do
                        e' <- eaExpr e -- Not sure if correct -IJW
                        s <- ("_vecinit" ++) <$> fresh
                        return (s, e')) elems
  v <- ("_vecalloc" ++) <$> fresh
  let
    initVec :: [(String, R3.Expr R3.Type)]
    initVec =
      map (\(idx, (name, ty)) -> ("_", (R3.VectorSet (R3.Var t v) idx (R3.Var ty name))))
      . zip [0..]
      . map (\(s, e) -> (s, R3.getType e))
      $ elemBinds
  return $
    makeBindings elemBinds $
      (R3.Let R3.TVoid "_"
        (R3.If R3.TVoid
          (R3.Cmp R3.Lt
             (R3.Add (R3.GlobalValue "free_ptr") (R3.Num bytes))
             (R3.GlobalValue "fromspace_end"))
          (R3.Void)
          (R3.Collect bytes))
      (R3.Let R3.TVoid v (R3.Allocate len t)
      (makeBindings initVec (R3.Var t v))))
eaExpr (R3.VectorRef t v idx) = do
  v' <- eaExpr v
  return $ R3.VectorRef t v' idx
eaExpr (R3.VectorSet v idx set) = do
  v' <- eaExpr v
  set' <- eaExpr set
  return $ R3.VectorSet v' idx set'
eaExpr R3.Void = return R3.Void
eaExpr (R3.Collect _) = undefined
eaExpr (R3.Allocate _ _) = undefined
eaExpr (R3.GlobalValue _) = undefined

--{----- Remove Complex Operations and Operands -----}
--
--rco :: R3.Program Type -> R3.Program Type
--rco (R3.Program e) = R3.Program $ runFreshEnv "_rco" (rcoExpr e)
--
--rcoExpr :: R3.Expr -> FreshEnv R3.Expr
--rcoExpr (R3.Num x) = return $ R3.Num x
--rcoExpr e@R3.Read = do
--  (bindings, e') <- rcoArg e
--  return $ makeBindings bindings e'
--rcoExpr (R3.Neg e) = do
--  (bindings, e') <- rcoArg e
--  return $ makeBindings bindings (R3.Neg e')
--rcoExpr (R3.Add eL eR) = do
--  (bindingsL, eL') <- rcoArg eL
--  (bindingsR, eR') <- rcoArg eR
--  return $ makeBindings (bindingsL++bindingsR) (R3.Add eL' eR')
--rcoExpr (R3.Sub _ _ ) = error "Found Sub in RCO step"
--rcoExpr (R3.Var name) = return $ R3.Var name
--rcoExpr (R3.Let name be e) = do
--  (bindingsBE, be') <- rcoArg be
--  e' <- rcoExpr e
--  return $ makeBindings bindingsBE (R3.Let name be' e')
--rcoExpr R3.T = return R3.T
--rcoExpr R3.F = return R3.F
--rcoExpr (R3.And _ _) = error "Found Add in RCO step"
--rcoExpr (R3.Or _ _) = error "Found Or in RCO step"
--rcoExpr (R3.Not e) = do
--  (bindings, e') <- rcoArg e
--  return $ makeBindings bindings (R3.Not e')
--rcoExpr (R3.Cmp cmp eL eR)
--  | cmp == R3.Eq || cmp == R3.Lt = do
--      (bindingsL, eL') <- rcoArg eL
--      (bindingsR, eR') <- rcoArg eR
--      return $ makeBindings (bindingsL++bindingsR) (R3.Cmp cmp eL' eR')
--  | otherwise = error $ "Found " ++ show cmp ++ "in RCO step."
--rcoExpr (R3.If cond eT eF) = do
--  (bindings, cond') <- rcoArg cond
--  eT' <- rcoExpr eT
--  eF' <- rcoExpr eF
--  return $ makeBindings bindings (R3.If cond' eT' eF')
--
--rcoArg :: R3.Expr -> FreshEnv ([(String, R3.Expr)], R3.Expr)
--rcoArg (R3.Num x) = return ([], R3.Num x)
--rcoArg R3.Read = do
--  n <- fresh
--  return ([(n , R3.Read)] , R3.Var n)
--rcoArg (R3.Neg e) = do
--  (bindings, e') <- rcoArg e
--  n <- fresh
--  return (bindings ++ [(n, R3.Neg e')]
--         , R3.Var n)
--rcoArg (R3.Add eL eR) = do
--  (bindingsL, eL') <- rcoArg eL
--  (bindingsR, eR') <- rcoArg eR
--  n <- fresh
--  return (bindingsL ++ bindingsR ++ [(n, R3.Add eL' eR')]
--         , R3.Var n)
--rcoArg (R3.Sub _ _) =error "Found Sub in RCO step"
--rcoArg (R3.Var name) = return ([], R3.Var name)
--rcoArg (R3.Let n be e) = do
--  (bindingsBE, be') <- rcoArg be
--  (bindings, e') <- rcoArg e
--  return (bindingsBE ++ [(n, be')] ++ bindings, e')
--rcoArg R3.T = return ([], R3.T)
--rcoArg R3.F = return ([], R3.F)
--rcoArg (R3.And _ _) =error "Found And in RCO step"
--rcoArg (R3.Or _ _) =error "Found Or in RCO step"
--rcoArg (R3.Not e) = do
--  (bindings, e') <- rcoArg e
--  n <- fresh
--  return (bindings ++ [(n, R3.Not e')], R3.Var n)
--rcoArg (R3.Cmp cmp eL eR)
--  | cmp == R3.Eq || cmp == R3.Lt = do
--      (bindingsL, eL') <- rcoArg eL
--      (bindingsR, eR') <- rcoArg eR
--      n <- fresh
--      return (bindingsL ++ bindingsR ++ [(n, R3.Cmp cmp eL' eR')]
--             , R3.Var n)
--  | otherwise = error $ "Found " ++ show cmp ++ "in RCO step."
--rcoArg (R3.If cond eT eF) = do
--  (bindings, cond') <- rcoArg cond
--  eT' <- rcoExpr eT
--  eF' <- rcoExpr eF
--  n <- fresh
--  return (bindings ++ [(n, R3.If cond' eT' eF')], R3.Var n)
--
makeBindings :: [(String, R3.Expr R3.Type)] -> R3.Expr R3.Type -> R3.Expr R3.Type
makeBindings ((b, be):bs) e =
  R3.Let (R3.getType be) b be (makeBindings bs e)
makeBindings [] e = e
--
--{----- Explicate Control -----}
--
--explicateControl :: R3.Program -> C1.Program ()
--explicateControl (R3.Program e) =
--  C1.Pgrm () (("start", startBlock):M.toList blocks)
-- where (startBlock, blocks) = runEcState e
--
--ecTail :: R3.Expr -> State EcS C1.Tail
--ecTail (R3.Let s be e) = do
--  e' <- ecTail e
--  ecAssign be s e'
--ecTail (R3.If eCmp eT eF ) = do
--  eT' <- ecTail eT
--  eF' <- ecTail eF
--  ecPred eCmp eT' eF'
--ecTail (R3.Num x) = return $ C1.Return (C1.Plain (C1.Num x))
--ecTail R3.Read =
--  error "ecTail: Found read in tail position"
--ecTail (R3.Neg e) = return $ C1.Return (C1.Neg (ecArg e))
--ecTail (R3.Add eL eR) = return $ C1.Return (C1.Plus (ecArg eL) (ecArg eR))
--ecTail (R3.Var s) =
--  return (C1.Return (C1.Plain (C1.Var s)))
--ecTail R3.T = return $ C1.Return (C1.Plain C1.T)
--ecTail R3.F = return $ C1.Return (C1.Plain C1.F)
--ecTail (R3.And _ _) =
--  error "ecTail: Found And"
--ecTail (R3.Or _ _) =
--  error "ecTail: Found Or"
--ecTail (R3.Sub _ _) =
--  error "ecTail: Found Sub"
--ecTail (R3.Not e) = return $ C1.Return (C1.Not (ecArg e))
--ecTail (R3.Cmp cmp eL eR) =
--  return $ C1.Return (C1.Cmp (ecCmp cmp) (ecArg eL) (ecArg eR))
--
--ecPred :: R3.Expr -> C1.Tail -> C1.Tail -> State EcS C1.Tail
--ecPred R3.T t1 _ =
--  return t1
--ecPred R3.F _ t2 =
--  return t2
--ecPred a@(R3.Var _) t1 t2 = do
--  l1 <- newBlock t1
--  l2 <- newBlock t2
--  return $ C1.If C1.Eq (ecArg a) C1.T l1 l2
--ecPred (R3.Not e) t1 t2 = do
--  l1 <- newBlock t1
--  l2 <- newBlock t2
--  return $ C1.If C1.Eq (ecArg e) C1.F l1 l2
--ecPred (R3.If cond eT eF) t1 t2 = do
--  l1 <- newBlock t1
--  l2 <- newBlock t2
--  eT' <- ecPred eT (C1.Goto l1) (C1.Goto l2)
--  eF' <- ecPred eF (C1.Goto l1) (C1.Goto l2)
--  ecPred cond eT' eF'
--ecPred (R3.Cmp cmp eL eR) t1 t2 = do
--  l1 <- newBlock t1
--  l2 <- newBlock t2
--  return $ C1.If (ecCmp cmp) (ecArg eL) (ecArg eR) l1 l2
--ecPred (R3.Let s eB e) t1 t2 = do
--  e' <- ecPred e t1 t2
--  ecAssign eB s e'
--ecPred e _ _ = error $ "ecPred: " ++ show e
--
--ecAssign :: R3.Expr -> String -> C1.Tail -> State EcS C1.Tail
--ecAssign R3.Read s t =
--  return $ C1.Seq (C1.Assign s C1.Read) t
--ecAssign (R3.Add eL eR) s t =
--  return $ C1.Seq (C1.Assign s (C1.Plus (ecArg eL) (ecArg eR))) t
--ecAssign (R3.Neg e) s t =
--  return $ C1.Seq (C1.Assign s (C1.Neg (ecArg e))) t
--ecAssign (R3.Not e) s t =
--  return $ C1.Seq (C1.Assign s (C1.Not (ecArg e))) t
--ecAssign (R3.Cmp cmp eL eR) s t =
--  return $ C1.Seq (C1.Assign s (C1.Cmp (ecCmp cmp) (ecArg eL) (ecArg eR))) t
--ecAssign e@(R3.Num _) s t =
--  return $ C1.Seq (C1.Assign s (C1.Plain (ecArg e))) t
--ecAssign e@(R3.Var _) s t =
--  return $ C1.Seq (C1.Assign s (C1.Plain (ecArg e))) t
--ecAssign R3.T s t =
--  return $ C1.Seq (C1.Assign s (C1.Plain C1.T)) t
--ecAssign R3.F s t =
--  return $ C1.Seq (C1.Assign s (C1.Plain C1.F)) t
--ecAssign (R3.If cond eT eF) s t = do
--  lbl <- newBlock t
--  eT' <- ecAssign eT s (C1.Goto lbl)
--  eF' <- ecAssign eF s (C1.Goto lbl)
--  ecPred cond eT' eF'
--ecAssign a@(R3.Let sIn bE e) sOut t = do
--  let' <- ecAssign e sOut t
--  ecAssign bE sIn let'
--
--ecAssign e s t = error $ "Called ecAssign on " ++ show e ++ ", " ++ show s ++ ", " ++ show t
--
--ecArg :: R3.Expr -> C1.Arg
--ecArg (R3.Num x) = C1.Num x
--ecArg (R3.Var x) = C1.Var x
--ecArg R3.T = C1.T
--ecArg R3.F = C1.F
--ecArg e = error $ "Called ecArg on " ++ show e
--
--ecCmp :: R3.Compare -> C1.Compare
--ecCmp R3.Eq = C1.Eq
--ecCmp R3.Lt = C1.Lt
--ecCmp c = error $ "Called ecCmp on " ++ show c
--
--{- A monad for explicate control -}
--data EcS = EcS { ecsBlocks :: Map String C1.Tail, freshBlockNum :: Int }
--
--runEcState :: R3.Expr -> (C1.Tail, Map String C1.Tail)
--runEcState e =
--  let (startBlock, ecsState) = runState (ecTail e) (EcS M.empty 0)
--  in (startBlock, ecsBlocks ecsState)
--
--newBlock :: C1.Tail -> State EcS String
--newBlock t = do
--  (EcS blocks x) <- get
--  let lbl = "block"++show x
--  put (EcS (M.insert lbl t blocks) (x+1))
--  return lbl
--
--{----- Build CFG -----}
--
--type CFG = Map String (Set String)
--
--buildCFG :: C1.Program () -> C1.Program CFG
--buildCFG (C1.Pgrm () bs) = C1.Pgrm cfg bs
-- where cfg = mkCFG bs M.empty
--
--mkCFG :: [(String, C1.Tail)]
--      -> Map String (Set String)
--      -> Map String (Set String)
--mkCFG ((s, b):bs) m = case b of
--  C1.Seq _ t  -> mkCFG ((s, t):bs) m
--  C1.Return _ ->
--    let m' = M.insert s S.empty m
--    in mkCFG bs m'
--  C1.Goto b'   ->
--    let m' = M.insert s (S.singleton b') m
--    in mkCFG bs m'
--  C1.If _ _ _ b1 b2 ->
--    let m' = M.insert s (S.fromList [b1, b2]) m
--    in mkCFG bs m'
--
--mkCFG [] m = m
--
--{----- Remove Unreachable Blocks -----}
--
--removeUnreachable :: C1.Program CFG -> C1.Program CFG
--removeUnreachable (C1.Pgrm cfg bs) = (C1.Pgrm cfg bs')
-- where
--   bs' = filter (\(lbl, _) -> lbl `elem` reachableBlks) bs
--
--   reachableBlks :: [String]
--   reachableBlks = map (\v -> fromJust $ M.lookup v v2lbl)
--                   $ reachable g startVert
--   startVert = fromJust $  M.lookup "start" lbl2v
--
--   (g, v2lbl, lbl2v) = mapSetToGraph cfg
--
--
--{----- Select Instructions -----}
--
--selectInstructions :: C1.Program CFG -> X1.Program CFG
--selectInstructions (C1.Pgrm cfg bs) = X1.Program cfg bs'
-- where
--  bs' = map (\(l, b) -> (l, X1.Block . siTail $ b)) bs
--
--siTail :: C1.Tail -> [X1.Instr]
--siTail (C1.Return (C1.Plain a))    =
--  [ X1.Movq (siArg a) (X1.Reg Rax)
--  , X1.Jmp "conclusion" ]
--siTail (C1.Return C1.Read)         =
--  [ X1.Callq "read_int"
--  , X1.Jmp "conclusion" ]
--siTail (C1.Return (C1.Neg a))      =
--  [ X1.Movq (siArg a) (X1.Reg Rax)
--  , X1.Negq (X1.Reg Rax)
--  , X1.Jmp "conclusion" ]
--siTail (C1.Return (C1.Plus aL aR)) =
--  [ X1.Movq (siArg aL) (X1.Reg Rax)
--  , X1.Addq (siArg aR) (X1.Reg Rax)
--  , X1.Jmp "conclusion" ]
--siTail (C1.Return (C1.Not a)) =
--  [ X1.Movq (siArg a) (X1.Reg Rax)
--  , X1.Xorq (X1.Num 1) (X1.Reg Rax)
--  , X1.Jmp "conclusion" ]
--siTail (C1.Return (C1.Cmp cmp aL aR)) =
--  [ X1.Cmpq (siArg aR) (siArg aL)
--  , X1.Set (siCompare cmp) (X1.ByteReg Al)
--  , X1.Movzbq (X1.ByteReg Al) (X1.Reg Rax)
--  , X1.Jmp "conclusion" ]
--siTail (C1.Seq assign t) = siStmt assign ++ siTail t
--siTail (C1.Goto s) = [X1.Jmp s]
--siTail (C1.If cmp aT aF gT gF) =
--  [ X1.Cmpq (siArg aF) (siArg aT)
--  , X1.JmpIf (siCompare cmp) gT
--  , X1.Jmp gF ]
--
--siStmt :: C1.Stmt -> [X1.Instr]
--siStmt (C1.Assign s (C1.Plain a))    =
--  [ X1.Movq (siArg a) (X1.Var s) ]
--siStmt (C1.Assign s C1.Read)       =
--  [ X1.Callq "read_int"
--  , X1.Movq (X1.Reg Rax) (X1.Var s) ]
--siStmt (C1.Assign s (C1.Neg a))
--  | a == C1.Var s =
--    [ X1.Negq (X1.Var s) ]
--  | otherwise    =
--    [ X1.Movq (siArg a) (X1.Var s)
--    , X1.Negq (X1.Var s) ]
--siStmt (C1.Assign s (C1.Plus aL aR))
--  | aL == C1.Var s =
--    [ X1.Addq (siArg aR) (X1.Var s) ]
--  | aR == C1.Var s =
--    [ X1.Addq (siArg aL) (X1.Var s) ]
--  | otherwise     =
--    [ X1.Movq (siArg aL) (X1.Var s)
--    , X1.Addq (siArg aR) (X1.Var s) ]
--siStmt (C1.Assign s (C1.Not a))
--  | a == C1.Var s =
--    [ X1.Xorq (X1.Num 1) (siArg a) ]
--  | otherwise =
--    [ X1.Movq (siArg a) (X1.Var s)
--    , X1.Xorq (X1.Num 1) (X1.Var s) ]
--siStmt (C1.Assign s (C1.Cmp cmp aL aR)) =
--  [ X1.Cmpq (siArg aR) (siArg aL)
--  , X1.Set (siCompare cmp) (X1.ByteReg Al)
--  , X1.Movzbq (X1.ByteReg Al) (X1.Var s) ]
--
--siArg :: C1.Arg -> X1.Arg
--siArg (C1.Num x) = X1.Num x
--siArg (C1.Var s) = X1.Var s
--siArg C1.T = X1.Num 1
--siArg C1.F = X1.Num 0
--
--siCompare :: C1.Compare -> X1.CC
--siCompare C1.Eq = X1.CCEq
--siCompare C1.Lt = X1.CCL
--
--{----- Uncover Live -----}
--
--printLiveSets :: [(String, X1.Block)] -> Map String [Set X1.Arg] -> String
--printLiveSets ((lbl, X1.Block is) : bs) liveSets =
--  let liveSets' = fromJust $ M.lookup lbl liveSets
--  in "\n" ++ lbl ++ ":\n" ++ printLiveSets' is liveSets' ++ printLiveSets bs liveSets
--printLiveSets [] _ = []
--
--printLiveSets' :: [X1.Instr] -> [Set X1.Arg] -> String
--printLiveSets' (i:is) (s:ss) =
--  prettyPrint i ++ printSet (S.toList s) ++ printLiveSets' is ss
-- where
--   printSet :: [X1.Arg] -> String
--   printSet args = "{" ++ unwords (map prettyPrint args) ++ "}\n"
--printLiveSets' [] [] = []
--printLiveSets' [] e = error $ "extra sets: " ++ show e
--printLiveSets' e [] = error $ "extra instructions: " ++ show e
--
--
--type LiveSets = [Set X1.Arg]
--
--uncoverLive :: X1.Program CFG -> X1.Program LiveSets
--uncoverLive (X1.Program cfg bs) = {- trace (show "\nLiveBefore:\n" ++ printLiveSets bs liveBefore) -} X1.Program liveSets bs
-- where
--   liveSets = concatMap (\(l, _) -> fromJust $ M.lookup l liveAfter) bs
--   liveAfter = liveAfterBlocks bs liveBefore
--   liveBefore = liveBeforeBlocks bs cfg trav M.empty
--
--   trav =
--     map (\v -> fromJust $ M.lookup v v2s)
--     . topSort . transposeG $ g
--
--   (g, v2s, _) = mapSetToGraph cfg
--
--liveAfterBlocks :: [(String, X1.Block)]
--                -> Map String [Set X1.Arg] -- Live before sets
--                -> Map String [Set X1.Arg]
--liveAfterBlocks bs liveBeforeSets =
--  M.fromList . (map (\(lbl, (X1.Block is)) ->
--                    (lbl, mkLiveAfters liveBeforeSets is (fromJust . M.lookup lbl $ liveBeforeSets)))) $ bs
--
--mkLiveAfters :: Map String [Set X1.Arg]
--             -> [X1.Instr]
--             -> [Set X1.Arg]
--             -> [Set X1.Arg]
--mkLiveAfters liveBefores ((X1.Jmp lbl):is) (s:ss) =
--  if null is then [liveNextBlock]
--  else S.union liveNextBlock (head ss) : mkLiveAfters liveBefores is ss
-- where
--   liveNextBlock =
--     case M.lookup lbl liveBefores of
--         Nothing -> S.empty
--         Just lb -> head lb
--
--mkLiveAfters liveBefores ((X1.JmpIf _ lbl):is) (s:ss) =
--  if null is then [liveNextBlock]
--  else S.union liveNextBlock (head ss) : mkLiveAfters liveBefores is ss
-- where
--   liveNextBlock =
--     case M.lookup lbl liveBefores of
--         Nothing -> S.empty
--         Just lb -> head lb
--
--mkLiveAfters liveBefores (i:is) (_:ss) =
--  head ss : mkLiveAfters liveBefores is ss
--mkLiveAfters _ [] [] = []
--
--liveBeforeBlocks :: [(String, X1.Block)]
--                 -> Map String (Set String)
--                 -> [String]
--                 -> Map String [Set X1.Arg]
--                 -> Map String [Set X1.Arg]
--liveBeforeBlocks  bs cfg (s:ss) m = case M.lookup s cfg of
--  Nothing -> error $ s ++ " is not in CFG"
--  Just succs ->
--    if null succs then
--      let (X1.Block is) = fromMaybe
--            (error $ "liveBeforeBlocks :Cant find " ++ show s ++ " in bs")
--            $ lookup s bs
--          m' = M.insert s (mkLiveBeforeSets is S.empty) m
--      in liveBeforeBlocks bs cfg ss m'
--    else
--      let liveAfter =
--            foldr S.union S.empty
--            . map head
--            . map (\s' ->
--                     fromMaybe
--                       (error $ "ulBlocks: Failed to find " ++ show s' ++
--                        " in liveAfterSets map")
--                       (M.lookup s' m))
--            . S.toList
--            $ succs
--          (X1.Block is) = fromJust $ lookup s bs
--          m' = M.insert s (mkLiveBeforeSets is liveAfter) m
--       in liveBeforeBlocks bs cfg ss m'
--liveBeforeBlocks _ _ [] m = m
--
--mkLiveBeforeSets :: [X1.Instr] -> Set X1.Arg -> [S.Set X1.Arg]
--mkLiveBeforeSets is liveAfter = reverse $ mkSets liveAfter (reverse is)
--
--mkSets :: S.Set X1.Arg -> [X1.Instr] -> [S.Set X1.Arg]
--mkSets liveAfter (i:is) = liveBefore : mkSets liveBefore is
-- where
--   liveBefore =
--     S.filter X1.isVar $ (liveAfter S.\\ w i) `S.union` r i
--
--   w instr =
--     case X1.writeArgs instr of
--       Just s   -> s
--       _        -> S.empty
--
--   r instr =
--     case X1.readArgs instr of
--       Just s -> s
--       _      -> S.empty
--
--mkSets _ [] = []
--
----  {----- Uncover Live -----}
----
----  type LiveSets = [Set X1.Arg]
----
----  uncoverLive :: X1.Program CFG -> X1.Program LiveSets
----  uncoverLive (X1.Program cfg bs) = X1.Program liveSets bs
----   where
----     liveSets = concatMap (\(l, _) -> fromJust $ M.lookup l liveSets') bs
----       where liveSets' = ulBlocks2 bs cfg trav M.empty
----
----     trav =
----       map (\v -> fromJust $ M.lookup v v2s)
----       . topSort . transposeG $ g
----
----     (g, v2s, _) = mapSetToGraph cfg
----
----  ulBlocks2 :: [(String, X1.Block)]
----           -> Map String (Set String)
----           -> [String]
----           -> Map String [Set X1.Arg]
----           -> Map String [Set X1.Arg]
----  ulBlocks2 bs cfg (s:ss) m = case M.lookup s cfg of
----    Nothing -> error $ s ++ " is not in CFG"
----    Just succs ->
----      if null succs then
----        let (X1.Block is) = fromMaybe
----              (error $ "ulBocks:Find to find " ++ show s ++ " in CFG")
----              $ lookup s bs
----            m' = M.insert s (mkLiveAfterSets is S.empty) m
----        in ulBlocks2 bs cfg ss m'
----      else
----        let init' =
----              foldr S.union S.empty
----              . head
----              . map (\s' ->
----                       fromMaybe
----                         (error $ "ulBlocks: Failed to find " ++ show s' ++
----                          " in liveAfterSets map")
----                         (M.lookup s' m))
----              . S.toList
----              $ succs
----            (X1.Block is) = fromJust $ lookup s bs
----            m' = M.insert s (mkLiveAfterSets is init') m
----         in ulBlocks2 bs cfg ss m'
----  ulBlocks2 _ _ [] m = m
----
----  mkLiveAfterSets :: [X1.Instr] -> Set X1.Arg -> [S.Set X1.Arg]
----  mkLiveAfterSets is init' = reverse $ mkSets init' (reverse is)
----
----  mkSets :: S.Set X1.Arg -> [X1.Instr] -> [S.Set X1.Arg]
----  mkSets set (i:is) = set : mkSets set' is
----   where
----     set' =
----       S.filter X1.isVar $ (set S.\\ w i) `S.union` r i
----
----     w instr =
----       case X1.writeArgs instr of
----         Just s   -> s
----         _        -> S.empty
----
----     r instr =
----       case X1.readArgs instr of
----         Just s -> s
----         _      -> S.empty
----
----  mkSets _ [] = []
--
--{----- Build Interference -----}
--
--type IGraph = Map X1.Arg (Set X1.Arg)
--
--buildInterference :: X1.Program LiveSets
--                  -> X1.Program IGraph
--buildInterference (X1.Program liveSets bs) =
--  X1.Program iGraph bs
-- where
--   iGraph = buildInterfere sets insts
--   sets = liveSets
--   insts = concatMap (\(_, X1.Block is) -> is) bs
--
--buildInterfere :: [S.Set X1.Arg] -> [X1.Instr] -> Map X1.Arg (Set X1.Arg)
--buildInterfere s i = execState (buildInterfere' s i) M.empty
--
--buildInterfere' :: [S.Set X1.Arg]
--                -> [X1.Instr]
--                -> State (Map X1.Arg (S.Set X1.Arg)) ()
--buildInterfere' (la:las) (i:is) =
--  case i of
--    (X1.Addq _ s@(X1.Var _)) -> do
--      addEdges s . S.filter (/= s) $ la
--      buildInterfere' las is
--    (X1.Subq _ s@(X1.Var _)) -> do
--      addEdges s . S.filter (/= s) $ la
--      buildInterfere' las is
--    (X1.Negq s@(X1.Var _))   -> do
--      addEdges s . S.filter (/= s) $ la
--      buildInterfere' las is
--    (X1.Xorq _ s@(X1.Var _)) -> do
--      addEdges s . S.filter (/= s) $ la
--      buildInterfere' las is
--    (X1.Cmpq _ s@(X1.Var _)) -> do
--      addEdges s . S.filter (/= s) $ la
--      buildInterfere' las is
--    (X1.Callq _)  -> do
--      addRegisters la
--      buildInterfere' las is
--    (X1.Movq s d@(X1.Var _)) -> do
--      addEdges d . S.filter (\k -> k /= s && k /= d) $ la
--      buildInterfere' las is
--    (X1.Movzbq s d@(X1.Var _)) -> do
--      addEdges d . S.filter (\k -> k /= s && k /= d) $ la
--      buildInterfere' las is
--    _             -> buildInterfere' las is
--
-- where
--  addEdges
--    :: X1.Arg
--    -> S.Set X1.Arg -> State (M.Map X1.Arg (S.Set X1.Arg)) ()
--  addEdges s la' = do
--    modify $ M.insertWith S.union s la'
--    mapM_ (addEdge s) la'
--
--  addEdge :: X1.Arg -> X1.Arg -> State (M.Map X1.Arg (S.Set X1.Arg)) ()
--  addEdge a1 a2 = do
--    modify $ M.insertWith S.union a2 (S.singleton a1)
--    return ()
--
--  addRegisters la' = do
--    let rs = S.map X1.Reg (S.fromList callerSaved)
--    mapM_ (`addEdges` rs) la'
--
--buildInterfere' [] [] = return ()
--buildInterfere' _ _ = error "buildInterfere: Mismatch between args and live after sets"
--
--{----- Allocate Registers -----}
--
--type LocMap = Map String X1.StoreLoc
--
--allocateRegisters :: X1.Program IGraph -> X1.Program LocMap
--allocateRegisters (X1.Program iGraph bs) = X1.Program locMap bs
-- where
--  locMap = colorGraph iGraph
--
--colorGraph :: Map X1.Arg (Set X1.Arg)
--           -> Map String X1.StoreLoc
--colorGraph iList =
--  M.fromList
--  . mapMaybe
--      (\(v, c) -> case lookup v vertexAssoc of
--          Just (X1.Reg _) -> Nothing
--          Just (X1.Var s) -> Just (s, storeLocFromColor c)
--          Nothing         -> Nothing
--          _               -> error $ "Found " ++ show v ++ "in vertexAssoc")
--  . M.toList
--  $ coloring
-- where
--  coloring :: M.Map Vertex Color
--  coloring = color g M.empty needColors alreadyColored
--
--  needColors :: S.Set Vertex
--  needColors = S.fromList . map fst $ varVerts
--
--  alreadyColored :: (M.Map Vertex Color)
--  alreadyColored =
--    M.fromList
--    . mapMaybe
--        (\(v, a) -> case a of
--            (X1.Reg r) -> case colorFromReg r of
--              Nothing -> Nothing
--              Just n  -> Just (v, n)
--            _ -> error $ "colorGraph: Don't expect " ++ show a ++
--                 " in the regVerts list.")
--    $ regVerts
--
--  varVerts = vertexAssoc \\ regVerts
--
--  regVerts :: [(Vertex, X1.Arg)]
--  regVerts = filter (\(_, a) -> X1.isReg a) vertexAssoc
--
--  vertexAssoc = M.toList vertexMap
--
--  (g, vertexMap, _) = mapSetToGraph iList
--
--regsToUse :: [Register]
--regsToUse = take 3 . tail $ callerSaved
--
--regIntAssoc :: [(Int, Register)]
--regIntAssoc = zip [0..] regsToUse
--
--storeLocFromColor :: Int -> X1.StoreLoc
--storeLocFromColor n = case lookup n regIntAssoc of
--  Just r -> X1.RegLoc r
--  Nothing -> X1.Stack $ negate $ 8 * n - length regIntAssoc
--
--colorFromReg :: Register -> Maybe Int
--colorFromReg r = lookup r (map swap regIntAssoc)
--
--{----- Assign Homes -----}
--
--type FrameSize = Int
--
--assignHomes :: X1.Program LocMap -> X1.Program FrameSize
--assignHomes (X1.Program locMap bs) = X1.Program (frameSize locMap) bs'
-- where
--  bs' = map (\(l, b) -> (l, ahBlock locMap b)) bs
--
--ahBlock :: M.Map String X1.StoreLoc -> X1.Block -> X1.Block
--ahBlock m (X1.Block instrs) =
--  X1.Block (map (ahInstr m) instrs)
--
--ahInstr :: M.Map String X1.StoreLoc -> X1.Instr -> X1.Instr
--ahInstr m (X1.Addq aL aR)   = X1.Addq (ahArg m aL) (ahArg m aR)
--ahInstr m (X1.Subq aL aR)   = X1.Subq (ahArg m aL) (ahArg m aR)
--ahInstr m (X1.Movq aL aR)   = X1.Movq (ahArg m aL) (ahArg m aR)
--ahInstr m (X1.Movzbq aL aR) = X1.Movzbq (ahArg m aL) (ahArg m aR)
--ahInstr _ X1.Retq           = X1.Retq
--ahInstr m (X1.Negq a)       = X1.Negq (ahArg m a)
--ahInstr _ i@(X1.Callq _)    = i
--ahInstr _ i@(X1.Jmp _)      = i
--ahInstr _ i@(X1.Pushq _)    = i
--ahInstr m (X1.Xorq aL aR)   = X1.Xorq (ahArg m aL) (ahArg m aR)
--ahInstr m (X1.Cmpq aL aR)   = X1.Cmpq (ahArg m aL) (ahArg m aR)
--ahInstr m (X1.Set cc a)     = X1.Set cc (ahArg m a)
--ahInstr _ i@(X1.JmpIf _ _)  = i
--ahInstr _ i@(X1.Label _)    = i
--ahInstr _ i@(X1.Popq _)     = i
--
--ahArg :: M.Map String X1.StoreLoc -> X1.Arg -> X1.Arg
--ahArg _ a@(X1.Num _) = a
--ahArg m (X1.Var s) = case M.lookup s m of
--  Nothing -> error $ "Assign homes: Variable " ++ s ++ " not found in map."
--  Just (X1.RegLoc r) -> X1.Reg r
--  Just (X1.Stack n)  -> X1.Deref Rbp n
--ahArg _ a@(X1.Reg _) = a
--ahArg _ a@(X1.Deref _ _) = a
--ahArg _ a@(X1.ByteReg _) = a
--
--frameSize :: M.Map String X1.StoreLoc -> Int
--frameSize locMap =
--  if nBytes `mod` 16 == 0
--  then nBytes
--  else 16 * ((nBytes `div` 16) + 1)
-- where
--   nBytes =  negate
--             . foldr (\n acc -> if n < acc then n else acc) 0
--             . mapMaybe (\x -> case x of
--                          (X1.Stack n) -> Just n
--                          _            -> Nothing)
--             . M.elems
--             $ locMap
--
--{----- Patch Instructions -----}
--
--patchInstructions :: X1.Program FrameSize -> X1.Program ()
--patchInstructions (X1.Program fSize bs) = X1.Program () bs'
-- where
--  bs' = intro fSize : conclusion fSize : map (\(l, b) -> (l, pBlock b)) bs
--
--intro :: Int -> (String, X1.Block)
--intro fSize
--  | fSize == 0 = ( "main",
--  X1.Block
--    [ X1.Pushq (X1.Reg Rbp)
--    , X1.Movq (X1.Reg Rsp) (X1.Reg Rbp)
--    , X1.Jmp "start" ] )
--  | otherwise  = ( "main",
--  X1.Block
--    [ X1.Pushq (X1.Reg Rbp)
--    , X1.Movq (X1.Reg Rsp) (X1.Reg Rbp)
--    , X1.Subq (X1.Num fSize) (X1.Reg Rsp)
--    , X1.Jmp "start" ] )
--
--conclusion :: Int -> (String, X1.Block)
--conclusion fSize
--  | fSize == 0 =
--    ( "conclusion", X1.Block
--      [ X1.Popq (X1.Reg Rbp)
--      , X1.Retq ] )
--  | otherwise  =
--    ( "conclusion", X1.Block
--      [ X1.Addq (X1.Num fSize) (X1.Reg Rsp)
--      , X1.Popq (X1.Reg Rbp)
--      , X1.Retq ] )
--
--pBlock :: X1.Block -> X1.Block
--pBlock (X1.Block instrs) = X1.Block (concatMap pInstrs instrs)
--
--pInstrs :: X1.Instr -> [X1.Instr]
--pInstrs (X1.Movq (X1.Deref regL offL) (X1.Deref regR offR)) =
--  [ X1.Movq (X1.Deref regL offL) (X1.Reg Rax)
--  , X1.Movq (X1.Reg Rax) (X1.Deref regR offR) ]
--pInstrs (X1.Addq (X1.Deref regL offL) (X1.Deref regR offR)) =
--  [ X1.Movq (X1.Deref regL offL) (X1.Reg Rax)
--  , X1.Addq (X1.Reg Rax) (X1.Deref regR offR) ]
--pInstrs (X1.Subq (X1.Deref regL offL) (X1.Deref regR offR)) =
--  [ X1.Movq (X1.Deref regL offL) (X1.Reg Rax)
--  , X1.Subq (X1.Reg Rax) (X1.Deref regR offR) ]
--pInstrs (X1.Xorq (X1.Deref regL offL) (X1.Deref regR offR)) =
--  [ X1.Movq (X1.Deref regL offL) (X1.Reg Rax)
--  , X1.Xorq (X1.Reg Rax) (X1.Deref regR offR) ]
--pInstrs (X1.Cmpq l@(X1.Deref _ _) r@(X1.Deref _ _)) =
--  [ X1.Movq l (X1.Reg Rax)
--  , X1.Cmpq (X1.Reg Rax) r ]
--pInstrs (X1.Cmpq l r@(X1.Num _)) =
--  [ X1.Movq r (X1.Reg Rax)
--  , X1.Cmpq l (X1.Reg Rax) ]
--pInstrs (X1.Movzbq l d@(X1.Deref _ _)) =
--  [ X1.Movzbq l (X1.Reg Rax)
--  , X1.Movq (X1.Reg Rax) d ]
--
--pInstrs i@(X1.Movq a1 a2) = [i | a1 /= a2]
--pInstrs i = [i]
--
--
--{-- End --}
--testExpr = "(cmp > (read) (read))"
--
---- after rco:
----(if #f (let ([_rco0 (if #f 0 0)]) (let ([_uni0 _rco0]) _uni0)) 0)
---- after explicateControl:
---- [("start",Return (Plain (Num 0))),
----    ("block0",Seq (Assign "_uni0" (Plain (Var "_rco0"))) (Return (Plain (Var "_uni0"))))]
--
--
--
--testThing = case R3.parse testExpr of
--  Left _ -> undefined
--  Right x -> removeUnreachable . buildCFG . explicateControl. rco . uniquify.  shrink $ x
--
--compileFailing = compileToFile R3.parse compile testExpr "./test/ch4test"
