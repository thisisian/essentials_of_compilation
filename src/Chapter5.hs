module Chapter5 where

import Control.Monad
import Control.Monad.State.Strict
import Data.Bits
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
import qualified C2
import qualified X862 as X2

import Common
import Color

compile =
  prettyPrint
  . patchInstructions
  . assignHomes
  . allocateRegisters
  . buildInterference
  . uncoverLive
  . selectInstructions
  . removeUnreachable
  . buildCFG
  . explicateControl
  . collectLocals
  . rco
  . exposeAllocation
  . uniquify
  . shrink
  . fromEither
  . R3.typeCheck

{----- Shrink -----}
--
shrink :: R3.Program () R3.Type -> R3.Program () R3.Type
shrink (R3.Program () e) = R3.Program () (shrinkExpr e)

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

uniquify :: R3.Program () R3.Type -> R3.Program () R3.Type
uniquify (R3.Program () e) = R3.Program () $
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

exposeAllocation :: R3.Program () R3.Type -> R3.Program () R3.Type
exposeAllocation (R3.Program () e) = R3.Program () $ runFreshEnv "" (eaExpr e)

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
  c <- ("_collectret" ++) <$> fresh
  initVec <- (mapM (\(idx, (name, ty)) -> do
                       i <- ("_initret" ++ ) <$> fresh
                       return (i
                              ,(R3.VectorSet (R3.Var t v) idx (R3.Var ty name))))
      . zip [0..]
      . map (\(s, e) -> (s, R3.getType e))
      $ elemBinds)
  return $
    makeBindings elemBinds $
      (R3.Let R3.TVoid c
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

{----- Remove Complex Operations and Operands -----}

rco :: R3.Program () R3.Type -> R3.Program () R3.Type
rco (R3.Program () e) = R3.Program () $ runFreshEnv "_rco" (rcoExpr e)

rcoExpr :: R3.Expr R3.Type -> FreshEnv (R3.Expr R3.Type)
rcoExpr e@(R3.Num _) = return e
rcoExpr e@R3.Read = do
  (bindings, e') <- rcoArg e
  return $ makeBindings bindings e'
rcoExpr (R3.Neg e) = do
  (bindings, e') <- rcoArg e
  return $ makeBindings bindings (R3.Neg e')
rcoExpr (R3.Add eL eR) = do
  (bindingsL, eL') <- rcoArg eL
  (bindingsR, eR') <- rcoArg eR
  return $ makeBindings (bindingsL++bindingsR) (R3.Add eL' eR')
rcoExpr (R3.Sub _ _ ) = error "Found Sub in RCO step"
rcoExpr e@(R3.Var _ _) = return e
rcoExpr (R3.Let t name be e) = do
  (bindingsBE, be') <- rcoArg be
  e' <- rcoExpr e
  return $ makeBindings bindingsBE (R3.Let t name be' e')
rcoExpr R3.T = return R3.T
rcoExpr R3.F = return R3.F
rcoExpr (R3.And _ _) = error "Found Add in RCO step"
rcoExpr (R3.Or _ _) = error "Found Or in RCO step"
rcoExpr (R3.Not e) = do
  (bindings, e') <- rcoArg e
  return $ makeBindings bindings (R3.Not e')
rcoExpr (R3.Cmp cmp eL eR)
  | cmp == R3.Eq || cmp == R3.Lt = do
      (bindingsL, eL') <- rcoArg eL
      (bindingsR, eR') <- rcoArg eR
      return $ makeBindings (bindingsL++bindingsR) (R3.Cmp cmp eL' eR')
  | otherwise = error $ "Found " ++ show cmp ++ "in RCO step."
rcoExpr (R3.If t cond eT eF) = do
  (bindings, cond') <- rcoArg cond
  eT' <- rcoExpr eT
  eF' <- rcoExpr eF
  return $ makeBindings bindings (R3.If t cond' eT' eF')
rcoExpr (R3.Vector t es) = undefined
 -- do
 -- (bindings, es') <- unzip <$> mapM rcoArg es
 -- return $ makeBindings (concat bindings) (R3.Vector t es')
rcoExpr (R3.VectorRef t v idx) = do
  (bindings, v') <- rcoArg v
  return $ makeBindings bindings (R3.VectorRef t v' idx)
rcoExpr (R3.VectorSet v idx set) = do
  (bindingsV, v') <- rcoArg v
  (bindingsSet, set') <- rcoArg set
  return $ makeBindings (bindingsV ++ bindingsSet) (R3.VectorSet v' idx set')
rcoExpr e@R3.Void = return e
rcoExpr e@(R3.Collect _) = return e
rcoExpr e@(R3.Allocate _ _) = return e
rcoExpr e@(R3.GlobalValue _) = return e


rcoArg :: R3.Expr R3.Type
       -> FreshEnv ([(String, (R3.Expr R3.Type))], (R3.Expr R3.Type))
rcoArg (R3.Num x) = return ([], R3.Num x)
rcoArg R3.Read = do
  n <- fresh
  return ([(n , R3.Read)] , R3.Var R3.TNum n)
rcoArg (R3.Neg e) = do
  (bindings, e') <- rcoArg e
  n <- fresh
  return (bindings ++ [(n, R3.Neg e')]
         , R3.Var R3.TNum n)
rcoArg (R3.Add eL eR) = do
  (bindingsL, eL') <- rcoArg eL
  (bindingsR, eR') <- rcoArg eR
  n <- fresh
  return (bindingsL ++ bindingsR ++ [(n, R3.Add eL' eR')]
         , R3.Var R3.TNum n)
rcoArg (R3.Sub _ _) =error "Found Sub in RCO step"
rcoArg e@(R3.Var _ _) = return ([], e)
rcoArg (R3.Let _ n be e) = do
  (bindingsBE, be') <- rcoArg be
  (bindings, e') <- rcoArg e
  return (bindingsBE ++ [(n, be')] ++ bindings, e')
rcoArg R3.T = return ([], R3.T)
rcoArg R3.F = return ([], R3.F)
rcoArg (R3.And _ _) = error "Found And in RCO step"
rcoArg (R3.Or _ _) = error "Found Or in RCO step"
rcoArg (R3.Not e) = do
  (bindings, e') <- rcoArg e
  n <- fresh
  return (bindings ++ [(n, R3.Not e')], R3.Var R3.TBool n)
rcoArg (R3.Cmp cmp eL eR)
  | cmp == R3.Eq || cmp == R3.Lt = do
      (bindingsL, eL') <- rcoArg eL
      (bindingsR, eR') <- rcoArg eR
      n <- fresh
      return (bindingsL ++ bindingsR ++ [(n, R3.Cmp cmp eL' eR')]
             , R3.Var R3.TBool n)
  | otherwise = error $ "Found " ++ show cmp ++ "in RCO step."
rcoArg (R3.If t cond eT eF) = do
  (bindings, cond') <- rcoArg cond
  eT' <- rcoExpr eT
  eF' <- rcoExpr eF
  n <- fresh
  return (bindings ++ [(n, R3.If t cond' eT' eF')], R3.Var t n)
-- Book doesn't mention anything about rco for vectors, so I'm just doing

-- what I think is correct by following a similar pattern as above
rcoArg (R3.Vector t es) = undefined
 -- do
 -- (binds, es') <- unzip <$>  mapM rcoArg es
 -- n <- fresh
 -- return ((concat binds) ++ [(n, R3.Vector t es')], R3.Var t n)
rcoArg (R3.VectorRef t v idx) = do
  (bindings, v') <- rcoArg v
  n <- fresh
  return (bindings ++ [(n, R3.VectorRef t v' idx)], R3.Var t n)
rcoArg (R3.VectorSet v idx set) = do
  (bindingsV, v') <- rcoArg v
  (bindingsSet, set') <- rcoArg set
  n <- fresh
  return ( bindingsV ++ bindingsSet ++ [(n, R3.VectorSet v' idx set')]
         , R3.Var R3.TVoid n )
rcoArg e@R3.Void = return ([], e)
rcoArg e@(R3.Collect _) = return ([], e)
rcoArg e@(R3.Allocate _ _) = return ([], e)
rcoArg e@(R3.GlobalValue _) = do
  n <- fresh
  return ([(n, e)], (R3.Var R3.TVoid n))



makeBindings :: [(String, R3.Expr R3.Type)] -> R3.Expr R3.Type -> R3.Expr R3.Type
makeBindings ((b, be):bs) e =
  R3.Let (R3.getType be) b be (makeBindings bs e)
makeBindings [] e = e

{----- Collect Locals -----}

-- Doing this before explicate control, contrary to what the book says
-- because I don't think it will make a difference and it will be
-- easier to collect locals in R3 than adding type info to C2...

type Locals = Map String C2.Type

collectLocals :: R3.Program () R3.Type -> R3.Program (Locals) (R3.Type)
collectLocals (R3.Program _ e) = R3.Program locals e
 where locals = M.fromList (clsExpr e)

clsExpr :: R3.Expr R3.Type -> [(String, C2.Type)]
clsExpr (R3.Num _)  = []
clsExpr R3.Read  = []
clsExpr (R3.Neg e) = clsExpr e
clsExpr (R3.Add eL eR) = clsExpr eL ++ clsExpr eR
clsExpr (R3.Sub eL eR) = clsExpr eL ++ clsExpr eR
clsExpr (R3.Var _ _) = []
clsExpr (R3.Let t s eB e) = (s, toC2Type t):(clsExpr eB ++ clsExpr e)
clsExpr R3.T = []
clsExpr R3.F = []
clsExpr (R3.And _ _) = undefined
clsExpr (R3.Or _ _) = undefined
clsExpr (R3.Not e) = clsExpr e
clsExpr (R3.Cmp _ eL eR) = clsExpr eL ++ clsExpr eR
clsExpr (R3.If _ cond eT eF) = clsExpr cond ++ clsExpr eT ++ clsExpr eF
clsExpr (R3.Vector _ es) = concatMap clsExpr es
clsExpr (R3.VectorSet v _ set) = clsExpr v ++ clsExpr set
clsExpr (R3.VectorRef _ _ _) = []
clsExpr R3.Void = []
clsExpr (R3.Collect _) = []
clsExpr (R3.Allocate _ _) = []
clsExpr (R3.GlobalValue _) = []

toC2Type :: R3.Type -> C2.Type
toC2Type R3.TBool = C2.TBool
toC2Type R3.TVoid = C2.TVoid
toC2Type R3.TNum = C2.TNum
toC2Type (R3.TVector ts) = (C2.TVector (map toC2Type ts))

{----- Explicate Control -----}

explicateControl :: R3.Program (Locals) (R3.Type) -> C2.Program (Locals)
explicateControl (R3.Program locals e) =
  C2.Pgrm locals (("start", startBlock):M.toList blocks)
 where (startBlock, blocks) = runEcState e

ecTail :: R3.Expr R3.Type -> State EcS C2.Tail
ecTail (R3.Let _ s be e) = do
  e' <- ecTail e
  ecAssign be s e'
ecTail (R3.If _ eCmp eT eF ) = do
  eT' <- ecTail eT
  eF' <- ecTail eF
  ecPred eCmp eT' eF'
ecTail (R3.Num x) = return $ C2.Return (C2.Plain (C2.Num x))
ecTail R3.Read =
  error "ecTail: Found read in tail position"
ecTail (R3.Neg e) = return $ C2.Return (C2.Neg (ecArg e))
ecTail (R3.Add eL eR) = return $ C2.Return (C2.Plus (ecArg eL) (ecArg eR))
ecTail (R3.Var _ s) =
  return (C2.Return (C2.Plain (C2.Var s)))
ecTail R3.T = return $ C2.Return (C2.Plain C2.T)
ecTail R3.F = return $ C2.Return (C2.Plain C2.F)
ecTail (R3.And _ _) =
  error "ecTail: Found And"
ecTail (R3.Or _ _) =
  error "ecTail: Found Or"
ecTail (R3.Sub _ _) =
  error "ecTail: Found Sub"
ecTail (R3.Not e) = return $ C2.Return (C2.Not (ecArg e))
ecTail (R3.Cmp cmp eL eR) =
  return $ C2.Return (C2.Cmp (ecCmp cmp) (ecArg eL) (ecArg eR))
ecTail (R3.Vector _ es) = error "Found Vector in ecTail"
ecTail (R3.VectorRef _ v idx) = do
  let v' = ecArg v
  return $ C2.Return (C2.VectorRef v' idx)
ecTail (R3.VectorSet v idx set) = do
  let v' = ecArg v
      set' = ecArg set
  return $ C2.Return (C2.VectorSet v' idx set')
ecTail (R3.Void) = return $ C2.Return C2.Void
ecTail (R3.Collect x) =
  return $ C2.Seq (C2.Collect x) (C2.Return C2.Void)
ecTail (R3.Allocate x t) =
  return $ C2.Return (C2.Allocate x (toC2Type t))
ecTail (R3.GlobalValue s) =
  return $ C2.Return (C2.GlobalValue s)

ecPred :: R3.Expr R3.Type -> C2.Tail -> C2.Tail -> State EcS C2.Tail
ecPred R3.T t1 _ =
  return t1
ecPred R3.F _ t2 =
  return t2
ecPred a@(R3.Var _ _) t1 t2 = do
  l1 <- newBlock t1
  l2 <- newBlock t2
  return $ C2.If C2.Eq (ecArg a) C2.T l1 l2
ecPred (R3.Not e) t1 t2 = do
  l1 <- newBlock t1
  l2 <- newBlock t2
  return $ C2.If C2.Eq (ecArg e) C2.F l1 l2
ecPred (R3.If _ cond eT eF) t1 t2 = do
  l1 <- newBlock t1
  l2 <- newBlock t2
  eT' <- ecPred eT (C2.Goto l1) (C2.Goto l2)
  eF' <- ecPred eF (C2.Goto l1) (C2.Goto l2)
  ecPred cond eT' eF'
ecPred (R3.Cmp cmp eL eR) t1 t2 = do
  l1 <- newBlock t1
  l2 <- newBlock t2
  return $ C2.If (ecCmp cmp) (ecArg eL) (ecArg eR) l1 l2
ecPred (R3.Let _ s eB e) t1 t2 = do
  e' <- ecPred e t1 t2
  ecAssign eB s e'
ecPred e _ _ = error $ "ecPred: " ++ show e

ecAssign :: R3.Expr R3.Type -> String -> C2.Tail -> State EcS C2.Tail
ecAssign R3.Read s t =
  return $ C2.Seq (C2.Assign s C2.Read) t
ecAssign (R3.Add eL eR) s t =
  return $ C2.Seq (C2.Assign s (C2.Plus (ecArg eL) (ecArg eR))) t
ecAssign (R3.Neg e) s t =
  return $ C2.Seq (C2.Assign s (C2.Neg (ecArg e))) t
ecAssign (R3.Not e) s t =
  return $ C2.Seq (C2.Assign s (C2.Not (ecArg e))) t
ecAssign (R3.Cmp cmp eL eR) s t =
  return $ C2.Seq (C2.Assign s (C2.Cmp (ecCmp cmp) (ecArg eL) (ecArg eR))) t
ecAssign e@(R3.Num _) s t =
  return $ C2.Seq (C2.Assign s (C2.Plain (ecArg e))) t
ecAssign e@(R3.Var _ _) s t =
  return $ C2.Seq (C2.Assign s (C2.Plain (ecArg e))) t
ecAssign R3.T s t =
  return $ C2.Seq (C2.Assign s (C2.Plain C2.T)) t
ecAssign R3.F s t =
  return $ C2.Seq (C2.Assign s (C2.Plain C2.F)) t
ecAssign (R3.If _ cond eT eF) s t = do
  lbl <- newBlock t
  eT' <- ecAssign eT s (C2.Goto lbl)
  eF' <- ecAssign eF s (C2.Goto lbl)
  ecPred cond eT' eF'
ecAssign (R3.Let _ sIn bE e) sOut t = do
  let' <- ecAssign e sOut t
  ecAssign bE sIn let'
ecAssign (R3.VectorRef _ v idx) s t = do
  let v' = ecArg v
  return $ C2.Seq (C2.Assign s (C2.VectorRef v' idx)) t
ecAssign (R3.VectorSet v idx set) s t = do
  let v' = ecArg v
      set' = ecArg set
  return $ C2.Seq (C2.Assign s (C2.VectorSet v' idx set')) t
ecAssign (R3.Void) s t =
  return $ C2.Seq (C2.Assign s C2.Void) t
ecAssign (R3.GlobalValue s') s t =
  return $ C2.Seq (C2.Assign s (C2.GlobalValue s')) t
ecAssign (R3.Allocate x ty) s t =
  return $ C2.Seq (C2.Assign s (C2.Allocate x (toC2Type ty))) t
ecAssign (R3.Collect x) s t =
  return $ (C2.Seq (C2.Assign s C2.Void) (C2.Seq (C2.Collect x) t))
ecAssign e s t =
  error $ "Called ecAssign on " ++ show e ++ ", " ++ show s ++ ", " ++ show t

ecArg :: R3.Expr R3.Type -> C2.Arg
ecArg (R3.Num x) = C2.Num x
ecArg (R3.Var _ x) = C2.Var x
ecArg R3.T = C2.T
ecArg R3.F = C2.F
ecArg e = error $ "Called ecArg on " ++ show e

ecCmp :: R3.Compare -> C2.Compare
ecCmp R3.Eq = C2.Eq
ecCmp R3.Lt = C2.Lt
ecCmp c = error $ "Called ecCmp on " ++ show c

{- A monad for explicate control -}
data EcS = EcS { ecsBlocks :: Map String C2.Tail, freshBlockNum :: Int }

runEcState :: R3.Expr R3.Type -> (C2.Tail, Map String C2.Tail)
runEcState e =
  let (startBlock, ecsState) = runState (ecTail e) (EcS M.empty 0)
  in (startBlock, ecsBlocks ecsState)

newBlock :: C2.Tail -> State EcS String
newBlock t = do
  (EcS blocks x) <- get
  let lbl = "block"++show x
  put (EcS (M.insert lbl t blocks) (x+1))
  return lbl

{----- Build CFG -----}

type CFG = Map String (Set String)

buildCFG :: C2.Program (Locals) -> C2.Program (Locals, CFG)
buildCFG (C2.Pgrm locals bs) = C2.Pgrm (locals, cfg) bs
 where cfg = mkCFG bs M.empty

mkCFG :: [(String, C2.Tail)]
      -> Map String (Set String)
      -> Map String (Set String)
mkCFG ((s, b):bs) m = case b of
  C2.Seq _ t  -> mkCFG ((s, t):bs) m
  C2.Return _ ->
    let m' = M.insert s S.empty m
    in mkCFG bs m'
  C2.Goto b'   ->
    let m' = M.insert s (S.singleton b') m
    in mkCFG bs m'
  C2.If _ _ _ b1 b2 ->
    let m' = M.insert s (S.fromList [b1, b2]) m
    in mkCFG bs m'

mkCFG [] m = m

{----- Remove Unreachable Blocks -----}

removeUnreachable :: C2.Program (Locals, CFG) -> C2.Program (Locals, CFG)
removeUnreachable (C2.Pgrm (locals, cfg) bs) = (C2.Pgrm (locals, cfg) bs')
 where
   bs' = filter (\(lbl, _) -> lbl `elem` reachableBlks) bs

   reachableBlks :: [String]
   reachableBlks = map (\v -> fromJust $ M.lookup v v2lbl)
                   $ reachable g startVert
   startVert = fromJust $  M.lookup "start" lbl2v

   (g, v2lbl, lbl2v) = mapSetToGraph cfg


{----- Select Instructions -----}

selectInstructions :: C2.Program (Locals, CFG) -> X2.Program (Locals, CFG)
selectInstructions (C2.Pgrm cfg bs) = X2.Program cfg bs'
 where
  bs' = map (\(l, b) -> (l, X2.Block . siTail $ b)) bs

siTail :: C2.Tail -> [X2.Instr]
siTail (C2.Return (C2.Plain a))    =
  [ X2.Movq (siArg a) (X2.Reg Rax)
  , X2.Jmp "conclusion" ]
siTail (C2.Return C2.Read)         =
  [ X2.Callq "read_int"
  , X2.Jmp "conclusion" ]
siTail (C2.Return (C2.Neg a))      =
  [ X2.Movq (siArg a) (X2.Reg Rax)
  , X2.Negq (X2.Reg Rax)
  , X2.Jmp "conclusion" ]
siTail (C2.Return (C2.Plus aL aR)) =
  [ X2.Movq (siArg aL) (X2.Reg Rax)
  , X2.Addq (siArg aR) (X2.Reg Rax)
  , X2.Jmp "conclusion" ]
siTail (C2.Return (C2.Not a)) =
  [ X2.Movq (siArg a) (X2.Reg Rax)
  , X2.Xorq (X2.Num 1) (X2.Reg Rax)
  , X2.Jmp "conclusion" ]
siTail (C2.Return (C2.Cmp cmp aL aR)) =
  [ X2.Cmpq (siArg aR) (siArg aL)
  , X2.Set (siCompare cmp) (X2.ByteReg Al)
  , X2.Movzbq (X2.ByteReg Al) (X2.Reg Rax)
  , X2.Jmp "conclusion" ]
siTail (C2.Return (C2.Allocate x ty)) = undefined
siTail (C2.Return (C2.VectorRef a x)) =
  [ X2.Movq (siArg a) (X2.Reg R11)
  , X2.Movq (X2.Deref R11 (8*(x+1))) (X2.Reg Rax)
  , X2.Jmp "conclusion" ]
siTail (C2.Seq assign t) = siStmt assign ++ siTail t
siTail (C2.Goto s) = [X2.Jmp s]
siTail (C2.If cmp aT aF gT gF) =
  [ X2.Cmpq (siArg aF) (siArg aT)
  , X2.JmpIf (siCompare cmp) gT
  , X2.Jmp gF ]

siStmt :: C2.Stmt -> [X2.Instr]
siStmt (C2.Assign s (C2.Plain a))    =
  [ X2.Movq (siArg a) (X2.Var s) ]
siStmt (C2.Assign s C2.Read)       =
  [ X2.Callq "read_int"
  , X2.Movq (X2.Reg Rax) (X2.Var s) ]
siStmt (C2.Assign s (C2.Neg a))
  | a == C2.Var s =
    [ X2.Negq (X2.Var s) ]
  | otherwise    =
    [ X2.Movq (siArg a) (X2.Var s)
    , X2.Negq (X2.Var s) ]
siStmt (C2.Assign s (C2.Plus aL aR))
  | aL == C2.Var s =
    [ X2.Addq (siArg aR) (X2.Var s) ]
  | aR == C2.Var s =
    [ X2.Addq (siArg aL) (X2.Var s) ]
  | otherwise     =
    [ X2.Movq (siArg aL) (X2.Var s)
    , X2.Addq (siArg aR) (X2.Var s) ]
siStmt (C2.Assign s (C2.Not a))
  | a == C2.Var s =
    [ X2.Xorq (X2.Num 1) (siArg a) ]
  | otherwise =
    [ X2.Movq (siArg a) (X2.Var s)
    , X2.Xorq (X2.Num 1) (X2.Var s) ]
siStmt (C2.Assign s (C2.Cmp cmp aL aR)) =
  [ X2.Cmpq (siArg aR) (siArg aL)
  , X2.Set (siCompare cmp) (X2.ByteReg Al)
  , X2.Movzbq (X2.ByteReg Al) (X2.Var s) ]
siStmt (C2.Assign s (C2.VectorRef v x)) =
  [ X2.Movq (siArg v) (X2.Reg R11)
  , X2.Movq (X2.Deref R11 (8*(x+1))) (X2.Var s)
  ]
siStmt (C2.Assign s (C2.VectorSet v x a)) =
  [ X2.Movq (siArg v) (X2.Reg R11)
  , X2.Movq (siArg a) (X2.Deref R11 (8*(x+1)))
  , X2.Movq (X2.Num 0) (X2.Var s) ]
siStmt (C2.Assign s (C2.Allocate sz ty)) =
  [ X2.Movq (X2.GlobalValue "free_ptr") (X2.Var s)
  , X2.Addq (X2.Num (8*(sz+1))) (X2.GlobalValue "free_ptr")
  , X2.Movq (X2.Var s) (X2.Reg R11)
  , X2.Movq (X2.Num tag) (X2.Deref R11 0) ]
 where tag = mkTag ty
siStmt (C2.Assign s C2.Void) =
  [ X2.Movq (X2.Num 0) (X2.Var s) ]
siStmt (C2.Collect x) =
  [ X2.Movq (X2.Reg R15) (X2.Reg Rdi)
  , X2.Movq (X2.Num x) (X2.Reg Rsi)
  , X2.Callq "collect" ]
siStmt (C2.Assign s (C2.GlobalValue x)) =
  [ X2.Movq (X2.GlobalValue x) (X2.Var s) ]
siStmt e = error $ "siStmt: " ++ show e

mkTag :: C2.Type -> Int
mkTag ty = case ty of
  C2.TVector tys ->
    (shiftL 7 (ptrMask tys))
    .|. (shiftL 1 (length tys))
    .|. 1
  _ -> error $ "Trying to make tag of type " ++ show ty
 where ptrMask tys =
         foldr (\ty acc ->
                  (shiftL 1 acc)
                  .|. (case ty of
                         C2.TVector _ -> 1
                         _ -> 0))
               zeroBits tys



siArg :: C2.Arg -> X2.Arg
siArg (C2.Num x) = X2.Num x
siArg (C2.Var s) = X2.Var s
siArg C2.T = X2.Num 1
siArg C2.F = X2.Num 0

siCompare :: C2.Compare -> X2.CC
siCompare C2.Eq = X2.CCEq
siCompare C2.Lt = X2.CCL

{----- Uncover Live -----}

--printLiveSets :: [(String, X2.Block)] -> Map String [Set X2.Arg] -> String
--printLiveSets ((lbl, X2.Block is) : bs) liveSets =
--  let liveSets' = fromJust $ M.lookup lbl liveSets
--  in "\n" ++ lbl ++ ":\n" ++ printLiveSets' is liveSets' ++ printLiveSets bs liveSets
--printLiveSets [] _ = []
--
--printLiveSets' :: [X2.Instr] -> [Set X2.Arg] -> String
--printLiveSets' (i:is) (s:ss) =
--  prettyPrint i ++ printSet (S.toList s) ++ printLiveSets' is ss
-- where
--   printSet :: [X2.Arg] -> String
--   printSet args = "{" ++ unwords (map prettyPrint args) ++ "}\n"
--printLiveSets' [] [] = []
--printLiveSets' [] e = error $ "extra sets: " ++ show e
--printLiveSets' e [] = error $ "extra instructions: " ++ show e


type LiveSets = [Set X2.Arg]

uncoverLive :: X2.Program (Locals, CFG) -> X2.Program (Locals, LiveSets)
uncoverLive (X2.Program (locals, cfg) bs) = {- trace (show "\nLiveBefore:\n" ++ printLiveSets bs liveBefore) -} X2.Program (locals, liveSets) bs
 where
   liveSets = concatMap (\(l, _) -> fromJust $ M.lookup l liveAfter) bs
   liveAfter = liveAfterBlocks bs liveBefore
   liveBefore = liveBeforeBlocks bs cfg trav M.empty

   trav =
     map (\v -> fromJust $ M.lookup v v2s)
     . topSort . transposeG $ g

   (g, v2s, _) = mapSetToGraph cfg

liveAfterBlocks :: [(String, X2.Block)]
                -> Map String [Set X2.Arg] -- Live before sets
                -> Map String [Set X2.Arg]
liveAfterBlocks bs liveBeforeSets =
  M.fromList . (map (\(lbl, (X2.Block is)) ->
                    (lbl, mkLiveAfters liveBeforeSets is (fromJust . M.lookup lbl $ liveBeforeSets)))) $ bs

mkLiveAfters :: Map String [Set X2.Arg]
             -> [X2.Instr]
             -> [Set X2.Arg]
             -> [Set X2.Arg]
mkLiveAfters liveBefores ((X2.Jmp lbl):is) (s:ss) =
  if null is then [liveNextBlock]
  else S.union liveNextBlock (head ss) : mkLiveAfters liveBefores is ss
 where
   liveNextBlock =
     case M.lookup lbl liveBefores of
         Nothing -> S.empty
         Just lb -> head lb

mkLiveAfters liveBefores ((X2.JmpIf _ lbl):is) (s:ss) =
  if null is then [liveNextBlock]
  else S.union liveNextBlock (head ss) : mkLiveAfters liveBefores is ss
 where
   liveNextBlock =
     case M.lookup lbl liveBefores of
         Nothing -> S.empty
         Just lb -> head lb

mkLiveAfters liveBefores (i:is) (_:ss) =
  head ss : mkLiveAfters liveBefores is ss
mkLiveAfters _ [] [] = []

liveBeforeBlocks :: [(String, X2.Block)]
                 -> Map String (Set String)
                 -> [String]
                 -> Map String [Set X2.Arg]
                 -> Map String [Set X2.Arg]
liveBeforeBlocks  bs cfg (s:ss) m = case M.lookup s cfg of
  Nothing -> error $ s ++ " is not in CFG"
  Just succs ->
    if null succs then
      let (X2.Block is) = fromMaybe
            (error $ "liveBeforeBlocks :Cant find " ++ show s ++ " in bs")
            $ lookup s bs
          m' = M.insert s (mkLiveBeforeSets is S.empty) m
      in liveBeforeBlocks bs cfg ss m'
    else
      let liveAfter =
            foldr S.union S.empty
            . map head
            . map (\s' ->
                     fromMaybe
                       (error $ "ulBlocks: Failed to find " ++ show s' ++
                        " in liveAfterSets map")
                       (M.lookup s' m))
            . S.toList
            $ succs
          (X2.Block is) = fromJust $ lookup s bs
          m' = M.insert s (mkLiveBeforeSets is liveAfter) m
       in liveBeforeBlocks bs cfg ss m'
liveBeforeBlocks _ _ [] m = m

mkLiveBeforeSets :: [X2.Instr] -> Set X2.Arg -> [S.Set X2.Arg]
mkLiveBeforeSets is liveAfter = reverse $ mkSets liveAfter (reverse is)

mkSets :: S.Set X2.Arg -> [X2.Instr] -> [S.Set X2.Arg]
mkSets liveAfter (i:is) = liveBefore : mkSets liveBefore is
 where
   liveBefore =
     S.filter X2.isVar $ (liveAfter S.\\ w i) `S.union` r i

   w instr =
     case X2.writeArgs instr of
       Just s   -> s
       _        -> S.empty

   r instr =
     case X2.readArgs instr of
       Just s -> s
       _      -> S.empty

mkSets _ [] = []

{----- Build Interference -----}

type IGraph = Map X2.Arg (Set X2.Arg)

buildInterference :: X2.Program (Locals, LiveSets)
                  -> X2.Program (Locals, IGraph)
buildInterference (X2.Program (locals, liveSets) bs) =
  X2.Program (locals, iGraph) bs
 where
   iGraph = buildInterfere vectors liveSets insts
   insts = concatMap (\(_, X2.Block is) -> is) bs
   vectors =
     S.fromList
     . map (\s -> X2.Var s)
     . M.keys
     . M.filter (\t -> case t of
                    C2.TVector _ -> True
                    _ -> False)
     $ locals

buildInterfere :: S.Set (X2.Arg)
               -> [S.Set X2.Arg]
               -> [X2.Instr]
               -> Map X2.Arg (Set X2.Arg)
buildInterfere vectors s i = execState (buildInterfere' vectors s i) M.empty

buildInterfere' :: S.Set X2.Arg
                -> [S.Set X2.Arg]
                -> [X2.Instr]
                -> State (Map X2.Arg (S.Set X2.Arg)) ()
buildInterfere' vectors (la:las) (i:is) =
  case i of
    (X2.Addq _ s@(X2.Var _)) -> do
      addEdges s . S.filter (/= s) $ la
      buildInterfere' vectors las is
    (X2.Subq _ s@(X2.Var _)) -> do
      addEdges s . S.filter (/= s) $ la
      buildInterfere' vectors las is
    (X2.Negq s@(X2.Var _))   -> do
      addEdges s . S.filter (/= s) $ la
      buildInterfere' vectors las is
    (X2.Xorq _ s@(X2.Var _)) -> do
      addEdges s . S.filter (/= s) $ la
      buildInterfere' vectors las is
    (X2.Cmpq _ s@(X2.Var _)) -> do
      addEdges s . S.filter (/= s) $ la
      buildInterfere' vectors las is
    (X2.Callq _)  -> do
      addRegisters callerSaved la
      addRegisters calleeSaved
        (S.filter (\x-> S.member x vectors) $ la)
      buildInterfere' vectors las is
    (X2.Movq s d@(X2.Var _)) -> do
      addEdges d . S.filter (\k -> k /= s && k /= d) $ la
      buildInterfere' vectors las is
    (X2.Movzbq s d@(X2.Var _)) -> do
      addEdges d . S.filter (\k -> k /= s && k /= d) $ la
      buildInterfere' vectors las is
    _             -> buildInterfere' vectors las is

 where
  addEdges
    :: X2.Arg
    -> S.Set X2.Arg -> State (M.Map X2.Arg (S.Set X2.Arg)) ()
  addEdges s la' = do
    modify $ M.insertWith S.union s la'
    mapM_ (addEdge s) la'

  addEdge :: X2.Arg -> X2.Arg -> State (M.Map X2.Arg (S.Set X2.Arg)) ()
  addEdge a1 a2 = do
    modify $ M.insertWith S.union a2 (S.singleton a1)
    return ()

  addRegisters regs la' = do
    let rs = S.map X2.Reg (S.fromList regs)
    mapM_ (`addEdges` rs) la'

buildInterfere' _ [] [] = return ()
buildInterfere' _ _ _ = error "buildInterfere: Mismatch between args and live after sets"

{----- Allocate Registers -----}

type LocMap = Map String X2.StoreLoc

allocateRegisters :: X2.Program (Locals, IGraph) -> X2.Program LocMap
allocateRegisters (X2.Program (locals, iGraph) bs) = X2.Program locMap bs
 where
  locMap = colorGraph locals iGraph

colorGraph :: Locals
           -> Map X2.Arg (Set X2.Arg)
           -> Map String X2.StoreLoc
colorGraph locals iList = trace (show vectors) $
  M.fromList
  . mapMaybe
      (\(v, c) -> case lookup v vertexAssoc of
          Just (X2.Reg _) -> Nothing
          Just var@(X2.Var s) -> Just (s, storeLocFromColor vectors var c)
          Nothing         -> Nothing
          _               -> error $ "Found " ++ show v ++ "in vertexAssoc")
  . M.toList
  $ coloring
 where

  vectors =
    S.fromList
    . map (\s -> X2.Var s)
    . M.keys
    . M.filter (\t -> case t of
                   C2.TVector _ -> True
                   _ -> False)
    $ locals

  coloring :: M.Map Vertex Color
  coloring = color g M.empty needColors alreadyColored

  needColors :: S.Set Vertex
  needColors = S.fromList . map fst $ varVerts

  alreadyColored :: (M.Map Vertex Color)
  alreadyColored =
    M.fromList
    . mapMaybe
        (\(v, a) -> case a of
            (X2.Reg r) -> case colorFromReg r of
              Nothing -> Nothing
              Just n  -> Just (v, n)
            _ -> error $ "colorGraph: Don't expect " ++ show a ++
                 " in the regVerts list.")
    $ regVerts

  varVerts = vertexAssoc \\ regVerts

  regVerts :: [(Vertex, X2.Arg)]
  regVerts = filter (\(_, a) -> X2.isReg a) vertexAssoc

  vertexAssoc = M.toList vertexMap

  (g, vertexMap, _) = mapSetToGraph iList

regsToUse :: [Register]
regsToUse = take 3 . tail $ callerSaved

regIntAssoc :: [(Int, Register)]
regIntAssoc = zip [0..] regsToUse

storeLocFromColor :: Set X2.Arg -> X2.Arg -> Int -> X2.StoreLoc
storeLocFromColor vectors var n = case lookup n regIntAssoc of
  Just r -> X2.RegLoc r
  Nothing ->
    if S.member var vectors
    then X2.RootStack $ negate $ 8 * n - length regIntAssoc
    else X2.Stack $ negate $ 8 * n - length regIntAssoc

colorFromReg :: Register -> Maybe Int
colorFromReg r = lookup r (map swap regIntAssoc)

{----- Assign Homes -----}

type StackSize = Int
type RootStackSize = Int

assignHomes :: X2.Program LocMap -> X2.Program (StackSize, RootStackSize)
assignHomes (X2.Program locMap bs) = X2.Program (frameSize locMap) bs'
 where
  bs' = map (\(l, b) -> (l, ahBlock locMap b)) bs

ahBlock :: M.Map String X2.StoreLoc -> X2.Block -> X2.Block
ahBlock m (X2.Block instrs) =
  X2.Block (map (ahInstr m) instrs)

ahInstr :: M.Map String X2.StoreLoc -> X2.Instr -> X2.Instr
ahInstr m (X2.Addq aL aR)   = X2.Addq (ahArg m aL) (ahArg m aR)
ahInstr m (X2.Subq aL aR)   = X2.Subq (ahArg m aL) (ahArg m aR)
ahInstr m (X2.Movq aL aR)   = X2.Movq (ahArg m aL) (ahArg m aR)
ahInstr m (X2.Movzbq aL aR) = X2.Movzbq (ahArg m aL) (ahArg m aR)
ahInstr _ X2.Retq           = X2.Retq
ahInstr m (X2.Negq a)       = X2.Negq (ahArg m a)
ahInstr _ i@(X2.Callq _)    = i
ahInstr _ i@(X2.Jmp _)      = i
ahInstr _ i@(X2.Pushq _)    = i
ahInstr m (X2.Xorq aL aR)   = X2.Xorq (ahArg m aL) (ahArg m aR)
ahInstr m (X2.Cmpq aL aR)   = X2.Cmpq (ahArg m aL) (ahArg m aR)
ahInstr m (X2.Set cc a)     = X2.Set cc (ahArg m a)
ahInstr _ i@(X2.JmpIf _ _)  = i
ahInstr _ i@(X2.Label _)    = i
ahInstr _ i@(X2.Popq _)     = i

ahArg :: M.Map String X2.StoreLoc -> X2.Arg -> X2.Arg
ahArg _ a@(X2.Num _) = a
ahArg m (X2.Var s) = case M.lookup s m of
  Nothing -> error $ "Assign homes: Variable " ++ s ++ " not found in map."
  Just (X2.RegLoc r) -> X2.Reg r
  Just (X2.Stack n)  -> X2.Deref Rbp n
  Just (X2.RootStack n) -> X2.Deref R15 (negate n)
ahArg _ a@(X2.Reg _) = a
ahArg _ a@(X2.Deref _ _) = a
ahArg _ a@(X2.ByteReg _) = a

frameSize :: M.Map String X2.StoreLoc -> (StackSize, RootStackSize)
frameSize locMap = trace ("\nrootBytes: " ++ show rootBytes ++ "\nLocMap: " ++ show locMap)
  (stackBytes, rootBytes)
 where
  rootBytes = foldr (\n acc -> if n < acc then n else acc) 0
            . mapMaybe (\x -> case x of
                         (X2.RootStack n) -> Just n
                         _            -> Nothing)
            . M.elems
            $ locMap

  stackBytes =
    if stackBytes' `mod` 16 == 0
    then stackBytes'
    else 16 * ((stackBytes' `div` 16) + 1)

  stackBytes' =  negate
              . foldr (\n acc -> if n < acc then n else acc) 0
              . mapMaybe (\x -> case x of
                           (X2.Stack n) -> Just n
                           _            -> Nothing)
              . M.elems
              $ locMap

{----- Patch Instructions -----}

patchInstructions :: X2.Program (StackSize, RootStackSize) -> X2.Program ()
patchInstructions (X2.Program (sSize, rsSize) bs) = X2.Program () bs'
 where
  bs' = intro sSize rsSize
      : conclusion sSize rsSize
      : map (\(l, b) -> (l, pBlock b)) bs

intro :: StackSize -> RootStackSize -> (String, X2.Block)
intro sSize rsSize = ( "main",
  X2.Block (
    [ X2.Pushq (X2.Reg Rbp)
    , X2.Movq (X2.Reg Rsp) (X2.Reg Rbp)
    , X2.Pushq (X2.Reg R12)
    , X2.Pushq (X2.Reg Rbx)
    , X2.Pushq (X2.Reg R13)
    , X2.Pushq (X2.Reg R14)
    , X2.Subq (X2.Num sSize) (X2.Reg Rsp)
    , X2.Movq (X2.Num 16384) (X2.Reg Rdi)
    , X2.Movq (X2.Num (rsSize+8)) (X2.Reg Rsi)
    , X2.Callq "initialize"
    , X2.Movq (X2.GlobalValue "rootstack_begin") (X2.Reg R15) ]
    ++ clearRootStack rsSize ++
    [ X2.Jmp "start" ] ))
 where
  clearRootStack n
    | n == 0 = []
    | n < 0 = error "Invalid root stack size"
    | otherwise =
        X2.Movq (X2.Num 0) (X2.Deref R15 0)
        : X2.Addq (X2.Num 8) (X2.Reg R15)
        : clearRootStack (n-8)


conclusion :: StackSize -> RootStackSize -> (String, X2.Block)
conclusion sSize rsSize  =
    ( "conclusion", X2.Block
      [ X2.Subq (X2.Num rsSize) (X2.Reg R15)
      , X2.Addq (X2.Num sSize) (X2.Reg Rsp)
      , X2.Popq (X2.Reg R14)
      , X2.Popq (X2.Reg R13)
      , X2.Popq (X2.Reg Rbx)
      , X2.Popq (X2.Reg R12)
      , X2.Popq (X2.Reg Rbp)
      , X2.Retq ] )

pBlock :: X2.Block -> X2.Block
pBlock (X2.Block instrs) = X2.Block (concatMap pInstrs instrs)

pInstrs :: X2.Instr -> [X2.Instr]
pInstrs (X2.Movq (X2.Deref regL offL) (X2.Deref regR offR)) =
  [ X2.Movq (X2.Deref regL offL) (X2.Reg Rax)
  , X2.Movq (X2.Reg Rax) (X2.Deref regR offR) ]
pInstrs (X2.Addq (X2.Deref regL offL) (X2.Deref regR offR)) =
  [ X2.Movq (X2.Deref regL offL) (X2.Reg Rax)
  , X2.Addq (X2.Reg Rax) (X2.Deref regR offR) ]
pInstrs (X2.Subq (X2.Deref regL offL) (X2.Deref regR offR)) =
  [ X2.Movq (X2.Deref regL offL) (X2.Reg Rax)
  , X2.Subq (X2.Reg Rax) (X2.Deref regR offR) ]
pInstrs (X2.Xorq (X2.Deref regL offL) (X2.Deref regR offR)) =
  [ X2.Movq (X2.Deref regL offL) (X2.Reg Rax)
  , X2.Xorq (X2.Reg Rax) (X2.Deref regR offR) ]
pInstrs (X2.Cmpq l@(X2.Deref _ _) r@(X2.Deref _ _)) =
  [ X2.Movq l (X2.Reg Rax)
  , X2.Cmpq (X2.Reg Rax) r ]
pInstrs (X2.Cmpq l r@(X2.Num _)) =
  [ X2.Movq r (X2.Reg Rax)
  , X2.Cmpq l (X2.Reg Rax) ]
pInstrs (X2.Movzbq l d@(X2.Deref _ _)) =
  [ X2.Movzbq l (X2.Reg Rax)
  , X2.Movq (X2.Reg Rax) d ]

pInstrs i@(X2.Movq a1 a2) = [i | a1 /= a2]
pInstrs i = [i]


--{-- End --}

testExpr = "(vector-ref (vector-ref (vector (vector 42)) 0) 0)"

testComp = case R3.parse testExpr of
  Left _ -> undefined
  Right x -> putStrLn $ compile x

testThing = case R3.parse testExpr of
  Left _ -> undefined
  Right x -> putStrLn . show $
    --prettyPrint
    -- . patchInstructions
    -- . assignHomes
    -- . allocateRegisters
    -- . buildInterference
    -- . uncoverLive
    -- . selectInstructions
    -- . removeUnreachable
    -- . buildCFG
    explicateControl
    . collectLocals
    . rco
    . exposeAllocation
    . uniquify
    . shrink
    . fromEither
    . R3.typeCheck
    $ x



-- Expected:
--
--(program ()
-- (vector-ref
--  (vector-ref
--   (let ((vecinit48
--          (let ((vecinit44 42))
--            (let ((collectret46
--                   (if (<
--                        (+ (global-value free_ptr) 16)
--                        (global-value fromspace_end))
--                     (void)
--                     (collect 16))))
--              (let ((alloc43 (allocate 1 (Vector Integer))))
--                (let ((initret45 (vector-set! alloc43 0 vecinit44)))
--                  alloc43))))))
--     (let ((collectret50
--            (if (< (+ (global-value free_ptr) 16)
--                   (global-value fromspace_end))
--              (void)
--              (collect 16))))
--       (let ((alloc47 (allocate 1 (Vector (Vector Integer)))))
--         (let ((initret49 (vector-set! alloc47 0 vecinit48)))
--           alloc47))))
--   0)
--  0))
