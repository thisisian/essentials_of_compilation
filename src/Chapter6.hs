module Chapter6 where

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

import Prelude
import qualified R4
import qualified C3
import qualified X863 as X3

import Common
import Color

import Debug.Trace
import Safe (headNote)

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
  . limitFunctions
  . revealFunctions
  . uniquify
  . shrink
  . addMain
  . fromEither
  . R4.typeCheck


{--- Add MainFunc ---}
-- Move "main" expression into a function definition and call it "main"

addMain :: R4.Program () R4.Type () -> R4.Program () R4.Type ()
addMain (R4.Program i ds e) = R4.Program i (mainDef:ds) (R4.App R4.TNum (R4.Var (R4.TFunc [] R4.TNum) "main") [])
 where mainDef = R4.Define "main" [] R4.TNum () e :: R4.Def R4.Type ()

{----- Shrink -----}
-- Removes some possible expressions by replacing them with equivalents.
-- e.g. (- x y) => (+ x (- y)),
--      (cmp > x y) => (let ([b x]) (cmp < y b)

shrink :: R4.Program () R4.Type () -> R4.Program () R4.Type ()
shrink (R4.Program () ds main) = R4.Program () ds' (shrinkExpr main)
  where ds' = map (\(R4.Define s args ty i e) -> R4.Define s args ty i (shrinkExpr e)) ds

shrinkExpr :: R4.Expr R4.Type -> R4.Expr R4.Type
shrinkExpr e@(R4.Num _) = e
shrinkExpr e@R4.Read = e
shrinkExpr (R4.Neg e) = R4.Neg (shrinkExpr e)
shrinkExpr (R4.Add eL eR) =
  R4.Add (shrinkExpr eL) (shrinkExpr eR)
shrinkExpr (R4.Sub eL eR) =
  R4.Add (shrinkExpr eL) (R4.Neg (shrinkExpr eR))
shrinkExpr (R4.Var t s) = R4.Var t s
shrinkExpr (R4.Let t s eB e) = R4.Let t s (shrinkExpr eB) (shrinkExpr e)
shrinkExpr e@R4.T = e
shrinkExpr e@R4.F = e
shrinkExpr (R4.And eL eR) =
  R4.If R4.TBool (shrinkExpr eL) (shrinkExpr eR) (R4.F)
shrinkExpr (R4.Or eL eR) =
  R4.If R4.TBool (shrinkExpr eL) R4.T (shrinkExpr eR)
shrinkExpr (R4.Not e) = R4.Not (shrinkExpr e)
shrinkExpr (R4.Cmp R4.Eq eL eR) =
  R4.Cmp R4.Eq (shrinkExpr eL) (shrinkExpr eR)
shrinkExpr (R4.Cmp R4.Lt eL eR) =
  R4.Cmp R4.Lt (shrinkExpr eL) (shrinkExpr eR)
shrinkExpr (R4.Cmp R4.Le eL eR) =
  R4.Let R4.TBool "_shrnk"
    (shrinkExpr eL)
    (R4.Not (R4.Cmp R4.Lt (shrinkExpr eR) (R4.Var R4.TNum "_shrnk")))
shrinkExpr (R4.Cmp R4.Gt eL eR) =
  R4.Let R4.TBool "_shrnk"
    (shrinkExpr eL)
    (R4.Cmp R4.Lt (shrinkExpr eR) (R4.Var R4.TNum "_shrnk"))
shrinkExpr (R4.Cmp R4.Ge eL eR) =
  R4.Not (R4.Cmp R4.Lt (shrinkExpr eL) (shrinkExpr eR))
shrinkExpr (R4.If t cond eT eF) =
  R4.If t (shrinkExpr cond) (shrinkExpr eT) (shrinkExpr eF)
shrinkExpr (R4.Vector t elems)  =
  R4.Vector t (map shrinkExpr elems)
shrinkExpr (R4.VectorRef t vec idx) =
  R4.VectorRef t (shrinkExpr vec) idx
shrinkExpr (R4.VectorSet vec idx set) =
  R4.VectorSet (shrinkExpr vec) idx (shrinkExpr set)
shrinkExpr e@R4.Void = e
shrinkExpr e@(R4.App t f as) = R4.App t (shrinkExpr f) (map shrinkExpr as)
shrinkExpr (R4.Collect _) = undefined
shrinkExpr (R4.Allocate _ _) = undefined
shrinkExpr (R4.GlobalValue _) = undefined
shrinkExpr (R4.FunRef _ _) = undefined

{----- Uniquify -----}
-- Gives unique names to all variables bound with let.

type SymbolTable = Map String String

uniquify :: R4.Program () R4.Type () -> R4.Program () R4.Type ()
uniquify (R4.Program () ds e) = R4.Program () ds' e
 where
   ds' = runFreshEnv "_uni" (mapM (uniquifyDef st) ds)
   st = M.fromList . map (\(R4.Define s _ _ _ _) -> (s, s)) $ ds

uniquifyDef :: SymbolTable -> R4.Def R4.Type () -> FreshEnv (R4.Def R4.Type ())
uniquifyDef st (R4.Define s args retTy i e) = do
  argSt <- uniquifyArgs args
  let args' = zip (map snd argSt) (map snd args) :: [(String, R4.Type)]
      st' = M.union (M.fromList argSt) st

  e' <- uniquifyExpr st' e
  return $ (R4.Define s args' retTy i e')

uniquifyArgs :: [(String, R4.Type)] -> FreshEnv [(String, String)]
uniquifyArgs as = mapM (\(s,_) -> do
                           s' <- fresh
                           return (s, s')) as

uniquifyExpr :: SymbolTable -> R4.Expr R4.Type -> FreshEnv (R4.Expr R4.Type)
uniquifyExpr _ e@(R4.Num _) =
  return e
uniquifyExpr _ e@R4.Read =
  return e
uniquifyExpr st (R4.Neg e) =
  R4.Neg <$> uniquifyExpr st e
uniquifyExpr st (R4.Add eL eR) =
  return R4.Add `ap` uniquifyExpr st eL `ap` uniquifyExpr st eR
uniquifyExpr _ (R4.Sub _ _) = error "Found Sub in uniquify step"
uniquifyExpr st (R4.Var t name) =
  case M.lookup name st of
    Just name' -> return (R4.Var t name')
    Nothing ->
      error $ "uniquifyExpr: Symbol " ++ name ++ " not found in symbol table"
uniquifyExpr st (R4.Let t name be e) = do
  name' <- fresh
  let st' = M.insert name name' st
  be' <- uniquifyExpr st be
  e' <- uniquifyExpr st' e
  return (R4.Let t name' be' e')
uniquifyExpr _ e@R4.T = return e
uniquifyExpr _ e@R4.F = return e
uniquifyExpr _ (R4.And _ _) = error "Found And in uniquify step"
uniquifyExpr _ (R4.Or _ _) = error "Found Or in uniquify step"
uniquifyExpr st (R4.Not e) =
  R4.Not <$> uniquifyExpr st e
uniquifyExpr st (R4.Cmp cmp eL eR)
  | cmp == R4.Eq || cmp == R4.Lt =
      return (R4.Cmp cmp) `ap` uniquifyExpr st eL `ap` uniquifyExpr st eR
  | otherwise = error $ "Found " ++ show cmp ++ " in uniquify step"
uniquifyExpr st (R4.If t cond eT eF) =
  return (R4.If t)
    `ap` uniquifyExpr st cond
    `ap` uniquifyExpr st eT
    `ap` uniquifyExpr st eF
uniquifyExpr st (R4.Vector t elems) = do
  elems' <- mapM (uniquifyExpr st) elems
  return $ R4.Vector t elems'
uniquifyExpr st (R4.VectorRef t v idx) = do
  v' <- uniquifyExpr st v
  return $ R4.VectorRef t v' idx
uniquifyExpr st (R4.VectorSet v idx set) = do
  v' <- uniquifyExpr st v
  set' <- uniquifyExpr st set
  return $ R4.VectorSet v' idx set'
uniquifyExpr _ e@R4.Void = return e
uniquifyExpr _ (R4.Collect _) = undefined
uniquifyExpr _ (R4.Allocate _ _) = undefined
uniquifyExpr _ (R4.GlobalValue _) = undefined
uniquifyExpr st (R4.App t f args) = do
  f' <- uniquifyExpr st f
  args' <- mapM (uniquifyExpr st) args
  return (R4.App t f' args')
uniquifyExpr _ (R4.FunRef _ _) = undefined

{----- Reveal Functions -----}
-- Replaces variable references to functions with fun-ref node.

revealFunctions :: R4.Program () R4.Type () -> R4.Program () R4.Type ()
revealFunctions (R4.Program () ds e) = R4.Program () ds' e'
 where
  ds' = map (\(R4.Define s args retTy i ex) ->
               R4.Define s args retTy i (rfExpr ex)) ds
  e' = rfExpr e

rfExpr :: R4.Expr R4.Type -> R4.Expr R4.Type
rfExpr e@(R4.Num _) = e
rfExpr e@(R4.Read) = e
rfExpr (R4.Neg e) = R4.Neg (rfExpr e)
rfExpr (R4.Add e1 e2) = R4.Add (rfExpr e1) (rfExpr e2)
rfExpr (R4.Sub e1 e2) = R4.Sub (rfExpr e1) (rfExpr e2)
rfExpr (R4.Var t@(R4.TFunc _ _) s) = R4.FunRef t s
        -- APT: I think you have a fundamental misunderstanding here.
        -- Only top-level functions should be changed here; let-bound vars of function type should not.
        -- Use the Def list rather than the type to identify the top-level names.
rfExpr e@(R4.Var _ _) = e
rfExpr (R4.Let t s e1 e2) =
  R4.Let t s (rfExpr e1) (rfExpr e2)
rfExpr e@R4.T = e
rfExpr e@R4.F = e
rfExpr (R4.And e1 e2)= (R4.And (rfExpr e1) (rfExpr e2))
rfExpr (R4.Or e1 e2) = (R4.Or (rfExpr e1) (rfExpr e2))
rfExpr (R4.Not e) = R4.Not (rfExpr e)
rfExpr (R4.Cmp cmp e1 e2) = R4.Cmp cmp (rfExpr e1) (rfExpr e2)
rfExpr (R4.If t cond et ef) = R4.If t (rfExpr cond) (rfExpr et) (rfExpr ef)
rfExpr (R4.Vector t es) = R4.Vector t (map rfExpr es)
rfExpr (R4.VectorRef t e x) = R4.VectorRef t (rfExpr e) x
rfExpr (R4.VectorSet e x e') = R4.VectorSet (rfExpr e) x (rfExpr e')
rfExpr e@R4.Void = e
rfExpr (R4.Collect _) = undefined
rfExpr (R4.Allocate _ _) = undefined
rfExpr (R4.GlobalValue _) = undefined
rfExpr (R4.App t f args) = R4.App t (rfExpr f) (map rfExpr args)
rfExpr (R4.FunRef _ _) = undefined

{----- Limit Functions -----}
-- Here we limit
-- There is an additional constraint not specified in the book,
-- arguments with index > 5 canot be functions... because it's not obvious
-- how to deal with the func-refs we added in the revealFunctions step. Though
-- I may just remove the revealFunction step since we can determine a var
-- is a function from its type info.
-- APT: No, see my note above.

limitFunctions :: R4.Program () R4.Type () -> R4.Program () R4.Type ()
limitFunctions (R4.Program () ds e) = R4.Program () ds' e
 where
  ds' = map lfDef ds

lfDef :: R4.Def R4.Type () -> R4.Def R4.Type ()
lfDef d@(R4.Define s args t i e) =
  case splitAt 5 args of
    (_, []) -> d
    (args', vecArgs) ->
      let (argNames, argTys) = unzip vecArgs
          idxMap = zip argNames [0..]
          vecTy = (R4.TVector argTys) :: R4.Type
          args'' = args' ++ [("_vecArg", (R4.TVector argTys))]
          e' = lfExpr vecTy idxMap e
      in (R4.Define s args'' t i e')

lfExpr :: R4.Type -> [(String, Int)] -> R4.Expr R4.Type -> R4.Expr R4.Type
lfExpr _ _ e@(R4.Num _) = e
lfExpr _ _ e@(R4.Read) = e
lfExpr vecTy idxMap (R4.Neg e) = R4.Neg (lfExpr vecTy idxMap e)
lfExpr vecTy idxMap (R4.Add e1 e2) =
  R4.Add (lfExpr vecTy idxMap e1) (lfExpr vecTy idxMap e2)
lfExpr vecTy idxMap (R4.Sub e1 e2) =
  R4.Sub (lfExpr vecTy idxMap e1) (lfExpr vecTy idxMap e2)
lfExpr vecTy idxMap e@(R4.Var t s) = case lookup s idxMap of
  Just idx -> (R4.VectorRef t (R4.Var vecTy "_vecArg") idx)
  Nothing -> e
lfExpr vecTy idxMap (R4.Let t s e1 e2) =
  R4.Let t s (lfExpr vecTy idxMap e1) (lfExpr vecTy idxMap e2)
lfExpr _ _ e@R4.T = e
lfExpr _ _ e@R4.F = e
lfExpr vecTy idxMap (R4.And e1 e2) =
    (R4.And (lfExpr vecTy idxMap e1) (lfExpr vecTy idxMap e2))
lfExpr vecTy idxMap (R4.Or e1 e2) =
    (R4.Or (lfExpr vecTy idxMap e1) (lfExpr vecTy idxMap e2))
lfExpr vecTy idxMap (R4.Not e) = R4.Not (lfExpr vecTy idxMap e)
lfExpr vecTy idxMap (R4.Cmp cmp e1 e2) =
  R4.Cmp cmp (lfExpr vecTy idxMap e1) (lfExpr vecTy idxMap e2)
lfExpr vecTy idxMap (R4.If t cond et ef) =
  R4.If t
    (lfExpr vecTy idxMap cond)
    (lfExpr vecTy idxMap et)
    (lfExpr vecTy idxMap ef)
lfExpr vecTy idxMap (R4.Vector t es) =
  R4.Vector t (map (lfExpr vecTy idxMap) es)
lfExpr vecTy idxMap (R4.VectorRef t e x) =
  R4.VectorRef t (lfExpr vecTy idxMap e) x
lfExpr vecTy idxMap (R4.VectorSet e x e') =
  R4.VectorSet (lfExpr vecTy idxMap e) x (lfExpr vecTy idxMap e')
lfExpr _ _ e@R4.Void = e
lfExpr _ _ (R4.Collect _) = undefined
lfExpr _ _ (R4.Allocate _ _) = undefined
lfExpr _ _ (R4.GlobalValue _) = undefined
lfExpr vecTy idxMap (R4.App t f args) =
  R4.App t (lfExpr vecTy idxMap f) (map (lfExpr vecTy idxMap) args)
lfExpr vecTy idxMap e@(R4.FunRef t s) = case lookup s idxMap of
  Just idx -> (R4.VectorRef t (R4.Var vecTy "_vecArg") idx)
  Nothing -> e

{----- Expose Allocation -----}

exposeAllocation :: R4.Program () R4.Type () -> R4.Program () R4.Type ()
exposeAllocation (R4.Program () ds e) = R4.Program () ds' e
 where
  ds' = runFreshEnv "" (mapM eaDef ds)

eaDef :: R4.Def R4.Type () -> FreshEnv (R4.Def R4.Type ())
eaDef (R4.Define s args ret () e) = do
  e' <- eaExpr e
  return $ R4.Define s args ret () e'

eaExpr :: R4.Expr R4.Type -> FreshEnv (R4.Expr R4.Type)
eaExpr e@(R4.Num _) = return e
eaExpr e@R4.Read = return e
eaExpr (R4.Neg e) = do
  e' <- eaExpr e
  return $ R4.Neg e'
eaExpr (R4.Add eL eR) = do
  eL' <- eaExpr eL
  eR' <- eaExpr eR
  return $ R4.Add eL' eR'
eaExpr (R4.Sub _ _) = error "Found Sub in exposeAllocation step"
eaExpr e@(R4.Var _ _) = return e
eaExpr (R4.Let t s bE e) = do
  bE' <- eaExpr bE
  e' <- eaExpr e
  return $ R4.Let t s bE' e'
eaExpr e@R4.T = return e
eaExpr e@R4.F = return e
eaExpr (R4.And _ _) = error "Found And in exposeAllocation step"
eaExpr (R4.Or _ _) = error "Found Or in exposeAllocation step"
eaExpr (R4.Not e) = do
  e' <- eaExpr e
  return $ R4.Not e'
eaExpr (R4.Cmp cmp eL eR) = do
  eL' <- eaExpr eL
  eR' <- eaExpr eR
  return $ R4.Cmp cmp eL' eR'
eaExpr (R4.If t cond eT eF) = do
  cond' <- eaExpr cond
  eT' <- eaExpr eT
  eF' <- eaExpr eF
  return $ R4.If t cond' eT' eF'
eaExpr (R4.Vector t elems) = do
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
                              ,(R4.VectorSet (R4.Var t v) idx (R4.Var ty name))))
      . zip [0..]
      . map (\(s, e) -> (s, R4.getType e))
      $ elemBinds)
  return $
    makeBindings elemBinds $
      (R4.Let R4.TVoid c
        (R4.If R4.TVoid
          (R4.Cmp R4.Lt
             (R4.Add (R4.GlobalValue "free_ptr") (R4.Num bytes))
             (R4.GlobalValue "fromspace_end"))
          (R4.Void)
          (R4.Collect bytes))
      (R4.Let R4.TVoid v (R4.Allocate len t)
      (makeBindings initVec (R4.Var t v))))
eaExpr (R4.VectorRef t v idx) = do
  v' <- eaExpr v
  return $ R4.VectorRef t v' idx
eaExpr (R4.VectorSet v idx set) = do
  v' <- eaExpr v
  set' <- eaExpr set
  return $ R4.VectorSet v' idx set'
eaExpr R4.Void = return R4.Void
eaExpr (R4.Collect _) = undefined
eaExpr (R4.Allocate _ _) = undefined
eaExpr (R4.GlobalValue _) = undefined
eaExpr (R4.App t e es) = do
  e' <- eaExpr e
  es' <- mapM eaExpr es
  return $ R4.App t e' es'
eaExpr e@(R4.FunRef _ _) = return e

{----- Remove Complex Operations and Operands -----}

rco :: R4.Program () R4.Type () -> R4.Program () R4.Type ()
rco p = runFreshEnv "_rco" (rcoProg p)

rcoProg :: R4.Program () R4.Type () -> FreshEnv (R4.Program () R4.Type ())
rcoProg (R4.Program () ds e) = do
  e' <- rcoExpr e
  ds' <- mapM rcoDef ds
  return (R4.Program () ds' e')

rcoDef :: R4.Def R4.Type () -> FreshEnv (R4.Def R4.Type ())
rcoDef (R4.Define s args retTy i e) = do
  e' <- rcoExpr e
  return $ R4.Define s args retTy i e'

rcoExpr :: R4.Expr R4.Type -> FreshEnv (R4.Expr R4.Type)
rcoExpr e@(R4.Num _) = return e
rcoExpr e@R4.Read = do
  (bindings, e') <- rcoArg e
  return $ makeBindings bindings e'
rcoExpr (R4.Neg e) = do
  (bindings, e') <- rcoArg e
  return $ makeBindings bindings (R4.Neg e')
rcoExpr (R4.Add eL eR) = do
  (bindingsL, eL') <- rcoArg eL
  (bindingsR, eR') <- rcoArg eR
  return $ makeBindings (bindingsL++bindingsR) (R4.Add eL' eR')
rcoExpr (R4.Sub _ _ ) = error "Found Sub in RCO step"
rcoExpr e@(R4.Var _ _) = return e
rcoExpr (R4.Let t name be e) = do
  (bindingsBE, be') <- rcoArg be
  e' <- rcoExpr e
  return $ makeBindings bindingsBE (R4.Let t name be' e')
rcoExpr R4.T = return R4.T
rcoExpr R4.F = return R4.F
rcoExpr (R4.And _ _) = error "Found Add in RCO step"
rcoExpr (R4.Or _ _) = error "Found Or in RCO step"
rcoExpr (R4.Not e) = do
  (bindings, e') <- rcoArg e
  return $ makeBindings bindings (R4.Not e')
rcoExpr (R4.Cmp cmp eL eR)
  | cmp == R4.Eq || cmp == R4.Lt = do
      (bindingsL, eL') <- rcoArg eL
      (bindingsR, eR') <- rcoArg eR
      return $ makeBindings (bindingsL++bindingsR) (R4.Cmp cmp eL' eR')
  | otherwise = error $ "Found " ++ show cmp ++ "in RCO step."
rcoExpr (R4.If t cond eT eF) = do
  (bindings, cond') <- rcoArg cond
  eT' <- rcoExpr eT
  eF' <- rcoExpr eF
  return $ makeBindings bindings (R4.If t cond' eT' eF')
rcoExpr (R4.Vector _ _) = error $ "rcoExpr called on Vector"
rcoExpr (R4.VectorRef t v idx) = do
  (bindings, v') <- rcoArg v
  return $ makeBindings bindings (R4.VectorRef t v' idx)
rcoExpr (R4.VectorSet v idx set) = do
  (bindingsV, v') <- rcoArg v
  (bindingsSet, set') <- rcoArg set
  return $ makeBindings (bindingsV ++ bindingsSet) (R4.VectorSet v' idx set')
rcoExpr e@R4.Void = return e
rcoExpr e@(R4.Collect _) = return e
rcoExpr e@(R4.Allocate _ _) = return e
rcoExpr e@(R4.GlobalValue _) = return e
rcoExpr (R4.App t f as) = do
  (bindingsF, f') <- rcoArg f
  (bindingsArg, as') <- unzip <$> mapM rcoArg as
  let bindings = bindingsF ++ concat bindingsArg
  return $ makeBindings (bindings) (R4.App t f' as')
rcoExpr e@(R4.FunRef _ _) = return e


rcoArg :: R4.Expr R4.Type
       -> FreshEnv ([(String, (R4.Expr R4.Type))], (R4.Expr R4.Type))
rcoArg (R4.Num x) = return ([], R4.Num x)
rcoArg R4.Read = do
  n <- fresh
  return ([(n , R4.Read)] , R4.Var R4.TNum n)
rcoArg (R4.Neg e) = do
  (bindings, e') <- rcoArg e
  n <- fresh
  return (bindings ++ [(n, R4.Neg e')]
         , R4.Var R4.TNum n)
rcoArg (R4.Add eL eR) = do
  (bindingsL, eL') <- rcoArg eL
  (bindingsR, eR') <- rcoArg eR
  n <- fresh
  return (bindingsL ++ bindingsR ++ [(n, R4.Add eL' eR')]
         , R4.Var R4.TNum n)
rcoArg (R4.Sub _ _) =error "Found Sub in RCO step"
rcoArg e@(R4.Var _ _) = return ([], e)
rcoArg (R4.Let _ n be e) = do
  (bindingsBE, be') <- rcoArg be
  (bindings, e') <- rcoArg e
  return (bindingsBE ++ [(n, be')] ++ bindings, e')
rcoArg R4.T = return ([], R4.T)
rcoArg R4.F = return ([], R4.F)
rcoArg (R4.And _ _) = error "Found And in RCO step"
rcoArg (R4.Or _ _) = error "Found Or in RCO step"
rcoArg (R4.Not e) = do
  (bindings, e') <- rcoArg e
  n <- fresh
  return (bindings ++ [(n, R4.Not e')], R4.Var R4.TBool n)
rcoArg (R4.Cmp cmp eL eR)
  | cmp == R4.Eq || cmp == R4.Lt = do
      (bindingsL, eL') <- rcoArg eL
      (bindingsR, eR') <- rcoArg eR
      n <- fresh
      return (bindingsL ++ bindingsR ++ [(n, R4.Cmp cmp eL' eR')]
             , R4.Var R4.TBool n)
  | otherwise = error $ "Found " ++ show cmp ++ "in RCO step."
rcoArg (R4.If t cond eT eF) = do
  (bindings, cond') <- rcoArg cond
  eT' <- rcoExpr eT
  eF' <- rcoExpr eF
  n <- fresh
  return (bindings ++ [(n, R4.If t cond' eT' eF')], R4.Var t n)
rcoArg (R4.Vector _ _) = error "Called rcoArg on Vector"
rcoArg (R4.VectorRef t v idx) = do
  (bindings, v') <- rcoArg v
  n <- fresh
  return (bindings ++ [(n, R4.VectorRef t v' idx)], R4.Var t n)
rcoArg (R4.VectorSet v idx set) = do
  (bindingsV, v') <- rcoArg v
  (bindingsSet, set') <- rcoArg set
  n <- fresh
  return ( bindingsV ++ bindingsSet ++ [(n, R4.VectorSet v' idx set')]
         , R4.Var R4.TVoid n )
rcoArg e@R4.Void = return ([], e)
rcoArg e@(R4.Collect _) = return ([], e)
rcoArg e@(R4.Allocate _ _) = return ([], e)
rcoArg e@(R4.GlobalValue _) = do
  n <- fresh
  return ([(n, e)], (R4.Var R4.TVoid n))
rcoArg (R4.App t f as) = do
  (bindingsF, f') <- rcoArg f
  (bindingsArg, as') <- unzip <$> mapM rcoArg as
  let bindings = bindingsF ++ concat bindingsArg
  n <- fresh
  return (bindings ++ [(n, R4.App t f' as')], R4.Var t n)
rcoArg (R4.FunRef t s) = do
  n <- fresh
  return ([(n, R4.FunRef t s)], R4.Var t n)

makeBindings :: [(String, R4.Expr R4.Type)] -> R4.Expr R4.Type -> R4.Expr R4.Type
makeBindings ((b, be):bs) e =
  R4.Let (R4.getType be) b be (makeBindings bs e)
makeBindings [] e = e

{----- Collect Locals -----}
-- Create a map of variables and their associated type for each definition.

type Locals = Map String C3.Type

collectLocals :: R4.Program () R4.Type ()
              -> R4.Program () (R4.Type) Locals
collectLocals (R4.Program () ds e) = R4.Program () ds' e
 where
   ds' = map (\(R4.Define s args ty () e') ->
                let locals = M.fromList (clsExpr e')
                in (R4.Define s args ty locals e')) ds

clsExpr :: R4.Expr R4.Type -> [(String, C3.Type)]
clsExpr (R4.Num _)  = []
clsExpr R4.Read  = []
clsExpr (R4.Neg e) = clsExpr e
clsExpr (R4.Add eL eR) = clsExpr eL ++ clsExpr eR
clsExpr (R4.Sub eL eR) = clsExpr eL ++ clsExpr eR
clsExpr (R4.Var _ _) = []
clsExpr (R4.Let t s eB e) = (s, toC2Type t):(clsExpr eB ++ clsExpr e)
clsExpr R4.T = []
clsExpr R4.F = []
clsExpr (R4.And _ _) = undefined
clsExpr (R4.Or _ _) = undefined
clsExpr (R4.Not e) = clsExpr e
clsExpr (R4.Cmp _ eL eR) = clsExpr eL ++ clsExpr eR
clsExpr (R4.If _ cond eT eF) = clsExpr cond ++ clsExpr eT ++ clsExpr eF
clsExpr (R4.Vector _ es) = concatMap clsExpr es
clsExpr (R4.VectorSet v _ set) = clsExpr v ++ clsExpr set
clsExpr (R4.VectorRef _ _ _) = []
clsExpr R4.Void = []
clsExpr (R4.Collect _) = []
clsExpr (R4.Allocate _ _) = []
clsExpr (R4.GlobalValue _) = []
clsExpr (R4.App _ f args) =
  clsExpr f ++ concatMap clsExpr args
clsExpr (R4.FunRef _ _) = []

toC2Type :: R4.Type -> C3.Type
toC2Type R4.TBool = C3.TBool
toC2Type R4.TVoid = C3.TVoid
toC2Type R4.TNum = C3.TNum
toC2Type (R4.TVector ts) = (C3.TVector (map toC2Type ts))
toC2Type (R4.TFunc ts t) = C3.TFunc ts' t'
 where
  ts' = map toC2Type ts
  t' = toC2Type t


{----- Explicate Control -----}
-- Make the ordre of execution explicit. Translate to C3.

explicateControl :: R4.Program () (R4.Type) (Locals) -> C3.Program () (Locals)
explicateControl (R4.Program () ds _) = C3.Pgrm () ds'
 where ds' = evalState (mapM ecDef ds) (EcS M.empty 0)

ecDef :: R4.Def R4.Type Locals -> State EcS (C3.Def Locals)
ecDef (R4.Define s args retTy locals e) = do
  let args' = map (\(s', ty) -> (s', toC2Type ty)) args
      retTy' = toC2Type retTy
  e' <- ecTail e
  bs <- M.toList <$> flushBlocks
  return $ (C3.Def s args' retTy' locals ((s, e'):bs))

ecTail :: R4.Expr R4.Type -> State EcS C3.Tail
ecTail (R4.Let _ s be e) = do
  e' <- ecTail e
  ecAssign be s e'
ecTail (R4.If _ eCmp eT eF ) = do
  eT' <- ecTail eT
  eF' <- ecTail eF
  ecPred eCmp eT' eF'
ecTail (R4.Num x) = return $ C3.Return (C3.Plain (C3.Num x))
ecTail R4.Read =
  error "ecTail: Found read in tail position"
ecTail (R4.Neg e) = return $ C3.Return (C3.Neg (ecArg e))
ecTail (R4.Add eL eR) = return $ C3.Return (C3.Plus (ecArg eL) (ecArg eR))
ecTail (R4.Var _ s) =
  return (C3.Return (C3.Plain (C3.Var s)))
ecTail R4.T = return $ C3.Return (C3.Plain C3.T)
ecTail R4.F = return $ C3.Return (C3.Plain C3.F)
ecTail (R4.And _ _) =
  error "ecTail: Found And"
ecTail (R4.Or _ _) =
  error "ecTail: Found Or"
ecTail (R4.Sub _ _) =
  error "ecTail: Found Sub"
ecTail (R4.Not e) = return $ C3.Return (C3.Not (ecArg e))
ecTail (R4.Cmp cmp eL eR) =
  return $ C3.Return (C3.Cmp (ecCmp cmp) (ecArg eL) (ecArg eR))
ecTail (R4.Vector _ _) = error "Found Vector in ecTail"
ecTail (R4.VectorRef _ v idx) = do
  let v' = ecArg v
  return $ C3.Return (C3.VectorRef v' idx)
ecTail (R4.VectorSet v idx set) = do
  let v' = ecArg v
      set' = ecArg set
  return $ C3.Return (C3.VectorSet v' idx set')
ecTail (R4.Void) = return $ C3.Return C3.Void
ecTail (R4.Collect x) =
  return $ C3.Seq (C3.Collect x) (C3.Return C3.Void)
ecTail (R4.Allocate x t) =
  return $ C3.Return (C3.Allocate x (toC2Type t))
ecTail (R4.GlobalValue s) =
  return $ C3.Return (C3.GlobalValue s)
ecTail (R4.FunRef _ s) =
  return $ (C3.Return (C3.FunRef s))
ecTail (R4.App _ e es) =
  return $ C3.TailCall (ecArg e) (map ecArg es)


ecPred :: R4.Expr R4.Type -> C3.Tail -> C3.Tail -> State EcS C3.Tail
ecPred R4.T t1 _ =
  return t1
ecPred R4.F _ t2 =
  return t2
ecPred a@(R4.Var _ _) t1 t2 = do
  l1 <- newBlock t1
  l2 <- newBlock t2
  return $ C3.If C3.Eq (ecArg a) C3.T l1 l2
ecPred (R4.Not e) t1 t2 = do
  l1 <- newBlock t1
  l2 <- newBlock t2
  return $ C3.If C3.Eq (ecArg e) C3.F l1 l2
ecPred (R4.If _ cond eT eF) t1 t2 = do
  l1 <- newBlock t1
  l2 <- newBlock t2
  eT' <- ecPred eT (C3.Goto l1) (C3.Goto l2)
  eF' <- ecPred eF (C3.Goto l1) (C3.Goto l2)
  ecPred cond eT' eF'
ecPred (R4.Cmp cmp eL eR) t1 t2 = do
  l1 <- newBlock t1
  l2 <- newBlock t2
  return $ C3.If (ecCmp cmp) (ecArg eL) (ecArg eR) l1 l2
ecPred (R4.Let _ s eB e) t1 t2 = do
  e' <- ecPred e t1 t2
  ecAssign eB s e'
ecPred e _ _ = error $ "ecPred: " ++ show e

ecAssign :: R4.Expr R4.Type -> String -> C3.Tail -> State EcS C3.Tail
ecAssign R4.Read s t =
  return $ C3.Seq (C3.Assign s C3.Read) t
ecAssign (R4.Add eL eR) s t =
  return $ C3.Seq (C3.Assign s (C3.Plus (ecArg eL) (ecArg eR))) t
ecAssign (R4.Neg e) s t =
  return $ C3.Seq (C3.Assign s (C3.Neg (ecArg e))) t
ecAssign (R4.Not e) s t =
  return $ C3.Seq (C3.Assign s (C3.Not (ecArg e))) t
ecAssign (R4.Cmp cmp eL eR) s t =
  return $ C3.Seq (C3.Assign s (C3.Cmp (ecCmp cmp) (ecArg eL) (ecArg eR))) t
ecAssign e@(R4.Num _) s t =
  return $ C3.Seq (C3.Assign s (C3.Plain (ecArg e))) t
ecAssign e@(R4.Var _ _) s t =
  return $ C3.Seq (C3.Assign s (C3.Plain (ecArg e))) t
ecAssign R4.T s t =
  return $ C3.Seq (C3.Assign s (C3.Plain C3.T)) t
ecAssign R4.F s t =
  return $ C3.Seq (C3.Assign s (C3.Plain C3.F)) t
ecAssign (R4.If _ cond eT eF) s t = do
  lbl <- newBlock t
  eT' <- ecAssign eT s (C3.Goto lbl)
  eF' <- ecAssign eF s (C3.Goto lbl)
  ecPred cond eT' eF'
ecAssign (R4.Let _ sIn bE e) sOut t = do
  let' <- ecAssign e sOut t
  ecAssign bE sIn let'
ecAssign (R4.VectorRef _ v idx) s t = do
  let v' = ecArg v
  return $ C3.Seq (C3.Assign s (C3.VectorRef v' idx)) t
ecAssign (R4.VectorSet v idx set) s t = do
  let v' = ecArg v
      set' = ecArg set
  return $ C3.Seq (C3.Assign s (C3.VectorSet v' idx set')) t
ecAssign (R4.Void) s t =
  return $ C3.Seq (C3.Assign s C3.Void) t
ecAssign (R4.GlobalValue s') s t =
  return $ C3.Seq (C3.Assign s (C3.GlobalValue s')) t
ecAssign (R4.Allocate x ty) s t =
  return $ C3.Seq (C3.Assign s (C3.Allocate x (toC2Type ty))) t
ecAssign (R4.Collect x) s t =
  return $ (C3.Seq (C3.Assign s C3.Void) (C3.Seq (C3.Collect x) t))
ecAssign (R4.FunRef _ f) s t =
  return $ (C3.Seq (C3.Assign s (C3.FunRef f)) t)
ecAssign (R4.App _ f as) s t =
  return $ (C3.Seq (C3.Assign s (C3.Call (ecArg f) (map ecArg as))) t)
ecAssign e s t =
  error $ "Called ecAssign on " ++ show e ++ ", " ++ show s ++ ", " ++ show t

ecArg :: R4.Expr R4.Type -> C3.Arg
ecArg (R4.Num x) = C3.Num x
ecArg (R4.Var _ x) = C3.Var x
ecArg R4.T = C3.T
ecArg R4.F = C3.F
ecArg e = error $ "Called ecArg on " ++ show e

ecCmp :: R4.Compare -> C3.Compare
ecCmp R4.Eq = C3.Eq
ecCmp R4.Lt = C3.Lt
ecCmp c = error $ "Called ecCmp on " ++ show c

{- A monad for explicate control -}
data EcS = EcS { ecsBlocks :: Map String C3.Tail, freshBlockNum :: Int }

{- APT:
runEcState :: R4.Expr R4.Type -> (C3.Tail, Map String C3.Tail)
runEcState e =
  let (startBlock, ecsState) = runState (ecTail e) (EcS M.empty 0)
  in (startBlock, ecsBlocks ecsState)
-}

freshNum :: State EcS Int
freshNum = do
  (EcS blocks x) <- get
  put (EcS blocks (x+1))
  return x

flushBlocks :: State EcS (Map String C3.Tail)
flushBlocks = do
  (EcS blocks x) <- get
  put (EcS M.empty x)
  return blocks

newBlock :: C3.Tail -> State EcS String
newBlock t = do
  (EcS blocks x) <- get
  let lbl = "block"++show x
  put (EcS (M.insert lbl t blocks) (x+1))
  return lbl

{----- Build CFG -----}

type CFG = Map String (Set String)

buildCFG :: C3.Program () (Locals) -> C3.Program () (Locals, CFG)
buildCFG (C3.Pgrm () ds) = C3.Pgrm () ds'
 where
   ds' = map (\(C3.Def s args ret locals bs) ->
                let cfg = mkCFG bs M.empty
                in C3.Def s args ret (locals, cfg) bs) ds

mkCFG :: [(String, C3.Tail)]
      -> Map String (Set String)
      -> Map String (Set String)
mkCFG ((s, b):bs) m = case b of
  C3.Seq _ t  -> mkCFG ((s, t):bs) m
  C3.Return _ ->
    let m' = M.insert s S.empty m
    in mkCFG bs m'
  C3.Goto b'   ->
    let m' = M.insert s (S.singleton b') m
    in mkCFG bs m'
  C3.If _ _ _ b1 b2 ->
    let m' = M.insert s (S.fromList [b1, b2]) m
    in mkCFG bs m'
  C3.TailCall _ _ ->
    let m' = M.insert s S.empty m
    in mkCFG bs m'

mkCFG [] m = m

{----- Remove Unreachable Blocks -----}

removeUnreachable :: C3.Program () (Locals, CFG) -> C3.Program () (Locals, CFG)
removeUnreachable (C3.Pgrm () ds) = (C3.Pgrm () ds')
 where ds' = map ruDef ds

ruDef :: C3.Def (Locals, CFG) -> C3.Def (Locals, CFG)
ruDef (C3.Def s args ty (locals, cfg) bs) = (C3.Def s args ty (locals, cfg) bs')
 where
   bs' = filter (\(lbl, _) -> lbl `elem` reachableBlks) bs

   reachableBlks :: [String]
   reachableBlks = mapMaybe (\v -> M.lookup v v2lbl)
                   $ reachable g startVert
   startVert = fromJust $  M.lookup (fst . head $ bs) lbl2v

   (g, v2lbl, lbl2v) = mapSetToGraph cfg


{----- Select Instructions -----}

selectInstructions :: C3.Program () (Locals, CFG) -> X3.Program () (Locals, CFG)
selectInstructions (C3.Pgrm () ds) = X3.Program () ds'
 where
  ds' = map siDef ds

siDef :: C3.Def (Locals, CFG) -> X3.Def (Locals, CFG)
siDef (C3.Def s args _ i bs) = (X3.Def s i bs')
 where
  bs' = map (\(l, b) -> (l, X3.Block . (siTail s params) $ b)) bs
  params = map fst args

siTail :: String -> [String] -> C3.Tail -> [X3.Instr]
siTail fName params (C3.Return (C3.Plain a))    =
  moveParam params a ++
  [ X3.Movq (siArg a) (X3.Reg Rax)
  , X3.Jmp (fName++"conclusion") ]
siTail fName _ (C3.Return C3.Read)         =
  [ X3.Callq "read_int"
  , X3.Jmp (fName++"conclusion") ]
siTail fName params (C3.Return (C3.Neg a))      =
  moveParam params a ++
  [ X3.Movq (siArg a) (X3.Reg Rax)
  , X3.Negq (X3.Reg Rax)
  , X3.Jmp (fName++"conclusion") ]
siTail fName params (C3.Return (C3.Plus aL aR)) =
  moveParam params aL ++ moveParam params aR ++
  [ X3.Movq (siArg aL) (X3.Reg Rax)
  , X3.Addq (siArg aR) (X3.Reg Rax)
  , X3.Jmp (fName++"conclusion") ]
siTail fName params (C3.Return (C3.Not a)) =
  moveParam params a ++
  [ X3.Movq (siArg a) (X3.Reg Rax)
  , X3.Xorq (X3.Num 1) (X3.Reg Rax)
  , X3.Jmp (fName++"conclusion") ]
siTail fName params (C3.Return (C3.Cmp cmp aL aR)) =
  moveParam params aR ++
  moveParam params aL ++
  [ X3.Cmpq (siArg aR) (siArg aL)
  , X3.Set (siCompare cmp) (X3.ByteReg Al)
  , X3.Movzbq (X3.ByteReg Al) (X3.Reg Rax)
  , X3.Jmp (fName++"conclusion") ]
siTail fName params (C3.Return (C3.VectorRef a x)) =
  moveParam params a ++
  [ X3.Movq (siArg a) (X3.Reg R11)
  , X3.Movq (X3.Deref R11 (8*(x+1))) (X3.Reg Rax)
  , X3.Jmp (fName++"conclusion") ]
siTail fName params (C3.Seq assign t) =
  siStmt params assign ++ siTail fName params t
siTail _ params (C3.Goto s) = [X3.Jmp s]
siTail _ params (C3.If cmp aT aF gT gF) =
  moveParam params aT ++
  moveParam params aF ++
  [ X3.Cmpq (siArg aF) (siArg aT)
  , X3.JmpIf (siCompare cmp) gT
  , X3.Jmp gF ]
siTail _ params (C3.TailCall a as) =
  moveParam params a ++
  concatMap (moveParam params) as ++
  zipWith (\arg reg -> X3.Movq (siArg arg) (X3.Reg reg))
    as
    paramRegs ++
  [ X3.TailJmp (siArg a) ]
siTail _ _ e = error $ "siTail: " ++ show e

siStmt :: [String] -> C3.Stmt -> [X3.Instr]
siStmt params (C3.Assign s (C3.Plain a))    =
  moveParam params a ++
  [ X3.Movq (siArg a) (X3.Var s) ]
siStmt _ (C3.Assign s C3.Read)       =
  [ X3.Callq "read_int"
  , X3.Movq (X3.Reg Rax) (X3.Var s) ]
siStmt params (C3.Assign s (C3.Neg a))
  | a == C3.Var s =
    moveParam params a ++
    [ X3.Negq (X3.Var s) ]
  | otherwise    =
    moveParam params a ++
    [ X3.Movq (siArg a) (X3.Var s)
    , X3.Negq (X3.Var s) ]
siStmt params (C3.Assign s (C3.Plus aL aR))
  | aL == C3.Var s =
    moveParam params aL ++
    moveParam params aR ++
    [ X3.Addq (siArg aR) (X3.Var s) ]
  | aR == C3.Var s =
    moveParam params aL ++
    moveParam params aR ++
    [ X3.Addq (siArg aL) (X3.Var s) ]
  | otherwise     =
    moveParam params aL ++
    moveParam params aR ++
    [ X3.Movq (siArg aL) (X3.Var s)
    , X3.Addq (siArg aR) (X3.Var s) ]
siStmt params (C3.Assign s (C3.Not a))
  | a == C3.Var s =
    moveParam params a ++
    [ X3.Xorq (X3.Num 1) (siArg a) ]
  | otherwise =
    moveParam params a ++
    [ X3.Movq (siArg a) (X3.Var s)
    , X3.Xorq (X3.Num 1) (X3.Var s) ]
siStmt params (C3.Assign s (C3.Cmp cmp aL aR)) =
  moveParam params aL ++
  moveParam params aR ++
  [ X3.Cmpq (siArg aR) (siArg aL)
  , X3.Set (siCompare cmp) (X3.ByteReg Al)
  , X3.Movzbq (X3.ByteReg Al) (X3.Var s) ]
siStmt params (C3.Assign s (C3.VectorRef v x)) =
  moveParam params v ++
  [ X3.Movq (siArg v) (X3.Reg R11)
  , X3.Movq (X3.Deref R11 (8*(x+1))) (X3.Var s)
  ]
siStmt params (C3.Assign s (C3.VectorSet v x a)) =
  moveParam params v ++
  moveParam params a ++
  [ X3.Movq (siArg v) (X3.Reg R11)
  , X3.Movq (siArg a) (X3.Deref R11 (8*(x+1)))
  , X3.Movq (X3.Num 0) (X3.Var s) ]
siStmt _ (C3.Assign s (C3.Allocate sz ty)) =
  [ X3.Movq (X3.GlobalValue "free_ptr") (X3.Var s)
  , X3.Addq (X3.Num (8*(sz+1))) (X3.GlobalValue "free_ptr")
  , X3.Movq (X3.Var s) (X3.Reg R11)
  , X3.Movq (X3.Num tag) (X3.Deref R11 0) ]
 where tag = mkTag ty
siStmt _ (C3.Assign s C3.Void) =
  [ X3.Movq (X3.Num 0) (X3.Var s) ]
siStmt _ (C3.Collect x) =
  [ X3.Movq (X3.Reg R15) (X3.Reg Rdi)
  , X3.Movq (X3.Num x) (X3.Reg Rsi)
  , X3.Callq "collect" ]
siStmt _ (C3.Assign s (C3.GlobalValue x)) =
  [ X3.Movq (X3.GlobalValue x) (X3.Var s) ]
siStmt _ (C3.Assign s (C3.FunRef f)) =
  [ X3.Leaq (X3.FunRef f) (X3.Var s) ]
siStmt params (C3.Assign s (C3.Call a as)) =
  moveParam params a ++
  concatMap (moveParam params) as ++
  zipWith (\arg reg -> X3.Movq (siArg arg) (X3.Reg reg))
    as
    paramRegs ++
  [ X3.IndirectCallq (siArg a)
  , X3.Movq (X3.Reg Rax) (X3.Var s) ]

mkTag :: C3.Type -> Int
mkTag ty = case ty of
  C3.TVector tys ->
    (shiftL (ptrMask tys) 7)
    .|. (shiftL (length tys) 1)
    .|. 1
  _ -> error $ "Trying to make tag of type " ++ show ty
 where ptrMask tys =
         foldr (\ty' acc ->
                  (shiftL acc 1)
                  .|. (case ty' of
                         C3.TVector _ -> 1
                         _ -> 0))
               zeroBits tys

moveParam :: [String] -> C3.Arg -> [X3.Instr]
moveParam params a@(C3.Var s) = case elemIndex s params of
  Just x ->
    let reg = paramRegs !! x
    in [X3.Movq (X3.Reg reg) (siArg a)]
  Nothing -> []
moveParam _ _ = []

siArg :: C3.Arg -> X3.Arg
siArg (C3.Num x) = X3.Num x
siArg (C3.Var s) = X3.Var s
siArg C3.T = X3.Num 1
siArg C3.F = X3.Num 0

siCompare :: C3.Compare -> X3.CC
siCompare C3.Eq = X3.CCEq
siCompare C3.Lt = X3.CCL

paramRegs :: [Register]
paramRegs = [Rdi, Rsi, Rdx, Rcx, R8, R9]

{----- Uncover Live -----}

printLiveSets :: [(String, X3.Block)] -> Map String [Set X3.Arg] -> String
printLiveSets ((lbl, X3.Block is) : bs) liveSets =
  let liveSets' = fromJust $ M.lookup lbl liveSets
  in "\n" ++ lbl ++ ":\n" ++ printLiveSets' is liveSets' ++ printLiveSets bs liveSets
printLiveSets [] _ = []

printLiveSets' :: [X3.Instr] -> [Set X3.Arg] -> String
printLiveSets' (i:is) (s:ss) =
  prettyPrint i ++ printSet (S.toList s) ++ printLiveSets' is ss
 where
   printSet :: [X3.Arg] -> String
   printSet args = "{" ++ unwords (map prettyPrint args) ++ "}\n"
printLiveSets' [] [] = []
printLiveSets' [] e = error $ "extra sets: " ++ show e
printLiveSets' e [] = error $ "extra instructions: " ++ show e


type LiveSets = [Set X3.Arg]

uncoverLive :: X3.Program () (Locals, CFG) -> X3.Program () (Locals, LiveSets)
uncoverLive (X3.Program () ds) = X3.Program () ds'
 where
  ds' = map ulDef ds

ulDef :: X3.Def (Locals, CFG) -> X3.Def (Locals, LiveSets)
ulDef (X3.Def s (locals, cfg) bs) = {-trace (printLiveSets bs liveAfter)-}
  X3.Def s (locals, liveSets) bs
 where
   liveSets = concatMap (\(l, _) -> fromJust $ M.lookup l liveAfter) bs
   liveAfter = liveAfterBlocks bs liveBefore
   liveBefore = liveBeforeBlocks bs cfg trav M.empty

   trav =
     map (\v -> fromJust $ M.lookup v v2s)
     . topSort . transposeG $ g

   (g, v2s, _) = mapSetToGraph cfg

liveAfterBlocks :: [(String, X3.Block)]
                -> Map String [Set X3.Arg] -- Live before sets
                -> Map String [Set X3.Arg]
liveAfterBlocks bs liveBeforeSets =
  M.fromList . (map (\(lbl, (X3.Block is)) ->
                    (lbl, mkLiveAfters liveBeforeSets is (fromJust . M.lookup lbl $ liveBeforeSets)))) $ bs

mkLiveAfters :: Map String [Set X3.Arg]
             -> [X3.Instr]
             -> [Set X3.Arg]
             -> [Set X3.Arg]
mkLiveAfters liveBefores ((X3.Jmp lbl):is) (_:ss) =
  if null is then [liveNextBlock]
  else S.union liveNextBlock (head ss) : mkLiveAfters liveBefores is ss
 where
   liveNextBlock =
     case M.lookup lbl liveBefores of
         Nothing -> S.empty
         Just lb -> head lb

mkLiveAfters liveBefores ((X3.TailJmp f):is) (_:ss) =
  if null is then [S.empty]
  else head ss : mkLiveAfters liveBefores is ss

mkLiveAfters liveBefores ((X3.JmpIf _ lbl):is) (_:ss) =
  if null is then [liveNextBlock]
  else S.union liveNextBlock (headNote "c" ss) : mkLiveAfters liveBefores is ss
 where
   liveNextBlock =
     case M.lookup lbl liveBefores of
         Nothing -> S.empty
         Just lb -> (headNote "d" lb)

mkLiveAfters liveBefores (_:is) (_:ss) = case ss of
  [] -> mkLiveAfters liveBefores is ss
  _ -> (headNote "e" ss) : mkLiveAfters liveBefores is ss
mkLiveAfters _ [] [] = []
mkLiveAfters _ _ _  = error "mkLiveAfters"

liveBeforeBlocks :: [(String, X3.Block)]
                 -> Map String (Set String)
                 -> [String]
                 -> Map String [Set X3.Arg]
                 -> Map String [Set X3.Arg]
liveBeforeBlocks  bs cfg (s:ss) m = case M.lookup s cfg of
  Nothing -> error $ s ++ " is not in CFG"
  Just succs ->
    if null succs then
      let (X3.Block is) = fromMaybe
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
          (X3.Block is) = fromJust $ lookup s bs
          m' = M.insert s (mkLiveBeforeSets is liveAfter) m
       in liveBeforeBlocks bs cfg ss m'
liveBeforeBlocks _ _ [] m = m

mkLiveBeforeSets :: [X3.Instr] -> Set X3.Arg -> [S.Set X3.Arg]
mkLiveBeforeSets is liveAfter = reverse $ mkSets liveAfter (reverse is)

mkSets :: S.Set X3.Arg -> [X3.Instr] -> [S.Set X3.Arg]
mkSets liveAfter (i:is) = liveBefore : mkSets liveBefore is
 where
   liveBefore =
     S.filter X3.isVar $ (liveAfter S.\\ w i) `S.union` r i

   w instr =
     case X3.writeArgs instr of
       Just s   -> s
       _        -> S.empty

   r instr =
     case X3.readArgs instr of
       Just s -> s
       _      -> S.empty

mkSets _ [] = []

{----- Build Interference -----}

type IGraph = Map X3.Arg (Set X3.Arg)

buildInterference :: X3.Program () (Locals, LiveSets)
                  -> X3.Program () (Locals, IGraph)
buildInterference (X3.Program () ds) = X3.Program () ds'
 where ds' = map biDef ds

biDef :: X3.Def (Locals, LiveSets)
      -> X3.Def (Locals, IGraph)
biDef (X3.Def name (locals, liveSets) bs) = X3.Def name (locals, iGraph) bs
 where
   iGraph = buildInterfere vectors liveSets insts
   insts = concatMap (\(_, X3.Block is) -> is) bs
   vectors =
     S.fromList
     . map X3.Var
     . M.keys
     . M.filter (\t -> case t of
                    C3.TVector _ -> True
                    _ -> False)
     $ locals

buildInterfere :: S.Set (X3.Arg)
               -> [S.Set X3.Arg]
               -> [X3.Instr]
               -> Map X3.Arg (Set X3.Arg)
buildInterfere vectors s i = execState (buildInterfere' vectors s i) M.empty

buildInterfere' :: S.Set X3.Arg
                -> [S.Set X3.Arg]
                -> [X3.Instr]
                -> State (Map X3.Arg (S.Set X3.Arg)) ()
buildInterfere' vectors (la:las) (i:is) =
  case i of
    (X3.Addq _ s@(X3.Var _)) -> do
      addEdges s . S.filter (/= s) $ la
      buildInterfere' vectors las is
    (X3.Subq _ s@(X3.Var _)) -> do
      addEdges s . S.filter (/= s) $ la
      buildInterfere' vectors las is
    (X3.Negq s@(X3.Var _))   -> do
      addEdges s . S.filter (/= s) $ la
      buildInterfere' vectors las is
    (X3.Xorq _ s@(X3.Var _)) -> do
      addEdges s . S.filter (/= s) $ la
      buildInterfere' vectors las is
    (X3.Cmpq _ s@(X3.Var _)) -> do
      addEdges s . S.filter (/= s) $ la
      buildInterfere' vectors las is
    (X3.Callq _)  -> do
      addRegisters callerSaved la
      addRegisters calleeSaved
        (S.filter (\x-> S.member x vectors) $ la)
      buildInterfere' vectors las is
    (X3.Movq s d@(X3.Var _)) -> do
      addEdges d . S.filter (\k -> k /= s && k /= d) $ la
      buildInterfere' vectors las is
    (X3.Movzbq s d@(X3.Var _)) -> do
      addEdges d . S.filter (\k -> k /= s && k /= d) $ la
      buildInterfere' vectors las is
    (X3.IndirectCallq _) -> do
      addRegisters callerSaved la
      addRegisters calleeSaved
        (S.filter (\x-> S.member x vectors) $ la)
      buildInterfere' vectors las is
    (X3.TailJmp _) -> do
      addRegisters callerSaved la
      addRegisters calleeSaved
        (S.filter (\x-> S.member x vectors) $ la)
      buildInterfere' vectors las is
    (X3.Leaq s d@(X3.Var _)) -> do
      addEdges d . S.filter (\k -> k /= s && k /= d) $ la
      buildInterfere' vectors las is
    _             -> buildInterfere' vectors las is

 where
  addEdges
    :: X3.Arg
    -> S.Set X3.Arg -> State (M.Map X3.Arg (S.Set X3.Arg)) ()
  addEdges s la' = do
    modify $ M.insertWith S.union s la'
    mapM_ (addEdge s) la'

  addEdge :: X3.Arg -> X3.Arg -> State (M.Map X3.Arg (S.Set X3.Arg)) ()
  addEdge a1 a2 = do
    modify $ M.insertWith S.union a2 (S.singleton a1)
    return ()

  addRegisters regs la' = do
    let rs = S.map X3.Reg (S.fromList regs)
    mapM_ (`addEdges` rs) la'

buildInterfere' _ [] [] = return ()
buildInterfere' _ _ _ = error "buildInterfere: Mismatch between args and live after sets"

{----- Allocate Registers -----}

type LocMap = Map String X3.StoreLoc

allocateRegisters :: X3.Program () (Locals, IGraph) -> X3.Program () LocMap
allocateRegisters (X3.Program () ds) = X3.Program () ds'
 where
  ds' = map arDef ds

arDef :: X3.Def (Locals, IGraph) -> X3.Def LocMap
arDef (X3.Def s (locals, iGraph) bs) = {-trace ("ar locals: " ++ show locals) -} X3.Def s locMap bs
 where
  locMap = colorGraph locals iGraph

colorGraph :: Locals
           -> Map X3.Arg (Set X3.Arg)
           -> Map String X3.StoreLoc
colorGraph locals iList =
  M.fromList
  . mapMaybe
      (\(v, c) -> case lookup v vertexAssoc of
          Just (X3.Reg _) -> Nothing
          Just var@(X3.Var s) -> Just (s, storeLocFromColor vectors var c)
          Nothing         -> Nothing
          _               -> error $ "Found " ++ show v ++ "in vertexAssoc")
  . M.toList
  $ coloring
 where

  vectors =
    S.fromList
    . map (\s -> X3.Var s)
    . M.keys
    . M.filter (\t -> case t of
                   C3.TVector _ -> True
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
            (X3.Reg r) -> case colorFromReg r of
              Nothing -> Nothing
              Just n  -> Just (v, n)
            _ -> error $ "colorGraph: Don't expect " ++ show a ++
                 " in the regVerts list.")
    $ regVerts

  varVerts = vertexAssoc \\ regVerts

  regVerts :: [(Vertex, X3.Arg)]
  regVerts = filter (\(_, a) -> X3.isReg a) vertexAssoc

  vertexAssoc = M.toList vertexMap

  (g, vertexMap, _) = mapSetToGraph iList

regsToUse :: [Register]
regsToUse = take 3 . tail $ callerSaved

regIntAssoc :: [(Int, Register)]
regIntAssoc = zip [0..] regsToUse

storeLocFromColor :: Set X3.Arg -> X3.Arg -> Int -> X3.StoreLoc
storeLocFromColor vectors var n = case lookup n regIntAssoc of
  Just r -> X3.RegLoc r
  Nothing ->
    if S.member var vectors
    then X3.RootStack $ 8 * (n - length regIntAssoc + 1)
    else X3.Stack $ negate $ 8 * (n - length regIntAssoc)

colorFromReg :: Register -> Maybe Int
colorFromReg r = lookup r (map swap regIntAssoc)

{----- Assign Homes -----}

type StackSize = Int
type RootStackSize = Int

assignHomes :: X3.Program () LocMap
            -> X3.Program () (StackSize, RootStackSize)
assignHomes (X3.Program () ds) = X3.Program () ds'
 where ds' = map ahDef ds

ahDef :: X3.Def LocMap -> X3.Def (StackSize, RootStackSize)
ahDef (X3.Def s locMap bs) = {- trace ("\nah locmap: " ++ show locMap) -}
  X3.Def s (frameSize locMap) bs'
 where
  bs' = map (\(l, b) -> (l, ahBlock locMap b)) bs

ahBlock :: M.Map String X3.StoreLoc -> X3.Block -> X3.Block
ahBlock m (X3.Block instrs) =
  X3.Block (map (ahInstr m) instrs)

ahInstr :: M.Map String X3.StoreLoc -> X3.Instr -> X3.Instr
ahInstr m (X3.Addq aL aR)   = X3.Addq (ahArg m aL) (ahArg m aR)
ahInstr m (X3.Subq aL aR)   = X3.Subq (ahArg m aL) (ahArg m aR)
ahInstr m (X3.Movq aL aR)   = X3.Movq (ahArg m aL) (ahArg m aR)
ahInstr m (X3.Movzbq aL aR) = X3.Movzbq (ahArg m aL) (ahArg m aR)
ahInstr _ X3.Retq           = X3.Retq
ahInstr m (X3.Negq a)       = X3.Negq (ahArg m a)
ahInstr _ i@(X3.Callq _)    = i
ahInstr _ i@(X3.Jmp _)      = i
ahInstr _ i@(X3.Pushq _)    = i
ahInstr m (X3.Xorq aL aR)   = X3.Xorq (ahArg m aL) (ahArg m aR)
ahInstr m (X3.Cmpq aL aR)   = X3.Cmpq (ahArg m aL) (ahArg m aR)
ahInstr m (X3.Set cc a)     = X3.Set cc (ahArg m a)
ahInstr _ i@(X3.JmpIf _ _)  = i
ahInstr _ i@(X3.Label _)    = i
ahInstr _ i@(X3.Popq _)     = i
ahInstr m (X3.IndirectCallq a) = X3.IndirectCallq (ahArg m a)
ahInstr m (X3.TailJmp a) = X3.TailJmp (ahArg m a)
ahInstr m (X3.Leaq al ar) = X3.Leaq (ahArg m al) (ahArg m ar)

ahArg :: M.Map String X3.StoreLoc -> X3.Arg -> X3.Arg
ahArg _ a@(X3.Num _) = a
ahArg m (X3.Var s) = case M.lookup s m of
  Nothing -> error $ "Assign homes: Variable " ++ s ++ " not found in map."
  Just (X3.RegLoc r) -> X3.Reg r
  Just (X3.Stack n)  -> X3.Deref Rbp n
  Just (X3.RootStack n) -> X3.Deref R15 (negate n)
ahArg _ a@(X3.Reg _) = a
ahArg _ a@(X3.Deref _ _) = a
ahArg _ a@(X3.ByteReg _) = a
ahArg _ a@(X3.GlobalValue _) = a
ahArg _ a@(X3.FunRef s) = a

frameSize :: M.Map String X3.StoreLoc -> (StackSize, RootStackSize)
frameSize locMap = (stackBytes, rootBytes)
 where
  rootBytes = foldr (\n acc -> if n > acc then n else acc) 0
            . mapMaybe (\x -> case x of
                         (X3.RootStack n) -> Just n
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
                           (X3.Stack n) -> Just n
                           _            -> Nothing)
              . M.elems
              $ locMap

{----- Patch Instructions -----}

patchInstructions :: X3.Program () (StackSize, RootStackSize)
                  -> X3.Program () ()
patchInstructions (X3.Program () ds) = X3.Program () ds'
 where ds' = map piDef ds

piDef :: X3.Def (StackSize, RootStackSize) -> X3.Def ()
piDef (X3.Def s (sSize, rsSize) ((fName, bl):bs)) = X3.Def s () bs'
 where
  bs' = intro fName sSize rsSize
      : start
      : conclusion fName sSize rsSize
      : map (\(l, b) -> (l, pBlock sSize rsSize b)) bs
  start = (fName++"start", pBlock sSize rsSize bl)
piDef _ = undefined

intro :: String -> StackSize -> RootStackSize -> (String, X3.Block)
intro fName sSize rsSize = ( fName++"intro",
  X3.Block (
    [ X3.Pushq (X3.Reg Rbp)
    , X3.Movq (X3.Reg Rsp) (X3.Reg Rbp)
    , X3.Pushq (X3.Reg R12)
    , X3.Pushq (X3.Reg Rbx)
    , X3.Pushq (X3.Reg R13)
    , X3.Pushq (X3.Reg R14)
    , X3.Subq (X3.Num sSize) (X3.Reg Rsp) ] ++ initRootStack ++
    [ X3.Jmp (fName++"start")]))
 where
  initRootStack = case fName of
    "main" ->
      [ X3.Movq (X3.Num 16384) (X3.Reg Rdi)
      , X3.Movq (X3.Num (rsSize+8)) (X3.Reg Rsi)
      , X3.Callq "initialize"
      , X3.Movq (X3.GlobalValue "rootstack_begin") (X3.Reg R15) ] ++
      clearRootStack rsSize
    _ -> []
  clearRootStack n
    | n == 0 = []
    | n < 0 = error "Invalid root stack size"
    | otherwise =
        X3.Movq (X3.Num 0) (X3.Deref R15 0)
        : X3.Addq (X3.Num 8) (X3.Reg R15)
        : clearRootStack (n-8)


conclusion :: String -> StackSize -> RootStackSize -> (String, X3.Block)
conclusion fName sSize rsSize  =
    ( fName++"conclusion", X3.Block
    ( popFrame sSize rsSize ++
      [ X3.Retq ] ))

popFrame :: StackSize -> RootStackSize -> [X3.Instr]
popFrame sSize rsSize =
      [ X3.Subq (X3.Num rsSize) (X3.Reg R15)
      , X3.Addq (X3.Num sSize) (X3.Reg Rsp)
      , X3.Popq (X3.Reg R14)
      , X3.Popq (X3.Reg R13)
      , X3.Popq (X3.Reg Rbx)
      , X3.Popq (X3.Reg R12)
      , X3.Popq (X3.Reg Rbp) ]


pBlock :: StackSize -> RootStackSize -> X3.Block -> X3.Block
pBlock sSize rsSize (X3.Block instrs) =
  X3.Block (concatMap (pInstrs sSize rsSize) instrs)

pInstrs :: StackSize -> RootStackSize -> X3.Instr -> [X3.Instr]
pInstrs _ _ (X3.Movq (X3.Deref regL offL) (X3.Deref regR offR)) =
  [ X3.Movq (X3.Deref regL offL) (X3.Reg Rax)
  , X3.Movq (X3.Reg Rax) (X3.Deref regR offR) ]
pInstrs _ _ (X3.Addq (X3.Deref regL offL) (X3.Deref regR offR)) =
  [ X3.Movq (X3.Deref regL offL) (X3.Reg Rax)
  , X3.Addq (X3.Reg Rax) (X3.Deref regR offR) ]
pInstrs _ _ (X3.Subq (X3.Deref regL offL) (X3.Deref regR offR)) =
  [ X3.Movq (X3.Deref regL offL) (X3.Reg Rax)
  , X3.Subq (X3.Reg Rax) (X3.Deref regR offR) ]
pInstrs _ _(X3.Xorq (X3.Deref regL offL) (X3.Deref regR offR)) =
  [ X3.Movq (X3.Deref regL offL) (X3.Reg Rax)
  , X3.Xorq (X3.Reg Rax) (X3.Deref regR offR) ]
pInstrs _ _(X3.Cmpq l@(X3.Deref _ _) r@(X3.Deref _ _)) =
  [ X3.Movq l (X3.Reg Rax)
  , X3.Cmpq (X3.Reg Rax) r ]
pInstrs _ _(X3.Cmpq l r@(X3.Num _)) =
  [ X3.Movq r (X3.Reg Rax)
  , X3.Cmpq l (X3.Reg Rax) ]
pInstrs _ _(X3.Movzbq l d@(X3.Deref _ _)) =
  [ X3.Movzbq l (X3.Reg Rax)
  , X3.Movq (X3.Reg Rax) d ]
pInstrs _ _ i@(X3.Leaq _ (X3.Reg _)) = [i] -- Right argument must be a reg
pInstrs sSize rsSize (X3.Leaq l r) =
  concatMap (pInstrs sSize rsSize) $ [ X3.Leaq l (X3.Reg Rax)
                                     , X3.Movq (X3.Reg Rax) r ]
pInstrs _ _ i@(X3.TailJmp (X3.Reg Rax)) = [i]
pInstrs sSize rsSize (X3.TailJmp a) =
  concatMap (pInstrs sSize rsSize) [ X3.Movq a (X3.Reg Rax) ] ++
  popFrame sSize rsSize ++
  [ X3.TailJmp (X3.Reg Rax) ]
pInstrs _ _ i@(X3.Movq a1 a2) = [i | a1 /= a2]
pInstrs _ _ i = [i]

-- End --

testExpr = "(define (nthfib [ct : Integer]) : Integer (nthfibp ct 0 1)) (define (nthfibp [ct : Integer] [n-2 : Integer] [n-1 : Integer]) : Integer (if (cmp eq? ct 0) n-2 (nthfibp (- ct 1) n-1 (+ n-2 n-1)))) (nthfib 8)"

testExpr2 = "(define (simpleRec [x : Integer]) : Integer (if (cmp eq? x 0) 0 (simpleRec (- x 1)))) (simpleRec 2)"

--(define (simpleRec [x : Integer]) : Integer (if (cmp eq? x 0) 0 (simpleRec (- x 1))))
--(simpleRec 2)
testIt e =
  let p = R4.parseError e
  in compile p

testCompile e = compileToFile R4.parse compile e "./testComp"
