module Chapter4 where

import qualified R2

import Control.Monad
import Data.Map (Map)
import qualified Data.Map as M

import Common

{----- Shrink -----}

shrink :: R2.Program -> R2.Program
shrink (R2.Program i e) = (R2.Program i (shrinkExpr e))

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
shrinkExpr (R2.Cmp R2.Leq eL eR) =
  (R2.Not (R2.Cmp R2.Lt (shrinkExpr eR) (shrinkExpr eL)))
shrinkExpr (R2.Cmp R2.Gt eL eR) =
  (R2.Cmp R2.Lt (shrinkExpr eR) (shrinkExpr eL))
shrinkExpr (R2.Cmp R2.Geq eL eR) =
  (R2.Not (R2.Cmp R2.Lt (shrinkExpr eL) (shrinkExpr eR)))
shrinkExpr (R2.If cond eT eF) =
  (R2.If (shrinkExpr cond) (shrinkExpr eT) (shrinkExpr eF))

{----- Uniquify -----}

type SymbolTable = Map String String

uniquify :: R2.Program -> R2.Program
uniquify (R2.Program i e) = R2.Program i $
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
rco (R2.Program i e) = R2.Program i $ runFreshEnv "_rco" (rcoExpr e)

rcoExpr :: R2.Expr -> FreshEnv R2.Expr
rcoExpr (R2.Num x) = return $ R2.Num x
rcoExpr R2.Read = return R2.Read
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
  (bindingsCond, cond') <- rcoArg cond
  (bindingsT, eT') <- rcoArg eT
  (bindingsF, eF') <- rcoArg eF
  return $ makeBindings (bindingsCond++bindingsT++bindingsF) (R2.If cond' eT' eF')


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
  return (bindings, (R2.Not e'))
rcoArg (R2.Cmp cmp eL eR)
  | cmp == R2.Eq || cmp == R2.Lt = do
      (bindingsL, eL') <- rcoArg eL
      (bindingsR, eR') <- rcoArg eR
      return $ (bindingsL++bindingsR , R2.Cmp cmp eL' eR')
  | otherwise = error $ "Found " ++ show cmp ++ "in RCO step."
rcoArg (R2.If cond eT eF) = do
  (bindingsCond, cond') <- rcoArg cond
  (bindingsT, eT') <- rcoArg eT
  (bindingsF, eF') <- rcoArg eF
  return $ (bindingsCond++bindingsT++bindingsF, R2.If cond' eT' eF')


makeBindings :: [(String, R2.Expr)] -> R2.Expr -> R2.Expr
makeBindings ((b, be):bs) e =
  R2.Let b be (makeBindings bs e)
makeBindings [] e = e
