module Chapter4 where

import qualified R2


{----- Shrink -----}

--shrink :: R2.Program -> R2.Program
--shrink (Program i e) = (Program i (shrinkExpr e))

-- Subtract, and, or, <=, >, >=
--shrinkExpr (R1.Num x) = R1.Num x
--shrinkExpr (R1.Neg e) = (R1.Neg (shrinkExpr e))
--shrinkExpr (R1.Add eL eR) = (R1.Add (shrinkExpr eL) (shrinkExpr eR))
--shrinkExpr (R1.Sub eL eR) = (R1.Add (shrinkExpr eL) (R1.Neg (shrinkExpr eR)))
--shrinkExpr (R1.Var s) = R1.Var s
--shrinkExpr (R1.Let s eB e) = (R1.Let s (shrinkExpr eB) (shrinkExpr e))
--shrinkExpr R1.T = T
--shrinkExpr R1.F = F
---- Simplify with if, I guess?
--shrinkExpr (R1.And eL eR) = (R1.If (shrinkExpr eL) (shinkExpr eR) R1.F)
--shrinkExpr (R1.Or eL eR) = (R1.If (shrinkExpr eL) R1.T (shrinkExpr eR))
--shrinkExpr (R1.Not e) = (R1.Not (shrinkExpr e))
--shrinkExpr (R1.Cmp R1.Eq eL eR) =
--  (R1.Let (
--shrinkExpr (R1.Cmp R1.Lt eL eR) = undefined
--shrinkExpr (R1.Cmp R1.Leq eL eR) = undefined
--shrinkExpr (R1.Cmp R1.Gt eL eR) = undefined
--shrinkExpr (R1.Cmp R1.Geq eL eR) = undefined
--shrinkExpr (R1.If cond eT eF) =
--  (R1.If (shrinkExpr cond) (shrinkExpr eT) (shrinkExpr eF))
