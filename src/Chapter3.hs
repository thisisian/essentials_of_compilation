module Chapter3 where

import qualified PsuedoX860 as PX
import qualified X860 as X
import Data.Set ((\\), union)
import qualified Data.Set as S
import qualified Data.Map as M
import Chapter2 ( patchInstructions, selectInstructions
                , uncoverLocals, explicateControl
                , rco, uniquify )
import Data.Graph
import Data.Maybe
import Data.Tuple
import Color
import qualified R1
import Common
import Debug.Trace

compile :: R1.Program -> String
compile =
  prettyPrint
  . patchInstructions
  . allocateRegisters
  . buildInterference
  . uncoverLive
  . selectInstructions
  . uncoverLocals
  . explicateControl
  . rco
  . uniquify

{- Uncover Locals -}


uncoverLive :: PX.Program -> PX.Program
uncoverLive (PX.Program i bs) =
  (PX.Program i (map (\(l, b) -> (l, uLBlock b)) bs))

uLBlock :: PX.Block -> PX.Block
uLBlock (PX.Block _ is) = (PX.Block info is)
 where
   info = PX.emptyBInfo { PX.bInfoLiveAfterSets = mkLiveAfterSets is}

mkLiveAfterSets :: [PX.Instr] -> [S.Set PX.Arg]
mkLiveAfterSets is = reverse $ mkSets S.empty (reverse is)

mkSets :: S.Set PX.Arg -> [PX.Instr] -> [S.Set PX.Arg]
mkSets set (i:is) = trace
  ("\nInstr: " ++ show i ++
   "\nset: " ++ show set ++
   "\nr: " ++ (show (r i)) ++
   "\nw: " ++ show (w i) ++
   "\nset': " ++ show set' )
  (set : (mkSets set' is))
 where
   set' =
     S.filter (PX.isVar) $ (set \\ w i) `union` r i

   w instr =
     case PX.writeArgs instr of
       Just s   -> s
       _        -> S.empty

   r instr =
     case PX.readArgs instr of
       Just s -> s
       _      -> S.empty

mkSets _ [] = []

{- Build Interference Graph -}

buildInterference :: PX.Program -> PX.Program
buildInterference (PX.Program i bs') = (PX.Program i bs)
 where bs = map (\(l, b) -> (l, bIBlock b)) bs'

bIBlock :: PX.Block -> PX.Block
bIBlock (PX.Block i' is) = (PX.Block i is)
 where
  i =
    i' { PX.bInfoConflicts =
           bIInterfere (PX.bInfoLiveAfterSets i) is M.empty }

bIInterfere
  :: [S.Set PX.Arg]
  -> [PX.Instr]
  -> M.Map PX.Arg (S.Set PX.Arg)
  -> M.Map PX.Arg (S.Set PX.Arg)
bIInterfere (la:las) (i:is) imap =
  if PX.isArithOp i
  then case PX.writeArg i of
    Just var@(PX.Var _) ->
      let
        imapNew = M.unionWith S.union imap (mkEdges var (S.delete var la))
      in bIInterfere las is imapNew
    _ -> bIInterfere las is imap
  else case i of
    (PX.Callq _) ->
      let
        regMaps =
          map (\r -> mkEdges (PX.Reg r) la) (S.toList PX.callerSaved)
        imapNew = M.unionsWith S.union (imap : regMaps)
      in bIInterfere las is imapNew
    (PX.Movq v1@(PX.Var _) v2@(PX.Var _)) ->
      let laRemoved = (S.delete v1 (S.delete v2 la))
      in M.unionsWith S.union $
        [imap, mkEdges v1 (laRemoved), (mkEdges v2 (laRemoved))]
    _ -> bIInterfere las is imap
bIInterfere [] [] imap = imap
bIInterfere _ _ _ = error "Live sets and Instructions don't match"

mkEdges :: (Ord a) => a -> S.Set a -> M.Map a (S.Set a)
mkEdges a as =
  M.unionWith S.union (M.singleton a as) (M.fromSet (\_ -> S.singleton a) as)

{- Allocate Registers -}
allocateRegisters :: PX.Program -> X.Program
allocateRegisters (PX.Program _ bs) = (X.Program info bs')
 where
  bs' = map (\(l, b) -> (l, alBlock b)) bs
  info = X.PInfo 1600 -- TODO

alBlock :: PX.Block -> X.Block
alBlock (PX.Block i is) =
  let storeLocs = colorGraph . PX.bInfoConflicts $ i
  in X.Block X.BInfo (map (alInstr storeLocs) is)

alInstr :: M.Map String StoreLoc -> PX.Instr -> X.Instr
alInstr m (PX.Addq aL aR) = (X.Addq (alArg m aL) (alArg m aR))
alInstr m (PX.Movq aL aR) = (X.Movq (alArg m aL) (alArg m aR))
alInstr m (PX.Subq aL aR) = (X.Subq (alArg m aL) (alArg m aR))
alInstr m (PX.Negq a)     = (X.Negq (alArg m a))
alInstr _ (PX.Retq)       = X.Retq
alInstr _ (PX.Callq s)    = X.Callq s
alInstr _ (PX.Jmp s)      = X.Jmp s

alArg :: M.Map String StoreLoc -> PX.Arg -> X.Arg
alArg m (PX.Var s) = case M.lookup s m of
  Nothing -> (X.Reg (X.Rcx)) -- Wha should it map to?
  Just (Reg r) -> (X.Reg (PX.toX860 r))
  Just (Stack n) -> (X.Deref X.Rbp n)
alArg _ (PX.Num x) = (X.Num x)
alArg _ (PX.Deref r x) = (X.Deref (PX.toX860 r) x)
alArg _ (PX.Reg r) = (X.Reg (PX.toX860 r))

data StoreLoc = Reg PX.Register | Stack Int

colorGraph :: (M.Map PX.Arg (S.Set PX.Arg)) -> (M.Map String StoreLoc)
colorGraph g' =
  M.fromList
  . mapMaybe
      (\(v,c) -> case nodeFromVertex v of
          (_, (PX.Var s), _) -> Just (s, storeLocFromColor c)
          _                  -> Nothing )
  . M.toList
  $ coloring

 where
  (g, nodeFromVertex, _) = toGraph g'
  regVerts :: [(Vertex, PX.Register)]
  regVerts = regVerts' $ vertices g
   where
    regVerts' (v:vs) =
      case nodeFromVertex v of
        (_, (PX.Reg r), _) -> (v, r) : regVerts' vs
        (_, _, _)          -> regVerts' vs
    regVerts' [] = []
  toColor = (S.fromList $ vertices g) \\ (S.fromList (map fst regVerts))
  alreadyColored :: (M.Map Vertex Color)
  alreadyColored =
    let
      t :: [(Vertex, Color)]
      t = map (\(v,r) -> (v, fromJust $ keyFromReg r)) regVerts
    in M.fromList $ t
  coloring :: M.Map Vertex Color
  coloring = color g toColor alreadyColored

toGraph
  :: M.Map PX.Arg (S.Set PX.Arg)
  -> (Graph, Vertex -> ((), PX.Arg, [PX.Arg]), PX.Arg -> Maybe Vertex)
toGraph conflicts = graphFromEdges $
  map (\(k, ks) -> ((), k, ks)) . M.toList . M.map (S.toList) $ conflicts

regIntAssoc :: [(Int, PX.Register)]
regIntAssoc = [ (0, PX.Rdx)
              , (1, PX.Rcx)
              , (2, PX.Rsi)
              , (3, PX.Rdi)
              , (4, PX.R8)
              , (5, PX.R9)
              , (6, PX.R10)
              , (7, PX.R11) ]

storeLocFromColor :: Int -> StoreLoc
storeLocFromColor n = case lookup n regIntAssoc of
  Just r -> Reg r
  Nothing -> Stack $ 8 * (negate (n - (length regIntAssoc)))

keyFromReg :: PX.Register -> Maybe Int
keyFromReg r = lookup r (map swap regIntAssoc)

exampleProblem :: IO ()
exampleProblem = do
  let after_UncoverLive = uncoverLive after_instr_selection
  putStrLn ( show $ after_UncoverLive)
  pure ()


exampleProgram :: String
exampleProgram = "(let ([v 1]) (let ([w 46]) (let ([x (+ v 7)]) (let ([y (+ 4 x)]) (let ([z (+ x w)]) (+ z (- y)))))))"

-- (let ([v 1])
-- (let ([w 46])
-- (let ([x (+ v 7)])
-- (let ([y (+ 4 x)])
-- (let ([z (+ x w)])
-- (+ z (- y)))))))

-- (let ([v 1])
-- (let ([w 46])
-- (let ([_temp0 (+ v 7)])
-- (let ([x _temp0])
-- (let ([_temp1 (+ 4 x)])
-- (let ([y _temp1])
-- (let ([_temp2 (+ x w)])
-- (let ([z _temp2])
-- (let ([_temp3 (- y)])
--       (+ z _temp3))))))))))

--  ,fromList ["v"]
--  ,fromList ["v","w"]
--  ,fromList ["w"]
--  ,fromList ["w","x"]
--  ,fromList ["w","x"]
--  ,fromList ["w","x","y"]
--  ,fromList ["w","y"]  -- WRONG
--  ,fromList ["y","z"]
--  ,fromList ["t.1","z"]
--  ,fromList ["t.1","z"]
--  ,fromList ["t.1"]
--  ,fromList []
--  ,fromList []

--fromList [Var "v"]
--fromList [Var "v",Var "w"]
--fromList [Var "w",Var "x"]
--fromList [Var "w",Var "x"]
--fromList [Var "w",Var "x",Var "y"]
--fromList [Var "w",Var "x",Var "y"]
--fromList [Var "w",Var "y",Var "z"]
--fromList [Var "y",Var "z"]
--fromList [Var "t.1",Var "z"]
--fromList [Var "t.1",Var "z"]
--fromList [Var "t.1"]
--fromList []
--fromList []



after_instr_selection =
  (PX.Program
    (PX.PInfo {PX.pInfoLocals = ["v","w","x","y","z","t.1"]})
    [("start",PX.Block (PX.BInfo {PX.bInfoLiveAfterSets = [], PX.bInfoConflicts = M.fromList []})
  [PX.Movq (PX.Num 1) (PX.Var "v")        --
  ,PX.Movq (PX.Num 46) (PX.Var "w")       --
  ,PX.Movq (PX.Var "v") (PX.Var "x")      --
  ,PX.Addq (PX.Num 7) (PX.Var "x")        --
  ,PX.Movq (PX.Var "x") (PX.Var "y")      --
  ,PX.Addq (PX.Num 4) (PX.Var "y")        --
  ,PX.Movq (PX.Var "x") (PX.Var "z")      --
  ,PX.Addq (PX.Var "w") (PX.Var "z")      --
  ,PX.Movq (PX.Var "y") (PX.Var "t.1")    --
  ,PX.Negq (PX.Var "t.1")                 --
  ,PX.Movq (PX.Var "z") (PX.Reg PX.Rax)   --
  ,PX.Addq (PX.Var "t.1") (PX.Reg PX.Rax) --
  ,PX.Jmp "conclusion"])])                --
