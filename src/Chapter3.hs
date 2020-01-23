module Chapter3 where

import qualified PsuedoX860 as PX
import qualified X860 as X
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
import Data.List
import Common
import Debug.Trace
import Control.Monad.State.Strict

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
mkSets set (i:is) = set : (mkSets set' is)
 where
   set' =
     S.filter (PX.isVar) $ (set S.\\ w i) `S.union` r i

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
           buildInterfere (PX.bInfoLiveAfterSets i) is }

buildInterfere
  :: [S.Set PX.Arg]
  -> [PX.Instr]
  -> M.Map PX.Arg (S.Set PX.Arg)
buildInterfere s i = execState (buildInterfere' s i) M.empty

buildInterfere'
  :: [S.Set PX.Arg]
  -> [PX.Instr]
  -> State (M.Map PX.Arg (S.Set PX.Arg)) ()
buildInterfere' (la:las) (i:is) =
  case i of
    (PX.Addq _ s@(PX.Var _)) -> do
      addEdges s . S.filter (/= s) $ la
      buildInterfere' las is
    (PX.Subq _ s@(PX.Var _)) -> do
      addEdges s . S.filter (/= s) $ la
      buildInterfere' las is
    (PX.Negq s@(PX.Var _))   -> do
      addEdges s . S.filter (/= s) $ la
      buildInterfere' las is
    (PX.Callq _)  -> do
      addRegisters la
      buildInterfere' las is
    (PX.Movq s d@(PX.Var _)) -> do
      addEdges d . S.filter (\k -> k /= s && k /= d) $ la
      buildInterfere' las is
    _             -> buildInterfere' las is

 where
  addEdges
    :: PX.Arg
    -> S.Set PX.Arg -> State (M.Map PX.Arg (S.Set PX.Arg)) ()
  addEdges s la' = do
    modify $ M.insertWith (S.union) s la'
    mapM_ (addEdge s) la'
    return ()

  addEdge :: PX.Arg -> PX.Arg -> State (M.Map PX.Arg (S.Set PX.Arg)) ()
  addEdge a1 a2 = do
    modify $ M.insertWith (S.union) a2 (S.singleton a1)
    return ()

  addRegisters la' = do
    let rs = S.map PX.Reg PX.callerSaved
    mapM_ (\s -> addEdges s rs) la'

buildInterfere' [] [] = return ()
buildInterfere' _ _ = error "buildInterfere: Mismatch between args and live after sets"





-- Jeez, just compare to the pure functional version:
--bIInterfere
--  :: [S.Set PX.Arg]
--  -> [PX.Instr]
--  -> M.Map PX.Arg (S.Set PX.Arg)
--  -> M.Map PX.Arg (S.Set PX.Arg)
--bIInterfere (la:las) (i:is) imap =
--  if PX.isArithOp i
--  then case PX.writeArg i of
--    Just var@(PX.Var _) ->
--      let
--        imapNew = M.unionWith S.union imap (mkEdges var (S.delete var la))
--      in bIInterfere las is imapNew
--    _ -> bIInterfere las is imap
--  else case i of
--    (PX.Callq _) ->
--      let
--        regMaps =
--          map (\r -> mkEdges (PX.Reg r) la) (S.toList PX.callerSaved)
--        imapNew = M.unionsWith S.union (imap : regMaps)
--      in bIInterfere las is imapNew
--    (PX.Movq v1@(PX.Var _) v2@(PX.Var _)) ->
--      let laRemoved = (S.delete v1 (S.delete v2 la))
--      in M.unionsWith S.union $
--        [imap, mkEdges v1 (laRemoved), (mkEdges v2 (laRemoved))]
--    _ -> bIInterfere las is imap
--bIInterfere [] [] imap = imap
--bIInterfere _ _ _ = error "Live sets and Instructions don't match"

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
  in {-trace ("\n"++show storeLocs++"\n")-} (X.Block X.BInfo (map (alInstr storeLocs) is))

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
  Just (Reg r) -> (X.Reg (PX.toX860Reg r))
  Just (Stack n) -> (X.Deref X.Rbp n)
alArg _ (PX.Num x) = (X.Num x)
alArg _ (PX.Deref r x) = (X.Deref (PX.toX860Reg r) x)
alArg _ (PX.Reg r) = (X.Reg (PX.toX860Reg r))

data StoreLoc = Reg PX.Register | Stack Int
  deriving (Show)

colorGraph :: (M.Map PX.Arg (S.Set PX.Arg)) -> (M.Map String StoreLoc)
colorGraph g =
  let
    (g', nodeFromVertex, _) = toGraph g
    vertexAssoc =
      map (\v -> let (_, a, _) = nodeFromVertex v in (v, a))
      . vertices
      $ g'
    regVerts :: [(Vertex, PX.Arg)]
    regVerts = filter (\(_, a) -> PX.isReg a) vertexAssoc
    varVerts = (vertexAssoc \\ regVerts)
    needColors :: S.Set Vertex
    needColors = S.fromList . map fst $ varVerts
    alreadyColored :: (M.Map Vertex Color)
    alreadyColored =
      M.fromList
      . map (\(v, (PX.Reg a)) -> (v, fromJust . colorFromReg $ a))
      $ regVerts
    coloring :: M.Map Vertex Color
    coloring = color g' needColors alreadyColored
  in {-trace ("\nvarVets: " ++ show varVerts) -}
    M.fromList
    . mapMaybe
        (\(v, c) -> case lookup v vertexAssoc of
            Just (PX.Reg r) -> Nothing
            Just (PX.Var s) -> Just (s, storeLocFromColor c)
            Nothing         -> Nothing)
    . M.toList
    $ coloring

toGraph
  :: M.Map PX.Arg (S.Set PX.Arg)
  -> (Graph, Vertex -> ((), PX.Arg, [PX.Arg]), PX.Arg -> Maybe Vertex)
toGraph conflicts = graphFromEdges .
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

colorFromReg :: PX.Register -> Maybe Int
colorFromReg r = lookup r (map swap regIntAssoc)

exampleProblem :: IO ()
exampleProblem = do
  let after_UncoverLive = allocateRegisters . buildInterference . uncoverLive $ after_instr_selection
  putStrLn $ prettyPrint after_UncoverLive


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
