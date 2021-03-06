module Chapter3 where

import qualified PsuedoX860 as PX
import qualified X860 as X
import Data.Set (Set)
import qualified Data.Set as S
import Data.Map (Map)
import qualified Data.Map as M
import qualified Chapter2 as Ch2
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
import Control.Monad.State.Strict

compile :: R1.Program -> String
compile =
  prettyPrint
  . patchInstructions
  . allocateRegisters
  . buildMoveBias
  . buildInterference
  . uncoverLive
  . selectInstructions
  . uncoverLocals
  . explicateControl
  . rco
  . uniquify

{- Uncover Live -}


uncoverLive :: PX.Program -> PX.Program
uncoverLive (PX.Program i bs) =
  PX.Program i (map (\(l, b) -> (l, uLBlock b)) bs)

uLBlock :: PX.Block -> PX.Block
uLBlock (PX.Block _ is) = PX.Block info is
 where
   info = PX.emptyBInfo { PX.bInfoLiveAfterSets = mkLiveAfterSets is}

mkLiveAfterSets :: [PX.Instr] -> [S.Set PX.Arg]
mkLiveAfterSets is = reverse $ mkSets S.empty (reverse is)

mkSets :: S.Set PX.Arg -> [PX.Instr] -> [S.Set PX.Arg]
mkSets set (i:is) = set : mkSets set' is
 where
   set' =
     S.filter PX.isVar $ (set S.\\ w i) `S.union` r i

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
buildInterference (PX.Program i bs) = PX.Program i bs'
 where bs' = map (\(l, b) -> (l, bIBlock b)) bs

bIBlock :: PX.Block -> PX.Block
bIBlock (PX.Block i is) = PX.Block i' is
 where
  i' =
    i { PX.bInfoConflicts =
           buildInterfere (PX.bInfoLiveAfterSets i) is }

buildInterfere
  :: [S.Set PX.Arg]
  -> [PX.Instr]
  -> Map PX.Arg (Set PX.Arg)
buildInterfere s i = execState (buildInterfere' s i) M.empty

buildInterfere'
  :: [S.Set PX.Arg]
  -> [PX.Instr]
  -> State (Map PX.Arg (S.Set PX.Arg)) ()
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
    modify $ M.insertWith S.union s la'
    mapM_ (addEdge s) la'

  addEdge :: PX.Arg -> PX.Arg -> State (M.Map PX.Arg (S.Set PX.Arg)) ()
  addEdge a1 a2 = do
    modify $ M.insertWith S.union a2 (S.singleton a1)
    return ()

  addRegisters la' = do
    let rs = S.map PX.Reg (S.fromList callerSaved)
    mapM_ (`addEdges` rs) la'

buildInterfere' [] [] = return ()
buildInterfere' _ _ = error "buildInterfere: Mismatch between args and live after sets"

{- Build Move Biased Graph -}

buildMoveBias :: PX.Program -> PX.Program
buildMoveBias (PX.Program i bs) = PX.Program i bs'
 where
   bs' = map (\(l, b) -> (l, bMvBBlock b)) bs
   bMvBBlock (PX.Block i' is) =
     PX.Block i' {PX.bInfoMoveRelated = buildMvBGraph is} is

buildMvBGraph :: [PX.Instr] -> Map PX.Arg (Set PX.Arg)
buildMvBGraph = foldr bld M.empty
 where
  bld i acc =
    case i of
      (PX.Movq v1@(PX.Var _) v2@(PX.Var _)) ->
        M.unionWith S.union
          (M.fromList [(v1, S.singleton v2), (v2, S.singleton v1)])
          acc
      _ -> acc

{- Allocate Registers -}

allocateRegisters :: PX.Program -> X.Program
allocateRegisters p@(PX.Program _ bs) = Ch2.assignHomes' locMap p
 where
   (PX.Block info _) = snd . head $ bs
   locMap =
         colorGraph
           (PX.bInfoConflicts info)
           (PX.bInfoMoveRelated info)

-- Returns list of Strings to StoreLocs and frameSize
colorGraph
  :: Map PX.Arg (Set PX.Arg)
  -> Map PX.Arg (Set PX.Arg)
  -> Map String PX.StoreLoc
colorGraph iList mvBList  =
  let
    (g', nodeFromVertex, vertexFromNode) = toGraph iList
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
      . mapMaybe
          (\(v, a) -> case a of
              (PX.Reg r) -> case colorFromReg r of
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
            Just (PX.Reg _) -> Nothing
            Just (PX.Var s) -> Just (s, storeLocFromColor c)
            Nothing         -> Nothing
            _               -> error $ "Found " ++ show v ++ "in vertexAssoc")
    . M.toList
    $ coloring

toGraph
  :: M.Map PX.Arg (S.Set PX.Arg)
  -> (Graph, Vertex -> ((), PX.Arg, [PX.Arg]), PX.Arg -> Maybe Vertex)
toGraph =
  graphFromEdges
  . map (\(k, ks) -> ((), k, ks)) . M.toList . M.map S.toList

regsToUse :: [Register]
regsToUse = [ Rbx ]

regIntAssoc :: [(Int, Register)]
regIntAssoc = zip [0..] regsToUse

storeLocFromColor :: Int -> PX.StoreLoc
storeLocFromColor n = case lookup n regIntAssoc of
  Just r -> PX.RegLoc r
  Nothing -> PX.Stack $ negate $ 8 * (n - length regIntAssoc)

colorFromReg :: Register -> Maybe Int
colorFromReg r = lookup r (map swap regIntAssoc)
