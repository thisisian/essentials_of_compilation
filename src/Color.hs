module Color where

import Data.Graph
import Data.Maybe
import qualified Data.Map as M
import Data.Map (Map)
import Data.Array ((!))
import qualified Data.Set as S
import Data.Set (Set)

type Color = Int

color
  :: Graph
  -> S.Set Vertex       -- ^ Vertices not yet to colored
  -> Map Vertex Color
  -> Map Vertex Color
color g vs cmap = case maxSat cmap vs of
  Nothing -> cmap
  Just (v, sat) ->
    let clr = minFree sat
    in color g (S.delete v vs) (M.insert v clr cmap)
 where
  maxSat :: Map Vertex Color -> S.Set Vertex -> Maybe (Vertex, Set Color)
  maxSat cmap s = foldr findMax Nothing s
    where findMax
            :: (Vertex)
            -> Maybe (Vertex, Set Color) -> Maybe (Vertex, Set Color)
          findMax a b = case b of
            Nothing -> b
            Just (_, sat') ->
              let sat = saturation cmap a
              in if S.size sat > S.size sat'
              then Just (a, sat)
              else b

  saturation
    :: M.Map Vertex Color
    -> Vertex
    -> Set Color
  saturation cmap v =
    S.fromList
    . mapMaybe (\n -> M.lookup n $ cmap)
    . neighbors
    $ v

  minFree sat =
    case S.lookupMin sat of
      Nothing -> 0
      Just n -> S.findMin ((S.fromList [0..n]) `S.difference` sat)

  neighbors v = g ! v
