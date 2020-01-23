module Color where

import Data.Graph
import Data.Maybe
import qualified Data.Map as M
import Data.Map (Map)
import Data.Array ((!))
import qualified Data.Set as S
import Data.Set (Set)
import Debug.Trace

type Color = Int

color
  :: Graph
  -> S.Set Vertex       -- ^ Vertices not yet to colored
  -> Map Vertex Color
  -> Map Vertex Color
color g vs cmap = {- trace ("color: " ++ show vs) -} res
 where
  res = case maxSat cmap vs of
    Nothing -> cmap
    Just (v, sat) ->
      let clr = minFree sat
      in color g (S.delete v vs) (M.insert v clr cmap)

  maxSat :: Map Vertex Color -> S.Set Vertex -> Maybe (Vertex, Set Color)
  maxSat cmap vs' = {- trace ("maxSat: " ++ show res) -} res
    where
      res = foldr findMax Nothing vs'
      findMax
         :: (Vertex)
         -> Maybe (Vertex, Set Color) -> Maybe (Vertex, Set Color)
      findMax a acc = case acc of
        Nothing -> Just (a, saturation cmap a)
        Just (_, satAcc) ->
          let satA = saturation cmap a
          in if S.size satA > S.size satAcc
          then Just (a, satA)
          else acc

  saturation
    :: M.Map Vertex Color
    -> Vertex
    -> Set Color
  saturation cmap v = {- trace ("\nSaturation of " ++ show v ++ ": " ++ show res) -} res
   where
     res =
       S.fromList
       . mapMaybe (\n -> M.lookup n $ cmap)
       . neighbors
       $ v

  minFree sat = {- trace ("\nminFree: " ++ show sat ++ " " ++ show res) -} res
   where
     res = case S.lookupMax sat of
       Nothing -> 0
       Just n -> S.findMin ((S.fromList [0..(n+1)]) `S.difference` sat)

  neighbors v = g ! v
