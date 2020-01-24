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
  -> Map Vertex (Set Vertex) -- ^ Prefer to color connected vertices alike
  -> S.Set Vertex            -- ^ Vertices not yet to colored
  -> Map Vertex Color
  -> Map Vertex Color
color g pMap vs cmap = case maxSat vs of
  Nothing -> cmap
  Just (v, sat) -> case M.lookup v pMap of
    Nothing ->
      let clr = minFree sat
      in color g pMap (S.delete v vs) (M.insert v clr cmap)
    Just preferedVs ->
      let
        preferredColors =
          S.difference
            (S.fromList
            . mapMaybe (\p -> M.lookup p cmap)
            $ (S.toList preferedVs))
            sat
      in case S.lookupMin preferredColors of
        Nothing ->
          let clr = minFree sat
          in color g pMap (S.delete v vs) (M.insert v clr cmap)
        Just clr ->
          color g pMap (S.delete v vs) (M.insert v clr cmap)
 where

  maxSat :: S.Set Vertex -> Maybe (Vertex, Set Color)
  maxSat vs' = foldr findMax Nothing vs'
    where
      findMax
         :: (Vertex)
         -> Maybe (Vertex, Set Color) -> Maybe (Vertex, Set Color)
      findMax a acc = case acc of
        Nothing -> Just (a, saturation a)
        Just (_, satAcc) ->
          let satA = saturation a
          in if S.size satA > S.size satAcc
          then Just (a, satA)
          else acc

  saturation :: Vertex -> Set Color
  saturation v =
    S.fromList
    . mapMaybe (\n -> M.lookup n $ cmap)
    . neighbors
    $ v

  minFree sat = case S.lookupMax sat of
    Nothing -> 0
    Just n -> S.findMin ((S.fromList [0..(n+1)]) `S.difference` sat)

  neighbors v = g ! v
