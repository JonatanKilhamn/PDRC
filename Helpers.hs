module Helpers where

import Data.Maybe
import qualified Data.Map as M
import qualified Data.Set as S

indent :: [String] -> [String]
indent = concat . map (map ("  "++)) . map lines
-- lines . (map ("  "++)) . unlines

maybeMap :: Ord a => [a] -> [Maybe b] -> M.Map a b
maybeMap xs ys = M.fromList $ catMaybes $ zipWith f xs ys
 where f x (Nothing) = Nothing
       f x (Just y) = Just (x,y)

(+++) :: [a] -> a -> [a]
list +++ elem = list ++ [elem]

mapFst :: (a -> b) -> (a, c) -> (b, c)
mapFst f (x,y) = (f x,y)


keySet :: (Ord a) => M.Map a b -> S.Set a
keySet = S.fromList . M.keys


setIndex :: (Num c, Ord a) => a -> S.Set a -> c
setIndex x = fromIntegral . (S.findIndex x)
