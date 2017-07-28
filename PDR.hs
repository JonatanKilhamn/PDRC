module PDR where 

import Control.Applicative
import Control.Monad
import Data.Maybe
import Data.List
import qualified Data.Traversable as T
import qualified Data.Map as M
import ControlMonadLoops


import Z3.Monad

----------------

type System = Int
type Frame = Int


init :: System -> Frame
init = undefined

-- Returns true if property holds, false otherwise
pdr :: System -> IO Bool
pdr s = 
  if ((find (/= 0) ints) == (Just 1))
  then (return True)
  else (return False)
  where
    (frames, ints) = unzip $ iterate ((doOneIteration s) . fst) ([PDR.init s],0)

doOneIteration :: System -> [Frame] -> ([Frame],Int)
doOneIteration = undefined

doOneIteration' :: System -> [Frame] -> IO ([Frame],Int)
doOneIteration' s fs = do
 s2 <- getLine
 return ([],length s2)

pdr' :: System -> IO Bool
pdr' s = do
     ress <- iterateMListWhile ((== 0) . snd) ((doOneIteration' s) . fst) ([PDR.init s],0)
     let (frames, ints) = unzip ress
     return ((last ints) == 1)



iterateMListWhile :: Monad m => (a -> Bool) -> (a -> m a) -> a -> m [a]
iterateMListWhile cond f start = if (not $ cond start)
                                 then return [start]
                                 else do
 next <- f start
 rest <- iterateMListWhile cond f next
 return (start:rest)


buildString :: String -> IO String
buildString s = do
 s2 <- getLine
 return (s++s2)
 
test :: IO [String]
test = do
  strings <- iterateMListWhile (\s -> length s < 5) buildString ""
  return $ take 2 strings




-- Input: n::Int is iteration, which also corresponds to the highest frame index
outerPdrLoop :: Int -> Z3 Bool
outerPdrLoop n = do
  failed <- blockAllBadStatesInLastFrame n
  if failed
  then return False
  else do
  addNewFrame
  success <- forwardPropagation
  if success
  then return True
  else do
  outerPdrLoop (n+1)


-- TODO: add statefulness
-- Input: k::Int, the current iteration
-- Returns: false if property is disproved, true if all states could be blocked
blockAllBadStatesInLastFrame :: Int -> Z3 Bool
blockAllBadStatesInLastFrame k = do
  let setup = undefined -- some setup surely needed
  (sat, maybeAssignment) <- unsafeStateQuery
  if (not sat)
  then return True
  else do
  assignment <- generalise1 (fromJust maybeAssignment)
  let queue = priorityQueue (assignment,k)
  failed <- blockEntireQueue queue
  if failed
  then return False
  else do
  blockAllBadStatesInLastFrame k
  -- this hinges on some statefulness carrying over in the Z3 monad,
  -- specifically the frames. Right now it doesn't, so either I'll
  -- have to augment the Z3 monad, or pass around a Context object
  -- which will then be updated before the recursive call.
  

-- TODO
-- Returns: false if property is disproved, true if all states could be blocked
blockEntireQueue :: PriorityQueue -> Z3 Bool
blockEntireQueue queue = do
  if ((length queue) == 0)
  then return True
  else do
  let ((t,k),queue') = popMin queue
  (failed, queue'') <- blockBadState (t,k) queue'
  if failed
  then return False
  else do
  blockEntireQueue queue''


blockBadState :: (Assignment, Int) -> PriorityQueue -> Z3 (Bool, PriorityQueue)
blockBadState (s,k) queue = do
  if k == 0
  then return (False, queue)
  else do
  (sat, maybeAssignment) <- consecutionQuery (s,k)
  queue' <-
   if sat
   then do
    m <- generalise2 (fromJust maybeAssignment)
    let newQueue = (m, k-1):(queue ++ [(s,k)])
    return newQueue
   else do
    updateFrames s k
    n <- getMaxFrameIndex
    let newQueue = if (k < n) then (queue++[(s,k+1)]) else queue
    return newQueue
  return (True, queue')



-- TODO
-- Needs to either augment the monad, or add return type other than ()
addNewFrame :: Z3 ()
addNewFrame = return ()

-- TODO:
-- * Should update all frames with i≤k
-- * subsumption?
-- * Do we keep all clauses in all frames, or just in the last one where
--   they appear?
-- Needs to either augment the monad, or add return type other than ()
updateFrames :: Assignment -> Int -> Z3 ()
updateFrames s k = undefined

-- TODO
-- Assuming Z3 monad is augmented to hold the frames
getMaxFrameIndex :: Z3 Int
getMaxFrameIndex = undefined

-- TODO
forwardPropagation :: Z3 Bool
forwardPropagation = return True

-- TODO
type Assignment = Int -- placeholder

--TODO
unsafeStateQuery :: Z3 (Bool, Maybe Assignment)
unsafeStateQuery = undefined

-- TODO
consecutionQuery :: (Assignment, Int) -> Z3 (Bool, Maybe Assignment)
consecutionQuery = undefined

-- TODO
generalise1 :: Assignment -> Z3 Assignment
generalise1 a = undefined

generalise2 :: Assignment -> Z3 Assignment
generalise2 a = undefined


type PriorityQueue = [(Assignment, Int)] -- maybe placeholder?

-- TODO: change prioQ implementation to actual queue
priorityQueue :: (Assignment, Int) -> PriorityQueue
priorityQueue elem = [elem]

-- TODO: actual popMin / change prioQ implementation
popMin :: PriorityQueue -> ((Assignment, Int), PriorityQueue)
popMin q = (head q, tail q)


data SMTContext
  = C
  { astMap :: M.Map String AST
  , frames :: [Frame]
  , prioQueue :: PriorityQueue
  , z3Env :: Z3 ()
  }


-- TODO: actually use this!
emptySmtContext :: SMTContext
emptySmtContext = C { astMap = M.fromList []
                    , frames = []
                    , prioQueue = []
                    , z3Env = return ()
                    }



