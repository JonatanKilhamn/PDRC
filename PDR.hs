module PDR where 

import Control.Applicative
import Control.Monad
import Data.Maybe
import Data.List
import qualified Data.Traversable as T
import qualified Data.Map as M
import ControlMonadLoops
import Control.Monad.State.Lazy

import Z3.Monad

----------------

-- Placeholders! TODO: fix them
type System = Int
type Frame = Int



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


blockBadState :: TimedCube -> PriorityQueue -> Z3 (Bool, PriorityQueue)
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
consecutionQuery :: TimedCube -> Z3 (Bool, Maybe Assignment)
consecutionQuery = undefined

-- TODO
generalise1 :: Assignment -> Z3 Assignment
generalise1 a = undefined

generalise2 :: Assignment -> Z3 Assignment
generalise2 a = undefined

type TimedCube = (Assignment, Int)
type PriorityQueue = [TimedCube] -- maybe placeholder?

-- TODO: change prioQ implementation to actual queue
priorityQueue :: TimedCube -> PriorityQueue
priorityQueue elem = [elem]

-- TODO: actual popMin / change prioQ implementation
popMin :: PriorityQueue -> (TimedCube, PriorityQueue)
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

doZ3 :: (Z3 a) -> State SMTContext ()
doZ3 z = state $ \c -> ((), c {z3Env = z3Env'})
 where z3Env' = do
        z
        return ()




