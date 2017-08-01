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
type Frame = [Clause]

data Clause = Clause [AST]
data Cube = Cube [AST]


runPdr :: System -> IO Bool
runPdr s = do
  res <- evalZ3 $ pdr s
  return res

pdr :: System -> Z3 Bool
pdr s = do
  c <- initialSmtContext s
  outerPdrLoop s c 0
      

-- Input: n::Int is iteration, which also corresponds to the highest frame index
outerPdrLoop :: System -> SMTContext -> Int -> Z3 Bool
outerPdrLoop s c n = do
  failed <- blockAllBadStatesInLastFrame c n
  if failed
  then return False
  else do
  c <- addNewFrame c
  success <- forwardPropagation
  if success
  then return True
  else do
  outerPdrLoop s c (n+1)


-- TODO: add statefulness
-- Input: k::Int, the current iteration
-- Returns: false if property is disproved, true if all states could be blocked
blockAllBadStatesInLastFrame :: SMTContext -> Int -> Z3 Bool
blockAllBadStatesInLastFrame c k = do
  let setup = undefined -- some setup surely needed
  (res, maybeAssignment) <- unsafeStateQuery c
  if (res == Unsat)
  then return True
  else do
  assignment <- generalise1 (fromJust maybeAssignment)
  let queue = priorityQueue (assignment,k)
  failed <- blockEntireQueue c queue
  if failed
  then return False
  else do
  blockAllBadStatesInLastFrame c k
  -- this hinges on some statefulness carrying over in the Z3 monad,
  -- specifically the frames. Right now it doesn't, so either I'll
  -- have to augment the Z3 monad, or pass around a Context object
  -- which will then be updated before the recursive call.
  

blockEntireQueue :: SMTContext -> PriorityQueue -> Z3 Bool
blockEntireQueue c queue = do
  if ((length queue) == 0)
  then return True
  else do
  let ((t,k),queue') = popMin queue
  (failed, queue'') <- blockBadState c (t,k) queue'
  if failed
  then return False
  else do
  blockEntireQueue c queue''


blockBadState :: SMTContext -> TimedCube -> PriorityQueue -> Z3 (Bool, PriorityQueue)
blockBadState c (s,k) queue = do
  if k == 0
  then return (False, queue)
  else do
  (res, maybeAssignment) <- consecutionQuery c (s,k)
  queue' <-
   if (res == Sat)
   then do
    m <- generalise2 (fromJust maybeAssignment)
    let newQueue = (m, k-1):(queue ++ [(s,k)])
    return newQueue
   else do
    updateFrames s k
    n <- getMaxFrameIndex c
    let newQueue = if (k < n) then (queue++[(s,k+1)]) else queue
    return newQueue
  return (True, queue')



addNewFrame :: SMTContext -> Z3 (SMTContext)
addNewFrame c = return (c {frames = (frames c)++[emptyFrame]})

-- TODO placeholder
emptyFrame :: Frame
emptyFrame = []

-- TODO:
-- * Should update all frames with i≤k
-- * subsumption?
-- * Do we keep all clauses in all frames, or just in the last one where
--   they appear?
-- Needs to either augment the monad, or add return type other than ()
updateFrames :: Assignment -> Int -> Z3 ()
updateFrames s k = undefined


getMaxFrameIndex :: SMTContext -> Z3 Int
getMaxFrameIndex c = return $ length $ frames c

-- TODO
forwardPropagation :: Z3 Bool
forwardPropagation = return True

-- TODO
type Assignment = [Bool] -- placeholder


unsafeStateQuery :: SMTContext -> Z3 (Result, Maybe Assignment)
unsafeStateQuery c = do
  let p = prop c
      n = length $ frames c
  push
  np <- mkNot p
  assert np
  f_n <- mkFrame $ last $ frames c
  assert f_n
  assVars <- getVars c n
  res <- withModel $ \m ->
    catMaybes <$> mapM (evalBool m) assVars
  pop 1
  return res
  

mkFrame :: Frame -> Z3 AST
mkFrame fr = do
  clauses <- mapM mkClause fr
  mkAnd clauses

mkClause :: Clause -> Z3 AST
mkClause (Clause asts) = mkOr asts

-- TODO
consecutionQuery :: SMTContext -> TimedCube -> Z3 (Result, Maybe Assignment)
consecutionQuery c (ass,k) = do
  let p = prop c
  push
  s <- mkTimedCube c (ass,k-1)
  assert s
  s' <- mkTimedCube c (ass,k)
  assert =<< mkNot s'
  t <- mkTransRelation c (k-1)
  f_kminus1 <- mkFrame $ (frames c)!!(k-1)
  assert f_kminus1
  
  assVars <- getVars c (k-1)
  res <- withModel $ \m ->
    catMaybes <$> mapM (evalBool m) assVars
  pop 1
  return res

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
  , prop :: AST
  }


-- TODO: actually use this!
initialSmtContext :: System -> Z3 SMTContext
initialSmtContext s = do
  p <- getProp s
  return $ C { astMap = M.fromList []
             , frames = []
             , prioQueue = []
             , prop = p
             }

-- TODO
getProp :: System -> Z3 AST
getProp = undefined

-- "i" is the frame
-- TODO
getVars :: SMTContext -> Int -> Z3 [AST]
getVars c i = undefined

-- TODO
mkTimedCube :: SMTContext -> TimedCube -> Z3 AST
mkTimedCube tc = undefined

-- "i" is the frame index of the next-state variables
-- TODO
mkTransRelation :: SMTContext -> Int -> Z3 AST
mkTransRelation c i = undefined

{--doZ3 :: (Z3 a) -> State SMTContext ()
doZ3 z = state $ \c -> ((), c {z3Env = z3Env'})
 where z3Env' = do
        z
        return ()
--}



