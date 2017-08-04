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

import System
----------------

-- Placeholders! TODO: fix them
type Frame = [Clause]

data Clause = Clause [AST]
data Cube = Cube [AST]


type PDRZ3 = StateT SMTContext Z3

-- runStateT :: StateT s a -> s -> m (a, s)

runPdr :: System -> IO Bool
runPdr s = do
  (res, finalState) <- evalZ3 $ runStateT (pdr s) (emptyContext)
  return res

pdr :: System -> PDRZ3 Bool
pdr s = do
  putInitialSmtContext s
  outerPdrLoop s
      

-- Input: n::Int is iteration, which also corresponds to the highest frame index
outerPdrLoop :: System -> PDRZ3 Bool
outerPdrLoop s = do
  failed <- blockAllBadStatesInLastFrame
  if failed
  then return False
  else do
  addNewFrame
  success <- forwardPropagation
  if success
  then return True
  else do
  outerPdrLoop s


-- TODO: add statefulness
-- Input: k::Int, the current iteration
-- Returns: false if property is disproved, true if all states could be blocked
blockAllBadStatesInLastFrame :: PDRZ3 Bool
blockAllBadStatesInLastFrame = do
  let setup = undefined -- some setup surely needed
  k <- getMaxFrameIndex
  (res, maybeAssignment) <- unsafeStateQuery
  if (res == Unsat)
  then return True
  else do
  assignment <- generalise1 (fromJust maybeAssignment)
  let queue = priorityQueue (assignment,k)
  failed <- blockEntireQueue queue
  if failed
  then return False
  else do
  blockAllBadStatesInLastFrame
  

blockEntireQueue :: PriorityQueue -> PDRZ3 Bool
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


blockBadState :: TimedCube -> PriorityQueue -> PDRZ3 (Bool, PriorityQueue)
blockBadState (s,k) queue =
  if k == 0
  then return (False, queue)
  else do
  c <- get
  (res, maybeAssignment) <- consecutionQuery (s,k)
  queue' <-
   if (res == Sat)
   then do
    m <- generalise2 (fromJust maybeAssignment)
    let newQueue = (m, k-1):(queue ++ [(s,k)])
    return newQueue
   else do
    updateFrames s k
    c <- get
    n <- getMaxFrameIndex
    let newQueue = if (k < n) then (queue++[(s,k+1)]) else queue
    return newQueue
  return (True, queue')



addNewFrame :: PDRZ3 ()
addNewFrame = do
  c <- get
  put $ c {frames = (frames c)++[emptyFrame]}
  return ()

-- TODO placeholder
emptyFrame :: Frame
emptyFrame = []

-- TODO:
-- * Should update all frames with i≤k
-- * subsumption?
-- * Do we keep all clauses in all frames, or just in the last one where
--   they appear?
-- Needs to either augment the monad, or add return type other than ()
updateFrames :: Assignment -> Int -> PDRZ3 ()
updateFrames s k = undefined


getMaxFrameIndex :: PDRZ3 Int
getMaxFrameIndex = get >>= (return . length . frames)

-- TODO
forwardPropagation :: PDRZ3 Bool
forwardPropagation = return True

-- TODO
type Assignment = [Bool] -- placeholder


unsafeStateQuery :: PDRZ3 (Result, Maybe Assignment)
unsafeStateQuery = do
  c <- get
  let p = prop c
      n = length $ frames c
  lift push
  np <- lift $ mkNot p
  lift $ assert np
  f_n <- mkFrame $ last $ frames c
  lift $ assert f_n
  assVars <- getVars n
  res <- lift $ withModel $ \m ->
    catMaybes <$> mapM (evalBool m) assVars
  lift $ pop 1
  return res
  

mkFrame :: Frame -> PDRZ3 AST
mkFrame fr = do
  clauses <- mapM mkClause fr
  lift $ mkAnd clauses

mkClause :: Clause -> PDRZ3 AST
mkClause (Clause asts) = lift $ mkOr asts

-- TODO
consecutionQuery :: TimedCube -> PDRZ3 (Result, Maybe Assignment)
consecutionQuery (ass,k) = do
  c <- get
  let p = prop c
  lift push
  s <- mkTimedCube (ass,k-1)
  lift $ assert s
  s' <- mkTimedCube (ass,k)
  lift $ assert =<< mkNot s'
  t <- mkTransRelation (k-1)
  f_kminus1 <- mkFrame $ (frames c)!!(k-1)
  lift $ assert f_kminus1
  
  assVars <- getVars (k-1)
  res <- lift $ withModel $ \m ->
    catMaybes <$> mapM (evalBool m) assVars
  lift $ pop 1
  return res

-- TODO
generalise1 :: Assignment -> PDRZ3 Assignment
generalise1 a = undefined

generalise2 :: Assignment -> PDRZ3 Assignment
generalise2 a = undefined

type TimedCube = Timed Assignment

type PriorityQueue = [TimedCube] -- maybe placeholder?

-- TODO: change prioQ implementation to actual queue
priorityQueue :: TimedCube -> PriorityQueue
priorityQueue elem = [elem]

-- TODO: actual popMin / change prioQ implementation
popMin :: PriorityQueue -> (TimedCube, PriorityQueue)
popMin q = (head q, tail q)

type Timed a = (a,Int)




data SMTContext
  = C
  { system :: System
  , predMap :: M.Map (Timed Predicate) AST
  , intExpMap :: M.Map (Timed IntExpr) AST
  , litMap :: M.Map (Timed Literal) AST
  , varMap :: M.Map (Timed Variable) AST
  , frames :: [Frame]
  , prioQueue :: PriorityQueue
  , prop :: AST
  }


emptyContext :: SMTContext
emptyContext = C { system = undefined
                 , predMap = M.empty
                 , intExpMap = M.empty
                 , litMap = M.empty
                 , varMap = M.empty
                 , frames = []
                 , prioQueue = []
                 , prop = undefined
                 }

-- TODO: actually use this!
putInitialSmtContext :: System -> PDRZ3 ()
putInitialSmtContext s = do
  p <- getProp s
  c <- get
  put $ c {system = s, prop = p} 
  return ()


-- TODO
getProp :: System -> PDRZ3 AST
getProp s = mkPredicate (safetyProp s)

mkPredicate :: Predicate -> PDRZ3 AST
mkPredicate (P lit) = mkLiteral lit
mkPredicate (PNot p) = do
  p_ast <- mkPredicate p
  not_p_ast <- lift $ mkNot p_ast
  return not_p_ast
{-mkPredicate c (PAnd ps) = do
  (c2,p_ast) <- mkPredicate c p
  not_p_ast <- mkNot p_ast
  return (c2, not_p_ast)
-}

-- TODO
mkLiteral :: Literal -> PDRZ3 AST
mkLiteral = undefined

-- "i" is the frame
-- TODO
getVars :: Int -> PDRZ3 [AST]
getVars i = undefined

-- TODO
mkTimedCube :: TimedCube -> PDRZ3 AST
mkTimedCube tc = undefined

-- "i" is the frame index of the next-state variables
-- TODO
mkTransRelation :: Int -> PDRZ3 AST
mkTransRelation i = undefined


