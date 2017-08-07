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


type PDRZ3 = StateT SMTContext Z3

z = lift


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
  putQueue $ priorityQueue (assignment,k)
  failed <- blockEntireQueue
  if failed
  then return False
  else do
  blockAllBadStatesInLastFrame
  

blockEntireQueue :: PDRZ3 Bool
blockEntireQueue = do
  queue <- fmap prioQueue get
  if ((length queue) == 0)
  then return True
  else do
  t <- popMin
  failed <- blockBadState t
  if failed
  then return False
  else do
  blockEntireQueue


blockBadState :: TimedCube -> PDRZ3 Bool
blockBadState (s,k) =
  if k == 0
  then return False
  else do
  queue <- fmap prioQueue get
  (res, maybeAssignment) <- consecutionQuery (s,k)
  if (res == Sat)
  then do
    m <- generalise2 (fromJust maybeAssignment)
    putQueue $ (m, k-1):(queue ++ [(s,k)])
  else do
    updateFrames s k
    n <- getMaxFrameIndex
    putQueue $ if (k < n) then (queue++[(s,k+1)]) else queue
  return True



addNewFrame :: PDRZ3 ()
addNewFrame = do
  c <- get
  put $ c {frames = (frames c)++[emptyFrame]}
  return ()

emptyFrame :: Frame
emptyFrame = ([], Nothing)

getMaxFrameIndex :: PDRZ3 Int
getMaxFrameIndex = get >>= (return . length . frames)

-- TODO:
-- * Should update all frames with i≤k
-- * subsumption?
-- * Do we keep all clauses in all frames, or just in the last one where
--   they appear?
-- Needs to either augment the monad, or add return type other than ()
updateFrames :: Assignment -> Int -> PDRZ3 ()
updateFrames s k = undefined


-- TODO
forwardPropagation :: PDRZ3 Bool
forwardPropagation = return True

-- TODO: this type does not infer all known properties of assignments. Problem?
type Assignment = [Literal] -- placeholder


unsafeStateQuery :: PDRZ3 (Result, Maybe Assignment)
unsafeStateQuery = do
  c <- get
  let p = prop c
      n = length $ frames c
  z push
  z $ mkNot p >>= assert
  f_n <- mkFrame n
  z $ assert f_n
  assVars <- getVars
  res <- lift $ withModel $ \m ->
    catMaybes <$> mapM (evalBool m) assVars
  z $ pop 1
  return undefined --TODO
  



consecutionQuery :: TimedCube -> PDRZ3 (Result, Maybe Assignment)
consecutionQuery (ass,k) = do
  c <- get
  let p = prop c
  z push
  s <- mkTimedCube (ass,k-1)
  z $ assert s
  s' <- mkTimedCube (ass,k)
  z $ assert =<< mkNot s'
  t <- mkTransRelation (k-1)
  f_kminus1 <- mkFrame (k-1)
  z $ assert f_kminus1
  assVars <- getVars
  res <- z $ withModel $ \m ->
    catMaybes <$> mapM (evalBool m) assVars
  z $ pop 1
  return undefined --TODO



generalise1 :: Assignment -> PDRZ3 Assignment
generalise1 a = do undefined
  

generalise2 :: Assignment -> PDRZ3 Assignment
generalise2 a = undefined

type TimedCube = Timed Assignment

type PriorityQueue = [TimedCube] -- maybe placeholder?

-- TODO: change prioQ implementation to actual queue
priorityQueue :: TimedCube -> PriorityQueue
priorityQueue elem = [elem]

-- TODO: actual popMin / change prioQ implementation
popMin :: PDRZ3 TimedCube
popMin = do
  c <- get
  let q = prioQueue c
      tc = head q
      q' = tail q
  putQueue q'
  return tc



type Timed a = (a,Int)

-- Placeholders! TODO: fix them
type Frame = ([Predicate], Maybe AST)



data SMTContext
  = C
  { system :: System
  , predMap :: M.Map (Predicate) AST
  , intExprMap :: M.Map (IntExpr) AST
  , litMap :: M.Map (Literal) AST
  , varMap :: M.Map (Variable) AST
  , frames :: [Frame]
  , prioQueue :: PriorityQueue
  , prop :: AST
  }


emptyContext :: SMTContext
emptyContext = C { system = undefined
                 , predMap = M.empty
                 , intExprMap = M.empty
                 , litMap = M.empty
                 , varMap = M.empty
                 , frames = []
                 , prioQueue = []
                 , prop = undefined
                 }

putInitialSmtContext :: System -> PDRZ3 ()
putInitialSmtContext s = do
  p <- getProp s
  c <- get
  put $ c {system = s, prop = p} 
  return ()


putQueue :: PriorityQueue -> PDRZ3 ()
putQueue q = do
  c <- get
  put c {prioQueue = q}

getProp :: System -> PDRZ3 AST
getProp s = mkPredicate (safetyProp s)


------


-- Int is the frame index
mkFrame :: Int -> PDRZ3 AST
mkFrame k = do
  c <- get
  let (ps,maybe_ast) = (frames c)!!k
  case maybe_ast of
    (Just ast) -> return ast
    (Nothing) -> do
      ast <- mkPredicate (PAnd ps)
      let frames' = replaceAtIndex k (ps,Just ast) (frames c)
      put $ c {frames = frames'}
      return ast

replaceAtIndex :: Int -> a -> [a] -> [a]
replaceAtIndex n item ls = a ++ (item:b) where (a, (_:b)) = splitAt n ls




mkPredicate :: Predicate -> PDRZ3 AST
mkPredicate p = do
  ast <- mkPredicate' p
  c <- get
  let pm = predMap c
  let pm' = M.insert p ast pm
  put c {predMap = pm'}
  return ast

mkPredicate' :: Predicate -> PDRZ3 AST
mkPredicate' (P lit) = mkLiteral lit
mkPredicate' (PNot p) = do
  ast <- mkPredicate p
  z $ mkNot ast
mkPredicate' (PAnd ps) = do
  asts <- mapM mkPredicate ps
  z $ mkAnd asts
mkPredicate' (POr ps) = do
  asts <- mapM mkPredicate ps
  z $ mkOr asts

mkLiteral :: Literal -> PDRZ3 AST
mkLiteral l = do
  lm <- fmap litMap get
  let maybeAst = M.lookup l lm
  case maybeAst of (Just ast) -> return ast
                   (Nothing) -> mkLiteral' l

mkLiteral' :: Literal -> PDRZ3 AST
mkLiteral' l = do
  ast <- mkLiteral'' l
  c <- get
  let lm = litMap c
  let lm' = M.insert l ast lm
  put c {litMap = lm'}
  return ast

mkLiteral'' :: Literal -> PDRZ3 AST
mkLiteral'' (BLit v) = mkVariable v
mkLiteral'' (ILit bp e1 e2) = do
 ast1 <- mkIntExpr e1
 ast2 <- mkIntExpr e2
 z $ (zfunction bp) ast1 ast2
  where zfunction Equals = mkEq
        zfunction NEquals = curry ((mkNot =<<) . (uncurry mkEq))
        zfunction LessThan = mkLt
        zfunction LessThanEq = mkLe
        zfunction GreaterThan = mkGt
        zfunction GreaterThanEq = mkGe

mkIntExpr :: IntExpr -> PDRZ3 AST
mkIntExpr ie = do
  iem <- fmap intExprMap get
  let maybeAst = M.lookup ie iem
  case maybeAst of (Just ast) -> return ast
                   (Nothing) -> mkIntExpr' ie
       
mkIntExpr' :: IntExpr -> PDRZ3 AST
mkIntExpr' ie = do
  ast <- mkIntExpr'' ie
  c <- get
  let iem = intExprMap c
  let iem' = M.insert ie ast iem
  put c {intExprMap = iem'}
  return ast

mkIntExpr'' :: IntExpr -> PDRZ3 AST
mkIntExpr'' (IntConst n) = z $ mkIntNum n
mkIntExpr'' (Plus ie1 ie2) = mkIntExprOp mkAdd [ie1, ie2]
mkIntExpr'' (Minus ie1 ie2) = mkIntExprOp mkSub [ie1, ie2]
mkIntExpr'' (IntVar v) = mkVariable v

mkIntExprOp :: ([AST] -> Z3 AST) -> [IntExpr] -> PDRZ3 AST
mkIntExprOp fun ies = do
  asts <- mapM mkIntExpr ies
  z $ fun asts

mkVariable :: Variable -> PDRZ3 AST
mkVariable v = do
  vm <- fmap varMap get
  let maybeAst = M.lookup v vm
  case maybeAst of (Just ast) -> return ast
                   (Nothing) -> mkVariable' v

mkVariable' :: Variable -> PDRZ3 AST
mkVariable' v = mkVar' v ""
 where mkVar' (Var v) s = z $ mkFreshBoolVar (v++s)
       mkVar' (Next v) s = mkVar' v (s++"'")






--data Literal = BLit Variable | ILit BinaryPred (IntExpr) (IntExpr)

-- "i" is the frame
-- TODO
getVars :: PDRZ3 [AST]
getVars = do
  c <- get
  let vs = getAllVars (system c)
  undefined



-- TODO
mkTimedCube :: TimedCube -> PDRZ3 AST
mkTimedCube tc = undefined

-- "i" is the frame index of the next-state variables
-- TODO
mkTransRelation :: Int -> PDRZ3 AST
mkTransRelation i = undefined














testz = do
 v <- mkVariable (Next $ Var "foo")
 z $ assert v
 nv <- z $ mkNot v
 --z $ assert nv
 z check

