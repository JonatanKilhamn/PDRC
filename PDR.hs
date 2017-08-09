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
zlocal = z . local

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

data Assignment = A { bvs :: M.Map Variable Bool
                    , ivs :: M.Map Variable Integer
                    }

removeVar :: Assignment -> Variable -> Assignment
removeVar a v = a { bvs = M.delete v $ bvs a
                  , ivs = M.delete v $ ivs a }


unsafeStateQuery :: PDRZ3 (Result, Maybe Assignment)
unsafeStateQuery = do
  c <- get
  let p = prop c
      n = length $ frames c
  f_n <- mkFrame n
  let (bvs, ivs) = getAllVars (system c)
  bv_asts <- mapM mkVariable bvs
  iv_asts <- mapM mkVariable ivs
  (res, maybeVals) <- zlocal $ do
    assert =<< mkNot p
    assert f_n
    withModel $ \m ->
      evalBoolsAndInts m (bv_asts, iv_asts)
  let assignment = case maybeVals of (Nothing) -> Nothing
                                     (Just (maybeBools, maybeInts)) -> Just $
                                      A { bvs = maybeMap bvs maybeBools
                                        , ivs = maybeMap ivs maybeInts }
  return (res, assignment)

maybeMap :: Ord a => [a] -> [Maybe b] -> M.Map a b
maybeMap xs ys = M.fromList $ catMaybes $ zipWith f xs ys
 where f x (Nothing) = Nothing
       f x (Just y) = Just (x,y)


evalBoolsAndInts :: Model -> ([AST],[AST]) -> Z3 ([Maybe Bool],[Maybe Integer])
evalBoolsAndInts m (as1,as2) = do
  maybes1 <- mapM (evalBool m) as1
  maybes2 <- mapM (evalInt m) as1
  return (maybes1, maybes2)


consecutionQuery :: TimedCube -> PDRZ3 (Result, Maybe Assignment)
consecutionQuery (ass,k) = do
  c <- get
  let p = prop c
  s <- mkTimedCube (ass,k-1)
  s' <- mkTimedCube (ass,k)
  t <- mkTransRelation (k-1)
  f_kminus1 <- mkFrame (k-1)
  let (bvs, ivs) = getAllVars (system c)
      (bvs', ivs') = (map Next bvs, map Next ivs)
      (bvs'', ivs'') = (bvs++bvs', ivs++ivs')
  bv_asts <- mapM mkVariable bvs''
  iv_asts <- mapM mkVariable ivs''
  -- Assertions and actual SAT check:
  (res, maybeVals) <- zlocal $ do
    assert s
    assert =<< mkNot s'
    assert f_kminus1
    withModel $ \m ->
      (evalBoolsAndInts m) (bv_asts, iv_asts)
  let assignment = case maybeVals of (Nothing) -> Nothing
                                     (Just (maybeBools, maybeInts)) -> Just $
                                      A { bvs = maybeMap bvs'' maybeBools
                                        , ivs = maybeMap ivs'' maybeInts }
  return (res, assignment)

-- Generalising an assignment which breaks the safety property in F_N
generalise1 :: Assignment -> PDRZ3 Assignment
generalise1 a = do
  let vars = (M.keys $ bvs a) ++ (M.keys $ ivs a)
  c <- get
  let p = prop c
      n = length $ frames c
  f_n <- mkFrame n  
  z push
  -- Assume the frame and safety property:
  z $ assert f_n  
  z $ assert p
  -- Try the assignment once for each variable:
  a' <- foldM generalise1once a vars
  z $ pop 1
  return a'
 where
  generalise1once ass var = do
   redundant <- checkLiteral1 ass var
   return $ if redundant then (removeVar ass var) else ass

-- Checks one literal to see if it can be removed from the assignment
checkLiteral1 :: Assignment -> Variable -> PDRZ3 Bool
checkLiteral1 a var = do
  -- Assume the modified assignment
  asts <- mapM mkPredicate $ [ (if (v==var) then id else pnot) $
                                (if b then id else pnot) $
                                 P $ BLit v
                             | (v,b) <- M.toList $ bvs a
                             ] ++
                             [ (if (v==var) then id else pnot) $
                                P $ ILit Equals (IntVar v) (IntConst (n))
                             | (v,n) <- M.toList $ ivs a
                             ]
  res <- zlocal $ do
   mapM assert asts
   check
  return (res == Unsat)



-- TODO
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
  (z . mkNot) =<< (mkPredicate p)
mkPredicate' (PAnd ps) = do
  (z . mkAnd) =<< (mapM mkPredicate ps)
mkPredicate' (POr ps) = do
  (z . mkOr) =<< (mapM mkPredicate ps)

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
mkIntExpr'' (Plus ie1 ie2) = (z . mkAdd) =<< (mapM mkIntExpr [ie1, ie2])
mkIntExpr'' (Minus ie1 ie2) = (z . mkSub) =<< (mapM mkIntExpr [ie1, ie2])
mkIntExpr'' (IntVar v) = mkVariable v

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

