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
  if (not failed)
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
    m <- generalise2 (fromJust maybeAssignment) (s,k)
    putQueue $ (m, k-1):(queue ++ [(s,k)])
  else do
    updateFrames (s, k)
    n <- getMaxFrameIndex
    putQueue $ if (k < n) then (queue++[(s,k+1)]) else queue
  return True



-- TODO
-- Returns: true if property is proven (inductive invariant found),
--   false if another iteration is needed
forwardPropagation :: PDRZ3 Bool
forwardPropagation = return undefined


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
  s <- mkAssignment ass
  s' <- mkAssignment $ next ass
  t <- mkTransRelation
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
   redundant <- checkLiteral ass var
   return $ if redundant then (removeVar ass var) else ass

-- Checks one literal to see if it can be removed from the assignment
checkLiteral :: Assignment -> Variable -> PDRZ3 Bool
checkLiteral a var = do
  -- Assume the modified assignment
  ast <- mkPredicate $ PAnd $ [ P $ BLit v (if (v==var) then b else not b)
                              | (v,b) <- M.toList $ bvs a
                              ] ++
                              [ (if (v==var) then id else pnot) $
                                 P $ ILit Equals (IntVar v) (IntConst (n))
                              | (v,n) <- M.toList $ ivs a
                              ]
  res <- zlocal $ do
   assert ast
   check
  return (res == Unsat)


-- Generalising an assignment which breaks consecution of another property !s
-- (!s a clause based on the previously found bac cube s)
generalise2 :: Assignment -> TimedCube -> PDRZ3 Assignment
generalise2 a (ass,k) = do
  let vars = (M.keys $ bvs a) ++ (M.keys $ ivs a)
  f_kminus1 <- mkFrame (k-1)
  s <- mkAssignment ass
  s' <- mkAssignment $ next ass
  trans_kminus1 <- mkTransRelation
  z push
  -- Assume !s, frame, transition and !s'
  -- if satisfiable with one literal changed, that literal is necessary
  -- if unsatisfiable       -  |  |  -        that literal can be removed
  z $ do
    assert f_kminus1
    assert =<< mkNot s
    assert =<< mkNot s'
    assert trans_kminus1
  -- Try the assignment once for each variable:
  a' <- foldM generalise2once a vars
  z $ pop 1
  return a'
 where
  generalise2once ass var = do
   redundant <- checkLiteral ass var
   return $ if redundant then (removeVar ass var) else ass

addNewFrame :: PDRZ3 ()
addNewFrame = do
  c <- get
  put $ c {frames = (frames c) +++ emptyFrame}
  return ()

emptyFrame :: Frame
emptyFrame = Frame []

getMaxFrameIndex :: PDRZ3 Int
getMaxFrameIndex = get >>= (return . length . frames)

-- TODO:
-- * Should update all frames with i≤k
-- * subsumption?
-- * Do we keep all clauses in all frames, or just in the last one where
--   they appear?
updateFrames :: TimedCube -> PDRZ3 ()
updateFrames (s, k) = do
  let clause = invertAssignment s
  c <- get
  let newFrames = [ if (i < k) then (addTo fr clause) else fr
                  | fr <- frames c
                    , i <- [1..]
                  ]
  put $ c {frames = newFrames}
  return ()
 where addTo (Init p) cl = (Init p)
       addTo (Frame [cls]) cl = do
         undefined
  





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
type TimedCube = Timed Assignment


-- Each clause is the negation of a (generalised) bad cube
data Frame = Init Predicate | Frame [Clause]

type Clause = [Literal]


----


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
  put $ c {system = s, prop = p, frames = [Init (System.init s)]} 
  return ()


putQueue :: PriorityQueue -> PDRZ3 ()
putQueue q = do
  c <- get
  put c {prioQueue = q}

getProp :: System -> PDRZ3 AST
getProp s = mkPredicate (safetyProp s)


------


-- k is the frame index
mkFrame :: Int -> PDRZ3 AST
mkFrame k = do
  c <- get
  -- If there are fr_0, fr_1, ..., fr_5, this will be called with k=5.
  -- Haskell's zero-indexing means we must use (frames c)!!(k-1)
  let fr_k = (frames c)!!(k-1)
  case fr_k of
    (Init p) -> mkPredicate (p)
    (Frame cs) -> mkPredicate . PAnd . map clauseToPredicate $ cs

clauseToPredicate :: Clause -> Predicate
clauseToPredicate lits = POr (map P lits)


mkPredicate :: Predicate -> PDRZ3 AST
mkPredicate p = do
  c <- get
  let pm = predMap c
  let maybeAst = M.lookup p pm
  case maybeAst of (Just ast) -> return ast
                   (Nothing) -> do
                    ast <- mkPredicate' p
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
mkLiteral'' (BLit v b) = do
 (z . mkNot) =<< mkVariable v
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

mkAssignment :: Assignment -> PDRZ3 AST
mkAssignment a =
  mkPredicate $ assignmentToPred a

assignmentToPred :: Assignment -> Predicate
assignmentToPred a = PAnd $
  [ P $ BLit v b
  | (v,b) <- M.toList $ bvs a
  ] ++
  [ P $ ILit Equals (IntVar v) (IntConst (n))
  | (v,n) <- M.toList $ ivs a
  ]

invertAssignment :: Assignment -> Clause
invertAssignment a =
  [ BLit v (not b)
  | (v,b) <- M.toList $ bvs a
  ] ++
  [ ILit NEquals (IntVar v) (IntConst (n))
  | (v,n) <- M.toList $ ivs a
  ]



-- TODO
mkTimedCube :: TimedCube -> PDRZ3 AST
mkTimedCube tc = undefined

-- "i" is the frame index of the current-state
-- TODO
mkTransRelation :: PDRZ3 AST
mkTransRelation = undefined









(+++) :: [a] -> a -> [a]
list +++ elem = list ++ [elem]



testz = do
 v <- mkVariable (Next $ Var "foo")
 z $ assert v
 nv <- z $ mkNot v
 --z $ assert nv
 z check

