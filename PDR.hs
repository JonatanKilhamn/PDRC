module PDR where 

import Control.Applicative
import Control.Monad
import Data.Maybe
import Data.List
import qualified Data.Traversable as T
import qualified Data.Map as M
import qualified Data.Set as S
import qualified Data.PQueue.Min as Q
import Control.Monad.State.Lazy


import Z3.Monad

import Helpers
import System
----------------


type PDRZ3 = StateT SMTContext Z3

z = lift
zlocal = z . local

runPdr :: System -> IO Bool
runPdr s = do
  (res, finalState) <- evalZ3 $ runStateT (pdr s) (emptyContext)
  putStr (pdrlog finalState)
  return res

pdr :: System -> PDRZ3 Bool
pdr s = do
  putInitialSmtContext s
  res <- outerPdrLoop s
  c <- get
  lg (show c)
  return res


-- Input: n::Int is iteration, which also corresponds to the highest frame index
outerPdrLoop :: System -> PDRZ3 Bool
outerPdrLoop s = do
  failed <- blockAllBadStatesInLastFrame 0
  if (not failed)
  then do
    lg "Failed to block bad state"
    return False
  else do
  success <- forwardPropagation
  if success
  then return True
  else do
  outerPdrLoop s


-- Input i :: Int is a DEBUG parameter, to force termination when it would
--  otherwise run forever. To be removed as soon as the underlying issue is
--  fixed.
-- Returns: false if property is disproved, true if all states could be blocked
blockAllBadStatesInLastFrame :: Int -> PDRZ3 Bool
blockAllBadStatesInLastFrame i = do
  let setup = undefined -- some setup surely needed
  n <- getMaxFrameIndex
  (res, maybeAssignment) <- unsafeStateQuery
  if (res == Unsat) -- There is no unsafe state in F_n
  then do
    lg "All bad states blocked – no more unsafe states found at this depth"
    return True
  else do
  assignment <- generalise1 (fromJust maybeAssignment)
  lg $ "Generalised assignment: " ++ show assignment
  putQueue $ priorityQueue (TC assignment n)
  success <- blockEntireQueue
  if (not success)
  then do
    lg $ "Failed to block; original bad state was " ++ (show assignment)
    return False
  else do
  if i>=5
  then do
  lg "DEBUG: breaking after 5 iteration of bABSILF"
  return True
  else do
  blockAllBadStatesInLastFrame (i+1)


-- Returns: true when entire queue is blocked; false if property is disproven
blockEntireQueue :: PDRZ3 Bool
blockEntireQueue = do
  queue <- fmap prioQueue get
  if (Q.null queue)
  then do
  lg "Queue is empty, finished blocking step"
  return True
  else do
  t <- popMin
  lg $ "Blocking bad state: "++show t
  success <- blockBadState t
  lg $ "Blocking "++ if success then "succeeded" else "failed"
  --lg =<< fmap (show . prioQueue) get 
  if (not success)
  then return False
  else do
  blockEntireQueue

-- Returns: false if property was disproven, true if state was blocked (or delegated)
blockBadState :: TimedCube -> PDRZ3 Bool
blockBadState (TC s k) = do
  if k == 0
  then return False
  else do
  (res, maybeAssignment) <- consecutionQuery (TC s k)
  if (res == Sat)
  then do
    m <- generalise2 (fromJust maybeAssignment) (TC s k)
    lg $ "Found bad predecessor cube: " ++ show (TC m (k-1))
    mapM_ queueInsert [TC m (k-1), TC s k]
  else do
    lg "Bad cubed blocked."
    updateFrames (TC s k)
    n <- getMaxFrameIndex
    when (k < n) (queueInsert (TC s (k+1)))
  return True



-- Returns: true if property is proven (inductive invariant found),
--   false if another iteration is needed
forwardPropagation :: PDRZ3 Bool
forwardPropagation = do
  addNewFrame
  n <- getMaxFrameIndex
  lg $ "Entered forward propagation, n=" ++ (show n)
  isFixedPoints <- mapM forwardPropOneFrame [1..(n-1)]
  return $ or isFixedPoints

-- Precondition: k>1
-- Returns: true if the next frame is syntactically equal to the current one
--   after propagation
forwardPropOneFrame :: Int -> PDRZ3 Bool
forwardPropOneFrame k = do
  c <- get
  let frs = frames c
  let (Frame clauses) = frs!!k
  clausesToMove <- foldM try (S.empty) clauses
  let (Frame nextClauses) = frs!!(k+1)
      nextClauses' = S.union nextClauses clausesToMove
      newFrames = (take (k+1) frs) ++ [Frame nextClauses'] ++ (drop (k+2) frs)
  c <- get
  put c { frames = newFrames }
  return (newFrames!!k == newFrames!!(k+1))
 where try acc clause = do
        res <- tryForwardProp k clause
        let newAcc = (S.union (S.singleton clause) acc)
        return $ if res then newAcc else acc

tryForwardProp :: Int -> Clause -> PDRZ3 Bool
tryForwardProp k clause = do
  fr_k <- mkFrame k
  cl' <- mkClause (next clause)
  res <- zlocal $ do
   assert fr_k
   assert =<< mkNot cl'
   check
  return (res == Unsat) -- TODO: what about Undef?


unsafeStateQuery :: PDRZ3 (Result, Maybe Assignment)
unsafeStateQuery = do
  c <- get
  let p = prop c
  n <- getMaxFrameIndex
  f_n <- mkFrame n
  let (bvs, ivs) = getAllVars (system c)
  bv_asts <- mapM mkBoolVariable bvs
  iv_asts <- mapM mkIntVariable ivs
  (res, maybeVals) <- zlocal $ do
    assert =<< mkNot p
    assert f_n
    withModel $ \m ->
      evalBoolsAndInts m (bv_asts, iv_asts)
  let assignment = case maybeVals of (Nothing) -> Nothing
                                     (Just (maybeBools, maybeInts)) -> Just $
                                      A { bvs = maybeMap bvs maybeBools
                                        , ivs = maybeMap ivs maybeInts }
  --lg $ show assignment
  return (res, assignment)


evalBoolsAndInts :: Model -> ([AST],[AST]) -> Z3 ([Maybe Bool],[Maybe Integer])
evalBoolsAndInts m (as1,as2) = do
  maybes1 <- mapM (evalBool m) as1
  maybes2 <- mapM (evalInt m) as2
  return (maybes1, maybes2)


consecutionQuery :: TimedCube -> PDRZ3 (Result, Maybe Assignment)
consecutionQuery (TC ass k) = do
  lg $ "Consecution query: " ++ (show $ next ass) ++ " at " ++ (show k)
  c <- get
  let p = prop c
  s <- mkAssignment ass
  s' <- mkAssignment $ next ass
  -- TODO: use the substitution part of the trans relation
  -- Commented-out: bad cube (assignment) includes next-state variables as well
  t <- mkTransRelation
  f_kminus1 <- mkFrame (k-1)
  let (bvs, ivs) = getAllVars (system c)
      --(bvs', ivs') = (map next bvs, map next ivs)
      --(bvs'', ivs'') = (bvs++bvs', ivs++ivs')
  bv_asts <- mapM mkBoolVariable bvs --bvs''
  iv_asts <- mapM mkIntVariable ivs --ivs''
  -- Assertions and actual SAT check:
  (res, maybeVals) <- zlocal $ do
    assert =<< mkNot s
    assert s'
    assert f_kminus1
    withModel $ \m ->
      (evalBoolsAndInts m) (bv_asts, iv_asts)
  let maybeAss = case maybeVals of (Nothing) -> Nothing
                                   (Just (maybeBools, maybeInts)) -> Just $
                                    --A { bvs = maybeMap bvs'' maybeBools
                                    --  , ivs = maybeMap ivs'' maybeInts } 
                                    A { bvs = maybeMap bvs maybeBools
                                      , ivs = maybeMap ivs maybeInts } 
  lg $ show maybeAss
  return (res, maybeAss)

-- Generalising an assignment which breaks the safety property in F_N
generalise1 :: Assignment -> PDRZ3 Assignment
generalise1 a = do
  let vars = (map BV $ M.keys $ bvs a) ++ (map IV $ M.keys $ ivs a)
  c <- get
  let p = prop c
  n <- getMaxFrameIndex
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
   lg $ (show var) ++ (if redundant then " is " else " is not ") ++ "redundant"
   return $ if redundant then (removeVar ass var) else ass

-- Checks one literal to see if it can be removed from the assignment
checkLiteral :: Assignment -> Variable -> PDRZ3 Bool
checkLiteral a var = do
  -- Assume the modified assignment
  let pred =           PAnd $ [ P $ BLit v (if ((BV v)==var) then not b else b)
                              | (v,b) <- M.toList $ bvs a
                              ] ++
                              [ (if ((IV v)==var) then pnot else id) $
                                 P $ ILit Equals (IEVar v) (IEConst (n))
                              | (v,n) <- M.toList $ ivs a
                              ]
  ast <- mkPredicate pred
  res <- zlocal $ do
   assert ast
   check
  return (res == Unsat)


-- Generalising an assignment which breaks consecution of another property !s
-- (!s a clause based on the previously found bad cube s)
generalise2 :: Assignment -> TimedCube -> PDRZ3 Assignment
generalise2 a (TC ass k) = do
  let vars = (map BV $ M.keys $ bvs a) ++ (map IV $ M.keys $ ivs a)
  f_kminus1 <- mkFrame (k-1)
  s <- mkAssignment ass
  s' <- mkAssignment $ next ass
  -- TODO: change the mkTransRelation to use the substitution technique for
  --  integer variables.
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
   lg $ (show var) ++ (if redundant then " is " else " is not ") ++ "redundant"
   return $ if redundant then (removeVar ass var) else ass

addNewFrame :: PDRZ3 ()
addNewFrame = do
  c <- get
  put $ c {frames = (frames c) +++ emptyFrame}
  return ()

emptyFrame :: Frame
emptyFrame = Frame (S.empty)

getMaxFrameIndex :: PDRZ3 Int
getMaxFrameIndex = get >>= (return . (+ (-1)) . length . frames)


updateFrames :: TimedCube -> PDRZ3 ()
updateFrames (TC s k) = do
  let clause = invertAssignment s
  c <- get
  let newFrames = [ if (i > 0 && i <= k) then (addTo fr clause) else fr
                  | (fr,i) <- zip (frames c) [0..]
                  ]
  c <- get
  put $ c {frames = newFrames}
  lg $ "Updated frames: "
  lg $ show newFrames
 where addTo (Init p) cl = (Init p)
       addTo (Frame cls) cl =
         -- TODO: subsumption check
         Frame (S.union (S.singleton cl) cls)




data TimedCube = TC Assignment Int
 deriving ( Eq, Show )

instance Ord TimedCube where
 (TC a i) <= (TC b j) = i <= j


type PriorityQueue = Q.MinQueue TimedCube

priorityQueue :: TimedCube -> PriorityQueue
priorityQueue elem = Q.singleton elem

popMin :: PDRZ3 TimedCube
popMin = do
  c <- get
  let q = prioQueue c
      tc = Q.findMin q
      q' = Q.deleteMin q
  putQueue q'
  return tc

queueInsert :: TimedCube -> PDRZ3 ()
queueInsert tc = do
  queue <- fmap prioQueue get
  putQueue $ Q.insert tc queue
  return ()
  



-- Each clause is the negation of a (generalised) bad cube
data Frame = Init Predicate | Frame (S.Set Clause)
 deriving ( Eq, Ord, Show )

type Clause = [Literal]


----


data SMTContext
  = C
  { system :: System
  , predMap :: M.Map (Predicate) AST
  , intExprMap :: M.Map (IntExpr) AST
  , litMap :: M.Map (Literal) AST
  , varMap :: M.Map (Variable) AST
  , frames :: [Frame] -- replace with M.Map Int Frame?
  , prioQueue :: PriorityQueue
  , prop :: AST
  , pdrlog :: String
  }
 deriving ( Eq, Ord )
 
instance Show SMTContext where
  show c = unlines $
    [ "=== PDR CONTEXT ==="] ++
    --[ "SYSTEM:"] ++ indent
    --[ show system c ]
    [ "PREDICATES:"] ++ indent
    [ show p
    | (p,_) <- M.toList $ predMap c
    ] ++
    [ "INTEGER EXPR'S:"] ++ indent
    [ show ie
    | (ie,_) <- M.toList $ intExprMap c
    ] ++
    [ "LITERALS:"] ++ indent
    [ show l
    | (l,_) <- M.toList $ litMap c
    ] ++
    [ "VARIABLES:"] ++ indent
    [ show v
    | (v,_) <- M.toList $ varMap c
    ] ++
    [ "FRAMES:"] ++ indent
    [ show fr
    | fr <- frames c
    ] ++
    [ "PRIO-QUEUE:"] ++ indent
    [ show $ prioQueue c ]


emptyContext :: SMTContext
emptyContext = C { system = undefined
                 , predMap = M.empty
                 , intExprMap = M.empty
                 , litMap = M.empty
                 , varMap = M.empty
                 , frames = []
                 , prioQueue = Q.empty
                 , prop = undefined
                 , pdrlog = ""
                 }

putInitialSmtContext :: System -> PDRZ3 ()
putInitialSmtContext s = do
  p <- getProp s
  c <- get
  put $ c {system = s, prop = p, frames = [Init (System.init s), emptyFrame]} 
  return ()


putQueue :: PriorityQueue -> PDRZ3 ()
putQueue q = do
  c <- get
  put c {prioQueue = q}

getProp :: System -> PDRZ3 AST
getProp s = mkPredicate (safetyProp s)

lg :: String -> PDRZ3 ()
lg s = do
  c <- get
  put $ c { pdrlog = (pdrlog c) ++ s ++ "\n"}


------

-- k is the frame index
mkFrame :: Int -> PDRZ3 AST
mkFrame k = do
  c <- get
  let fr_k = (frames c) !! k
  case fr_k of
    (Init p) -> mkPredicate (p)
    (Frame cs) -> mkPredicate . PAnd . map clauseToPredicate . S.toList $ cs

clauseToPredicate :: Clause -> Predicate
clauseToPredicate lits = POr (map P lits)

mkPredicate :: Predicate -> PDRZ3 AST
mkPredicate p = do
  pm <- fmap predMap get
  let maybeAst = M.lookup p pm
  case maybeAst of (Just ast) -> do
                    return ast
                   (Nothing) -> do
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
  (z . mkAnd) =<< (mapM mkPredicate (PTop : ps))
mkPredicate' (POr ps) = do
  (z . mkOr) =<< (mapM mkPredicate (PNot PTop : ps))
mkPredicate' (PTop) = z $ mkTrue

mkLiteral :: Literal -> PDRZ3 AST
mkLiteral l = do
  lm <- fmap litMap get
  let maybeAst = M.lookup l lm
  case maybeAst of (Just ast) -> return ast
                   (Nothing) -> do
                     ast <- mkLiteral' l
                     let lm' = M.insert l ast lm
                     c <- get
                     put c {litMap = lm'}
                     return ast


mkLiteral' :: Literal -> PDRZ3 AST
mkLiteral' (BLit v b) = do
   v_ast <- mkBoolVariable v
   z $ if b then return v_ast else mkNot v_ast
mkLiteral' (ILit bp e1 e2) = do
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
                   (Nothing) -> do
                     ast <- mkIntExpr' ie
                     c <- get
                     let iem = intExprMap c
                     let iem' = M.insert ie ast iem
                     put c {intExprMap = iem'}
                     return ast
                   

mkIntExpr' :: IntExpr -> PDRZ3 AST
mkIntExpr' (IEConst n) = z $ mkIntNum n
mkIntExpr' (IEPlus ie1 ie2) = (z . mkAdd) =<< (mapM mkIntExpr [ie1, ie2])
mkIntExpr' (IEMinus ie1 ie2) = (z . mkSub) =<< (mapM mkIntExpr [ie1, ie2])
mkIntExpr' (IEVar v) = mkIntVariable v

mkBoolVariable :: BoolVariable -> PDRZ3 AST
mkBoolVariable v = do
  vm <- fmap varMap get
  let maybeAst = M.lookup (BV v) vm
  case maybeAst of (Just a) -> return a
                   (Nothing) -> do
                     ast <- mkVariable (BV v)
                     c <- get
                     let vm = varMap c
                     let vm' = M.insert (BV v) ast vm
                     put c {varMap = vm'}
                     return ast
  

mkIntVariable :: IntVariable -> PDRZ3 AST
mkIntVariable v = do
  vm <- fmap varMap get
  let maybeAst = M.lookup (IV v) vm
  case maybeAst of (Just ast) -> return ast
                   (Nothing) -> do
                     ast <- mkVariable (IV v)
                     c <- get
                     let vm = varMap c
                     let vm' = M.insert (IV v) ast vm
                     put c {varMap = vm'}
                     return ast


mkVariable :: Variable -> PDRZ3 AST
mkVariable (BV (BoolVar v)) = z $ mkFreshBoolVar (show v)
mkVariable (IV (IntVar v)) = z $ mkFreshIntVar (show v)


{--
mkVariable :: Variable -> PDRZ3 AST
mkVariable v = do
  vm <- fmap varMap get
  let maybeAst = M.lookup v vm
  case maybeAst of (Just ast) -> return ast
                   (Nothing) -> mkVariable' v
--}


mkAssignment :: Assignment -> PDRZ3 AST
mkAssignment a =
  mkPredicate $ assignmentToPred a

assignmentToPred :: Assignment -> Predicate
assignmentToPred a = PAnd $
  [ P $ BLit v b
  | (v,b) <- M.toList $ bvs a
  ] ++
  [ P $ ILit Equals (IEVar v) (IEConst (n))
  | (v,n) <- M.toList $ ivs a
  ]

invertAssignment :: Assignment -> Clause
invertAssignment a =
  [ BLit v (not b)
  | (v,b) <- M.toList $ bvs a
  ] ++
  [ ILit NEquals (IEVar v) (IEConst (n))
  | (v,n) <- M.toList $ ivs a
  ]


mkClause :: Clause -> PDRZ3 AST
mkClause = mkPredicate . PAnd . (map P)


mkTransRelation :: PDRZ3 AST
mkTransRelation = do
  trs <- fmap (trans . system) get
  let trans_pred = PAnd (map POr (map (map transRelationToPred) trs))
  mkPredicate trans_pred
 where transRelationToPred tr =
         PAnd $ [ System.guard tr
                , nextRelation tr
                , nextGuard tr
                ] ++ map intUpdateToPred (intUpdates tr)
       intUpdateToPred (var, ie) =
         P $ ILit Equals (next $ IEVar var) ie







testz = do
 v <- mkVariable (next $ BV $ BoolVar $ Var "foo")
 z $ assert v
 nv <- z $ mkNot v
 --z $ assert nv
 z check


-- TODO: look into lenses for updating c
