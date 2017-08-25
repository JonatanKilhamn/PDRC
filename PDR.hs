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

debug :: Bool
debug = False

debug_iter_bABSILF, debug_iter_oPL, debug_iter_bEQ :: Int
debug_iter_bABSILF = 5
debug_iter_oPL = 5
debug_iter_bEQ = 10


type PDRZ3 = StateT SMTContext Z3

z = lift
zlocal = z . local

runPdr :: System -> IO Bool
runPdr s = do
  (res, finalState) <- evalZ3 $ runStateT (pdr s) (emptyContext)
  putStr (pdrlog finalState)
  --putStr $ show finalState -- use when log is too long
  return res

pdr :: System -> PDRZ3 Bool
pdr s = do
  putInitialSmtContext s
  res <- outerPdrLoop 0 s
  c <- get
  lg (show c)
  return res


-- Input i :: Int is a DEBUG parameter, to force termination when it would
outerPdrLoop :: Int -> System -> PDRZ3 Bool
outerPdrLoop i s = do
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
  if (debug && i>=debug_iter_oPL)
  then do
  lg $ "DEBUG: breaking after " ++ show debug_iter_oPL ++ 
       " iteration of outerPdrLoop"
  return True
  else do
  outerPdrLoop (i+1) s


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
  success <- blockEntireQueue 0
  if (not success)
  then do
    lg $ "Failed to block; original bad state was " ++ (show assignment)
    return False
  else do
  if (debug && i>= debug_iter_bABSILF)
  then do
  lg $ "DEBUG: breaking after " ++ show debug_iter_bABSILF ++
       " iteration of bABSILF"
  return True
  else do
  blockAllBadStatesInLastFrame (i+1)

-- Input i :: Int is a DEBUG parameter, to force termination when it would
-- Returns: true when entire queue is blocked; false if property is disproven
blockEntireQueue :: Int -> PDRZ3 Bool
blockEntireQueue i = do
  queue <- fmap prioQueue get
  if (Q.null queue)
  then do
  lg "Queue is empty, finished blocking step"
  return True
  else do
  t <- popMin
  lg $ "Blocking bad state: "++show t
  success <- blockBadState t
  --lg $ "Blocking "++ if success then "succeeded" else "failed"
  --lg =<< fmap (show . prioQueue) get 
  if (not success)
  then return False
  else do
  if (debug && i>=debug_iter_bEQ)
  then do
  lg $ "DEBUG: breaking after " ++ show debug_iter_bEQ ++
       " iteration of bEQ"
  return True
  else do
  blockEntireQueue (i+1)

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
    lg $ "Found bad predecessor cube: " ++ show m ++ " at frame " ++ show (k-1)
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

-- Precondition: k>0
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
  return (res == Unsat)


unsafeStateQuery :: PDRZ3 (Result, Maybe Assignment)
unsafeStateQuery = do
  c <- get
  -- Context:
  not_p <- mkPredicate $ pnot $ prop c
  f_n <- mkFrame =<< getMaxFrameIndex
  context <- z $ mkAnd [ not_p
                       , f_n ]
  -- Variables and lits to extract from query:
  let (bvs, ivs) = getAllVars (system c)
  lits <- fmap (S.toList . interestingLits) get
  -- Query:
  (res, maybeAss) <- doQuery $
    Q { queryBoolVars = bvs
      , queryIntVars = ivs
      , queryLits = lits
      , queryContext = context }
  --lg $ show maybeAss
  return (res, maybeAss)


consecutionQuery :: TimedCube -> PDRZ3 (Result, Maybe Assignment)
consecutionQuery (TC ass k) = do
  lg $ "Consecution query: " ++ (show $ next ass) ++ " at " ++ (show k)
  c <- get
  -- Context:
  s <- mkAssignment ass
  not_s <- z $ mkNot s
  s' <- mkAssignment $ map next ass
  -- TODO: use the substitution part of the trans relation
  t <- mkTransRelation
  f_kminus1 <- mkFrame (k-1)
  context <- z $ mkAnd [ not_s
                       , s'
                       , f_kminus1
                       , t ]
  -- Variables and lits to extract from query:
  let (bvs, ivs) = getAllVars (system c)
  lits <- fmap (S.toList . interestingLits) get
  -- Query:
  (res, maybeAss) <- doQuery $
    Q { queryBoolVars = bvs
      , queryIntVars = ivs
      , queryLits = lits
      , queryContext = context }
  lg $ show maybeAss
  return (res, maybeAss)

data Query = Q { queryContext :: AST
               , queryBoolVars :: [BoolVariable]
               , queryIntVars :: [IntVariable]
               , queryLits :: [Literal] }
 deriving ( Eq, Show, Ord )

doQuery :: Query -> PDRZ3 (Result, Maybe Assignment)
doQuery q = do
  let bvs = queryBoolVars q
      ivs = queryIntVars q
      lits = queryLits q
  bv_asts <- mapM mkBoolVariable $ bvs
  iv_asts <- mapM mkIntVariable $ ivs
  lit_asts <- mapM mkLiteral $ lits
  -- Assertions and actual SAT check:
  (res, maybeVals) <- zlocal $ do
    assert $ queryContext q
    withModel $ \m -> do
      maybeBools <- mapM (evalBool m) bv_asts
      maybeInts <- mapM (evalInt m) iv_asts
      maybeLits <- mapM (evalBool m) lit_asts
      return (maybeBools, maybeInts, maybeLits)
  let maybeAss =
       case maybeVals of (Nothing) -> Nothing
                         (Just (maybeBools, maybeInts, maybeLits)) ->
                           Just $ [ BLit bv b
                                  | (bv, Just b) <- zip bvs maybeBools ] ++
                                  [ ILit Equals (IEVar iv) (IEConst i)
                                  | (iv, Just i) <- zip ivs maybeInts ] ++
                                  [ (if b then id else pnot) lit
                                  | (lit, Just b) <- zip lits maybeLits ]
  return (res, maybeAss)

evalBoolsAndInts :: Model -> ([AST],[AST]) -> Z3 ([Maybe Bool],[Maybe Integer])
evalBoolsAndInts m (as1,as2) = do
  maybes1 <- mapM (evalBool m) as1
  maybes2 <- mapM (evalInt m) as2
  return (maybes1, maybes2)



-- Generalising an assignment which breaks the safety property in F_N
generalise1 :: Assignment -> PDRZ3 Assignment
generalise1 a = do
  --let vars = (map BV $ M.keys $ bvs a) ++ (map IV $ M.keys $ ivs a)
  let a' = nub a
  c <- get
  p <- mkPredicate $ prop c
  n <- getMaxFrameIndex
  f_n <- mkFrame n
  -- Try the assignment once for each variable:
  --  f_n is the context (the generalised assignment must hold in f_n)
  --  p is the consequent (the generalised assignment + context should make
  --  p impossible)
  a' <- foldM (tryRemoveLiteral f_n p) a a
  return a'

-- Generalising an assignment which breaks consecution of another property !s
-- (!s a clause based on the previously found bad cube s)
generalise2 :: Assignment -> TimedCube -> PDRZ3 Assignment
generalise2 a (TC ass k) = do
  --let vars = (map BV $ M.keys $ bvs a) ++ (map IV $ M.keys $ ivs a)
  f_kminus1 <- mkFrame (k-1)
  s <- mkAssignment ass
  s' <- mkAssignment $ next ass
  -- TODO: change the mkTransRelation to use the substitution technique for
  --  integer variables.
  trans_kminus1 <- mkTransRelation
  -- Assume !s, frame, transition and !s'
  -- if satisfiable with one literal changed, that literal is necessary
  -- if unsatisfiable       -  |  |  -        that literal can be removed
  (context, consequent) <- z $ do
    not_s <- mkNot s
    c1 <- mkAnd [ not_s
                , f_kminus1
                , trans_kminus1 ]
                -- , not_s' ]
    c2 <- mkNot s'
    return (c1, c2)
  -- Try the assignment once for each variable:
  a' <- foldM (tryRemoveLiteral context consequent) a a
  return a'

tryRemoveLiteral :: AST -> AST -> Assignment -> Literal -> PDRZ3 Assignment
tryRemoveLiteral context consequent ass lit = do
   redundant <- shouldRemoveLiteral context consequent  ass lit
   lg $ (show lit) ++ (if redundant then " is " else " is not ") ++ "redundant"
   return $ if redundant then (delete lit ass) else ass

-- Checks one literal to see if it can be removed from the assignment
shouldRemoveLiteral :: AST -> AST -> Cube -> Literal -> PDRZ3 Bool
shouldRemoveLiteral context consequent cube lit = do
  -- Assume the modified assignment
  let modCube = [ (if (lit==l) then (pnot l) else l)
                | l <- cube ]
  ast <- mkCube modCube
  -- Assert the modified assignment:
  res <- zlocal $ do
   assert ast
   check
  if (res==Unsat)
  -- The modified assignment is not even internally consistent
  then return True
  else do
  -- Assert the context in which the original cube led to a bad outcome:
  res <- zlocal $ do
   assert context
   assert ast
   check
  if (res==Unsat)
  -- This literal is necessary for the assignment to function in the context
  then return False
  else do
  -- Assert the context and the good outcome, which is unreachable under the
  -- original cube:
  res <- zlocal $ do
   assert context
   assert consequent
   assert ast
   check  
  -- If it's still unreachable, then this literal is unecessary
  return (res==Unsat)





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
  lg $ "Updated frames: added "++ show clause++" to frames 1—"++show k
  --lg $ show newFrames
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
type Cube = [Literal]

type Assignment = Cube


----


data SMTContext
  = C
  { system :: System
  , predMap :: M.Map (Predicate) AST
  , intExprMap :: M.Map (IntExpr) AST
  , litMap :: M.Map (Literal) AST
  , interestingLits :: S.Set Literal
  , varMap :: M.Map (Variable) AST
  , frames :: [Frame] -- TODO: replace with M.Map Int Frame?
  , prioQueue :: PriorityQueue
  , prop :: Predicate
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
    [ "INTERESTING LITERALS:"] ++ indent
    [ show l
    | l <- S.toList $ interestingLits c
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
                 , interestingLits = S.empty
                 , frames = []
                 , prioQueue = Q.empty
                 , prop = undefined
                 , pdrlog = ""
                 }

putInitialSmtContext :: System -> PDRZ3 ()
putInitialSmtContext s = do
  c <- get
  put $ c {system = s, prop = safetyProp s, frames = [Init (System.init s), emptyFrame]} 
  return ()


putQueue :: PriorityQueue -> PDRZ3 ()
putQueue q = do
  c <- get
  put c {prioQueue = q}
 

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
mkLiteral' l@(ILit bp e1 e2) = do
 ast1 <- mkIntExpr e1
 ast2 <- mkIntExpr e2
 final_ast <- z $ (zfunction bp) ast1 ast2
 addInterestingLiteral l
 return final_ast 
  where zfunction Equals = mkEq
        zfunction NEquals = curry ((mkNot =<<) . (uncurry mkEq))
        zfunction LessThan = mkLt
        zfunction LessThanEq = mkLe
        zfunction GreaterThan = mkGt
        zfunction GreaterThanEq = mkGe


addInterestingLiteral :: Literal -> PDRZ3 ()
addInterestingLiteral l = do
 c <- get
 let existing = interestingLits c
     interesting = isInteresting l (system c)
     new = not (S.member l existing || S.member (pnot l) existing)
 if (new && interesting)
 then put $ c { interestingLits = S.insert l (interestingLits c) }
 else return ()


isInteresting :: Literal -> System -> Bool
isInteresting (BLit _ _) _ = False
isInteresting (ILit bp e1 e2) s = inequality && current && relevant
 where inequality = (not $ elem bp [Equals, NEquals])
       current = (isCurrent $ P $ ILit bp e1 e2)
       relevant = let vs = S.union (allVarsInExpr e1) (allVarsInExpr e2) in
                  let (_,ivs) = getAllVars s in
                  vs `S.isSubsetOf` S.fromList (map IV ivs)
       

{--
addBreakPoint :: Literal -> PDRZ3 ()
addBreakPoint (BLit _ _) _ = return ()
addBreakPoint (ILit bp e1 e2) s = inequality && current && relevant
 where inequality = (not $ elem bp [Equals, NEquals, GreaterThan, GreaterThanEq])
       current = (isCurrent $ P $ ILit bp e1 e2)
       relevant = let vs = S.union (allVarsInExpr e1) (allVarsInExpr e2) in
                  let (_,ivs) = getAllVars s in
                  vs `S.isSubsetOf` S.fromList (map IV ivs)
--}

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



mkAssignment :: Assignment -> PDRZ3 AST
mkAssignment = mkCube . assignmentToCube

-- TODO: change Cube and Clause to Sets instead of lists?
assignmentToCube :: Assignment -> Cube
assignmentToCube = id

invertAssignment :: Assignment -> Clause
invertAssignment = (map pnot) . assignmentToCube


mkClause :: Clause -> PDRZ3 AST
mkClause = mkPredicate . POr . (map P)

mkCube :: Cube -> PDRZ3 AST
mkCube = mkPredicate . PAnd . (map P)






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



-- TODO: look into lenses for updating c
