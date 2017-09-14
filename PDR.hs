module PDR where 

import Control.Applicative
import Control.Monad
import Data.Maybe
import Data.List
import Data.Ord
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

pdrlocal :: PDRZ3 a -> PDRZ3 a
pdrlocal m = do
 z push
 res <- m
 z $ pop 1
 return res

---- MAIN FUNCTIONS

runPdr :: System -> IO (Bool, SMTContext)
runPdr s = do
  (res, finalState) <- evalZ3 $ runStateT (pdr s) (emptyContext)
  --putStr (pdrlog finalState)
  return (res, finalState)

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


---- BLOCKING FUNCTIONS

-- Input i :: Int is a DEBUG parameter, to force termination when it would
--  otherwise run forever. To be removed as soon as the underlying issue is
--  fixed.
-- Returns: false if property is disproved, true if all states could be blocked
blockAllBadStatesInLastFrame :: Int -> PDRZ3 Bool
blockAllBadStatesInLastFrame i = do
  let setup = undefined -- some setup surely needed
  n <- getMaxFrameIndex
  (res, maybeCube) <- unsafeStateQuery
  if (res == Unsat) -- There is no unsafe state in F_n
  then do
    lg "All bad states blocked – no more unsafe states found at this depth"
    return True
  else do
  lg $ "Original bad cube: " ++ show (fromJust maybeCube)
  lg $ "Sorted: " ++ show (sortInterestingLits (fromJust maybeCube))
  assignment <- generalise1 (fromJust maybeCube)
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
  queue <- prioQueue <$> get
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
  (res, maybeCube) <- consecutionQuery (TC s k)
  if (res == Sat)
  then do
    m <- generalise2 (fromJust maybeCube) (TC s k)
    lg $ "Found bad predecessor cube: " ++ show m ++ " at frame " ++ show (k-1)
    mapM_ queueInsert [TC m (k-1), TC s k]
  else do
    lg $ "Bad cubed blocked: "++ show s
    updateFrames (TC s k)
    n <- getMaxFrameIndex
    when (k < n) (queueInsert (TC s (k+1)))
  return True


---- FORWARD PROPAGATION FUNCTIONS

-- Returns: true if property is proven (inductive invariant found),
--   false if another iteration is needed
forwardPropagation :: PDRZ3 Bool
forwardPropagation = do
  computeNewInterestingLiterals
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
  lg $ "Forward prop.: " ++ show newFrames
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

addNewFrame :: PDRZ3 ()
addNewFrame = do
  c <- get
  put $ c {frames = (frames c) +++ emptyFrame}
  return ()

updateFrames :: TimedCube -> PDRZ3 ()
updateFrames (TC s k) = do
  let clause = invertCube s
  c <- get
  newFrames <- sequence $
   [ if (i > 0 && i <= k) then (addTo fr clause) else return fr
   | (fr,i) <- zip (frames c) [0..]
   ]
  c <- get
  put $ c {frames = newFrames}
  lg $ "Updated frames: added "++ show clause++" to frames 1—"++show k
  lg $ show newFrames
 where addTo (Init p) cl = return (Init p)
       addTo (Frame cls) cl = do
        --lg $ "Checking subsumption when adding "++(show cl)++" to "++(show cls)
        cl_ast <- mkClause cl
        new_cls <- pdrlocal $ do
         z $ assert cl_ast
         foldM trySubsume [] (S.toList cls)
        return $ Frame (S.fromList $ cl : new_cls)
       trySubsume acc cand = do
        cand_ast <- mkClause cand
        res <- zlocal $ do
         assert =<< mkNot cand_ast
         check
        if (res==Sat)
        -- This clause should not be removed by subsumption
        then return $ cand : acc
        else do
        lg $ "Clause "++(show cand)++"removed by subsumption"
        return acc

computeNewInterestingLiterals :: PDRZ3 ()
computeNewInterestingLiterals = do
 ils <- (S.toList . interestingLits) <$> get
 updateSets <- (getUpdateSets . system) <$> get
 let newLits = allNewLits ils updateSets
 lg "Generating new interesting literals:"
 lg $ show newLits
 mapM addInterestingLiteral (map simplifyIntLit newLits)
 return ()
  where
   allNewLits ils udss = 
    [ foldl updateLiteral l uds
    | l <- ils
    , uds <- udss
    ]
   updateLiteral l@(BLit _ _) _ = l
   updateLiteral l@(ILit bp e1 e2) ud = ILit bp (updateIE e1 ud) (updateIE e2 ud)
   updateIE (IEVar v1) (v2,e2) | (v1 == v2) = e2
   updateIE (IEPlus e1 e2) ud = IEPlus (updateIE e1 ud) (updateIE e2 ud)
   updateIE (IEMinus e1 e2) ud = IEMinus (updateIE e1 ud) (updateIE e2 ud)
   updateIE e _ = e




---- SMT QUERY FUNCTIONS
-- Specifically, the two functions that handle queries "is there another bad state at this frame" and "can we reach this particular bad state through a 1-step transition"

unsafeStateQuery :: PDRZ3 (Result, Maybe Cube)
unsafeStateQuery = do
  c <- get
  -- Context:
  not_p <- mkPredicate $ pnot $ prop c
  f_n <- mkFrame =<< getMaxFrameIndex
  context <- z $ mkAnd [ not_p
                       , f_n ]
  -- Variables and lits to extract from query:
  let (bvs, ivs) = getAllVars (system c)
  lits <- (S.toList . interestingLits) <$> get
  -- Query:
  (res, maybeAss) <- doQuery $
    Q { queryBoolVars = bvs
      , queryIntVars = ivs
      , queryLits = lits
      , queryContext = context }
  --lg $ show maybeAss
  return (res, maybeAss)


consecutionQuery :: TimedCube -> PDRZ3 (Result, Maybe Cube)
consecutionQuery (TC ass k) = do
  --lg $ "Consecution query: " ++ (show $ next ass) ++ " at " ++ (show k)
  c <- get
  -- Context:
  s <- mkCube ass
  not_s <- z $ mkNot s
  s' <- mkCube $ map next ass
  t <- mkTransRelation
  f_kminus1 <- mkFrame (k-1)
  context <- z $ mkAnd [ not_s
                       , s'
                       , f_kminus1
                       , t ]
  -- Variables and lits to extract from query:
  let (bvs, ivs) = getAllVars (system c)
  litsUnsorted <- (S.toList . interestingLits) <$> get
  let lits = litsUnsorted --sortInterestingLits litsUnsorted
  -- Query:
  (res, maybeAss) <- doQuery $
    Q { queryBoolVars = bvs
      , queryIntVars = ivs
      , queryLits = lits
      , queryContext = context }
  --lg $ show maybeAss
  return (res, maybeAss)

data Query = Q { queryContext :: AST
               , queryBoolVars :: [BoolVariable]
               , queryIntVars :: [IntVariable]
               , queryLits :: [Literal] }
 deriving ( Eq, Show, Ord )

doQuery :: Query -> PDRZ3 (Result, Maybe Cube)
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
                                  (sortInterestingLits $
                                   [ (if b then id else pnot) lit
                                   | (lit, Just b) <- zip lits maybeLits ] )
  return (res, maybeAss)

evalBoolsAndInts :: Model -> ([AST],[AST]) -> Z3 ([Maybe Bool],[Maybe Integer])
evalBoolsAndInts m (as1,as2) = do
  maybes1 <- mapM (evalBool m) as1
  maybes2 <- mapM (evalInt m) as2
  return (maybes1, maybes2)



---- GENERALISATION FUNCTIONS

-- Generalising an assignment which breaks the safety property in F_N
generalise1 :: Cube -> PDRZ3 Cube
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
generalise2 :: Cube -> TimedCube -> PDRZ3 Cube
generalise2 a (TC ass k) = do
  --let vars = (map BV $ M.keys $ bvs a) ++ (map IV $ M.keys $ ivs a)
  f_kminus1 <- mkFrame (k-1)
  s <- mkCube ass
  s' <- mkCube $ next ass
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

tryRemoveLiteral :: AST -> AST -> Cube -> Literal -> PDRZ3 Cube
tryRemoveLiteral context consequent ass lit = do
   redundant <- shouldRemoveLiteral context consequent  ass lit
   --lg $ (show lit) ++ (if redundant then " is " else " is not ") ++ "redundant"
   return $ if redundant then (delete lit ass) else ass

-- Checks one literal to see if it can be removed from the assignment
shouldRemoveLiteral :: AST -> AST -> Cube -> Literal -> PDRZ3 Bool
shouldRemoveLiteral context consequent cube lit = do
  -- Assume the modified assignment
  let modCube = [ (if (lit==l) then (pnot l) else l)
                | l <- cube ]
  ast <- mkCube modCube
  -- Assert the modified assignment:
  z push
  z $ assert ast
  res <- z check
  if (res==Unsat)
  -- The modified assignment is not even internally consistent
  then do
   z $ pop 1
   return True
  else do
  -- Assert the context in which the original cube led to a bad outcome:
  z push
  z $ assert context
  res <- z check
  if (res==Unsat)
  -- This literal is necessary for the assignment to function in the context
  then do
   z $ pop 2
   return False
  else do
  -- Assert the context and the good outcome, which is unreachable under the
  -- original cube:
  z push
  z $ assert consequent
  res <- z check
  z $ pop 3
  -- If it's still unreachable, then this literal is unecessary
  return (res==Unsat)









data TimedCube = TC Cube Int
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
  queue <- prioQueue <$> get
  putQueue $ Q.insert tc queue
  return ()
  



-- Each clause is the negation of a (generalised) bad cube
data Frame = Init Predicate | Frame (S.Set Clause)
 deriving ( Eq, Ord, Show )

emptyFrame :: Frame
emptyFrame = Frame (S.empty)

getMaxFrameIndex :: PDRZ3 Int
getMaxFrameIndex = get >>= (return . (+ (-1)) . length . frames)



type Clause = [Literal]
type Cube = [Literal]



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
    | l <- sortInterestingLits $ S.toList $ interestingLits c
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
  pm <- predMap <$> get
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
  lm <- litMap <$> get
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
 addInterestingLiteral (simplifyIntLit l)
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


-- TODO: maybe change names ("interesting lits", "more constraining")
-- TODO: see if moreConstraining can be rewritten to be more succinct!
-- TODO: as a full generalisation, switch to recording breakpoints;
--  evaluating each of these literals by math rather than by withModel
sortInterestingLits :: [Literal] -> [Literal]
sortInterestingLits ls = sortInterestingLits' ls
 where sortInterestingLits' = reverse . (sortBy moreConstraining)

moreConstraining :: Literal -> Literal -> Ordering
moreConstraining (BLit _ _) _ = EQ
moreConstraining _ (BLit _ _) = EQ
moreConstraining (ILit Equals _ _) _ = GT
moreConstraining _ (ILit Equals _ _) = LT
moreConstraining (ILit LessThan _ (IEConst x)) (ILit LessThan _ (IEConst y)) = compare y x
moreConstraining (ILit LessThanEq _ (IEConst x)) (ILit LessThan _ (IEConst y)) = compare y (x+1)
moreConstraining (ILit LessThan _ (IEConst x)) (ILit LessThanEq _ (IEConst y)) = compare (y+1) x
moreConstraining (ILit LessThanEq _ (IEConst x)) (ILit LessThanEq _ (IEConst y)) = compare y x
moreConstraining (ILit GreaterThan _ (IEConst x)) (ILit GreaterThan _ (IEConst y)) = compare x y
moreConstraining (ILit GreaterThanEq _ (IEConst x)) (ILit GreaterThan _ (IEConst y)) = compare (x-1) y
moreConstraining (ILit GreaterThan _ (IEConst x)) (ILit GreaterThanEq _ (IEConst y)) = compare x (y-1)
moreConstraining (ILit GreaterThanEq _ (IEConst x)) (ILit GreaterThanEq _ (IEConst y)) = compare x y
moreConstraining (ILit LessThan _ _) (ILit GreaterThan _ _) = LT
moreConstraining (ILit LessThanEq _ _) (ILit GreaterThan _ _) = LT
moreConstraining (ILit LessThan _ _) (ILit GreaterThanEq _ _) = LT
moreConstraining (ILit LessThanEq _ _) (ILit GreaterThanEq _ _) = LT
moreConstraining (ILit GreaterThan  _ _) (ILit LessThan _ _) = GT
moreConstraining (ILit GreaterThan  _ _) (ILit LessThanEq _ _) = GT
moreConstraining (ILit GreaterThanEq  _ _) (ILit LessThan _ _) = GT
moreConstraining (ILit GreaterThanEq  _ _) (ILit LessThanEq _ _) = GT
moreConstraining _ _ = EQ





mkIntExpr :: IntExpr -> PDRZ3 AST
mkIntExpr ie = do
  iem <- intExprMap <$> get
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
  vm <- varMap <$> get
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
  vm <- varMap <$> get
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



-- TODO: change Cube and Clause to Sets instead of lists?

invertCube :: Cube -> Clause
invertCube = (map pnot)


mkClause :: Clause -> PDRZ3 AST
mkClause = mkPredicate . POr . (map P)

mkCube :: Cube -> PDRZ3 AST
mkCube = mkPredicate . PAnd . (map P)






mkTransRelation :: PDRZ3 AST
mkTransRelation = do
  trs <- (trans . system) <$> get
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
