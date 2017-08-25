-- Old PDR attempt

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




-- Z3 experimentation

script :: Z3 (Result, Maybe [Bool])
script = do
  l1 <- mkFreshBoolVar "l1"
  l2 <- mkFreshBoolVar "l2"
  l3 <- mkFreshBoolVar "l3"
  l4 <- mkFreshBoolVar "l4"
  nl1 <- mkNot l1
  nl2 <- mkNot l2
  cl1 <- mkAnd [l1, l2, l3]
  cl2 <- mkAnd [nl1, nl2]
  r1 <- mkAnd [cl1, cl2]
  assert =<< mkEq r1 =<< mkTrue
  result <- check
  if (result==Sat)
  then
   withModel $ \m ->
    catMaybes <$> mapM (evalBool m) [l1,l2,cl1]
  else
   return (result, Just [])

boolScript :: Z3 AST
boolScript = do
  l1 <- mkFreshBoolVar "l1"
  l2 <- mkFreshBoolVar "l2"
  l3 <- mkFreshBoolVar "l3"
  l4 <- mkFreshBoolVar "l4"
  nl1 <- mkNot l1
  nl2 <- mkNot l2
  cl1 <- mkAnd [l1, l2]
  cl2 <- mkOr [nl1, nl2]
  mkAnd [cl1, cl2]

{--mkClause :: SMTContext -> [String] -> Z3 AST
mkClause c lits = do
  mkOr $ catMaybes $ map ((flip M.lookup) c) lits
  
mkFrame :: SMTContext -> [String] -> Z3 AST
mkFrame c lits = do
  mkAnd $ catMaybes $ map ((flip M.lookup) c) lits


nameAST :: SMTContext -> String -> AST -> SMTContext
nameAST c s ast = M.insert s ast c

-- TODO: the STMContext could be monadic, combined with the Z3 monad

mkBoolLit :: SMTContext -> String -> Z3 SMTContext
mkBoolLit c s = do
  l1 <- mkFreshBoolVar s
  return $ M.insert s l1 c
--}

intScript :: Z3 ()
intScript = do
  q1 <- mkFreshIntVar "q1"
  q2 <- mkFreshIntVar "q2"
  _5 <- mkInteger 5
  assert =<< mkGt q1 =<< mkAdd [q2, _5]
  assert =<< mkGt q2 =<< mkInteger 0
  


main :: IO (Maybe [Bool])
main = do
 (res, mbools) <- evalZ3 script
 return mbools
 
 
 
 
 
 
 
 
 
 
 
 
-- Experimentation: trying out the unsat core
-- This was taken from generalise2, and was intended to replace the call
-- to tryRemoveLiteral.

  cube_asts <- mapM mkCubeLiteral a
  (res, core) <- zlocal $ do
   assert =<< mkNot s
   assert f_kminus1
   assert trans_kminus1
   assert =<< mkNot s'
   res <- solverCheckAssumptions cube_asts
   core <- solverGetUnsatCore
   return (res,core)
  let core_lits = (map ((M.!) (M.fromList (zip cube_asts a))) core)
  lg $ "EXPERIMENT: " ++ show res
  lg $ "Unsat_core is " ++ show core_lits
  return core_lits
 where mkCubeLiteral lit = do
        l <- mkLiteral lit
        x <- z $ do
         x <- mkFreshBoolVar (show lit)
         x' <- mkNot x
         l' <- mkNot l
         d_1 <- mkOr [x, l']
         d_2 <- mkOr [x', l]
         c_1 <- mkAnd [d_1, d_2]
         assert c_1
         return x
        return x
 
 