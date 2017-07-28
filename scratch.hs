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