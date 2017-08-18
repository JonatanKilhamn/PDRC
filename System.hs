module System where

import qualified Data.Set as Set
import qualified Data.Map as M
import Data.List


class Temporal a where
    next :: a -> a

data VariableName = Var String | Next VariableName
 deriving (Eq, Ord)

instance Show VariableName where
 show (Var s) = s
 show (Next v) = (show v)++"'"

data BoolVariable = BoolVar VariableName
 deriving (Eq, Ord)
instance Show BoolVariable where
 show (BoolVar bv) = show bv


data IntVariable = IntVar VariableName
 deriving (Eq, Ord)
instance Show IntVariable where
 show (IntVar vn) = show vn

data Variable = BV BoolVariable | IV IntVariable
 deriving (Eq, Ord)
instance Show Variable where
 show (BV bv) = show bv
 show (IV iv) = show iv


instance Temporal VariableName where
  next = Next

instance Temporal BoolVariable where
  next (BoolVar vn) = BoolVar $ next vn
instance Temporal IntVariable where
  next (IntVar vn) = IntVar $ next vn
instance Temporal Variable where
  next (BV bv) = BV $ next bv
  next (IV iv) = IV $ next iv

data Literal = BLit BoolVariable Bool | ILit BinaryPred (IntExpr) (IntExpr)
 deriving (Eq, Ord)
instance Show Literal where
 show (BLit bv b) = if b then (show bv) else "~"++show bv
 show (ILit bp ie1 ie2) = show ie1 ++ show bp ++ show ie2

instance Temporal Literal where
  next (BLit v b) = BLit (next v) b
  next (ILit bp ie1 ie2) = ILit bp (next ie1) (next ie2)

instance (Temporal a) => Temporal [a] where
  next = map next


data Predicate
  = P Literal
  | PNot (Predicate)
  | PAnd [Predicate]
  | POr [Predicate]
  | PTop
   deriving ( Eq, Ord )
instance Show Predicate where
 show (P l) = show l
 show (PNot p) = "~("++show p++")"
 show (PAnd ps) = intercalate " ^ " (map show ps)
 show (POr ps) = intercalate " v " (map show ps)
 show (PTop) = "T"

instance Temporal Predicate where
  next (P l) = P (next l)
  next (PNot p) = PNot (next p)
  next (PAnd ps) = PAnd (map next ps)
  next (POr ps) = POr (map next ps)
  
data IntExpr
 = IEConst Integer
 | IEPlus (IntExpr) (IntExpr)
 | IEMinus (IntExpr) (IntExpr)
 | IEVar IntVariable
  deriving ( Eq, Ord)

instance Show IntExpr where
 show (IEConst i) = show i
 show (IEPlus ie1 ie2) = show ie1 ++ " + " ++ show ie2
 show (IEMinus ie1 ie2) = show ie1 ++ " - " ++ show ie2
 show (IEVar iv) = show iv
  

instance Temporal IntExpr where
  next (IEVar iv) = IEVar $ next iv
  next (IEPlus ie1 ie2) = IEPlus (next ie1) (next ie2)
  next (IEMinus ie1 ie2) = IEMinus (next ie1) (next ie2)
  next ie = ie
    
data BinaryPred
 = Equals
 | NEquals
 | LessThan
 | LessThanEq
 | GreaterThan
 | GreaterThanEq
  deriving ( Eq, Ord )

instance Show BinaryPred where
 show Equals = "=="
 show NEquals = "/="
 show LessThan = "<"
 show LessThanEq = "<="
 show GreaterThan = ">"
 show GreaterThanEq = ">="

pnot :: Predicate -> Predicate
pnot (PNot p) = p
pnot (PAnd ps) = POr (map pnot ps)
pnot (POr ps) = PAnd (map pnot ps)
pnot p = PNot p


data Assignment = A { bvs :: M.Map BoolVariable Bool
                    , ivs :: M.Map IntVariable Integer
                    }
 deriving ( Eq, Show )

removeVar :: Assignment -> Variable -> Assignment
removeVar a (BV bv) = a { bvs = M.delete bv $ bvs a }
removeVar a (IV iv) = a { ivs = M.delete iv $ ivs a }

instance Temporal Assignment where
  next a = a { bvs = updateKeys (bvs a) next
             , ivs = updateKeys (ivs a) next }

updateKeys :: (Ord k, Ord k2) => M.Map k v -> (k -> k2) -> M.Map k2 v
updateKeys m fun = M.fromList $ map (mapFst fun) $ M.toList m

mapFst :: (a -> b) -> (a, c) -> (b, c)
mapFst f (x,y) = (f x,y)


data System
  = S { boolVars :: Set.Set BoolVariable
      , intVars :: Set.Set IntVariable
      , trans :: [[TransitionRelation]]
      -- one transition relation out of each set must be true
      -- i.e. this list of lists represents a conjunction of disjunctions
      , init :: Predicate
      , safetyProp :: Predicate
      }
 deriving (Show, Eq, Ord)


getAllVars :: System -> ([BoolVariable],[IntVariable])
getAllVars s = ( Set.toList (boolVars s)
               , Set.toList (intVars s)
               )


data TransitionRelation
  = TR { guard :: Predicate
       , nextRelation :: Predicate
       , intUpdates :: [(IntVariable, IntExpr)]
       -- intUpdates should have the current variable, not next
       , nextGuard :: Predicate
       }
 deriving ( Eq, Ord )
 
instance Show TransitionRelation where
  show tr = let g = guard tr
                nr = nextRelation tr
                ng = nextGuard tr
                iu = intUpdates tr
   in unlines $
    [ show g | not (g == PTop)
    ] ++
    [ show nr | not (nr == PTop)
    ] ++
    [ (show iv) ++ "' := " ++ (show ie)
    | (iv, ie) <- iu
    ] ++
    [ show ng | not (ng == PTop)
    ]
    
    
makeCurrent :: Variable -> Variable
makeCurrent (IV (IntVar v)) = (IV . IntVar) $ makeCurrent' v
makeCurrent (BV (BoolVar v)) = (BV . BoolVar) $ makeCurrent' v

makeCurrent' :: VariableName -> VariableName
makeCurrent' (Next v) = makeCurrent' v
makeCurrent' (Var vn) = Var vn

allVarsInPred :: Predicate -> Set.Set Variable
allVarsInPred (P lit) = allVarsInLit lit
allVarsInPred (PNot p) = allVarsInPred p
allVarsInPred (POr ps) = Set.unions $ map allVarsInPred ps
allVarsInPred (PAnd ps) = Set.unions $ map allVarsInPred ps

allVarsInLit :: Literal -> Set.Set Variable
allVarsInLit (BLit bv _) = Set.singleton (BV bv)
allVarsInLit (ILit _ e1 e2) = Set.unions $ map allVarsInExpr [e1, e2]

allVarsInExpr :: IntExpr -> Set.Set Variable
allVarsInExpr (IEConst i) = Set.empty
allVarsInExpr (IEVar iv) = Set.singleton (IV iv)
allVarsInExpr (IEPlus e1 e2) = Set.unions $ map allVarsInExpr [e1, e2]
allVarsInExpr (IEMinus e1 e2) = Set.unions $ map allVarsInExpr [e1, e2]

allVarsInTransRel :: TransitionRelation -> Set.Set Variable
allVarsInTransRel tr =
  Set.unions $ [ allVarsInPred (guard tr)
               , allVarsInPred (nextRelation tr)
               , Set.fromList $ map (IV . fst) (intUpdates tr)
               , allVarsInPred (nextGuard tr)
               ] ++ map (allVarsInExpr . snd) (intUpdates tr)

isCurrent :: Predicate -> Bool
isCurrent p = let vs = (allVarsInPred p) in vs == (Set.map makeCurrent vs)

isSat :: System -> Bool
isSat s = and [(length $ intVars s) == 0
              , Set.isSubsetOf transVarSet boolVarSet]
  where transVarSet = Set.map makeCurrent $ Set.unions $ map allVarsInTransRel $ concat $ trans s
        boolVarSet = Set.map BV $ boolVars s







