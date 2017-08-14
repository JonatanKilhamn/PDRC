module System where

import qualified Data.Set as Set
import qualified Data.Map as M
import Data.Function

type VariableName = String
data Variable = Var VariableName | Next Variable
 deriving (Eq, Show, Ord)

class Temporal a where
    next :: a -> a


instance Temporal Variable where
  next = Next

data Literal = BLit Variable Bool | ILit BinaryPred (IntExpr) (IntExpr)
 deriving (Eq, Show, Ord)

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
   deriving ( Eq, Show, Ord )

instance Temporal Predicate where
  next (P l) = P (next l)
  next (PNot p) = PNot (next p)
  next (PAnd ps) = PAnd (map next ps)
  next (POr ps) = POr (map next ps)
  
data IntExpr
 = IntConst Integer
 | Plus (IntExpr) (IntExpr)
 | Minus (IntExpr) (IntExpr)
 | IntVar Variable
  deriving ( Eq, Show, Ord)

instance Temporal IntExpr where
  next (IntVar v) = IntVar $ next v
  next (Plus ie1 ie2) = Plus (next ie1) (next ie2)
  next (Minus ie1 ie2) = Minus (next ie1) (next ie2)
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


data Assignment = A { bvs :: M.Map Variable Bool
                    , ivs :: M.Map Variable Integer
                    }

removeVar :: Assignment -> Variable -> Assignment
removeVar a v = a { bvs = M.delete v $ bvs a
                  , ivs = M.delete v $ ivs a }

instance Temporal Assignment where
  next a = a { bvs = updateKeys (bvs a) next
             , ivs = updateKeys (ivs a) next }

updateKeys :: (Ord k, Ord k2) => M.Map k v -> (k -> k2) -> M.Map k2 v
updateKeys m fun = M.fromList $ map (mapFst fun) $ M.toList m

mapFst :: (a -> b) -> (a, c) -> (b, c)
mapFst f (x,y) = (f x,y)


data System
  = S { boolVars :: Set.Set VariableName
      , intVars :: Set.Set VariableName
      , trans :: [TransitionRelation]
      , init :: Predicate
      , safetyProp :: Predicate
      }


getAllVars :: System -> ([Variable],[Variable])
getAllVars s = (map Var $ (Set.toList (boolVars s))
               , map Var $ (Set.toList (intVars s))
               )


data TransitionRelation
  = TR { guard :: Predicate
       , nextRelation :: Predicate
       , intUpdates :: [(Variable, IntExpr)]
       , nextGuard :: Predicate
       }

makeCurrent :: Variable -> VariableName
makeCurrent (Next v) = makeCurrent v
makeCurrent (Var vn) = vn

allVarsInPred :: Predicate -> Set.Set Variable
allVarsInPred (P lit) = allVarsInLit lit
allVarsInPred (PNot p) = allVarsInPred p
allVarsInPred (POr ps) = Set.unions $ map allVarsInPred ps
allVarsInPred (PAnd ps) = Set.unions $ map allVarsInPred ps

allVarsInLit :: Literal -> Set.Set Variable
allVarsInLit (BLit v _) = Set.singleton v
allVarsInLit (ILit _ e1 e2) = Set.unions $ map allVarsInExpr [e1, e2]

allVarsInExpr :: IntExpr -> Set.Set Variable
allVarsInExpr (IntConst i) = Set.empty
allVarsInExpr (IntVar v) = Set.singleton v
allVarsInExpr (Plus e1 e2) = Set.unions $ map allVarsInExpr [e1, e2]
allVarsInExpr (Minus e1 e2) = Set.unions $ map allVarsInExpr [e1, e2]

allVarsInTransRel :: TransitionRelation -> Set.Set Variable
allVarsInTransRel tr =
  Set.unions $ [ allVarsInPred (guard tr)
               , allVarsInPred (nextRelation tr)
               , Set.fromList $ map fst (intUpdates tr)
               , allVarsInPred (nextGuard tr)
               ] ++ map (allVarsInExpr . snd) (intUpdates tr)

isCurrent :: Predicate -> Bool
isCurrent p = let vs = (allVarsInPred p) in vs == (Set.map (Var . makeCurrent) vs)

isSat :: System -> Bool
isSat s = and [(length $ intVars s) == 0
              , Set.isSubsetOf transVarSet boolVarSet]
  where transVarSet = Set.map makeCurrent $ Set.unions $ map allVarsInTransRel $ trans s
        boolVarSet = boolVars s







