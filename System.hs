module System where

import qualified Data.Set as Set
import Data.Function

type VariableName = String
data Variable = Var VariableName | Next Variable
 deriving (Eq, Show, Ord)

data Literal = BLit Variable | ILit BinaryPred (IntExpr) (IntExpr)

data Predicate
  = P Literal
  | PNot (Predicate)
  | PAnd [Predicate]
  | POr [Predicate]

data IntExpr
 = IntConst Int
 | Plus (IntExpr) (IntExpr)
 | Minus (IntExpr) (IntExpr)
 | IntVar Variable
  deriving ( Eq, Show )

data BinaryPred
 = Equals
 | NEquals
 | LessThan
 | LessThanEq
 | GreaterThan
 | GreaterThanEq
  deriving ( Eq )

instance Show BinaryPred where
 show Equals = "=="
 show NEquals = "/="
 show LessThan = "<"
 show LessThanEq = "<="
 show GreaterThan = ">"
 show GreaterThanEq = ">="

pnot :: Predicate -> Predicate
pnot (PNot p) = p
pnot p = PNot p

data System
  = S { boolVars :: Set.Set VariableName
      , intVars :: Set.Set VariableName
      , trans :: [TransitionRelation]
      , init :: Predicate
      , safetyProp :: Predicate
      }

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
allVarsInLit (BLit v) = Set.singleton v
allVarsInLit (ILit bp e1 e2) = Set.unions $ map allVarsInExpr [e1, e2]

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







