module Automata where

import Data.Maybe
import Data.Function
import qualified Data.Map as M
import Data.List
import qualified Control.Monad as C
import Control.Applicative
import qualified Data.Set as S
import Test.QuickCheck
import System

--------------------

ordNub :: (Ord a) => [a] -> [a]
ordNub l = go S.empty l
  where
    go _ [] = []
    go s (x:xs) = if x `S.member` s then go s xs
                                    else x : go (S.insert x s) xs

-- Only unary-encoded integer-valued state variables so far
type Name = String

type Event = Name
type VarName = Name
-- Location names only need to be unique within the automaton
type Location = Name

iePlus :: IntExpr -> IntExpr -> IntExpr
iePlus (IEConst x) (IEConst y) = IEConst (x+y)
iePlus a b = IEPlus a b

{--varNames :: IntExpr -> [VarName]
varNames (IntVar vn) = [vn]
varNames (Plus ie1 ie2) = union (varNames ie1) (varNames ie2)
varNames (Minus ie1 ie2) = union (varNames ie1) (varNames ie2)
varNames _ = []

guardVarName :: Guard -> VarName
guardVarName (GInt _ x _) = x
guardVarName (GNot g) = guardVarName g

guardVarNames :: Guard -> [VarName]
guardVarNames (GInt _ x exp) = union [x] (varNames exp)
guardVarNames (GNot g) = guardVarNames g
guardVarNames (GAnd gs) = foldl union [] (map guardVarNames gs)
guardVarNames (GOr gs) = foldl union [] (map guardVarNames gs)
guardVarNames Top = []
guardVarNames Bottom = []


updateVarName :: Update -> VarName
updateVarName (AssignInt x _) = x

updateVarNames :: Update -> [VarName]
updateVarNames (AssignInt x exp) = union [x] (varNames exp)
--}

data Domain
  = Domain
  { lower :: Int
  , upper :: Int
  , initial :: Int
  }
  deriving ( Eq )

-- TODO: current structure does not prohibit one automaton
-- from having several transitions from the same location,
-- firing on the same event – i.e. nondeterminism. In the
-- circuit translation, such a situation would be treated
-- as an error, when two transitions try to update the same
-- location variable. 
data Automaton
  = Aut
  { autName :: Name
  , locations :: S.Set Location
  , transitions :: [AutTransition]
  , marked :: [(Location, Predicate)]
  , initialLocation :: Location
  , uncontrollable :: S.Set Event
  , intDomains :: M.Map IntVariable Domain
  , boolInits :: M.Map BoolVariable Bool
  }
  
data AutTransition =
  AT { start :: Location
     , end :: Location
     , formula :: TransitionRelation
     , event :: Event }
 deriving ( Show, Eq )

instance Show Automaton where
  show aut = unlines $
    [ "NAME: " ++ autName aut ] ++
    [ "TRANSITIONS:"
    | not (null (transitions aut))
    ] ++
    [ "  " ++ (show t)
    | t <- transitions aut
    ] ++
    [ "MARKED:"
    | not (null (marked aut))
    ] ++
    [ "  " ++ show (l,p)
    | (l,p) <- marked aut
    ] ++
    [ "INITIAL: " ++ (show $ initialLocation aut)
    ] ++
    [ "UNCONTROLLABLE: " ++ (show $ uncontrollable aut)
    ]

data Synchronisation
  = Synch
  { automata :: [Automaton]
  , synchDomains :: M.Map IntVariable Domain
  , synchInits :: M.Map BoolVariable Bool
  }

instance Show Synchronisation where
  show synch = unlines $
    [ "=== SYNCHRONISATION ==="] ++
    [ "#AUTOMATA: " ++ (show $ length $ automata synch) ] ++
    [ "AUT. No "++ (show i) ++ " " ++ (show a)
    | (a,i) <- zip (automata synch) [1..]
    ] ++
    {--[ "ALL VARIABLES IN SYNCH: "
    | not (null (allVars synch))
    ] ++
    [ "  " ++ name ++ ": " ++ (show var)
    | (name, var) <- M.assocs $ allVars synch
    ] ++--}
    [ "UNCONTROLLABLE EVENTS: "
    | not (null (getAllUncontrollable synch))
    ] ++
    [ "  " ++ name
    | (name) <- S.toList $ getAllUncontrollable synch
    ]


events :: Automaton -> S.Set Event
events a = S.fromList $ map event (transitions a)

allEvents :: Synchronisation -> S.Set Event
allEvents s = foldl S.union S.empty (map events $ automata s)

allLocations :: Synchronisation -> S.Set Location
allLocations s = foldl S.union S.empty (map locations $ automata s)

{--
getAllVars :: Automaton -> M.Map VarName Variable
getAllVars a = M.fromList $ zip varNames (repeat unknownVar)
 where varNames = ordNub $ concat $ map varNames' (transitions a)
       varNames' t = concat $ (map guardVarNames (guards t)) ++ (map updateVarNames (updates t))
       unknownVar = Variable {lower = 0, upper = 3, initial = 0}
--}

setUncontrollable :: (Event, Bool) -> Automaton -> Automaton
setUncontrollable (e,b) aut =
 if b
 then aut { uncontrollable =
             if e `S.member` events aut
             then S.union (S.singleton e) (uncontrollable aut)
             else uncontrollable aut
          }
 else aut { uncontrollable = S.filter (/=e) (uncontrollable aut) }


synchronise :: Automaton -> Synchronisation -> Synchronisation
synchronise a s =
  s { automata = a:(automata s)
    , synchDomains = M.unionWith takeFirst (synchDomains s) (intDomains a)
    , synchInits = M.unionWith takeFirst (synchInits s) (boolInits a)
    }
 where takeFirst a b = a
 -- not stable in order of synchronisation, in the case where
 -- two automata specify different domains for the same variable

setDefault :: (IntVariable, Int) -> Synchronisation -> Synchronisation
setDefault (v, n) s =
  s {synchDomains = M.adjust (\d -> d {initial = n}) v (synchDomains s)
    }

setRangeMax :: (IntVariable, Int) -> Synchronisation -> Synchronisation
setRangeMax (v, n) s =
  s {synchDomains = M.adjust (\d -> d {upper = n}) v (synchDomains s)
    }

setRangeMin :: (IntVariable, Int) -> Synchronisation -> Synchronisation
setRangeMin (v, n) s =
  s {synchDomains = M.adjust (\d -> d {lower = n}) v (synchDomains s)
    }

setDomain :: (IntVariable, Domain) -> Synchronisation -> Synchronisation
setDomain (v, d) s = s {synchDomains = M.insert v d (synchDomains s)}


setDomains :: [(IntVariable, Domain)] -> Synchronisation -> Synchronisation
setDomains ds s = foldr (setDomain) s ds


emptySynch :: Synchronisation
emptySynch = Synch {automata = []
                   , synchDomains = M.empty
                   , synchInits = M.empty
                   --, synchLog = ""
                   }


setEventUncontrollable :: Event -> Synchronisation -> Synchronisation
setEventUncontrollable e s =
 s {automata = map (setUncontrollable (e,True)) (automata s)}

isEventUncontrollable :: Event -> Synchronisation -> Bool
isEventUncontrollable e =
 (elem e) . getAllUncontrollable

getAllUncontrollable :: Synchronisation -> S.Set Event
getAllUncontrollable =
 (foldr S.union S.empty) . (map uncontrollable) . automata



-- TODO
synchToSystem :: Synchronisation -> System
synchToSystem synch = undefined
 S { boolVars = bVars -- :: Set.Set VariableName
   , intVars = S.union iVars locVars -- :: Set.Set VariableName
   , trans = undefined -- :: [TransitionRelation]
   , System.init = undefined -- :: Predicate
   , safetyProp = PTop
   }
  where
   bVars = S.fromList $ M.keys $ synchInits synch
   iVars = undefined
   locVars = S.fromList $ map makeLocVar $ automata synch
   makeLocVar aut = IntVar $ Var $ (autName aut)++"_loc"
   --getLocNo aut n = elemAt n $ locations aut
   --findIndex loc (locations aut)
   
      







