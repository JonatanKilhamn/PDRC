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
import Helpers

--------------------


-- Only unary-encoded integer-valued state variables so far
type Name = String

type Event = Name
type VarName = Name
-- Location names only need to be unique within the automaton
type Location = Name

iePlus :: IntExpr -> IntExpr -> IntExpr
iePlus (IEConst x) (IEConst y) = IEConst (x+y)
iePlus a b = IEPlus a b


data Domain
  = Domain
  { lower :: Integer
  , upper :: Integer
  , initial :: Integer
  }
  deriving ( Eq, Ord, Show )

-- TODO: current structure does not prohibit one automaton
-- from having several transitions from the same location,
-- firing on the same event – i.e. nondeterminism. In the
-- PDR algorithm, such systems would not behave correctly.
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
 deriving ( Eq, Ord )
  
instance Show Automaton where
  show aut = unlines $
    [ "NAME: " ++ autName aut ] ++
    [ "TRANSITIONS:"
    | not (null (transitions aut))
    ] ++ indent
    [ (show t)
    | t <- transitions aut
    ] ++
    [ "MARKED:"
    | not (null (marked aut))
    ] ++ indent
    [ show (l,p)
    | (l,p) <- marked aut
    ] ++
    [ "INITIAL: " ++ (show $ initialLocation aut)
    ] ++
    [ "UNCONTROLLABLE: " ++ (show $ S.toList $ uncontrollable aut)
    ]

data AutTransition =
  AT { start :: Location
     , end :: Location
     , formula :: TransitionRelation
     , event :: Event }
 deriving ( Eq, Ord )

instance Show AutTransition where
  show at = unlines $
    [ (start at) ++ " --(" ++ (event at) ++ ")-> " ++ (end at) ] ++ indent
    [ show (formula at) ]

data Synchronisation
  = Synch
  { automata :: S.Set Automaton
  , synchDomains :: M.Map IntVariable Domain
  , synchInits :: M.Map BoolVariable Bool
  , synchSafety :: Predicate
  }

instance Show Synchronisation where
  show synch = unlines $
    [ "=== SYNCHRONISATION ==="] ++
    [ "#AUTOMATA: " ++ (show $ length $ automata synch) ++ "\n"] ++
    [ "AUT. No "++ (show i) ++ " " ++ (show a)
    | (a,i) <- zip (S.toList $ automata synch) [1..]
    ] ++
    {--[ "ALL VARIABLES IN SYNCH: "
    | not (null (allVars synch))
    ] ++
    [ "  " ++ name ++ ": " ++ (show var)
    | (name, var) <- M.assocs $ allVars synch
    ] ++--}
    [ "ALL UNCONTROLLABLE EVENTS: "
    | not (null (getAllUncontrollable synch))
    ] ++ indent
    [ (show $ S.toList $ getAllUncontrollable synch) ] ++
    [ "SAFETY PROPERTY: "
    | not (synchSafety synch == PTop)
    ] ++ indent
    [ (show $ synchSafety synch)
    | not (synchSafety synch == PTop) ]
    


events :: Automaton -> S.Set Event
events a = S.fromList $ map event (transitions a)

allEvents :: Synchronisation -> S.Set Event
allEvents s = foldl S.union S.empty (S.map events $ automata s)

allLocations :: Synchronisation -> S.Set Location
allLocations s = foldl S.union S.empty (S.map locations $ automata s)

findAllVars :: Automaton -> S.Set Variable
findAllVars a = S.map makeCurrent $ S.union fromTrans fromMarked
 where fromTrans = S.unions (map fromTrans' (transitions a))
       fromTrans' at = fromTrans'' (formula at)
       fromTrans'' tr = S.unions [ (allVarsInPred $ guard tr)
                                 , (allVarsInPred $ nextGuard tr)
                                 , (allVarsInPred $ nextRelation tr)
                                 , S.fromList $
                                    (map IV) . (map fst) $
                                     intUpdates tr
                                 , S.unions $
                                    map (allVarsInExpr . snd) $
                                     intUpdates tr
                                 ]
       fromMarked = S.unions (map (allVarsInPred . snd) (marked a))

findBoolVars :: Automaton -> S.Set BoolVariable
findBoolVars = (S.map toBV) . (S.filter isBV) . findAllVars
 where toBV (BV v) = v

findIntVars :: Automaton -> S.Set IntVariable
findIntVars = (S.map toIV) . (S.filter isIV) . findAllVars
 where toIV (IV v) = v


{--
  = TR { guard :: Predicate
       , nextRelation :: Predicate
       , intUpdates :: [(IntVariable, IntExpr)]
       -- intUpdates should have the current variable, not next
       , nextGuard :: Predicate
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
  s { automata = S.insert a (automata s)
    , synchDomains = M.unionWith takeFirst (synchDomains s) (intDomains a)
    , synchInits = M.unionWith takeFirst (synchInits s) (boolInits a)
    , synchSafety = synchSafety s
    }
 where takeFirst a b = a
 -- not stable in order of synchronisation, in the case where
 -- two automata specify different domains for the same variable

setDefault :: (IntVariable, Integer) -> Synchronisation -> Synchronisation
setDefault (v, n) s =
  s {synchDomains = M.adjust (\d -> d {initial = n}) v (synchDomains s)
    }

setRangeMax :: (IntVariable, Integer) -> Synchronisation -> Synchronisation
setRangeMax (v, n) s =
  s {synchDomains = M.adjust (\d -> d {upper = n}) v (synchDomains s)
    }

setRangeMin :: (IntVariable, Integer) -> Synchronisation -> Synchronisation
setRangeMin (v, n) s =
  s {synchDomains = M.adjust (\d -> d {lower = n}) v (synchDomains s)
    }

setDomain :: (IntVariable, Domain) -> Synchronisation -> Synchronisation
setDomain (v, d) s = s {synchDomains = M.insert v d (synchDomains s)}


setDomains :: [(IntVariable, Domain)] -> Synchronisation -> Synchronisation
setDomains ds s = foldr (setDomain) s ds


emptySynch :: Synchronisation
emptySynch = Synch {automata = S.empty
                   , synchDomains = M.empty
                   , synchInits = M.empty
                   , synchSafety = PTop
                   }


setEventUncontrollable :: Event -> Synchronisation -> Synchronisation
setEventUncontrollable e s =
 s {automata = S.map (setUncontrollable (e,True)) (automata s)}

isEventUncontrollable :: Event -> Synchronisation -> Bool
isEventUncontrollable e =
 (elem e) . getAllUncontrollable

getAllUncontrollable :: Synchronisation -> S.Set Event
getAllUncontrollable =
 (foldr S.union S.empty) . (S.map uncontrollable) . automata

getBoolVariables :: Synchronisation -> S.Set BoolVariable
getBoolVariables synch = foldl S.union S.empty $
 S.insert (keySet $ synchInits synch) $
 S.map findBoolVars (automata synch)

getIntVariables :: Synchronisation -> S.Set IntVariable
getIntVariables synch = foldl S.union S.empty $
 S.insert (keySet $ synchDomains synch) $
 S.map findIntVars (automata synch)


synchToSystem :: Synchronisation -> System
synchToSystem synch = 
 S { boolVars = bVars
   , intVars = S.unions [ iVars
                        , locVars 
                        --, updatedByTrackers
                        --, S.singleton eventVar
                        ]
   , auxVars = S.unions [ S.map IV updatedByTrackers
                        , S.singleton (IV eventVar) ]
   , trans = S.toList $
      S.union (S.map makeTransRels (automata synch))
              (S.map makeUpdateTransRels allVars)
   , System.init = makeInit -- :: Predicate
   , safetyProp = (synchSafety synch)
   }
  where
   -- variable sets
   bVars = getBoolVariables synch
   iVars = getIntVariables synch
   allVars = S.foldl S.union S.empty $ S.map findAllVars $ automata synch
   locVars = S.map makeLocVar $ automata synch
   updatedByTrackers = S.map makeUpdatedByTracker allVars
   isUpdatedTrackers = S.map makeIsUpdatedTracker allVars
   -- helpers
   makeLocVar aut = IntVar $ Var $ (autName aut)++"_loc"
   makeIsUpdatedTracker v = BoolVar $ Var $ (varName v)++"_is_updated"
   makeUpdatedByTracker v = IntVar $ Var $ (varName v)++"_updated_by"
   eventVar = IntVar $ Var $ "event"
   eventIs ev =
    P $ ILit Equals (IEVar eventVar)
                    (IEConst (setIndex ev (allEvents synch)))
   locationIs aut loc =
    P $ ILit Equals (IEVar $ makeLocVar aut)
                    (IEConst (setIndex loc (locations aut)))
   -- A collection of transition relations corresponding to the actions
   -- available to one automaton
   makeTransRels aut =
    (map (makeTransRel' aut) (transitions aut)) ++ (allowInvisible aut)
   -- A "transition" added to each automaton to allow it to do nothing while
   -- another automaton executes local behaviour
   allowInvisible aut = map invisibleEventTR (S.toList $ eventsNotIn aut)
   invisibleEventTR ev = TR { guard = eventIs ev
                            , nextRelation = PTop
                            , intUpdates = []
                            , nextGuard = PTop }
   eventsNotIn aut = S.difference (allEvents synch) (events aut)
   -- The transition of an automaton, extended to include locations and events
   makeTransRel' aut at =
    (formula at) { guard =
                    PAnd $ [ guard (formula at)
                           , locationIs aut (start at)
                           , eventIs (event at)
                           ] ++
                           [ (if (isUpdated v at) then id else pnot) $
                              ivIs (makeUpdatedByTracker v)
                                   (setIndex aut (automata synch))
                           | v <- S.toList allVars ]
                 , intUpdates =
                    (intUpdates (formula at)) ++
                      [ ( makeLocVar aut
                        , IEConst (setIndex (end at) (locations aut)))
                      ]
                 }
   isUpdated v at = elem v (updatedVars (formula at))
   updatedVars tr = union
    (S.toList $ S.map makeCurrent $ allVarsInPred (nextGuard tr))
    (map (IV . fst) (intUpdates tr))
   -- The transition relations ensuring each variable is updated
   -- or keeps its value:
   makeUpdateTransRels v = [ makeHasUpdatedTR v
                           , makeHasNotUpdatedTR v ]
   makeHasUpdatedTR v =
     TR { guard = PAnd [ P $ ILit GreaterThanEq (IEVar $ makeUpdatedByTracker v)
                                                (IEConst 0)
                       , P $ ILit LessThan (IEVar $ makeUpdatedByTracker v)
                                           (IEConst $ fromIntegral $
                                             S.size (automata synch))
                       ]
        , nextRelation = PTop
        , intUpdates = []
        , nextGuard = PTop }
   makeHasNotUpdatedTR v =
     TR { guard = ivIs (makeUpdatedByTracker v) (-1)
        , nextRelation = case (v) of
                              (BV bv) -> POr [ PAnd [ bvIs bv True
                                                    , setTo bv True ]
                                             , PAnd [ bvIs bv False
                                                    , setTo bv False ]
                                             ]
                              _ -> PTop
        , intUpdates = case (v) of
                            (IV iv) -> [(iv,IEVar iv)]
                            _ -> []
        , nextGuard = PTop }
   -- The initial state of the system
   makeInit = PAnd $ initLocs ++ 
                     initBoolVars ++
                     initIntVars
   initLocs = map (uncurry locationIs) [ (a,initialLocation a)
                                       | a <- S.toList $ automata synch
                                       ]
   initBoolVars = [ P $ BLit bv b
                  | (bv,b) <- M.toList $ synchInits synch ]
   initIntVars =  [ P $ ILit Equals (IEVar iv) (IEConst $ initial d)
                  | (iv,d) <- M.toList $ synchDomains synch ]

-- TODO: perhaps include guards enforcing the integer variable domains?
   









