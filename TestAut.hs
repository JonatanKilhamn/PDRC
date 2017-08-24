module TestAut where

import Data.Maybe
import Control.Monad
import qualified Data.Set as S
import qualified Data.Map as M

import System
import Automata
import PDR

--------------------------------------------------------------------------------
-- Defining the automata
--


testSynch :: Synchronisation
--autSynch = let s = (foldr synchronise emptySynch [testAutB, testAutA]) in
testSynch = let s = (foldr synchronise emptySynch [testAutA]) in
  s { synchSafety = POr [ P $ ILit LessThan (IEVar $ acounter) (IEConst 10)
                        , P $ ILit GreaterThan (IEVar $ acounter) (IEConst 13)
                        ] }

testAutA :: Automaton
testAutA = Aut { autName = "Aut1"
               , locations = S.fromList [locA, locB]
               , transitions = ts
               , marked = []
               , initialLocation = locA
               , uncontrollable = S.empty --S.singleton "b"
               , intDomains = doms
               , boolInits = M.empty
               } 
 where
  ts = [ downA
       , upA
       --, loopA
       ]
  downA =
   AT { start = locA
      , event = "a"
      , formula =
        TR { System.guard = PAnd [ P $ ILit LessThan (IEVar $ acounter) (IEConst 2)
                                 , P $ ILit GreaterThanEq (IEVar $ acounter) (IEConst 0)
                                 ]
           , nextRelation = PTop
           , intUpdates = [(acounter, IEPlus (IEVar acounter) (IEConst 1))]
           , nextGuard = PTop }
      , end = locB
      }
  upA = 
   AT { start = locB
      , event = "b"
      , formula =
        TR { System.guard = P $ ILit GreaterThanEq (IEVar $ acounter) (IEConst 0)
           , nextRelation = PTop
           , intUpdates = [(acounter, IEPlus (IEVar acounter) (IEConst 1))]
           , nextGuard = PTop }
      , end = locA
      }  
{--  loopA =
   AT { start = locB
      , event = "c"
      , formula =
        TR { System.guard =
               P (ILit Equals (IEVar $ bcounter) (IEConst 1))
           , nextRelation = PTop
           , intUpdates = [(acounter, IEConst 1)]
           , nextGuard = PTop }
      , end = locB
      }  
      --}
  locA = "A1"
  locB = "A2"
  doms = M.fromList [ (acounter, Domain { initial = 0, lower=0,upper=100})
                    --, (bcounter, Domain { initial = 0, lower=0,upper=100})
                    ]
 
acounter, bcounter :: IntVariable 
acounter = IntVar $ Var "acounter"
bcounter = IntVar $ Var "bcounter"
  

testAutB :: Automaton
testAutB = Aut { autName = "Aut2"
               , locations = S.fromList [locA, locB]
               , transitions = ts
               , marked = []
               , initialLocation = locA
               , uncontrollable = S.singleton "b"
               , intDomains = M.empty
               , boolInits = M.empty
               } 
 where
  ts = [ downB
       , upB
       ]
  downB =
   AT { start = locA
      , event = "b"
      , formula =
        TR { System.guard = PTop
           , nextRelation = PTop
           , intUpdates = [(bcounter, IEConst 1)]
           , nextGuard = PTop }
      , end = locB
      }
  upB = 
   AT { start = locB
      , event = "b"
      , formula =
        TR { System.guard = PTop
           , nextRelation = PTop
           , intUpdates = [(bcounter, IEConst 0)]
           , nextGuard = PTop }
      , end = locA
      }
  locA = "B1"
  locB = "B2"


----
-- System

testSys :: System
testSys = synchToSystem testSynch
