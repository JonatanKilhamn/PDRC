module TestAut2 where

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
  s { synchSafety = PAnd [pnot $ bvIs flag_b True] }

testAutA :: Automaton
testAutA = Aut { autName = "Aut1"
               , locations = S.fromList [locA, locB]
               , transitions = ts
               , marked = []
               , initialLocation = locA
               , uncontrollable = S.empty --S.singleton "b"
               , intDomains = M.empty
               , boolInits = M.fromList [(flag_a, False), (flag_b, False)]
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
        TR { System.guard = PTop
           , nextRelation = PTop
           , intUpdates = []
           , nextGuard = setTo flag_a True }
      , end = locB
      }
  upA = 
   AT { start = locB
      , event = "a"
      , formula =
        TR { System.guard = bvIs flag_a True
           , nextRelation = PTop
           , intUpdates = []
           , nextGuard = setTo flag_b True}
      , end = locA
      }  

  locA = "A1"
  locB = "A2"
 
flag_a, flag_b :: BoolVariable 
flag_a = BoolVar $ Var "flag_a"
flag_b = BoolVar $ Var "flag_b"

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
           , intUpdates = []
           , nextGuard = PTop }
      , end = locB
      }
  upB = 
   AT { start = locB
      , event = "b"
      , formula =
        TR { System.guard = PTop
           , nextRelation = PTop
           , intUpdates = []
           , nextGuard = PTop }
      , end = locA
      }
  locA = "B1"
  locB = "B2"


----
-- System

testSys :: System
testSys = synchToSystem testSynch
