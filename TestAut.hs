module TestAut where

import Data.Maybe
import Control.Monad
import qualified Data.Set as S
import qualified Data.Map as M

import System
import Automata


--------------------------------------------------------------------------------
-- Defining the automata
--


autSynch :: Synchronisation
autSynch = (foldr synchronise emptySynch [testAutB, testAutA])

testAutA :: Automaton
testAutA = Aut { autName = "Aut1"
               , locations = S.fromList [locA, locB]
               , transitions = ts
               , marked = []
               , initialLocation = locA
               , uncontrollable = S.singleton "b"
               , autDomains = M.empty
               } 
 where
  ts = [ downA
       , upA
       , loopA
       ]
  downA =
   AT { start = locA
      , event = "a"
      , formula =
        TR { System.guard = PTop
           , nextRelation = PTop
           , intUpdates = [(Var "acounter", IntConst 0)]
           , nextGuard = PTop }
      , end = locB
      }
  upA = 
   AT { start = locB
      , event = "b"
      , formula =
        TR { System.guard = PTop
           , nextRelation = PTop
           , intUpdates = [(Var "acounter", IntConst 0)]
           , nextGuard = PTop }
      , end = locA
      }  
  loopA =
   AT { start = locB
      , event = "c"
      , formula =
        TR { System.guard =
               P (ILit Equals (IntVar $ Var "bcounter") (IntConst 1))
           , nextRelation = PTop
           , intUpdates = [(Var "acounter", IntConst 1)]
           , nextGuard = PTop }
      , end = locB
      }  
  locA = "A1"
  locB = "A2"
  
  

testAutB :: Automaton
testAutB = Aut { autName = "Aut2"
               , locations = S.fromList [locA, locB]
               , transitions = ts
               , marked = []
               , initialLocation = locA
               , uncontrollable = S.singleton "b"
               , autDomains = M.empty
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
           , intUpdates = [(Var "bcounter", IntConst 1)]
           , nextGuard = PTop }
      , end = locB
      }
  upB = 
   AT { start = locB
      , event = "b"
      , formula =
        TR { System.guard = PTop
           , nextRelation = PTop
           , intUpdates = [(Var "bcounter", IntConst 0)]
           , nextGuard = PTop }
      , end = locA
      }
  locA = "B1"
  locB = "B2"


