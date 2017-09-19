module PhilosophersParsed where

import System
import Automata
import WmodParser
import Data.Maybe
import Control.Monad
import qualified Data.Set as S

-- Dining philosophers





--------------------------------------------------------------------------------
-- Defining the automata


-- possible values of nbrPhils: 5, 10
nbrPhils :: Int
nbrPhils = 5

-- possible values of nbrSteps: 10, 50, 100, 200, 500, 1000
nbrSteps :: Int
nbrSteps = 10

fileNameI :: Int -> Int -> FilePath
fileNameI i j = "examples/EDP" ++ (show i) ++ "_"++ (show j) ++ ".wmod"

fileName :: FilePath
fileName = fileNameI nbrPhils nbrSteps

philSynch :: IO Synchronisation
philSynch = readWmodFile fileName

--------------------------------------------------------------------------------
-- Circuits


main :: IO System
main = 
 do
  sc <- philSynch
  let system = synchToSystem sc
  --writeCircuit ("Examples/phils"++ (show nbrPhils) ++ "_"++ (show nbrSteps)) circ
  --return circ
  return system

