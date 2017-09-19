module WmodParser where

import Text.XML.Light
import System.IO
import qualified Data.Set as S
import Control.Monad
import Data.List
import Data.Maybe
import qualified Data.Map as M

import Automata
import System

readWmodFile :: FilePath -> IO Synchronisation
readWmodFile fp =
 do
  s <- readFile fp
  let xmlCont = parseXML s
  case (parseWmodXml xmlCont) of
       (Just s) -> return s
       (Nothing) -> return emptySynch

main :: IO Synchronisation
main = readWmodFile
       "examples/EDP5_10.wmod"
       --"Examples/simple_selfloop.wmod"
       --"Examples/cat_mouse.wmod"

debug :: IO String
debug = readFile "Examples/test_foo.wmod"



elemName :: String -> Content -> Bool
elemName s (Elem e) = (qName $ elName e) == s
elemName _ _        = False

getElem :: Content -> Maybe Element
getElem (Elem e) = return e
getElem _        = Nothing

getElemName :: Element -> String
getElemName = qName . elName



parseWmodXml :: [Content] -> Maybe Synchronisation
parseWmodXml cs =
 do
   cl <- firstOccurrence (elemName "ComponentList") getElem cs
   let scConts = filter (elemName "SimpleComponent") (elContent cl)
       scElems = mapMaybe getElem scConts
   auts <- mapM parseAutomaton scElems
   let synch = foldr synchronise emptySynch auts
   
   -- make some transitions uncontrollable
   edl <- firstOccurrence (elemName "EventDeclList") getElem cs
   let edConts = filter (elemName "EventDecl") (elContent edl)
       edElems = mapMaybe getElem edConts
       uncontEvents = mapMaybe (getAttribute "Name") $
                      filter isUncontrollable edElems
   let synch1 = foldr setEventUncontrollable synch uncontEvents
   
   -- handle variables
   let vcConts = filter (elemName "VariableComponent") (elContent cl)
       vcElems = mapMaybe getElem vcConts
   -- set initial values of variables
   synch2 <- foldM setVarInitAndRange synch1 vcElems
   
   return synch2
   



parseAutomaton :: Element -> Maybe Automaton
parseAutomaton e
 | getElemName e /= "SimpleComponent" = Nothing
 | otherwise =
  do
   -- Automaton name
   aName <- getAttribute "Name" e

   graph <- firstOccurrence (elemName "Graph") getElem (elContent e)
   
   -- Locations
   nodeList <- firstOccurrence (elemName "NodeList") getElem (elContent graph)
   (locs, initLoc) <- parseLocations nodeList
   
   -- Transitions
   edgeList <- firstOccurrence (elemName "EdgeList") getElem (elContent graph)
   transitions <- parseTransitions edgeList
   
   -- Marked / forbidden states
   acceptingPredicates <- parseAccepting nodeList
   
   return Aut { autName = aName
              , locations = locs
              , transitions = transitions -- :: [AutTransition]
              , marked = acceptingPredicates
              , initialLocation = initLoc -- :: Location
              , uncontrollable = S.empty
              , intDomains = M.empty
              , boolInits = M.empty
              }

parseLocations :: Element -> Maybe (S.Set Location, Location)
parseLocations e
 | getElemName e /= "NodeList" = Nothing
 | otherwise =
  do
   let nodes = mapMaybe getElem $ filter (elemName "SimpleNode") (elContent e)
       locations = mapMaybe (getAttribute "Name") nodes
   initLoc <- findInXml isInitial (getAttribute "Name") nodes
   return (S.fromList locations, initLoc)

parseAccepting :: Element -> Maybe [(Location, Predicate)]
parseAccepting e
 | getElemName e /= "NodeList" = Nothing
 | otherwise =
  do
   let nodes = mapMaybe getElem $ filter (elemName "SimpleNode") (elContent e)
       acceptingNames = findAllInXml isAccepting (getAttribute "Name") nodes
   return $ zip acceptingNames (repeat PTop)

parseTransitions :: Element -> Maybe [AutTransition]
parseTransitions e
 | getElemName e /= "EdgeList" = Nothing
 | otherwise =
  do
   let edges = mapMaybe getElem $ filter (elemName "Edge") (elContent e)
       transitions = concat $ mapMaybe parseTransition edges
   return transitions
 where getTwoAttributes = flip $ double . (flip getAttribute)


parseTransition :: Element -> Maybe [AutTransition]
parseTransition e
 | getElemName e /= "Edge" = Nothing
 | otherwise =
  do
   from <- getAttribute "Source" e
   to <- getAttribute "Target" e
   labelBlock <- firstOccurrence (elemName "LabelBlock") getElem (elContent e)
   let ids = mapMaybe getElem $ filter (elemName "SimpleIdentifier")
                                       (elContent labelBlock)
       names = mapMaybe (getAttribute "Name") ids
       
   -- handle guards:
   
   let gb = firstOccurrence (elemName "Guards") getElem (elContent e)
       gs =
        case (gb) of
             (Nothing) -> []
             (Just guardBlock) ->
              let guardExprElems = mapMaybe getElem (elContent guardBlock) in
              mapMaybe (exprToGuard <=< parseExpr) guardExprElems
   
   -- handle updates:
   
   let ub = firstOccurrence (elemName "Actions") getElem (elContent e)
       uds =
        case (ub) of
             (Nothing) -> []
             (Just updateBlock) ->
              let updateExprElems = mapMaybe getElem (elContent updateBlock) in
              mapMaybe (exprToUpdate <=< parseExpr) updateExprElems
   let form = TR { System.guard = PAnd gs
                 , nextRelation = PTop
                 , intUpdates = uds
                 , nextGuard = PTop
                 }
   return [ AT { start = from
               , end = to
               , event = name
               , formula = form
               --, uncontrollable = False
               }
          | name <- names ]


double :: (a -> Maybe b) -> (a,a) -> Maybe (b,b)
double fun (x,y) =
 do
  f <- fun x
  g <- fun y
  return (f,g)


getAttribute :: String -> Element -> Maybe String
getAttribute s e =
 do
  attr <- find (\a -> (qName $ attrKey a) == s) (elAttribs e)
  return $ attrVal attr


isInitial :: Element -> Bool
isInitial = hasAttrVal "Initial" "true"

isAccepting :: Element -> Bool
isAccepting e = isJust $ firstOccurrence isAccCont Just (elContent e)
 where isAccCont c = (fmap (hasAttrVal "Name" ":accepting") (getElem c)) == (Just True)


hasAttrVal :: String -> String -> Element -> Bool
hasAttrVal attr val e = (getAttribute attr e) == (Just val)



isUncontrollable :: Element -> Bool
isUncontrollable = hasAttrVal "Kind" "UNCONTROLLABLE"



{-
filterXmlContent :: String -> [Content] -> [Element]
filterXmlContent s cs = mapMaybe getElem $ filter (elemName s) cs
-}

findInXml :: (a -> Bool) -> (a -> Maybe b) -> [a] ->
  Maybe b
findInXml pred fun cs = find pred cs >>= fun

findAllInXml :: (a -> Bool) -> (a -> Maybe b) -> [a] -> [b]
findAllInXml pred fun cs = mapMaybe fun (filter pred cs)

firstOccurrence :: (Content -> Bool) -> (Content -> Maybe a) -> [Content] ->
  Maybe a
firstOccurrence a b cs = findInXml a b (flattenContent cs)


flattenContent :: [Content] -> [Content]
flattenContent = foldr expandAndAdd []
 where
  expandAndAdd (Elem e) rest = (Elem e) : (flattenContent (elContent e)) ++ rest
  expandAndAdd _        rest = rest


exprToGuard :: Expr -> Maybe Predicate
exprToGuard (UO OpNot e1) = do
 p1 <- exprToGuard e1
 return $ pnot p1
exprToGuard (BO OpAnd e1 e2) = do
 p1 <- exprToGuard e1
 p2 <- exprToGuard e2
 return $ PAnd [p1, p2]
exprToGuard (BO OpOr e1 e2) = do
 p1 <- exprToGuard e1
 p2 <- exprToGuard e2
 return $ POr [p1, p2]
exprToGuard (BO op (VName x) e) = do
 ie <- toIntExpr e
 bp <- toPred op
 return $ P $ ILit bp (IEVar (IntVar (Var x))) ie
exprToGuard _ = Nothing


exprToUpdate :: Expr -> Maybe (IntVariable, IntExpr)
exprToUpdate (BO OpAssign (VName x) e) =
 liftM2 (,) (return v) (toIntExpr e)
  where v = IntVar (Var x)
exprToUpdate (BO OpIncr (VName x) e) =
 liftM2 (,) (return v) (liftM (IEPlus (IEVar v)) (toIntExpr e))
  where v = IntVar (Var x)
exprToUpdate (BO OpDecr (VName x) e) =
 liftM2 (,) (return v) (liftM (IEMinus (IEVar v)) (toIntExpr e))
  where v = IntVar (Var x)
exprToUpdate _ = Nothing

toIntExpr :: Expr -> Maybe IntExpr
toIntExpr (Const n) = return $ IEConst (fromIntegral n)
toIntExpr (VName x) = return $ IEVar (IntVar (Var x))
toIntExpr (BO OpPlus e1 e2) = liftM2 IEPlus (toIntExpr e1) (toIntExpr e2)
toIntExpr (BO OpMinus e1 e2) = liftM2 IEMinus (toIntExpr e1) (toIntExpr e2)
toIntExpr _ = Nothing


setVarInitAndRange :: Synchronisation -> Element -> Maybe Synchronisation
setVarInitAndRange s e
 | getElemName e /= "VariableComponent" = Nothing
 | otherwise =
  do
   name <- getAttribute "Name" e 
   rangeElem <- firstOccurrence (elemName "VariableRange") getElem (elContent e)
   rangeBinExpr <- firstOccurrence
                   (\x -> or $ map (flip elemName x) ["BinaryExpression",
                                                      "EnumSetExpression"])
                   (getElem >=> parseExpr)
                   (elContent  rangeElem)
   (min, max) <-
    case (rangeBinExpr) of
         (BO OpRange (Const i) (Const j)) -> Just (i,j)
         (_) -> Nothing
         
   initElem <- firstOccurrence (elemName "VariableInitial")
                               (getElem) (elContent e)
   initExpr <- firstOccurrence (elemName "IntConstant")
                               (getElem >=> parseExpr)
                               (elContent initElem)   
   init <- case (initExpr) of
                (Const i) -> Just i
                (_) -> Nothing
   let var = IntVar (Var name)
   return $ setDomain ( var
                      , Domain { lower = fromIntegral min
                               , upper = fromIntegral max
                               , initial = fromIntegral init }
                      )
                      s


------------------
--- parsing expressions


parseExpr :: Element -> Maybe Expr
parseExpr e
 | getElemName e == "BinaryExpression" =
  do
   op <- parseBinaryOperator e
   -- This section relies on all well-formed input having exactly
   -- two sub-elements to every BinaryExpression element.
   let args = mapMaybe getElem (elContent e)
   arg1 <- parseExpr $ args!!0
   arg2 <- parseExpr $ args!!1
   return $ BO op arg1 arg2
 | getElemName e == "EnumSetExpression" =
  do
   let args = mapMaybe getElem (elContent e)
   enumNames <- mapM parseExpr args
   case (enumNames) of
        [VName "on", VName "off"] -> return $ BO OpRange (Const 0) (Const 1)
        _ -> Nothing

 | getElemName e == "UnaryExpression" =
  do
   op <- parseUnaryOperator e
   let args = mapMaybe getElem (elContent e)
   arg1 <- parseExpr $ args!!0
   return $ UO op arg1
 | getElemName e == "SimpleIdentifier" =
  do
   var <- getAttribute "Name" e
   return $ VName var
 | getElemName e == "IntConstant" =
  do
   val <- getAttribute "Value" e
   return $ Const (read val)
 | otherwise = Nothing


data Expr
  = Const Int
  | VName VarName
  | BO BinaryOp Expr Expr
  | UO UnaryOp Expr
  deriving ( Show )


data BinaryOp
 = OpEquals
 | OpNEquals
 | OpLessThan
 | OpLessThanEq
 | OpGreaterThan
 | OpGreaterThanEq
 | OpAssign
 | OpPlus
 | OpMinus
 | OpAnd
 | OpOr
 | OpRange
 | OpIncr
 | OpDecr
  deriving ( Show, Eq )
  
data UnaryOp
 = OpNot
  deriving ( Show, Eq )

toPred :: BinaryOp -> Maybe BinaryPred
toPred op = lookup op opToPred
 where opToPred = [ (OpEquals, Equals)
                  , (OpNEquals, NEquals)
                  , (OpLessThan, LessThan)
                  , (OpLessThanEq, LessThanEq)
                  , (OpGreaterThan, GreaterThan)
                  , (OpGreaterThanEq, GreaterThanEq) ]

parseBinaryOperator :: Element -> Maybe BinaryOp
parseBinaryOperator e
 = case (getAttribute "Operator" e) of
        (Just "==")   -> return OpEquals
        (Just "!=")   -> return OpNEquals
        (Just "=")    -> return OpAssign
        (Just "<") -> return OpLessThan
        (Just ">") -> return OpGreaterThan
        (Just "&le;") -> return OpLessThanEq
        (Just "&ge;") -> return OpGreaterThanEq
        (Just "&lt;") -> return OpLessThan
        (Just "&gt;") -> return OpGreaterThan
        (Just "+")    -> return OpPlus
        (Just "-")    -> return OpMinus
        (Just "..")   -> return OpRange
        (Just "+=")   -> return OpIncr
        (Just "-=")   -> return OpDecr
        (Just "|") -> return OpOr
        (Just "&") -> return OpAnd
        (Nothing)     -> Nothing
        
parseUnaryOperator :: Element -> Maybe UnaryOp
parseUnaryOperator e
 = case (getAttribute "Operator" e) of
        (Just "!")   -> return OpNot
        (Nothing)     -> Nothing
        





