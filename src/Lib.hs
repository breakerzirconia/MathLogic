module Lib 
    ( PropFormula (..)
    , LogicValue (..)
    , extractVariables 
    , retrieveValue
    , transform
    , isTautology
    , isContradictory
    ) where

import Data.Maybe
import Data.List

data LogicValue = L | T deriving Eq

instance Show LogicValue where
    show T = "1"
    show L = "0"

data PropFormula
    = PropVariable    Char
    | PropValue       LogicValue
    | Not             PropFormula
    | PropFormula :&  PropFormula
    | PropFormula :|  PropFormula
    | PropFormula :-> PropFormula

instance Show PropFormula where
    show (PropVariable x) = [x]
    show (PropValue    v) = show v
    show (Not          p) = "!(" ++ show p  ++ ")"
    show (p1    :&    p2) =  "(" ++ show p1 ++ " & "  ++ show p2 ++ ")"
    show (p1    :|    p2) =  "(" ++ show p1 ++ " v "  ++ show p2 ++ ")"
    show (p1    :->   p2) =  "(" ++ show p1 ++ " -> " ++ show p2 ++ ")"

infixr 1 :->
infixl 2 :|
infixl 3 :&

anti :: LogicValue -> LogicValue
anti T = L
anti L = T

(&:) :: LogicValue -> LogicValue -> LogicValue
T &: T = T
_ &: _ = L

(|:) :: LogicValue -> LogicValue -> LogicValue
L |: L = L
_ |: _ = T

(->:) :: LogicValue -> LogicValue -> LogicValue
T ->: L = L
_ ->: _ = T

infixr 1 ->:
infixl 2  |:
infixl 3  &:

extractVariables :: PropFormula -> [Char]
extractVariables p = nub $ extractVariables' p []

extractVariables' :: PropFormula -> [Char] -> [Char]
extractVariables' (PropVariable ch) acc =   ch : acc
extractVariables' (PropValue     v) acc =   acc
extractVariables' (Not           p) acc =   extractVariables' p  acc
extractVariables' (p1    :&     p2) acc =  (extractVariables' p1 acc) 
                                        ++ (extractVariables' p2 acc)
                                        ++  acc
extractVariables' (p1    :|     p2) acc =  (extractVariables' p1 acc) 
                                        ++ (extractVariables' p2 acc)
                                        ++  acc
extractVariables' (p1    :->    p2) acc =  (extractVariables' p1 acc) 
                                        ++ (extractVariables' p2 acc)
                                        ++  acc

type PropVarMap = [(Char, LogicValue)]

lookUpValue :: Char -> PropVarMap -> Maybe LogicValue
lookUpValue ch []            = Nothing
lookUpValue ch ((pv,v):tail) = if pv == ch 
                               then Just v 
                               else lookUpValue ch tail

retrieveValue :: PropFormula -> PropVarMap -> LogicValue
retrieveValue (PropVariable ch) list
    | lookUpValue ch list == Nothing = error "No such propositional variable could be found"
    | otherwise = fromJust $ lookUpValue ch list
retrieveValue (PropValue     v) list = v
retrieveValue (Not           p) list = anti $ retrieveValue p list
retrieveValue (p1    :&     p2) list = (retrieveValue p1 list)  &: (retrieveValue p2 list)
retrieveValue (p1    :|     p2) list = (retrieveValue p1 list)  |: (retrieveValue p2 list)
retrieveValue (p1    :->    p2) list = (retrieveValue p1 list) ->: (retrieveValue p2 list)

transform :: PropFormula -> PropVarMap -> String
transform (PropVariable ch) list
    | lookUpValue ch list == Nothing = error "No such propositional variable could be found"
    | otherwise = show . fromJust $ lookUpValue ch list
transform (PropValue     v) list = show v
transform (Not           p) list = "!(" ++ transform p  list ++ ")"
transform (p1    :&     p2) list =  "(" ++ transform p1 list ++ " & "  ++ transform p2 list ++ ")"
transform (p1    :|     p2) list =  "(" ++ transform p1 list ++ " v "  ++ transform p2 list ++ ")"
transform (p1    :->    p2) list =  "(" ++ transform p1 list ++ " -> " ++ transform p2 list ++ ")"

generateAllValues :: Int -> [[LogicValue]]
generateAllValues 0 = [[]]
generateAllValues n = let prev = generateAllValues (n - 1)
                      in map (L:) prev ++ map (T:) prev

isTautology :: PropFormula -> Bool
isTautology p = all (== T) 
              . map (retrieveValue p) 
              $ [zip propVars value | value <- generateAllValues $ length propVars] 
  where
    propVars = extractVariables p

isContradictory :: PropFormula -> Bool
isContradictory p = all (== L) 
              . map (retrieveValue p) 
              $ [zip propVars value | value <- generateAllValues $ length propVars] 
  where
    propVars = extractVariables p