module MathLogicEssentials 
    ( PropFormula (..)
    , LogicValue (..)
    , extractStrings 
    , retrieveValue
    , transform
    , isTautology
    , isContradictory
    , isOuterImplication
    ) where

import Data.Maybe
import Data.List

data LogicValue = L | T deriving (Eq, Ord)

instance Show LogicValue where
    show T = "1"
    show L = "0"

data PropFormula
    = PropString      String
    | PropValue       LogicValue
    | Not             PropFormula
    | PropFormula :&  PropFormula
    | PropFormula :|  PropFormula
    | PropFormula :-> PropFormula
    deriving (Eq, Ord)

instance Show PropFormula where
    show (PropString   s) = s
    show (PropValue    v) = show v
    show (Not          p) = "!" ++ show p
    show (p1    :&    p2) = "(" ++ show p1 ++ " & "  ++ show p2 ++ ")"
    show (p1    :|    p2) = "(" ++ show p1 ++ " | "  ++ show p2 ++ ")"
    show (p1    :->   p2) = "(" ++ show p1 ++ " -> " ++ show p2 ++ ")"

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

extractStrings :: PropFormula -> [String]
extractStrings p = nub $ extractStrings' p []

extractStrings' :: PropFormula -> [String] -> [String]
extractStrings' (PropString    s) acc =   s : acc
extractStrings' (PropValue     v) acc =   acc
extractStrings' (Not           p) acc =   extractStrings' p  acc
extractStrings' (p1    :&     p2) acc =  (extractStrings' p1 acc) 
                                        ++ (extractStrings' p2 acc)
                                        ++  acc
extractStrings' (p1    :|     p2) acc =  (extractStrings' p1 acc) 
                                        ++ (extractStrings' p2 acc)
                                        ++  acc
extractStrings' (p1    :->    p2) acc =  (extractStrings' p1 acc) 
                                        ++ (extractStrings' p2 acc)
                                        ++  acc

type PropVarMap = [(String, LogicValue)]

lookUpValue :: String -> PropVarMap -> Maybe LogicValue
lookUpValue s []            = Nothing
lookUpValue s ((pv,v):tail) = if pv == s 
                              then Just v 
                              else lookUpValue s tail

retrieveValue :: PropFormula -> PropVarMap -> LogicValue
retrieveValue (PropString s) list = case lookUpValue s list of
    Nothing -> error "No such propositional string could be found"
    Just res -> res

retrieveValue (PropValue     v) list = v
retrieveValue (Not           p) list = anti $ retrieveValue p list
retrieveValue (p1    :&     p2) list = (retrieveValue p1 list)  &: (retrieveValue p2 list)
retrieveValue (p1    :|     p2) list = (retrieveValue p1 list)  |: (retrieveValue p2 list)
retrieveValue (p1    :->    p2) list = (retrieveValue p1 list) ->: (retrieveValue p2 list)

transform :: PropFormula -> PropVarMap -> String
transform (PropString s) list = case lookUpValue s list of
    Nothing -> error "No such propositional string could be found"
    Just res -> show res

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
              $ [zip propString value | value <- generateAllValues $ length propString] 
  where
    propString = extractStrings p

isContradictory :: PropFormula -> Bool
isContradictory p = all (== L) 
              . map (retrieveValue p) 
              $ [zip propString value | value <- generateAllValues $ length propString] 
  where
    propString = extractStrings p

isOuterImplication :: PropFormula -> Bool
isOuterImplication (_ :-> _) = True
isOuterImplication _ = False
