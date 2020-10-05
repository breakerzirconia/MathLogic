{-# LANGUAGE Strict #-}

module MathLogicEssentials where

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
    | Forall String PropFormula
    | Exists String PropFormula
    | PeanoFormula := PeanoFormula
    deriving (Eq, Ord)

data PeanoFormula
    = Zero
    | Succ PeanoFormula
    | PeanoVariable String
    | PeanoFormula :+ PeanoFormula
    | PeanoFormula :* PeanoFormula
    deriving (Eq, Ord)

instance Show PeanoFormula where
    show Zero              = "0"
    show (Succ          p) = show p ++ "'"
    show (PeanoVariable s) = s
    show (p1     :+    p2) = "(" ++ show p1 ++ "+" ++ show p2 ++ ")"
    show (p1     :*    p2) = "(" ++ show p1 ++ "*" ++ show p2 ++ ")"

instance Show PropFormula where
    show (PropString  s) = s
    show (PropValue   v) = show v
    show (Not         p) = "(" ++ "!" ++ show p ++ ")"
    show (p1    :&   p2) = "(" ++ show p1 ++ "&"  ++ show p2 ++ ")"
    show (p1    :|   p2) = "(" ++ show p1 ++ "|"  ++ show p2 ++ ")"
    show (p1    :->  p2) = "(" ++ show p1 ++ "->" ++ show p2 ++ ")"
    show (Forall  s   p) = "(" ++ "@" ++ s ++ "." ++ show p ++ ")"
    show (Exists  s   p) = "(" ++ "?" ++ s ++ "." ++ show p ++ ")"
    show (p1    :=   p2) = "(" ++ show p1 ++ "=" ++ show p2 ++ ")"

infixr 1 :->
infixl 2 :|
infixl 3 :&
infixl 4 :=
infixl 5 :+
infixl 6 :*

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
  where
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

generateAllValues :: Int -> [[LogicValue]]
generateAllValues = fmap concat . traverse (\x -> [L : x, T : x]) . flip replicate []

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

splitPropFormula :: PropFormula -> [PropFormula]
splitPropFormula formula = case formula of
  (PropString _)      -> []
  (Not x)             -> [x]
  (a :& b)            -> [a, b]
  (a :| b)            -> [a, b]
  (a :-> b)           -> [a, b]
  (Forall x formula') -> [formula']
  (Exists x formula') -> [formula']
  (_ := _)            -> []

splitPeanoFormula :: PeanoFormula -> [PeanoFormula]
splitPeanoFormula formula = case formula of
  Zero            -> []
  Succ a          -> [a]
  PeanoVariable _ -> []
  (a :+ b)        -> [a, b]
  (a :* b)        -> [a, b]

splitQuantifier :: PropFormula -> Maybe (String, PropFormula)
splitQuantifier (Forall x formula) = Just (x, formula)
splitQuantifier (Exists x formula) = Just (x, formula)
splitQuantifier _ = Nothing

checkPropFormulaTypeIdentity :: PropFormula -> PropFormula -> Bool
checkPropFormulaTypeIdentity (PropString _) (PropString _) = True
checkPropFormulaTypeIdentity (PropValue _)  (PropValue _)  = True
checkPropFormulaTypeIdentity (Not _)        (Not _)        = True
checkPropFormulaTypeIdentity (_ :& _)       (_ :& _)       = True
checkPropFormulaTypeIdentity (_ :| _)       (_ :| _)       = True
checkPropFormulaTypeIdentity (_ :-> _)      (_ :-> _)      = True
checkPropFormulaTypeIdentity (Forall _ _)   (Forall _ _)   = True
checkPropFormulaTypeIdentity (Exists _ _)   (Exists _ _)   = True
checkPropFormulaTypeIdentity (_ := _)       (_ := _)       = True
checkPropFormulaTypeIdentity _              _              = False

checkPeanoFormulaTypeIdentity :: PeanoFormula -> PeanoFormula -> Bool
checkPeanoFormulaTypeIdentity Zero              Zero              = True
checkPeanoFormulaTypeIdentity (Succ _)          (Succ _)          = True
checkPeanoFormulaTypeIdentity (PeanoVariable _) (PeanoVariable _) = True
checkPeanoFormulaTypeIdentity (_ :+ _)          (_ :+ _)          = True
checkPeanoFormulaTypeIdentity (_ :* _)          (_ :* _)          = True
checkPeanoFormulaTypeIdentity _                 _                 = False