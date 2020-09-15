{-# LANGUAGE Strict #-}

module Proof 
    ( isAxiomSchema
    , try
    , Mode (..)
    , Row (..)
    , Error (..)
    , StepInformation (..)
    , constructMinProof
    , analyze
    ) where

import Data.List
import Data.Maybe
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set 
import MathLogicEssentials
import Parser
import Control.Applicative ((<|>))

data Mode 
    = AxiomSchema Int 
    | ModusPonens Int Int 
    | Hypothesis Int 
    | AxiomFormalArithmetic Int
    | Induction
    deriving (Eq, Ord)

instance Show Mode where
    show (AxiomSchema x) = "Ax. sch. " ++ show x
    show (ModusPonens a b) = "M.P. " ++ show a ++ ", " ++ show b
    show (Hypothesis h) = "Hypothesis " ++ show h
    show (AxiomFormalArithmetic x) = "Ax. A" ++ show x
    show Induction = "Ax. sch. A9"

data Row = Row { getPosition :: Int
               , getMode :: Mode 
               } deriving (Eq, Ord)

instance Show Row where
    show (Row i m) = "[" ++ show i ++ ". " ++ show m ++ "]"

data Quantifier = QForall | QExists deriving (Eq, Ord)

instance Show Quantifier where
    show QForall = "@"
    show QExists = "?"

data Error 
    = FreeOccurence Int String Quantifier
    | NotFreeVariable Int String PropFormula Quantifier
    | NotProven Int
    | DifferentProof
    deriving (Eq, Ord)

instance Show Error where
    show (FreeOccurence i s q) = "Expression " 
                               ++ show i 
                               ++ ": variable " 
                               ++ s
                               ++ "occurs free in "
                               ++ show q
                               ++ "-rule." 
    show (NotFreeVariable i s p q) = "Expression"
                                   ++ show i
                                   ++ ": variable "
                                   ++ s
                                   ++ "is not free for term "
                                   ++ show p
                                   ++ "in "
                                   ++ show q
                                   ++ "-axiom."
    show (NotProven i) = "Expression " ++ show i ++ " is not proved."
    show DifferentProof = "The proof proves different expression."

data StepInformation = Step Row PropFormula | Error Error deriving (Eq, Ord)

instance Show StepInformation where
    show (Step r p) = show r ++ " " ++ show p
    show (Error e) = show e

showRPF :: (PropFormula, Row) -> String
showRPF (p, r) = show r ++ " " ++ show p

constructMinProof 
    :: String 
    -> PropFormula 
    -> [PropFormula] 
    -> Map.Map PropFormula Row 
    -> Map.Map PropFormula [PropFormula] 
    -> String
constructMinProof rawInitial statement hypotheses buffer mpContainer
    = let lastPosition = getPosition $ buffer Map.! statement
          (keys, rows) = unzip $ Map.toList buffer
          positions = fmap getPosition rows
          modes = fmap getMode rows
--        [(PropFormula, {Int, Mode})]
--    --> [(Int, (PropFormula, Mode))]
          newBuffer = Map.fromList (zip positions (zip keys modes))
          inclusions = trim (Map.empty :: Map.Map Int Int) newBuffer lastPosition
          buffer' = Map.filterWithKey (\k _ -> inclusions Map.!? k /= Nothing) newBuffer
          newProof = fmap (fst . snd) $ Map.toList buffer'
          newDetailedProof = fromJust $ try statement hypotheses (zip [1..] newProof) (Just (Map.empty :: Map.Map PropFormula Row)) mpContainer
          newDetailedProof' = sortOn (getPosition . snd) $ Map.toList newDetailedProof
      in unlines . (:) rawInitial . fmap showRPF $ newDetailedProof'

trim :: Map.Map Int Int -> Map.Map Int (PropFormula, Mode) -> Int -> Map.Map Int Int
trim inclusions buffer currentPosition = case snd $ buffer Map.! currentPosition of
                                             ModusPonens i1 i2 -> let incls1 = trim newInclusions buffer i1
                                                                      incls2 = trim newInclusions buffer i2
                                                                  in Map.unionWith (+) incls1 incls2
                                             Hypothesis _ -> newInclusions
                                             AxiomSchema _ -> newInclusions
  where
    newInclusions = safeUpdate currentPosition inclusions

safeUpdate :: Int -> Map.Map Int Int -> Map.Map Int Int
safeUpdate position inclusions = if value == Nothing
                                 then Map.insert position 1 inclusions
                                 else Map.update (\x -> Just (x + 1)) position inclusions
  where
    value = inclusions Map.!? position
                                  
try :: PropFormula 
    -> [PropFormula] 
    -> [(Int, PropFormula)] 
    -> Maybe (Map.Map PropFormula Row) 
    -> Map.Map PropFormula [PropFormula]
    -> Maybe (Map.Map PropFormula Row)
try statement hypotheses proof buffer mpContainer = foldl' try' buffer proof
  where
    try' :: Maybe (Map.Map PropFormula Row) -> (Int, PropFormula) -> Maybe (Map.Map PropFormula Row)
    try' Nothing _ = Nothing
    try' (Just buffer') (pos, cur) 
        | isJust (buffer' Map.!? cur) = Just buffer'
        | otherwise = case ax cur <|> hyp cur <|> mp cur buffer' of
                          Just mode -> Just (Map.insert cur (Row pos mode) buffer')
                          Nothing -> Nothing

    ax :: PropFormula -> Maybe Mode
    ax = fmap AxiomSchema . isAxiomSchema

    hyp :: PropFormula -> Maybe Mode
    hyp cur = fmap Hypothesis . fmap (+1) $ findIndex (==cur) hypotheses

    mp :: PropFormula -> Map.Map PropFormula Row -> Maybe Mode
    mp cur buffer' = findMP cur buffer' mpContainer

findMP :: PropFormula -> Map.Map PropFormula Row -> Map.Map PropFormula [PropFormula] -> Maybe Mode
findMP b buffer mpContainer = case mpContainer Map.!? b of
                                  Nothing -> Nothing
                                  Just list -> case find (\a -> Map.member a buffer && Map.member (a :-> b) buffer) list of
                                                   Nothing -> Nothing
                                                   Just a -> Just $ ModusPonens (getPosition (buffer Map.! (a :-> b))) (getPosition (buffer Map.! a))

isAxiomSchema :: PropFormula -> Maybe Int
isAxiomSchema = isAxiom1

isAxiom1 p = case p of
--  a :-> b :-> a    
    a :-> b :-> c -> if a == c
                     then Just 1
                     else isAxiom2 p
    _ -> isAxiom2 p

isAxiom2 p = case p of
--  (a :-> b) :-> (a :-> b :-> c) :-> (a :-> c)
    (a :-> b) :-> (c :-> d :-> e) :-> (f :-> g) -> if a == c
                                                   && a == f
                                                   && b == d
                                                   && e == g 
                                                   then Just 2
                                                   else isAxiom3 p
    _ -> isAxiom3 p

isAxiom3 p = case p of
--  a :& b :-> a
--  a :& b :-> b
    a :& b :-> c -> if a == c
                    then Just 3
                    else if b == c
                         then Just 4
                         else isAxiom4or5 p
    _ -> isAxiom4or5 p

isAxiom4or5 p = case p of
--  a :-> b :-> a :& b
    a :-> b :-> c :& d -> if a == c && b == d
                          then Just 5
                          else isAxiom6or7 p
    _ -> isAxiom6or7 p

isAxiom6or7 p = case p of
--  a :-> a :| b
--  b :-> a :| b
    a :-> b :| c -> if a == b
                    then Just 6
                    else if a == c
                         then Just 7
                         else isAxiom8 p
    _ -> isAxiom8 p

isAxiom8 p = case p of
--  (a :-> c) :-> (b :-> c) :-> (a :| b :-> c)
    (a :-> b) :-> (c :-> d) :-> (e :| f :-> g) -> if a == e
                                                  && c == f
                                                  && b == d
                                                  && b == g
                                                  then Just 8
                                                  else isAxiom9 p
    _ -> isAxiom9 p    

isAxiom9 p = case p of
--  (a :-> b) :-> (a :-> Not b) :-> Not a
    (a :-> b) :-> (c :-> Not d) :-> Not e -> if a == c
                                             && a == e
                                             && b == d
                                             then Just 9
                                             else isAxiom10 p
    _ -> isAxiom10 p

isAxiom10 p = case p of
--  (Not (Not a)) :-> a
    (Not (Not a)) :-> b -> if a == b
                           then Just 10
                           else isAxiom11 p
    _ -> isAxiom11 p

isAxiom11 p = case p of
-- (Forall x a) :-> a{x := q}
    (Forall x a) :-> b -> if checkSubstitutionCorrectness a b x
                          then Just 11
                          else isAxiom12 p
    _ -> isAxiom12 p

isAxiom12 p = case p of
-- a{x := q} :-> (Exists x a)
    b :-> (Exists x a) -> if checkSubstitutionCorrectness a b x
                          then Just 12
                          else Nothing
    _ -> Nothing

checkSubstitutionCorrectness :: PropFormula -> PropFormula -> String -> Bool
checkSubstitutionCorrectness a b x = case checkSubstitutionCorrectnessDEEPER a b x of
                                         Just (_, _, True) -> True
                                         _                 -> False

checkSubstitutionCorrectnessDEEPER :: PropFormula -> PropFormula -> String -> Maybe (String, PeanoFormula, Bool)
checkSubstitutionCorrectnessDEEPER a b x 
    = if isSubstitutionCorrect terms
      then Just (x, getSubstitution terms, isFreeForReplacement x (getVariables $ getSubstitution terms) Set.empty a)
      else Nothing 
  where
    terms = setForReplacement a b x

isSubstitutionCorrect :: Maybe (Set.Set PeanoFormula) -> Bool
isSubstitutionCorrect (Just terms) = Set.size terms == 1
isSubstitutionCorrect _ = False

getSubstitution :: Maybe (Set.Set PeanoFormula) -> PeanoFormula
getSubstitution (Just terms) = Set.elemAt 0 terms

getVariables :: PeanoFormula -> Set.Set String
getVariables (PeanoVariable x) = Set.singleton x
getVariables Zero = Set.empty 
getVariables (Succ x) = getVariables x
getVariables (a :+ b) = Set.union (getVariables a) (getVariables b) 
getVariables (a :* b) = Set.union (getVariables a) (getVariables b) 
getVariables (a := b) = Set.union (getVariables a) (getVariables b)

isFreeForReplacement :: String -> Set.Set String -> Set.Set String -> PropFormula -> Bool
isFreeForReplacement x variables quantifiers formula = case formula of
    PropString var -> True
    Not          a -> isFreeForReplacement x variables quantifiers a
    a     :&     b -> isFreeForReplacement x variables quantifiers a && isFreeForReplacement x variables quantifiers b
    a     :|     b -> isFreeForReplacement x variables quantifiers a && isFreeForReplacement x variables quantifiers b
    a     :->    b -> isFreeForReplacement x variables quantifiers a && isFreeForReplacement x variables quantifiers b
    Forall   v   a -> (\set -> isFreeForReplacement x variables quantifiers a) (if x == v then quantifiers else Set.insert v quantifiers)
    Exists   v   a -> isFreeForReplacement x variables quantifiers $ Forall v a
    Peano        p -> isFreeForReplacementPeano x variables quantifiers p

isFreeForReplacementPeano :: String -> Set.Set String -> Set.Set String -> PeanoFormula -> Bool
isFreeForReplacementPeano x variables quantifiers formula = case formula of
    Zero                -> True
    (Succ            a) -> isFreeForReplacementPeano x variables quantifiers a
    (PeanoVariable var) -> not $ x == var && (not . Set.null) (Set.intersection variables quantifiers)
    (a       :+      b) -> isFreeForReplacementPeano x variables quantifiers a && isFreeForReplacementPeano x variables quantifiers b
    (a       :*      b) -> isFreeForReplacementPeano x variables quantifiers a && isFreeForReplacementPeano x variables quantifiers b
    (a       :=      b) -> isFreeForReplacementPeano x variables quantifiers a && isFreeForReplacementPeano x variables quantifiers b

setForReplacement :: PropFormula -> PropFormula -> String -> Maybe (Set.Set PeanoFormula)
setForReplacement    (PropString a)    (PropString b) x = if a == b then Just Set.empty else Nothing
setForReplacement    (Not        a)    (Not        b) x = setForReplacement a b x
setForReplacement    (a1   :&   a2)    (b1   :&   b2) x = setForReplacement a1 b1 x +:+ setForReplacement a2 b2 x
setForReplacement    (a1   :|   a2)    (b1   :|   b2) x = setForReplacement a1 b1 x +:+ setForReplacement a2 b2 x
setForReplacement    (a1   :->  a2)    (b1   :->  b2) x = setForReplacement a1 b1 x +:+ setForReplacement a2 b2 x
setForReplacement a'@(Forall  ax a) b'@(Forall  bx b) x = quantifiers a' b' a b ax bx x
setForReplacement a'@(Exists  ax a) b'@(Exists  bx b) x = quantifiers a' b' a b ax bx x
setForReplacement    (Peano      a)    (Peano      b) x = setForReplacementPeano a b x
setForReplacement _                   _                   _ = Nothing

setForReplacementPeano :: PeanoFormula -> PeanoFormula -> String -> Maybe (Set.Set PeanoFormula)
setForReplacementPeano source@(PeanoVariable a) replacement x = if a == x
                                                                then Just $ Set.singleton replacement
                                                                else if source == replacement 
                                                                     then Just Set.empty 
                                                                     else Nothing 
setForReplacementPeano Zero       Zero       x = Just Set.empty
setForReplacementPeano (Succ   a) (Succ   b) x = setForReplacementPeano a b x
setForReplacementPeano (a1 :+ a2) (b1 :+ b2) x = setForReplacementPeano a1 b1 x +:+ setForReplacementPeano a2 b2 x
setForReplacementPeano (a1 :* a2) (b1 :* b2) x = setForReplacementPeano a1 b1 x +:+ setForReplacementPeano a2 b2 x
setForReplacementPeano (a1 := a2) (b1 := b2) x = setForReplacementPeano a1 b1 x +:+ setForReplacementPeano a2 b2 x


quantifiers :: PropFormula -> PropFormula -> 
               PropFormula -> PropFormula -> 
               String -> String -> String -> 
               Maybe (Set.Set PeanoFormula)
quantifiers a' b' a b ax bx x
    | x /= ax && ax == bx = setForReplacement a b x
    | x == ax && a' == b' = Just Set.empty
    | otherwise = Nothing

(+:+) :: Maybe (Set.Set PeanoFormula) -> Maybe (Set.Set PeanoFormula) -> Maybe (Set.Set PeanoFormula)
(Just x) +:+ (Just y) = Just $ Set.union x y
_ +:+ _ = Nothing 

analyze 
    :: PropFormula  
    -> [PropFormula]
    -> [(Int, PropFormula)] 
    -> [StepInformation]
    -> Map.Map PropFormula [PropFormula]
    -> [StepInformation]
analyze given hypotheses proof buffer mpContainer = foldl' analyze' buffer proof
  where
    analyze' :: [StepInformation] -> (Int, PropFormula) -> [StepInformation]
    analyze' buffer' (pos, cur)
        | isJust (buffer' Map.!? cur) = buffer'
        | otherwise = case ax cur <|> hyp cur <|> mp cur buffer' of
                          Just mode -> Just (Map.insert cur (Row pos mode) buffer')
                          Nothing -> Nothing