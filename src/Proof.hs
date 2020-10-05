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
    = AxiomSchema Integer
    | ModusPonens Integer Integer
    | Hypothesis Integer
    | AxiomFormalArithmetic Integer
    | QIntro Integer
    | Induction
    deriving (Eq, Ord)

instance Show Mode where
    show (AxiomSchema x) = "Ax. sch. " ++ show x
    show (ModusPonens a b) = "M.P. " ++ show a ++ ", " ++ show b
    show (Hypothesis h) = "Hypothesis " ++ show h
    show (AxiomFormalArithmetic x) = "Ax. A" ++ show x
    show (QIntro k) = "@?-intro " ++ show k
    show Induction = "Ax. sch. A9"

data Row = Row { getPosition :: Integer
               , getMode :: Mode 
               } deriving (Eq, Ord)

instance Show Row where
    show (Row i m) = "[" ++ show i ++ ". " ++ show m ++ "]"

data Error 
    = FreeOccurence Integer String
    | NotFreeVariable Integer String PeanoFormula
    | NotProven Integer
    | DifferentProof
    deriving (Eq, Ord)

instance Show Error where
    show (FreeOccurence i s) = "Expression " 
                            ++ show i 
                            ++ ": variable " 
                            ++ s
                            ++ " occurs free in ?@-rule."
    show (NotFreeVariable i s p) = "Expression "
                                ++ show i
                                ++ ": variable "
                                ++ s
                                ++ " is not free for term "
                                ++ show p
                                ++ " in ?@-axiom."
    show (NotProven i) = "Expression " ++ show i ++ " is not proved."
    show DifferentProof = "The proof proves different expression."

data StepInformation = Step { getRow :: Row 
                            , getFormula :: PropFormula
                            } 
                     | Error { getError :: Error 
                             } 
                     deriving (Eq, Ord)

instance Show StepInformation where
    show (Step r p) = show r ++ " " ++ show p
    show (Error e) = show e

showRPF :: (PropFormula, Row) -> String
showRPF (p, r) = show r ++ " " ++ show p

isStep :: StepInformation -> Bool
isStep (Step _ _) = True
isStep _          = False

isError :: StepInformation -> Bool
isError (Error _) = True
isError _         = False

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
          inclusions = trim (Map.empty :: Map.Map Integer Integer) newBuffer lastPosition
          buffer' = Map.filterWithKey (\k _ -> inclusions Map.!? k /= Nothing) newBuffer
          newProof = fmap (fst . snd) $ Map.toList buffer'
          newDetailedProof = fromJust $ try statement hypotheses (zip [1..] newProof) (Just (Map.empty :: Map.Map PropFormula Row)) mpContainer
          newDetailedProof' = sortOn (getPosition . snd) $ Map.toList newDetailedProof
      in unlines . (:) rawInitial . fmap showRPF $ newDetailedProof'

trim :: Map.Map Integer Integer -> Map.Map Integer (PropFormula, Mode) -> Integer -> Map.Map Integer Integer
trim inclusions buffer currentPosition = case snd $ buffer Map.! currentPosition of
                                             ModusPonens i1 i2 -> let incls1 = trim newInclusions buffer i1
                                                                      incls2 = trim newInclusions buffer i2
                                                                  in Map.unionWith (+) incls1 incls2
                                             Hypothesis _ -> newInclusions
                                             AxiomSchema _ -> newInclusions
  where
    newInclusions = safeUpdate currentPosition inclusions

safeUpdate :: Integer -> Map.Map Integer Integer -> Map.Map Integer Integer
safeUpdate position inclusions = if value == Nothing
                                 then Map.insert position 1 inclusions
                                 else Map.update (\x -> Just (x + 1)) position inclusions
  where
    value = inclusions Map.!? position
                                  
try :: PropFormula 
    -> [PropFormula] 
    -> [(Integer, PropFormula)] 
    -> Maybe (Map.Map PropFormula Row) 
    -> Map.Map PropFormula [PropFormula]
    -> Maybe (Map.Map PropFormula Row)
try statement hypotheses proof buffer mpContainer = foldl' try' buffer proof
  where
    try' :: Maybe (Map.Map PropFormula Row) -> (Integer, PropFormula) -> Maybe (Map.Map PropFormula Row)
    try' Nothing _ = Nothing
    try' (Just buffer') (pos, cur) 
        | isJust (buffer' Map.!? cur) = Just buffer'
        | otherwise = case ax cur <|> hyp cur <|> mp cur buffer' of
                          Just mode -> Just (Map.insert cur (Row pos mode) buffer')
                          Nothing -> Nothing

    ax :: PropFormula -> Maybe Mode
    ax = fmap AxiomSchema . isAxiomSchema

    hyp :: PropFormula -> Maybe Mode
    hyp cur = fmap (Hypothesis . (+1) . toInteger) $ findIndex (==cur) hypotheses

    mp :: PropFormula -> Map.Map PropFormula Row -> Maybe Mode
    mp cur buffer' = findMP cur buffer' mpContainer

findMP :: PropFormula -> Map.Map PropFormula Row -> Map.Map PropFormula [PropFormula] -> Maybe Mode
findMP b buffer mpContainer = case mpContainer Map.!? b of
                                  Nothing -> Nothing
                                  Just list -> case find (\a -> Map.member a buffer && Map.member (a :-> b) buffer) list of
                                                   Nothing -> Nothing
                                                   Just a -> Just $ ModusPonens (getPosition (buffer Map.! (a :-> b))) (getPosition (buffer Map.! a))

isAxiomSchema :: PropFormula -> Maybe Integer
isAxiomSchema ((a :-> b :-> c)) | a == c = Just 1
isAxiomSchema ((a :-> b) :-> (c :-> d :-> e) :-> (f :-> g)) | a == c && 
                                                              a == f && 
                                                              b == d && 
                                                              e == g = Just 2
isAxiomSchema (a :& b :-> c) | a == c = Just 3
                             | b == c = Just 4
isAxiomSchema (a :-> b :-> c :& d) | a == c && b == d = Just 5
isAxiomSchema (a :-> b :| c) | a == b = Just 6
                             | a == c = Just 7
isAxiomSchema ((a :-> b) :-> (c :-> d) :-> (e :| f :-> g)) | a == e && 
                                                             c == f && 
                                                             b == d && 
                                                             b == g = Just 8
isAxiomSchema ((a :-> b) :-> (c :-> Not d) :-> Not e) | a == c &&
                                                        a == e &&
                                                        b == d = Just 9
isAxiomSchema ((Not (Not a)) :-> b) | a == b = Just 10
isAxiomSchema _                     = Nothing

isAxiomSchema11And12 :: PropFormula -> Maybe Integer
isAxiomSchema11And12 ((Forall x a) :-> b) | a == b || checkSubstitutionCorrectness a b x = Just 11
isAxiomSchema11And12 (b :-> (Exists x a)) | a == b || checkSubstitutionCorrectness a b x = Just 12
isAxiomSchema11And12 _ = Nothing

isAxiomFormalArithmetic :: PropFormula -> Maybe Integer
isAxiomFormalArithmetic (PeanoVariable "a" := PeanoVariable "b" :-> 
                         PeanoVariable "a" := PeanoVariable "c" :-> 
                         PeanoVariable "b" := PeanoVariable "c") = Just 1
isAxiomFormalArithmetic (PeanoVariable "a" := PeanoVariable "b" :-> 
                         Succ (PeanoVariable "a") := Succ (PeanoVariable "b")) = Just 2
isAxiomFormalArithmetic (Succ (PeanoVariable "a") := Succ (PeanoVariable "b") :-> 
                         PeanoVariable "a" := PeanoVariable "b") = Just 3
isAxiomFormalArithmetic (Not (Succ (PeanoVariable "a") := Zero)) = Just 4
isAxiomFormalArithmetic (PeanoVariable "a" :+ Zero := PeanoVariable "a") = Just 5
isAxiomFormalArithmetic (PeanoVariable "a" :+ Succ (PeanoVariable "b") := 
                         Succ (PeanoVariable "a" :+ PeanoVariable "b")) = Just 6
isAxiomFormalArithmetic (PeanoVariable "a" :* Zero := Zero) = Just 7
isAxiomFormalArithmetic (PeanoVariable "a" :* Succ (PeanoVariable "b") :=
                         PeanoVariable "a" :* PeanoVariable "b" :+ PeanoVariable "a") = Just 8
isAxiomFormalArithmetic _ = Nothing

isInduction :: PropFormula -> Maybe Int
isInduction (p0 :& (Forall x (px :-> px')) :-> p) | p == px && go p0 x px px' = Just 9
  where
    go p0 x px px' = getSubstitution cookedP0 == Zero && 
                     getSubstitution cookedPx' == Succ (PeanoVariable x) && 
                     all checkSetSize cooked
    cooked@[cookedP0, cookedPx'] = map (flip (replace px) x) [p0, px']
isInduction _ = Nothing

checkSubstitutionCorrectness :: PropFormula -> PropFormula -> String -> Bool
checkSubstitutionCorrectness a b x = case fmap fst (checkSubstitutionCorrectness' a b x) of
                                         Just True -> True
                                         _         -> False

checkSubstitutionCorrectness' :: PropFormula -> PropFormula -> String -> Maybe (Bool, PeanoFormula)
checkSubstitutionCorrectness' a b x 
  = if checkSetSize terms
    then Just (checkIfFreeToReplace x (getVariables $ getSubstitution terms) Set.empty a, getSubstitution terms)
    else Nothing 
  where
    terms = replace a b x

checkSetSize :: Maybe (Set.Set PeanoFormula) -> Bool
checkSetSize (Just pfs) = Set.size pfs == 1
checkSetSize _          = False

getSubstitution :: Maybe (Set.Set PeanoFormula) -> PeanoFormula
getSubstitution (Just terms) = Set.elemAt 0 terms
getSubstitution Nothing      = undefined

mapFold :: (b -> c -> b) -> b -> (a -> c) -> [a] -> b
mapFold f acc g t = foldl' f acc $ map g t

getVariables :: PeanoFormula -> Set.Set String
getVariables (PeanoVariable x) = Set.singleton x
getVariables p                 = mapFold Set.union Set.empty getVariables . splitPeanoFormula $ p

checkIfFreeToReplace :: String -> Set.Set String -> Set.Set String -> PropFormula -> Bool
checkIfFreeToReplace x variables quantifiers formula = case formula of
    (a := b)     -> mapFold (&&) True (checkIfFreeToReplace' x variables quantifiers) [a, b]
    (Forall v p) -> flip (checkIfFreeToReplace x variables) p (if x == v then quantifiers else Set.insert v quantifiers)
    (Exists v p) -> checkIfFreeToReplace x variables quantifiers (Forall v p)
    _            -> mapFold (&&) True (checkIfFreeToReplace x variables quantifiers) . splitPropFormula $ formula
  where
    checkIfFreeToReplace' :: String -> Set.Set String -> Set.Set String -> PeanoFormula -> Bool
    checkIfFreeToReplace' x variables quantifiers formula = case formula of
      (PeanoVariable v) -> x /= v || Set.null (Set.intersection variables quantifiers)
      _                 -> mapFold (&&) True (checkIfFreeToReplace' x variables quantifiers) . splitPeanoFormula $ formula

replace :: PropFormula -> PropFormula -> String -> Maybe (Set.Set PeanoFormula)
replace a b x
  = if not (checkPropFormulaTypeIdentity a b)
    then Nothing
    else case (a, b) of
      (PropString s, PropString t) -> if s == t then Just Set.empty else Nothing
      (u := v, u' := v')           -> replace' u u' x +:+ replace' v v' x
      _                            -> case (splitQuantifier a, splitQuantifier b) of
        (Just (ax, ap), Just (bx, bp)) -> quantifierChecker a b ap bp ax bx x
        _                              -> unionFoldX (flip (flip . replace)) (splitPropFormula a) (splitPropFormula b)
  where
    replace' a@(PeanoVariable v) b x
      | x == v    = Just (Set.singleton b)
      | a == b    = Just Set.empty
      | otherwise = Nothing
    replace' a b x
      | checkPeanoFormulaTypeIdentity a b 
        = unionFoldX (flip (flip . replace')) (splitPeanoFormula a) (splitPeanoFormula b)
      | otherwise = Nothing

    unionFoldX :: (String -> a -> b -> Maybe (Set.Set PeanoFormula)) -> [a] -> [b] -> Maybe (Set.Set PeanoFormula)
    unionFoldX f l1 l2 = foldl' (+:+) (Just Set.empty) $ zipWith (f x) l1 l2

    quantifierChecker :: PropFormula -> PropFormula -> 
                   PropFormula -> PropFormula -> 
                   String -> String -> String -> 
                   Maybe (Set.Set PeanoFormula)
    quantifierChecker a b ap bp ax bx x
        | x /= ax && ax == bx = replace ap bp x
        | x == ax && a == b   = Just Set.empty
        | otherwise           = Nothing

infixl 5 +:+
(+:+) :: Maybe (Set.Set PeanoFormula) -> Maybe (Set.Set PeanoFormula) -> Maybe (Set.Set PeanoFormula)
(Just x) +:+ (Just y) = Just $ Set.union x y
_        +:+ _        = Nothing 

analyze 
  :: PropFormula  
  -> [PropFormula]
  -> [(Integer, PropFormula)] 
  -> Map.Map PropFormula [PropFormula]
  -> [StepInformation]
analyze given hypotheses proof mpContainer = go given hypotheses proof mpContainer Map.empty
  where
    go :: PropFormula 
       -> [PropFormula]
       -> [(Integer, PropFormula)] 
       -> Map.Map PropFormula [PropFormula]
       -> Map.Map PropFormula StepInformation
       -> [StepInformation]
    go given hypotheses [] mpContainer buffer = []
    go given hypotheses ((n, l):ls) mpContainer buffer
      = case axSch n l <|> hyp n l <|> mp n l buffer <|> axFA n l <|> ind n l <|> intro n l buffer <|> axSch11And12 n l of
          Just si -> case si of 
            Step  _ _ -> if null ls
                         then if l == given
                              then si : go given hypotheses ls mpContainer (Map.insert l si buffer)
                              else si : [Error DifferentProof]
                         else si : go given hypotheses ls mpContainer (Map.insert l si buffer)
            Error _   -> [si]
          Nothing -> [Error (NotProven n)]

    axSch :: Integer -> PropFormula -> Maybe StepInformation
    axSch n f = fmap (\i -> Step (Row n (AxiomSchema i)) f) $ isAxiomSchema f

    hyp :: Integer -> PropFormula -> Maybe StepInformation
    hyp n cur = fmap (\i -> (Step (Row n (Hypothesis (toInteger (i + 1)))) cur)) 
              $ findIndex (==cur) hypotheses

    mp :: Integer -> PropFormula -> Map.Map PropFormula StepInformation -> Maybe StepInformation
    mp n cur buffer' = findMPReverse n cur buffer' mpContainer

    axFA :: Integer -> PropFormula -> Maybe StepInformation
    axFA n f = fmap (\i -> Step (Row n (AxiomFormalArithmetic i)) f) $ isAxiomFormalArithmetic f

    ind :: Integer -> PropFormula -> Maybe StepInformation
    ind n f = fmap (const (Step (Row n Induction) f)) $ isInduction f

    intro :: Integer -> PropFormula -> Map.Map PropFormula StepInformation -> Maybe StepInformation
    intro n f@(a :-> Forall x b) buffer
      | Map.member (a :-> b) buffer = if checkNonFreeOccurence a x 
                                      then Just $ Step (Row n (QIntro ((getPosition . getRow) (buffer Map.! (a :-> b))))) f
                                      else Just $ Error (FreeOccurence n x)
      | otherwise = Nothing
    intro n (Exists x b :-> a)   buffer = intro n (a :-> Forall x b) buffer
    intro _ _                    _      = Nothing

axSch11And12 :: Integer -> PropFormula -> Maybe StepInformation
axSch11And12 n (b :-> (Exists x a))   = axSch11And12 n ((Forall x a) :-> b)
axSch11And12 n f@((Forall x a) :-> b) = case isAxiomSchema11And12 f of
  Just k  -> Just $ Step (Row n (AxiomSchema k)) f
  Nothing -> fmap (\(_, term) -> Error (NotFreeVariable n x term)) (checkSubstitutionCorrectness' a b x)
axSch11And12 _ _                      = Nothing

findMPReverse 
  :: Integer 
  -> PropFormula 
  -> Map.Map PropFormula StepInformation 
  -> Map.Map PropFormula [PropFormula] 
  -> Maybe StepInformation
findMPReverse n b buffer mpContainer = case mpContainer Map.!? b of
  Nothing -> Nothing
  Just list -> case find (\a -> Map.member a buffer && Map.member (a :-> b) buffer) (reverse list) of
    Nothing -> Nothing
    Just a -> let l = ((getPosition . getRow) (buffer Map.! a))
                  r = ((getPosition . getRow) (buffer Map.! (a :-> b)))
              in Just $ Step (Row n (ModusPonens l r)) b

checkNonFreeOccurence :: PropFormula -> String -> Bool
checkNonFreeOccurence (Forall x p) v = x == v || checkNonFreeOccurence p v
checkNonFreeOccurence (Exists x p) v = x == v || checkNonFreeOccurence p v
checkNonFreeOccurence (p := q)     v = mapFold (&&) True (flip checkNonFreeOccurence' v) [p, q]
  where
    checkNonFreeOccurence' :: PeanoFormula -> String -> Bool
    checkNonFreeOccurence' (PeanoVariable x) v = x /= v
    checkNonFreeOccurence' f                 v = mapFold (&&) True (flip checkNonFreeOccurence' v) . splitPeanoFormula $ f
checkNonFreeOccurence _            _ = undefined