{-# LANGUAGE Strict #-}

module Proof 
    ( isAxiom
    , try
    , Mode (..)
    , Row (..)
    , constructMinProof
    ) where

import Data.List
import Data.Maybe
import qualified Data.Map.Strict as Map
import MathLogicEssentials
import Control.Applicative ((<|>))

data Mode = AxiomSchema Int | ModusPonens Int Int | Hypothesis Int deriving (Eq, Ord)

instance Show Mode where
    show (AxiomSchema x) = "Ax. sch. " ++ show x
    show (ModusPonens a b) = "M.P. " ++ show a ++ ", " ++ show b
    show (Hypothesis h) = "Hypothesis " ++ show h

data Row = Row { getPosition :: Int
               , getMode :: Mode 
               } deriving (Eq, Ord)

instance Show Row where
    show (Row i m) = "[" ++ show i ++ ". " ++ show m ++ "]"

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
    ax = fmap AxiomSchema . isAxiom

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

isAxiom :: PropFormula -> Maybe Int
isAxiom = isAxiom1

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
--  a :-> b :-> a :& b
    a :-> b :-> c :& d -> if a == c && b == d
                          then Just 3
                          else isAxiom4or5 p
    _ -> isAxiom4or5 p

isAxiom4or5 p = case p of
--  a :& b :-> a
--  a :& b :-> b
    a :& b :-> c -> if a == c
                    then Just 4
                    else if b == c
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
                           else Nothing
    _ -> Nothing
