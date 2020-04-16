module Proof 
    ( isAxiom
    , try
    , Mode (..)
    , Row (..)
    , constructMinProof
    ) where

import Data.List
import Data.Maybe
import qualified Data.Map as Map
import MathLogicEssentials

data Mode = AxiomSchema Int | ModusPonens Int Int | Hypothesis Int deriving Eq

instance Show Mode where
    show (AxiomSchema x) = "Ax. sch. " ++ show x
    show (ModusPonens a b) = "M.P. " ++ show a ++ ", " ++ show b
    show (Hypothesis h) = "Hypothesis " ++ show h

data Row = Row { getPosition :: Int
               , getMode :: Mode 
               } deriving Eq

instance Show Row where
    show (Row i m) = "[" ++ show i ++ ". " ++ show m ++ "]"

showRPF :: (PropFormula, Row) -> String
showRPF (p, r) = show r ++ " " ++ show p

constructMinProof :: String -> PropFormula -> [PropFormula] -> Map.Map PropFormula Row -> String
constructMinProof rawInitial statement hypotheses buffer 
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
          (checker, newDetailedProof) = try statement hypotheses (zip [1..] newProof) (Map.empty :: Map.Map PropFormula Row)
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
                                  
try 
    :: PropFormula 
    -> [PropFormula] 
    -> [(Int, PropFormula)] 
    -> Map.Map PropFormula Row 
    -> (Bool, Map.Map PropFormula Row)
try statement hypotheses [] buffer = (buffer Map.!? statement /= Nothing, buffer)
try statement hypotheses ((pos, cur):rest) buffer
    | ind /= Nothing = try statement hypotheses rest (Map.insert cur (Row pos (Hypothesis (fromJust ind + 1))) buffer)
    | ax /= Nothing = try statement hypotheses rest (Map.insert cur (Row pos (AxiomSchema (fromJust ax))) buffer)
    | mp /= Nothing = let (i1, i2) = fromJust mp 
                          (i1', i2') = (max i1 i2, min i1 i2)
                      in try statement hypotheses rest (Map.insert cur (Row pos (ModusPonens i1' i2')) buffer)
    | otherwise = (False, buffer)
    where ax = isAxiom cur
          ind = findIndex (==cur) hypotheses
          mp = findMP cur buffer

findMP :: PropFormula -> Map.Map PropFormula Row -> Maybe (Int, Int)
findMP b buffer = case find (\(a, row) -> Map.member (a :-> b) buffer) (Map.assocs buffer) of
                      Nothing -> Nothing
                      Just (a, row1) -> let row2 = buffer Map.! (a :-> b)
                                        in Just ((getPosition row1), (getPosition row2))


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
                                                   else isAxiom3or4 p
    _ -> isAxiom3or4 p

isAxiom3or4 p = case p of
--  a :& b :-> a
--  a :& b :-> b
    a :& b :-> c -> if a == c
                    then Just 3
                    else if b == c
                         then Just 4
                         else isAxiom5 p
    _ -> isAxiom5 p

isAxiom5 p = case p of
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
                           else Nothing
    _ -> Nothing
