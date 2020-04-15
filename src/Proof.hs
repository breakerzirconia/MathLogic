module Proof 
    ( isAxiom
--    , (|-)
    , isCorrect
    , performMinProof
    ) where

import MathLogicEssentials
import Data.List
import Data.Maybe

data Mode = AxiomSchema Int | ModusPonens Int Int | Hypothesis Int

instance Show Mode where
    show (AxiomSchema x) = "Ax. sch. " ++ show x
    show (ModusPonens a b) = "M.P. " ++ show a ++ ", " ++ show b
    show (Hypothesis h) = "Hypothesis " ++ show h

data Row = Row { getPosition :: Int
               , getMode :: Mode
               , getPropFormula :: PropFormula 
               }

instance Show Row where
    show (Row i m p) = "[" ++ show i ++ ". " ++ show m ++ "] " ++ show p

minimize
    :: [PropFormula] 
    -> [PropFormula] 
    -> [PropFormula]
    -> [PropFormula]
    -> [PropFormula]
minimize _ _ buffer [] = buffer
minimize hypotheses reverseProof buffer {-queue@-}(cur:rest)
    | cur `elem` hypotheses || fst (isAxiom cur) = minimize hypotheses reverseProof (cur:buffer) rest
    | otherwise = minimize hypotheses reverseProof (cur:buffer) (rest ++ findMP cur reverseProof)

findMP :: PropFormula -> [PropFormula] -> [PropFormula]
findMP statement reverseProof = findMP' statement $ (,) <$> reverseProof <*> reverseProof
  where
    findMP' b [] = []
    findMP' b ((ab,a):rest) = if isOuterImplication ab
                              then let (a' :-> b') = ab
                                   in if a == a'
                                      && b == b'
                                      then [ab, a]
                                      else findMP' b rest
                              else findMP' b rest

construct :: [PropFormula] -> [(Int, PropFormula)] -> [Row] -> [Row]
construct _ [] buffer = reverse buffer
construct hypotheses ((n,cur):rest) buffer
    | fst ax = construct hypotheses rest ((Row n (AxiomSchema (snd ax)) cur):buffer)
    | ind /= Nothing = construct hypotheses rest ((Row n (Hypothesis (fromJust ind + 1)) cur):buffer)
    | otherwise = let (i1, i2) = findMPIndices cur buffer
                  in construct hypotheses rest ((Row n (ModusPonens i1 i2) cur):buffer)
  where 
    ax = isAxiom cur
    ind = findIndex (==cur) hypotheses

findMPIndices :: PropFormula -> [Row] -> (Int, Int)
findMPIndices statement buffer = findMPIndices' statement $ (,) <$> buffer <*> buffer
  where
    findMPIndices' b [] = (0, 0)
    findMPIndices' b ((r1, r2):rest) = let Row n1 _ ab = r1
                                           Row n2 _ a = r2
                                       in if isOuterImplication ab
                                          then let (a' :-> b') = ab
                                               in if a == a'
                                                  && b == b'
                                                  then (n1, n2)
                                                  else findMPIndices' b rest
                                          else findMPIndices' b rest

performMinProof 
    :: PropFormula 
    -> [PropFormula] 
    -> [PropFormula]
    -> String
performMinProof s h p = let mP = minimize h (reverse p) [] [s]
                            cmP = construct h (zip [1..] mP) []
                        in unlines . map show $ cmP

isCorrect :: PropFormula -> [PropFormula] -> [PropFormula] -> [PropFormula] -> Bool
isCorrect statement _ [] (buf:_) = buf == statement
isCorrect statement hypotheses (cur:rest) buffer
    | cur `elem` hypotheses ||
      fst (isAxiom cur) ||
      isMP cur buffer = isCorrect statement hypotheses rest (cur:buffer)
    | otherwise = False

isMP :: PropFormula -> [PropFormula] -> Bool
isMP statement buffer = isMP' statement $ (,) <$> buffer <*> buffer
  where
    isMP' b [] = False
    isMP' b ((a,ab):rest) = if isOuterImplication ab
                            then let (a' :-> b') = ab
                                 in (a == a' && b == b') || isMP' b rest
                            else isMP' b rest

isAxiom :: PropFormula -> (Bool, Int)
isAxiom = isAxiom1

isAxiom1 p = case p of
--  a :-> b :-> c    
    a :-> b :-> c -> if a == c 
                     then (True, 1) 
                     else isAxiom2 p
    _ -> isAxiom2 p

isAxiom2 p = case p of
--  (a :-> b) :-> (a :-> b :-> c) :-> (a :-> c)
    (a :-> b) :-> (c :-> d :-> e) :-> (f :-> g) -> if a == c
                                                   && a == f
                                                   && b == d
                                                   && e == g 
                                                   then (True, 2) 
                                                   else isAxiom3or4 p
    _ -> isAxiom3or4 p

isAxiom3or4 p = case p of
--  a :& b :-> a
--  a :& b :-> b
    a :& b :-> c -> if a == c
                    then (True, 3)
                    else if b == c
                         then (True, 4)
                         else isAxiom5 p
    _ -> isAxiom5 p

isAxiom5 p = case p of
--  a :-> b :-> a :& b
    a :-> b :-> c :& d -> if a == c && b == d
                          then (True, 5)
                          else isAxiom6or7 p
    _ -> isAxiom6or7 p

isAxiom6or7 p = case p of
--  a :-> a :| b
--  b :-> a :| b
    a :-> b :| c -> if a == b
                    then (True, 6)
                    else if a == c
                         then (True, 7)
                         else isAxiom8 p
    _ -> isAxiom8 p

isAxiom8 p = case p of
--  (a :-> c) :-> (b :-> c) :-> (a :| b :-> c)
    (a :-> b) :-> (c :-> d) :-> (e :| f :-> g) -> if a == e
                                                  && c == f
                                                  && b == d
                                                  && b == g
                                                  then (True, 8)
                                                  else isAxiom9 p
    _ -> isAxiom9 p    

isAxiom9 p = case p of
--  (a :-> b) :-> (a :-> Not b) :-> Not a
    (a :-> b) :-> (c :-> Not d) :-> Not e -> if a == c
                                             && a == e
                                             && b == d
                                             then (True, 9)
                                             else isAxiom10 p
    _ -> isAxiom10 p

isAxiom10 p = case p of
--  (Not (Not a)) :-> a
    (Not (Not a)) :-> b -> if a == b
                           then (True, 10)
                           else (False, 0)
    _ -> (False, 0)
