module Main where

import qualified Data.Text as Text
import qualified Data.Map.Strict as Map
import qualified Data.List as List
import System.IO
import Parser
import Proof
import MathLogicEssentials

main :: IO ()
main = do
    -- handle <- openFile "in.txt" ReadMode
    -- everything <- hGetContents handle
    everything <- getContents
    let (rawInitial:rawProof) = lines everything
        proof = fmap parse rawProof
        toProve = fmap Text.unpack (Text.splitOn (Text.pack "|-") (Text.pack rawInitial))
        statement = parse . head . tail $ toProve
        rawHypotheses = fmap Text.unpack (Text.splitOn (Text.pack ",") (Text.pack (head toProve)))
        hypotheses = if null (head rawHypotheses) then [] else fmap parse rawHypotheses 
        (checker, buffer) = try statement hypotheses (zip [1..] proof) (Map.empty :: Map.Map PropFormula Row)
        initial = (concat (List.intersperse ", " hypotheses)) ++ (if null hypotheses
                                                                  then "|- "
                                                                  else " |- ") ++ show statement
    if checker 
    then putStrLn $ constructMinProof initial statement hypotheses buffer
    else putStrLn "Proof is incorrect" 
    -- hClose handle