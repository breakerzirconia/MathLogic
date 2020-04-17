{-# LANGUAGE Strict #-}

module Main where

import qualified Data.Text as Text
import qualified Data.Map.Strict as Map
import qualified Data.List as List
import Data.Maybe
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
        mpContainer = Map.fromListWith (++) . fmap (\(a :-> b) -> (b, [a])) $ filter isOuterImplication proof
        res = try statement hypotheses (zip [1..] proof) (Just (Map.empty :: Map.Map PropFormula Row)) mpContainer
    if last proof == statement && res /= Nothing 
    then let buffer = fromJust res
         in putStrLn $ constructMinProof rawInitial statement hypotheses buffer mpContainer
    else putStrLn "Proof is incorrect" 
    -- hClose handle