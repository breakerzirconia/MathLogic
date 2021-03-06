{-# LANGUAGE Strict #-}

module Main where

import qualified Data.List           as List
import qualified Data.Map.Strict     as Map
import           Data.Maybe
import qualified Data.Text           as Text
import           MathLogicEssentials
import           Parser
import           Proof
import           System.IO

-- given the formal proof, checks if it's correct and minimizes it (excluding predicate calculus and formal arithmetic)
-- main :: IO ()
-- main = do
--     -- handle <- openFile "in.txt" ReadMode
--     -- everything <- hGetContents handle
--     everything <- getContents
--     let (rawInitial:rawProof) = lines everything
--         proof = fmap parse rawProof
--         toProve = fmap Text.unpack (Text.splitOn (Text.pack "|-") (Text.pack rawInitial))
--         statement = parse . head . tail $ toProve
--         rawHypotheses = fmap Text.unpack (Text.splitOn (Text.pack ",") (Text.pack (head toProve)))
--         hypotheses = if null (head rawHypotheses) then [] else fmap parse rawHypotheses 
--         mpContainer = Map.fromListWith (++) . fmap (\(a :-> b) -> (b, [a])) $ filter isOuterImplication proof
--         res = try statement hypotheses (zip [1..] proof) (Just (Map.empty :: Map.Map PropFormula Row)) mpContainer
--     if last proof == statement && res /= Nothing 
--     then let buffer = fromJust res
--          in putStrLn $ constructMinProof rawInitial statement hypotheses buffer mpContainer
--     else putStrLn "Proof is incorrect" 
--     -- hClose handle

-- given the formal proof, checks if it's correct (including predicate calculus and formal arithmetic)
main :: IO ()
main = do
    handle <- openFile "C:\\Users\\ter-k\\Haskell\\MathLogic\\app\\in.txt" ReadMode
    everything <- hGetContents handle
    -- everything <- getContents
    let (rawFormula:rawProof) = lines everything
        formula = parse . tail . tail $ rawFormula
        proof = map parse rawProof
        -- mpContainer = Map.fromListWith (++) . fmap (\(a :-> b) -> (b, [a])) $ filter isOuterImplication proof
        cooked = analyze formula [] (zip [1..] proof) {-mpContainer-}
    putStrLn . unlines . (("|-" ++ show formula) :) . map show $ cooked
    hClose handle

-- -- given the propositional formula, constructs the proof
-- main :: IO ()
-- main = do
--     handle <- openFile "C:\\Users\\ter-k\\Haskell\\MathLogic\\app\\in.txt" ReadMode
--     everything <- hGetContents handle
--     -- everything <- getContents
--     let formula = parse everything
--         proof = constructProof formula
--     hClose handle