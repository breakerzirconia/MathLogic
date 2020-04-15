module Main where

import Data.List.Split
import System.IO
import Parser
import Proof

-- readLines :: IO [String]
-- readLines = do 
--     eof <- isEOF
--     if eof 
--     then return []
--     else do
--         line <- getLine
--         lines <- readLines
--         return $ line : lines

main :: IO ()
main = do
    handle <- openFile "in.txt" ReadMode
    everything <- hGetContents handle
    -- everything <- getContents
    let (rawInitial:rawProof) = lines everything
        proof = fmap parse rawProof
        toProve = splitOn "|-" rawInitial
        statement = parse . head . tail $ toProve
        rawHypotheses = splitOn "," $ head toProve
        hypotheses = if null (head rawHypotheses) then [] else fmap parse rawHypotheses 
    if isCorrect statement hypotheses proof [] 
    then putStrLn $ performMinProof statement hypotheses proof
    else putStrLn "Proof is incorrect" 
    hClose handle