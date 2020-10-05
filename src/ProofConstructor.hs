module ProofConstructor where

import MathLogicEssentials
import Parser

constructProof :: PropFormula -> [(PropFormula, [PropFormula])]
constructProof formula 
    = let extractedStrings = extractStrings formula
--        truthTable :: [(LogicValue, PropVarMap)] <-> [(LogicValue, [(String, LogicValue)])] 
          truthTable = map (\x -> (retrieveValue formula x, x)) 
                     $ [zip extractedStrings value | value <- generateAllValues $ length extractedStrings] 
          checker = case ((fst . head) truthTable, (fst . last) truthTable) of
                        (T, L) -> ":("
                        (L, L) -> "0"
                        _      -> "1"
          filtered = filter (\(v, _) -> case checker of
                                            "0"  -> v == L
                                            "1"  -> v == T
                                            ":(" -> False) truthTable
--        prepare :: [(PropFormula, [PropFormula])]
          prepare = map (\(val, pvm) -> (if val == T then formula else Not formula,
                                         map (\(str, binding) -> if binding == T
                                                                 then PropString str
                                                                 else Not (PropString str)) pvm)) filtered
          cooked = map (\(given, hypotheses) -> construct given hypotheses) prepare
      in prepare

construct :: PropFormula -> [PropFormula] -> [PropFormula]
construct given hypotheses = undefined

writePrimitive :: PropFormula -> [PropFormula] -> [PropFormula]
writePrimitive given hypotheses 
    = let extractedStrings = extractStrings given
          -- filteredHypotheses = filter (\x -> not $ x `elem` extractedStrings) hypotheses
      in {-filteredHypotheses-} undefined
                             
{-
constructProof (A -> A & B):
    filteredTruthTable <- [(1,[("A",0),("B",0)]),(1,[("A",0),("B",1)]),(1,[("A",1),("B",1)])]
    
-}