module Main where

import Lib

main :: IO ()
main = do
    print $ x
    print $ extractVariables x
    print $ map
    putStrLn $ transform x map
    print $ retrieveValue x map
    putStrLn $ "The given propositional formula is " 
             ++ if isTautology x
                then "a tautology."
                else "not a tautology."
  where
    x =   (PropVariable 'A') 
      :-> (PropVariable 'A')  :&  (PropVariable 'B') 
      :-> ((PropValue     L)  :-> (PropVariable 'C'))
      :-> (Not (PropVariable 'B')) 
    map = [('A', T), ('B', L), ('C', T)]