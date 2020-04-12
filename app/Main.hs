module Main where

import Lib

main :: IO ()
main = do
    print $ x
    print $ extractStrings x
    print $ map
    putStrLn $ transform x map
    print $ retrieveValue x map
    putStrLn $ "The given propositional formula is " 
             ++ if isTautology x
                then "a tautology."
                else "not a tautology."
  where
    x =   (PropString   "A") 
      :-> (PropString   "A")  :&  (PropString "B") 
      :-> ((PropValue     L)  :-> (PropString "C"))
      :-> (Not (PropString "B")) 
    map = [("A", T), ("B", L), ("C", T)]