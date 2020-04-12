import Test.Hspec
import Lib

main :: IO ()
main = hspec $ do
    describe "Axiom schema" $ do
        it "testing axiom #1: a -> b -> a" $ do
            isTautology ((PropString "A") 
                     :-> (PropString "B") 
                     :-> (PropString "A")) `shouldBe` True
        it "testing axiom #2: (a -> b) -> (a -> b -> c) -> (a -> c)" $ do
            isTautology (((PropString "A") :-> (PropString "B")) 
                     :-> ((PropString "A") :-> (PropString "B") :-> (PropString "C"))
                     :-> ((PropString "A") :-> (PropString "C"))) `shouldBe` True
        it "testing axiom #3: a & b -> a" $ do
            isTautology ((PropString "A") :& (PropString "B")
                     :-> (PropString "A")) `shouldBe` True
        it "testing axiom #4: a & b -> b" $ do
            isTautology ((PropString "A") :& (PropString "B")
                     :-> (PropString "B")) `shouldBe` True
        it "testing axiom #5: a -> b -> a & b" $ do
            isTautology ((PropString "A")
                     :-> (PropString "B")
                     :-> (PropString "A") :& (PropString "B")) `shouldBe` True
        it "testing axiom #6: a -> a v b" $ do
            isTautology ((PropString "A")
                     :-> (PropString "A") :| (PropString "B")) `shouldBe` True
        it "testing axiom #7: b -> a v b" $ do
            isTautology ((PropString "B")
                     :-> (PropString "A") :| (PropString "B")) `shouldBe` True
        it "testing axiom #8: (a -> c) -> (b -> c) -> (a v b -> c)" $ do
            isTautology (((PropString "A") :-> (PropString "C"))
                     :-> ((PropString "B") :-> (PropString "C"))
                     :-> ((PropString "A") :|  (PropString "B") :-> (PropString "C"))) `shouldBe` True
        it "testing axiom #9: (a -> b) -> (a -> !b) -> !a" $ do
            isTautology (((PropString "A") :-> (PropString "B"))
                     :-> ((PropString "A") :-> Not (PropString "B")) 
                     :-> Not (PropString "A")) `shouldBe` True
        it "testing axiom #10: !!a -> a" $ do
            isTautology (Not (Not (PropString "A"))
                     :-> (PropString "A")) `shouldBe` True
    describe "Contradictory statements" $ do
        it "testing contradictory statement #1: a & !a" $ do
            isContradictory ((PropString "A") :& Not (PropString "A")) `shouldBe` True
