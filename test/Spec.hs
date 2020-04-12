import Test.Hspec
import Lib

main :: IO ()
main = hspec $ do
    describe "Axiom schema" $ do
        it "testing axiom #1: a -> b -> a" $ do
            isTautology ((PropVariable 'A') 
                     :-> (PropVariable 'B') 
                     :-> (PropVariable 'A')) `shouldBe` True
        it "testing axiom #2: (a -> b) -> (a -> b -> c) -> (a -> c)" $ do
            isTautology (((PropVariable 'A') :-> (PropVariable 'B')) 
                     :-> ((PropVariable 'A') :-> (PropVariable 'B') :-> (PropVariable 'C'))
                     :-> ((PropVariable 'A') :-> (PropVariable 'C'))) `shouldBe` True
        it "testing axiom #3: a & b -> a" $ do
            isTautology ((PropVariable 'A') :& (PropVariable 'B')
                     :-> (PropVariable 'A')) `shouldBe` True
        it "testing axiom #4: a & b -> b" $ do
            isTautology ((PropVariable 'A') :& (PropVariable 'B')
                     :-> (PropVariable 'B')) `shouldBe` True
        it "testing axiom #5: a -> b -> a & b" $ do
            isTautology ((PropVariable 'A')
                     :-> (PropVariable 'B')
                     :-> (PropVariable 'A') :& (PropVariable 'B')) `shouldBe` True
        it "testing axiom #6: a -> a v b" $ do
            isTautology ((PropVariable 'A')
                     :-> (PropVariable 'A') :| (PropVariable 'B')) `shouldBe` True
        it "testing axiom #7: b -> a v b" $ do
            isTautology ((PropVariable 'B')
                     :-> (PropVariable 'A') :| (PropVariable 'B')) `shouldBe` True
        it "testing axiom #8: (a -> c) -> (b -> c) -> (a v b -> c)" $ do
            isTautology (((PropVariable 'A') :-> (PropVariable 'C'))
                     :-> ((PropVariable 'B') :-> (PropVariable 'C'))
                     :-> ((PropVariable 'A') :|  (PropVariable 'B') :-> (PropVariable 'C'))) `shouldBe` True
        it "testing axiom #9: (a -> b) -> (a -> !b) -> !a" $ do
            isTautology (((PropVariable 'A') :-> (PropVariable 'B'))
                     :-> ((PropVariable 'A') :-> Not (PropVariable 'B')) 
                     :-> Not (PropVariable 'A')) `shouldBe` True
        it "testing axiom #10: !!a -> a" $ do
            isTautology (Not (Not (PropVariable 'A'))
                     :-> (PropVariable 'A')) `shouldBe` True
    describe "Contradictory statements" $ do
        it "testing contradictory statement #1: a & !a" $ do
            isContradictory ((PropVariable 'A') :& Not (PropVariable 'A')) `shouldBe` True
