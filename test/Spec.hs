{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections     #-}
{-# LANGUAGE BangPatterns       #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE RecordWildCards    #-}
{-# LANGUAGE ScopedTypeVariables #-}

import Test.Hspec
import Control.Exception (evaluate)

import Parse
import Core
import Unify
import Text.Megaparsec (Parsec)
import qualified Text.Megaparsec as M
import qualified Text.Megaparsec.Error
import qualified Text.Megaparsec.Char as M
import qualified Text.Megaparsec.Char.Lexer as L
import Data.Text (strip, unpack, Text, pack)
import qualified Data.Set as S
import qualified Data.HashMap.Strict as H
import Control.Monad

import Debug.Trace

-- ndetake source: https://stackoverflow.com/a/54130302
ndetake :: Int -> [a] -> [[a]]
ndetake n xs = go (length xs) n xs
    where
    go spare n _  | n >  spare = []
    go spare n xs | n == spare = [xs]
    go spare 0 _      =  [[]]
    go spare n []     =  []
    go spare n (x:xs) =  map (x:) (go (spare-1) (n-1) xs)
                            ++     go (spare-1)  n   xs

main :: IO ()
main = hspec $ do
  describe "Complex rules" $ do
      it "(1 - simple case) ancestry example with three terms: parent, sibling, has_children" $ do
        let termsEnv = H.fromListWith (++) [
              ("parent/2", [TermExp "parent" [(LiteralExp (AtomVal "stephen")), (LiteralExp (AtomVal "josh"))]])
              , ("parent/2", [TermExp "parent" [(LiteralExp (AtomVal "stephen")), (LiteralExp (AtomVal "michael"))]])
              , ("parent/2", [TermExp "parent" [(LiteralExp (AtomVal "stephen")), (LiteralExp (AtomVal "clarisa"))]])
              , ("parent/2", [TermExp "parent" [(LiteralExp (AtomVal "stephen")), (LiteralExp (AtomVal "sarah"))]])
              , ("parent/2", [TermExp "parent" [(LiteralExp (AtomVal "stephen")), (LiteralExp (AtomVal "jessicah"))]])
              , ("parent/2", [TermExp "parent" [(LiteralExp (AtomVal "michael")), (LiteralExp (AtomVal "brian"))]])
              , ("has_children/1", [ClosureExpr "has_children" [VarExp "P"] (TermExp "parent" [VarExp "P", VarExp "C"])])
              , ("siblings/2", [ClosureExpr "siblings" [VarExp "P", VarExp "S"] (BinaryExpression OpAnd
                   (TermExp "parent" [VarExp "Y", VarExp "P"]) -- dim(Y) == 1
                   (BinaryExpression OpAnd
                      (TermExp "parent" [VarExp "Y", VarExp "S"]) -- dim(Y) == 1 but dim(S) == 5
                      (BinaryExpression OpNotEq
                        (VarExp "P")
                        (VarExp "S"))
                 ))])
               ]
        let expression = (TermExp "siblings" [LiteralExp (AtomVal "michael"), (VarExp "S")])
        let expectedSolutions = [
              [("S", (LiteralExp (AtomVal "josh")))]
              , [("S", (LiteralExp (AtomVal "clarisa")))]
              , [("S", (LiteralExp (AtomVal "sarah")))]
              , [("S", (LiteralExp (AtomVal "jessicah")))]
              ]
        (unify termsEnv [] expression) `shouldBe` (True, expectedSolutions)

      it "(2 - cut operator case) if expression ambiguous branches" $ do
        let termsEnv = H.fromListWith (++) [
              ("xy/2", [TermExp "xy" [(LiteralExp (NumVal 5)), (LiteralExp (NumVal 5))]])
              , ("xy/2", [TermExp "xy" [(LiteralExp (NumVal 5)), (LiteralExp (NumVal 15))]])
              , ("xy/2", [TermExp "xy" [(LiteralExp (NumVal 5)), (LiteralExp (NumVal 20))]])
              , ("find_y/2", [ClosureExpr "find_y" [VarExp "X", VarExp "Y"] (BinaryExpression OpAnd
                      (CutExp (TermExp "xy" [VarExp "X", VarExp "Y"]))
                      (BinaryExpression
                        OpCompGt
                        (VarExp "Y") (LiteralExp (NumVal 5))))
                 ])
               ]
        let expression = (TermExp "find_y" [LiteralExp (NumVal 5), VarExp "Y"])
        let expectedSolutions = [
              [("Y", (LiteralExp (NumVal 20)))]
              ]
        (unify termsEnv [] expression) `shouldBe` (True, expectedSolutions)

  describe "Unification" $ do
    describe "term unifications" $ do
      it "unify(term(enumerated list)) with const list expr" $ do
        let termsEnv = H.fromListWith (++) [
              ("a/1", [TermExp "a" [(ListExp (EnumeratedList [LiteralExp (NumVal 1), LiteralExp (NumVal 2), LiteralExp (NumVal 3)]))]])
              , ("a/1", [TermExp "a" [(LiteralExp (AtomVal "a"))]])
               ]
        let expression = (TermExp "a" [ListExp (ConsList (VarExp "H") (VarExp "L"))])
        let expectedSolutions = [
              [("L", (ListExp (EnumeratedList [(LiteralExp (NumVal 2)), (LiteralExp (NumVal 3))]))), ("H", (LiteralExp (NumVal 1)))]
              ]
        (unify termsEnv [] expression) `shouldBe` (True, expectedSolutions)

      it "unify(term(enumerated list)) with enumerated list expr" $ do
        let termsEnv = H.fromListWith (++) [
              ("a/1", [TermExp "a" [(ListExp (EnumeratedList [LiteralExp (NumVal 1), LiteralExp (NumVal 2), LiteralExp (NumVal 3)]))]])
             ]
        let expression = (TermExp "a" [ListExp (EnumeratedList [(VarExp "H"), (VarExp "L"), (VarExp "D")])])
        let expectedSolutions = [
              [("H", (LiteralExp (NumVal 1))), ("L", (LiteralExp (NumVal 2))), ("D", (LiteralExp (NumVal 3)))]
              ]
        (unify termsEnv [] expression) `shouldBe` (True, expectedSolutions)

      it "unify(term(literal))" $ do
        let termsEnv = H.fromListWith (++) [
              -- first term: a(1)
              ("a/1", [TermExp "a" [(LiteralExp (NumVal 1))]])
              -- second term: a(a)
              , ("a/1", [TermExp "a" [(LiteralExp (AtomVal "a"))]])
               ]
        let expression = (TermExp "a" [VarExp "X"])
        let expectedSolutions = [
              [("X", (LiteralExp (NumVal 1)))]
              , [("X", (LiteralExp (AtomVal "a")))]
              ]
        (unify termsEnv [] expression) `shouldBe` (True, expectedSolutions)

      it "unify(rule) non-recursive, positive, no subst" $ do
        let termsEnv = H.fromListWith (++) [
              -- first term: check-a(X) :- X > 7.
              ("check-a/1", [ClosureExpr "check-a" [VarExp "X"] (BinaryExpression OpCompGt (VarExp "X") (LiteralExp (NumVal 7)))])
              -- second term: check-a(X, Y) :- X > Y.
              , ("check-a/2", [ClosureExpr "check-a" [VarExp "X", VarExp "Y"] (BinaryExpression OpCompGt (VarExp "X") (VarExp "Y"))])
               ]
        let expression = (TermExp "check-a" [LiteralExp (NumVal 12)])
        (unify termsEnv [] expression) `shouldBe` (True, [])

      it "unify(rule) non-recursive, negative" $ do
        let termsEnv = H.fromListWith (++) [
              -- first term: check-a(X) :- X > 7.
              ("check-a/1", [ClosureExpr "check-a" [VarExp "X"] (BinaryExpression OpCompGt (VarExp "X") (LiteralExp (NumVal 7)))])
              -- second term: check-a(X, Y) :- X > Y.
              , ("check-a/2", [ClosureExpr "check-a" [VarExp "X", VarExp "Y"] (BinaryExpression OpCompGt (VarExp "X") (VarExp "Y"))])
               ]
        let expression = (TermExp "check-a" [LiteralExp (NumVal 6)])
        (unify termsEnv [] expression) `shouldBe` (True, [])

      it "unify(binary expression, rule) recursive, positive, with subst" $ do
        let termsEnv = H.fromListWith (++) [
              -- first term: check-a(X) :- X > 7.
              ("check-a/1", [ClosureExpr "check-a" [VarExp "X"] (BinaryExpression OpAnd (TermExp "check-a" [VarExp "X", VarExp "Y"])
                  (BinaryExpression OpCompGt (VarExp "Y") (LiteralExp (NumVal 7))))])
              -- second term: check-a(X, Y) :- X > Y.
              , ("check-a/2", [TermExp "check-a" [LiteralExp (NumVal 10), LiteralExp (NumVal 10)]])
              , ("check-a/2", [TermExp "check-a" [LiteralExp (NumVal 9), LiteralExp (NumVal 9)]])
              , ("check-a/2", [TermExp "check-a" [LiteralExp (NumVal 8), LiteralExp (NumVal 8)]])
              , ("check-a/2", [TermExp "check-a" [LiteralExp (NumVal 7), LiteralExp (NumVal 6)]])
               ]
        let expression = (TermExp "check-a" [VarExp "X"])
        let solutions = (unify termsEnv [] expression)
        solutions `shouldBe` (True, [
          [("X", (LiteralExp (NumVal 10)))]
          , [("X", (LiteralExp (NumVal 9)))]
          , [("X", (LiteralExp (NumVal 8)))]
          ])
      it "unify(unary expression, rule) recursive, positive, with subst" $ do
        let termsEnv = H.fromListWith (++) [
              -- first term: check-a(X) :- X > 7.
              ("check-a/1", [ClosureExpr "check-a" [VarExp "X"] (BinaryExpression OpCompGt
                (UnaryExpression OpMin (VarExp "X"))
                (LiteralExp (NumVal 5)))])
               ]
        let expressions = fmap (\counter -> (((-counter) > 5), (TermExp "check-a" [LiteralExp (NumVal counter)]))) (fmap (\x -> -1 * x) [0..9])
        let solutions = fmap (\(expected, exp) ->
              case (unify termsEnv [] exp) of
                (actualVal, _) -> actualVal == expected) expressions
        solutions `shouldBe` (take 6 (repeat False)) ++ (take 4 (repeat True))


  describe "Parsing" $ do
    describe "instructions support" $ do
      it "a consult instruction" $ do
        result <- processInstructions [ConsultStmt "test/resources/test01.prolog"]
        result `shouldBe` (Right [
            (RuleStmt "fact" [LiteralExp (AtomVal "a")] Nothing)
            , (RuleStmt "fact" [LiteralExp (AtomVal "b")] Nothing)
            , (RuleStmt "fact" [LiteralExp (AtomVal "c")] Nothing)
            , (RuleStmt "factB" [VarExp "C", VarExp "A"] Nothing)
            , (RuleStmt "factD" [VarExp "C"] (Just (BinaryExpression OpAnd (BinaryExpression OpCompGt (VarExp "C") (LiteralExp (NumVal 1))) (LiteralExp (BoolVal True)))))
          ])

    describe "statements parsing" $ do
      it "a single fact" $ do
        M.runParser (program "test") "" "factC(A)." `shouldBe` (Right (Right (Program "test" [(RuleStmt "factC" [VarExp "A"] Nothing)])))

      it "a consult instruction" $ do
        M.runParser (program "test") "" "consult('resources/test01.prolog')." `shouldBe` (Right (Right (Program "test" [ConsultStmt "resources/test01.prolog"])))

      it "multiple facts (no body)" $ do
        let facts = (take 100 (repeat ("factC(1, a, d).", RuleStmt "factC" [(LiteralExp (NumVal 1)), (LiteralExp (AtomVal "a")), (LiteralExp (AtomVal "d"))] Nothing)))
        let results = (fmap (\fact ->
                case (M.runParser (program "test") "" (fst fact)) of
                  (Right (Right (Program _ stms))) ->
                    (length stms) == 1 && (head stms) == (snd fact)
                  _ -> False
              ) facts)
        results `shouldBe` (take 100 (repeat True))

      it "a rule with a cut operator" $ do
        let fact = RuleStmt "fact" [VarExp "A"] (Just (BinaryExpression OpAnd (CutExp (TermExp "test" [VarExp "A"])) (LiteralExp (BoolVal True))))
        let result = (M.runParser (program "test") "" "fact(A) :- test(A), !.")
        result `shouldBe` (Right (Right (Program "test" [fact])))

      it "multiple rules" $ do
        let facts = (take 100 (repeat ("factC(X, A, D) :- X > A, A > D, fact(D).",
              RuleStmt "factC" [VarExp "X", VarExp "A", VarExp "D"] (Just
                (BinaryExpression OpAnd
                  (BinaryExpression OpCompGt (VarExp "X") (VarExp "A"))
                  (BinaryExpression OpAnd
                    (BinaryExpression OpCompGt (VarExp "A") (VarExp "D"))
                    (BinaryExpression OpAnd
                      (TermExp "fact" [VarExp "D"])
                      (LiteralExp (BoolVal True)))
                ))))))
        let results = (fmap (\fact ->
                case (M.runParser (program "test") "" (fst fact)) of
                  (Right (Right (Program _ stms))) ->
                    let
                      result = (length stms) == 1 && (head stms) == (snd fact)
                    in
                      if result then result
                      else trace("Length: expected=1, actual=" ++ (show (length stms)) ++ "\n\r Value: expected=" ++ (show (snd fact)) ++ ", actual: " ++ (show (head stms))) result
                  _ -> False
              ) facts)
        results `shouldBe` (take 100 (repeat True))

    describe "expressions parsing" $ do
      it "an integer (unsigned)" $ do
        M.runParser (expression) "" "4242" `shouldBe` (Right (Right (LiteralExp (NumVal 4242))))

      it "a parameterised term expression (1)" $ do
        M.runParser (expression) "" "factC(A)." `shouldBe` (Right (Right (TermExp "factC" [VarExp "A"])))

      it "a parameterised term expression: var + enum list" $ do
        M.runParser (expression) "" "factC(A, [1, True, 'test'])." `shouldBe` (Right (Right (TermExp "factC" [VarExp "A",
             (ListExp (EnumeratedList [(LiteralExp (NumVal 1)), (LiteralExp (BoolVal True)), (LiteralExp (StringVal "test"))]))])))

      it "a parameterised term expression: unary expression" $ do
        M.runParser (expression) "" "factC(not A)." `shouldBe` (Right (Right (TermExp "factC" [(UnaryExpression OpNot (VarExp "A"))])))

      it "a non-parameterised term expression" $ do
        M.runParser (expression) "" "factC()" `shouldBe` (Right (Right (TermExp "factC" [])))

      it "a binary expression (nested)" $ do
        M.runParser (expression) "" "A and (B or (B and C))" `shouldBe` (Right (Right (BinaryExpression OpAnd (VarExp "A") (BinaryExpression OpOr (VarExp "B") (BinaryExpression OpAnd (VarExp "B") (VarExp "C"))))))

      it "a binary expression (simple) - var and term" $ do
        M.runParser (expression) "" "A and fact(C)" `shouldBe` (Right (Right (BinaryExpression OpAnd (VarExp "A") (TermExp "fact" [VarExp "C"]))))

      it "a binary expression (simple) - var and literal" $ do
        M.runParser (expression) "" "A and 1" `shouldBe` (Right (Right (BinaryExpression OpAnd (VarExp "A") (LiteralExp (NumVal 1)))))

      it "a binary expression (simple) - literal and literal" $ do
        M.runParser (expression) "" "25 and False" `shouldBe` (Right (Right (BinaryExpression OpAnd (LiteralExp (NumVal 25)) (LiteralExp (BoolVal False)))))

      it "a binary expression (simple) [all operators]" $ do
        let ops = [("not", OpNot), ("-", OpMin)]
        let operands = [("A", VarExp "A")
                          , ("2", LiteralExp (NumVal 2))
                          , ("False", (LiteralExp (BoolVal False)))
                          , ("True", (LiteralExp (BoolVal True)))
                          , ("name()", (TermExp "name" []))
                          , ("name(B)", (TermExp "name" [VarExp "B"]))
                          , ("term(a)", (TermExp "term" [LiteralExp (AtomVal "a")]))]

        let expected = (Right [Right (UnaryExpression OpNot (LiteralExp (BoolVal False)))
                              , Right (UnaryExpression OpMin (LiteralExp (BoolVal False)))])

        let testPairs = ndetake 2 operands
        let results = ops >>= (\op ->
              fmap (\pair ->
                case pair of
                  (left:(right:[])) ->
                    case M.runParser (expression) "" (pack ((fst left) ++ " " ++ (fst op) ++ " " ++ (fst right))) of
                      (Right (Right exp)) ->
                        exp == (BinaryExpression (snd op) (snd left) (snd right))
                      _ -> False
                ) testPairs)
        results `shouldBe` (take ((length testPairs) * (length ops)) (repeat True))

      it "cons list" $ do
        M.runParser (expression) "" "[A | [B | [C | []]]]]" `shouldBe` (Right (Right (ListExp (ConsList (VarExp "A") (ListExp (ConsList (VarExp "B") (ListExp (ConsList (VarExp "C") (ListExp EmptyList)))))))))

      it "unary expressions (literals) on [-, not]" $ do
        let ops = [("not", OpNot), ("-", OpMin)]
        let expected = (Right [Right (UnaryExpression OpNot (LiteralExp (BoolVal False)))
                              , Right (UnaryExpression OpMin (LiteralExp (BoolVal False)))])
        (sequence $ fmap (\op -> M.runParser (expression) "" (pack ((fst op) ++ "False"))) ops) `shouldBe` expected
