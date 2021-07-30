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
import Control.Monad

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
  describe "expressions parsing" $ do
    it "a parameterised term expression (1)" $ do
      M.runParser (expression) "" "factC(A)." `shouldBe` (Right (Right (TermExp "factC" [VarExp "A"])))

    it "a parameterised term expression: var + enum list" $ do
      M.runParser (expression) "" "factC(A, [1, True, 'test'])." `shouldBe` (Right (Right (TermExp "factC" [VarExp "A",
           (ListExp (EnumeratedList [(LiteralExp (IntVal 1)), (LiteralExp (BoolVal True)), (LiteralExp (StringVal "test"))]))])))

    it "a parameterised term expression: unary expression" $ do
      M.runParser (expression) "" "factC(not A)." `shouldBe` (Right (Right (TermExp "factC" [(UnaryExpression OpNot (VarExp "A"))])))

    it "a non-parameterised term expression" $ do
      M.runParser (expression) "" "factC()" `shouldBe` (Right (Right (TermExp "factC" [])))

    it "a binary expression (nested)" $ do
      M.runParser (expression) "" "A and (B or (B and C))" `shouldBe` (Right (Right (BinaryExpression OpAnd (VarExp "A") (BinaryExpression OpOr (VarExp "B") (BinaryExpression OpAnd (VarExp "B") (VarExp "C"))))))

    it "a binary expression (simple) - var and term" $ do
      M.runParser (expression) "" "A and fact(C)" `shouldBe` (Right (Right (BinaryExpression OpAnd (VarExp "A") (TermExp "fact" [VarExp "C"]))))

    it "a binary expression (simple) - var and literal" $ do
      M.runParser (expression) "" "A and 1" `shouldBe` (Right (Right (BinaryExpression OpAnd (VarExp "A") (LiteralExp (IntVal 1)))))

    it "a binary expression (simple) - literal and literal" $ do
      M.runParser (expression) "" "25 and False" `shouldBe` (Right (Right (BinaryExpression OpAnd (LiteralExp (IntVal 25)) (LiteralExp (BoolVal False)))))

    it "a binary expression (simple) [all operators]" $ do
      let ops = [("not", OpNot), ("-", OpMin)]
      let operands = [("A", VarExp "A")
                        , ("2", LiteralExp (IntVal 2))
                        , ("False", (LiteralExp (BoolVal False)))
                        , ("True", (LiteralExp (BoolVal True)))
                        , ("name()", (TermExp "name" []))
                        , ("name(B)", (TermExp "name" [VarExp "B"]))]

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

  describe "Prelude.head" $ do
    it "[1] simple unification" $ do
      head [23 ..] `shouldBe` (23 :: Int)
