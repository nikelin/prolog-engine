{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections     #-}
{-# LANGUAGE BangPatterns       #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE RecordWildCards    #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Main where

  import Parse
  import Core
  import Unify
  import Text.Megaparsec (Parsec)
  import qualified Text.Megaparsec as M
  import qualified Text.Megaparsec.Error
  import qualified Text.Megaparsec.Char as M
  import qualified Text.Megaparsec.Char.Lexer as L
  import Data.Text (strip, unpack, Text, pack)

  answerQuery1 :: IO ()
  answerQuery1 = do
    query <- getLine
    putStrLn (show $ do
      program <- M.runParser (program "test-program") "" "fact(a). man(b, fact(a, a)). fact(a, b). fact(b). factC(A) :- factD(b, a  ,   'B'). factD(B, C, A) :- A > 2, !, fact(C), man(B, fact(C, C))."
      expression <- (M.runParser (expression) "" (pack query))
      let result = (do
          (Program _ stmts) <- program
          expr <- expression
          return (solve stmts expr))
      return result)

  answerQuery :: IO ()
  answerQuery = putStrLn (show $ do
    program <- M.runParser (program "test-program") "" "fact(a). man(b, fact(a, b)). fact(a, b). fact(b). factC(A) :- factD('A'). factD(A):-W+W,[X,A],[X|[Y|[]]],not D,fact(D,fact(C)),!Z."
    expression <- M.runParser (expression) "" "man(A, fact(a, X))"
    let result = (do
        (Program _ stmts) <- program
        expr <- expression
        return (solve stmts expr))
    return result)

  answerQuery3 :: IO ()
  answerQuery3 = putStrLn (show (do
    program <- M.runParser (program "test-program") "" "fact(10,1). fact(9,2). fact(8,3). fact(7,4). factC(X) :- fact(A,X), A > 9."
    expression <- M.runParser (expression) "" "factC(7)."
    let result = (do
        (Program _ stmts) <- program
        expr <- expression
        return (solve stmts expr))
    return result))

  main :: IO ()
  main = answerQuery3
