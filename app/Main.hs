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
  import Control.Monad
  import Debug.Trace

  answerQuery3 :: IO ()
  answerQuery3 = let
      result = (do
        parsedp <- M.runParser (program "test-program") "" "consult('G:/repositories/test.pl'). fact(10,1). fact(9,2). fact(8,3). fact(7,4). fact(7,5). fact(7,6). factC(X) :- fact(A,X), A > 1."
        parsede <- M.runParser (expression) "" "factC(A)."
        return (parsedp >>= (\p -> fmap (\e -> (p, e)) parsede)))
    in
      (case result of
        Right (Right (Program _ stmts, expr)) ->
          solve stmts expr >>= (\result ->
            case (result) of
              Right solutions ->
                do
                  putStrLn "- yes"
                  putStrLn (join $ fmap (\solution ->
                      "Solution: \n\r" ++ (join (fmap (\subst -> (fst subst) ++ " = " ++ (show (snd subst)) ++ "\n\r") solution))
                    ) solutions)
              Left e -> putStrLn "- no"
          )
        (Left pe) -> putStrLn ("[error] Failed to parse the program: " ++ (show pe))
      )

  main :: IO ()
  main = answerQuery3
