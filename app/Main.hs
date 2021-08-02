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
  import Data.Maybe (fromMaybe)
  import System.Exit

  outputRepl :: Maybe Program -> (String -> IO()) -> String -> IO()
  outputRepl p cmd txt = cmd $ ("repl " ++ (fromMaybe "" (fmap (\(Program n _) -> "*" ++ n) p)) ++ ">> ") ++ txt

  readLineRepl :: String -> IO String
  readLineRepl txt = putStrLn txt >> getLine

  printLineRepl :: Maybe Program -> String -> IO ()
  printLineRepl p txt = outputRepl p putStrLn txt

  printRepl :: Maybe Program -> String -> IO ()
  printRepl p txt = outputRepl p putStr txt

  repl :: Maybe Program -> IO ()
  repl p = do
    printRepl p ""
    line <- getLine
    (case (Data.Text.strip (pack line)) of
      ":quit" ->
        (printLineRepl p "$ Goodbye!") >> exitWith(ExitSuccess)
      ":open" ->
        (readLineRepl "Enter path to the file: ") >>= (\path ->
          (readFile path) >>= (\code ->
            case (M.runParser (program path) "" (pack code)) of
              (Right (Right p2 @ (Program _ stms))) ->
                (printLineRepl (Just p2) " Ok.") >> (repl (Just p2))
              (Left e) ->
               printLineRepl p (" Failure: " ++ show(e)) >> repl Nothing
           )
         )
      expr ->
        case p of
          Just (Program n stms) ->
            case (M.runParser (expression) "" expr) of
              (Right (Right expr)) ->
                (solve stms expr) >>= (\results ->
                  case results of
                    Right s ->
                      do
                        putStrLn ("? - yes")
                        sequence ((fmap (\pairs ->
                            putStrLn " " >> (sequence (fmap (\pair ->
                              putStr $ (fst pair) ++ "=" ++ (show (snd pair)) ++ "  "
                            ) pairs))
                          ) s))
                        sequence (take 3 (repeat $ putStrLn ""))
                        putStrLn "[Done]"
                        repl p
                    Left e ->
                      putStrLn ("? - no") >> (printLineRepl p (show e))
                ) >> (repl p)
              (Right (Left err)) ->
                printLineRepl p ("Syntax error: " ++ (show err)) >> repl p
              (Left err) ->
                printLineRepl p ("Syntax error: " ++ (show err)) >> repl p


          Nothing ->
            printLineRepl p ("Unknown command") >> repl Nothing
      )

  main :: IO ()
  main = do
    printLineRepl Nothing "Welcome to Prolog Engine REPL"
    printLineRepl Nothing ":open filename - loads the Prolog source code"
    printLineRepl Nothing ":quit - exits the REPL process"
    printLineRepl Nothing "or just type in you query if you have loaded the source file already"
    repl Nothing
