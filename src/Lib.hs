{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections     #-}

module Lib
    ( someFunc
    ) where

import Debug.Trace
import Control.Applicative
import Data.Char
import Data.Monoid
import Data.Text (strip, unpack, Text, pack)
import Data.Void
import Text.Megaparsec (Parsec)
import qualified Text.Megaparsec as M
import qualified Text.Megaparsec.Char as M
import Control.Monad (void)

data Val = AtomVal String |
           IntVal String |
           BoolVal Bool
           deriving (Show, Eq)

type Identifier = String

data Operator = OpAdd | OpMin | OpMult | OpDiv | OpAnd | OpOr | OpEq | OpNotEq | OpNot deriving (Show, Eq)

data Expression = VarExp String |
                  LiteralExp Val |
                  LogicalNotOp Expression |
                  ArithAddOp Expression Expression |
                  ArithMultOp Expression Expression |
                  ArithDivOp Expression Expression |
                  LogicalAndOp Expression Expression |
                  LogicalOrOp Expression Expression |
                  EqOp Expression Expression |
                  NotEqOp Expression Expression |
                  Skip
                  deriving (Show, Eq)

data Statement = FactStmt String [Val] |
                 RuleStmt String [Val] Expression
                 deriving (Show, Eq)

type MParser = Parsec Void Text

getOrElse::Maybe a -> a -> a
getOrElse (Just v) d = v
getOrElse Nothing d  = d

whitespace :: MParser ()
whitespace = do
  void $ M.spaceChar
  return ()

integer :: MParser Val
integer = do
  v <- M.many M.digitChar
  return (IntVal v)

boolean :: MParser Val
boolean = M.try ( M.string "true"  >> return (BoolVal True)  )
           <|> M.try ( M.string "false" >> return (BoolVal False) )

atom :: MParser Val
atom = do
  v <- identifier
  return (AtomVal v)

openParen :: MParser Char
openParen = M.char '('

closeParen :: MParser Char
closeParen = M.char ')'

parens :: MParser a -> MParser a
parens = M.between openParen closeParen

identifier :: MParser String
identifier = M.between M.space M.space parser
  where
    parser = do
       fst <- firstChar
       rest <- M.many nonFirstChar
       return (fst:rest)
      where
       firstChar = M.letterChar <|> M.char '_'
       nonFirstChar = M.alphaNumChar

operator :: MParser Operator
operator = (M.try (M.chunk "*" >> (return OpMult))) <|>
    (M.try (M.chunk "+" >> (return OpAdd))) <|>
    (M.try (M.chunk "/" >> (return OpDiv))) <|>
    (M.try (M.chunk "-" >> (return OpMin))) <|>
    (M.try (M.chunk "=\\=" >> (return OpNotEq))) <|>
    (M.try (M.chunk "==" >> (return OpEq)))

binaryOperation :: MParser Expression
binaryOperation = do
  trace ("in binary function (left) ") $ return ()
  left <- M.try lit <|> M.try expression
  void $ M.space
  op <- operator
  void $ M.space
  trace ("in binary function (operator) " ++ (show op)) $ return ()
  right <- M.try lit <|> M.try expression
  trace ("in binary function (right) " ++ (show left) ++ " " ++ (show op) ++ " " ++ (show right)) $ return ()
  return (case op of
    OpAdd -> ArithAddOp left right
    OpMult -> ArithMultOp left right
    OpDiv -> ArithDivOp left right
    OpAnd -> LogicalAndOp left right
    OpOr -> LogicalOrOp left right
    OpEq -> EqOp left right
    OpNotEq -> NotEqOp left right)
  where
    lit = do
      v <- literal
      void $ M.try $ M.lookAhead operator
      return v

unaryOperation :: MParser Expression
unaryOperation = do
  trace ("Unary operation") $ return ()
  op <- operator
  void $ M.space
  right <- expression
  trace ("Operator " ++ (show op) ++ " and right " ++ (show right)) $ return ()
  return (case op of
    OpNot -> (LogicalNotOp right))

literal :: MParser Expression
literal = do
  trace ("In literal") $ return ()
  v <- val
  return (case v of
     AtomVal v -> VarExp v
     v @ otherwise -> LiteralExp v)

expression :: MParser Expression
expression = do
    trace ("In expression") $ return ()
    op <- M.try unaryOperation <|> M.try binaryOperation <|> M.try literal
    return op

val :: MParser Val
val = do
  val <- (M.try integer) <|> (M.try atom)
  return val

fact :: MParser Statement
fact = do
  name <- identifier
  args <- (M.between openParen closeParen (M.optional (M.many val)))
  return (FactStmt name (getOrElse args []))

singleTermRuleBody :: MParser Expression
singleTermRuleBody = do
  trace "single term rule" $ return ()
  exp <- expression
  c <- M.char '.'
  return (exp)

multipleTermRuleBody :: MParser Expression
multipleTermRuleBody = do
  predicates <- M.manyTill (do
    trace "multiple term rule" $ return ()
    exp <- expression
    c <- (M.optional (M.char ',' <|> M.char ';'))
    return (case c of
      Just ',' -> (Left exp)
      Just ';' -> (Right exp)
      Nothing -> (Right exp))) (M.try (M.char '.'))
  return (foldl ((\l ->
    \vv ->
      case vv of
        Left v -> (LogicalAndOp l v)
        Right v -> (LogicalOrOp l v))) (LiteralExp (BoolVal True)) predicates)

rule :: MParser Statement
rule = do
  name <- identifier
  args <- (parens (M.optional (M.sepBy val ",")))
  void $ (M.optional (M.many M.space))
  void $ M.string ":-"
  void $ (M.optional (M.many M.space))
  expression <- M.try singleTermRuleBody <|> M.try multipleTermRuleBody
  return (RuleStmt name (getOrElse args []) expression)

someFunc :: IO ()
someFunc = putStrLn $ (case (M.runParser (fact) "fact" "fact(A).") of
  (Right stm) -> (show stm)
  (Left err) -> error (show "Error: " ++ (show err)))
