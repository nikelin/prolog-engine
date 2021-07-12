{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections     #-}
{-# LANGUAGE BangPatterns       #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE RecordWildCards    #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Lib
    ( someFunc
    ) where
import Data.Data
import Debug.Trace
import Control.Applicative
import Data.Char
import Data.Monoid
import Data.Text (strip, unpack, Text, pack)
import Data.Void
import Text.Megaparsec (Parsec)
import qualified Text.Megaparsec as M
import qualified Text.Megaparsec.Error
import qualified Text.Megaparsec.Char as M
import qualified Text.Megaparsec.Char.Lexer as L
import qualified Data.Set              as S

import Control.Monad (void)

data Val = AtomVal String |
           IntVal String |
           StringVal String |
           BoolVal Bool
           deriving (Show, Eq)

type Identifier = String

data Operator = OpAdd | OpMin | OpMult | OpDiv | OpAnd | OpOr | OpCompLt | OpCompLte | OpCompGt | OpCompGte |
                OpEq | OpNotEq | OpNot deriving (Show, Eq)

data List = ConsList Expression Expression |
            EnumeratedList [Expression] |
            EmptyList
            deriving (Show, Eq)

data Expression = VarExp String |
                  TermExp String [Expression] |
                  LiteralExp Val |
                  ListExp List |
                  LogicalNotOp Expression |
                  ArithNegOp Expression |
                  ArithAddOp Expression Expression |
                  ArithMultOp Expression Expression |
                  ArithDivOp Expression Expression |
                  LogicalAndOp Expression Expression |
                  LogicalOrOp Expression Expression |
                  EqOp Expression Expression |
                  NotEqOp Expression Expression |
                  CompLtOp Expression Expression |
                  CompGtOp Expression Expression |
                  CompLteOp Expression Expression |
                  CompGteOp Expression Expression |
                  Skip
                  deriving (Show, Eq)

data Statement = RuleStmt String [Val] (Maybe Expression)
                 deriving (Show, Eq)

data Program = Program String [Statement]
                  deriving (Show, Eq)

type MParser = Parsec Void Text

getOrElse::Maybe a -> a -> a
getOrElse (Just v) d = v
getOrElse Nothing d  = d

whitespace :: MParser ()
whitespace = do
  void $ M.spaceChar
  return ()

boolean :: MParser Val
boolean = M.try ( M.string "true"  >> return (BoolVal True)  )
           <|> M.try ( M.string "false" >> return (BoolVal False) )

sc :: MParser ()
sc = L.space
  M.space1                         -- (2)
  (L.skipLineComment "//")       -- (3)
  (L.skipBlockComment "/*" "*/") -- (4)

symbol :: Text -> MParser Text
symbol = L.symbol sc

parens :: MParser a -> MParser a
parens = M.between (symbol "(") (symbol ")")

identifier :: MParser String
identifier = M.between (M.optional M.space) (M.optional M.space) parser
  where
    parser = do
       fst <- firstChar
       traceM ("First character parsed: " ++ (show fst))
       rest <- M.many nonFirstChar
       let result = fst:rest
       traceM ("Identifier parsed: " ++ (show result))
       return result
      where
       firstChar = M.char '_' <|> M.letterChar
       nonFirstChar = M.alphaNumChar

unaryOperator :: MParser Operator
unaryOperator = (M.chunk "-" *> (return OpMin)) <|>
    (M.chunk "not" *> (return OpNot)) <|>
    (M.chunk "!" *> (return OpNot))

binaryOperator :: MParser Operator
binaryOperator = unaryOperator <|>
    (M.chunk "*" *> (return OpMult)) <|>
    (M.chunk "+" *> (return OpAdd)) <|>
    (M.chunk "/" *> (return OpDiv)) <|>
    (M.chunk ">" *> (return OpCompGt)) <|>
    (M.chunk "<" *> (return OpCompLt)) <|>
    (M.chunk ">=" *> (return OpCompLte)) <|>
    (M.chunk "<=" *> (return OpCompGte)) <|>
    (M.chunk "=\\=" *> (return OpNotEq)) <|>
    (M.chunk "==" *> (return OpEq)) <|>
    (M.chunk "and" *> (return OpAnd)) <|>
    (M.chunk "or" *> (return OpOr))

binaryOperation :: MParser (Either String Expression)
binaryOperation = do
  traceM ("in binary function (left) ")
  left <- literalExp
  op <- (fmap Right binaryOperator)
  traceM ("in binary function (operator) " ++ (show op))
  right <- literalExp
  traceM ("in binary function (right) " ++ (show left) ++ " " ++ (show op) ++ " " ++ (show right))
  return (do
    l <- left
    r <- right
    o <- op
    v <- (case o of
          OpCompLt -> Right (CompLtOp l r)
          OpCompLte -> Right (CompLteOp l r)
          OpCompGte -> Right (CompGteOp l r)
          OpCompGt -> Right (CompGtOp l r)
          OpAdd -> Right (ArithAddOp l r)
          OpMult -> Right (ArithMultOp l r)
          OpDiv -> Right (ArithDivOp l r)
          OpAnd -> Right (LogicalAndOp l r)
          OpOr -> Right (LogicalOrOp l r)
          OpEq -> Right (EqOp l r)
          OpNotEq -> Right (NotEqOp l r)
          otherwise -> Left ("operator cannot be in a binary position: " ++ (show op)))
    return v)

unaryOperation :: MParser (Either String Expression)
unaryOperation = do
  traceM ("Unary operation")
  op <- unaryOperator
  exp <- expression
  traceM ("Operator " ++ (show op) ++ " and right " ++ (show exp))
  return (exp >>= (\right -> (case op of
    OpMin -> Right (ArithNegOp right)
    OpNot -> Right (LogicalNotOp right)
    otherwise -> (Left ("operator cannot be in an unary position: " ++ show(op))))))

termExp :: MParser (Either String Expression)
termExp = do
  traceM ("Term expression")
  name <- identifier
  argsList <- (parens (M.sepBy1 (literalExp <|> termExp) (symbol ",")))
  let (args :: Either String [Expression]) = foldl (\l ->
        \r ->
          case r of
            Right arg ->
              case l of
                (Right lv) -> (Right (arg:lv))
                (Left lv) -> (Left lv)
            Left err ->
              case l of
                (Right _) -> (Left err)
                (Left lv) -> (Left (lv ++ ", " ++ err))) (Right []) argsList
  return (fmap (\v -> (TermExp name (reverse v))) args)

literalExp :: MParser (Either String Expression)
literalExp = do
  traceM ("In literal")
  v <- M.choice [(fmap Right integer), (fmap Right atom), (fmap Right stringExp)]
  traceM ("Result " ++ (show v))
  return (fmap (\vf -> (case vf of
     AtomVal d -> VarExp d
     d @ otherwise -> LiteralExp d)) v)

expression :: MParser (Either String Expression)
expression = do
    traceM ("In expression")
    op <- M.try listExp <|> M.try unaryOperation <|> M.try binaryOperation <|> M.try termExp <|> M.try literalExp
    return op

consList :: MParser (Either String Expression)
consList = do
  head <- expression
  traceM ("Head of the list " ++ (show head))
  _ <- symbol "|"
  tail <- expression
  return (tail >>= (\t -> (fmap (\h -> (ListExp (ConsList h t))) head)))

enumeratedList :: MParser (Either String Expression)
enumeratedList = do
  items <- M.try (M.sepBy1 expression (symbol ","))
  let itemsList = (foldl (\l -> \r ->
        case r of
          Right rv ->
            case l of
              Left lv -> (Left lv)
              Right lv -> (Right (rv:lv))
          Left rv ->
            case l of
              Left lv -> (Left (rv ++ "," ++ lv))
              Right lv -> (Left rv)
        ) (Right []) items)
  return (fmap (\v -> (ListExp (EnumeratedList v))) itemsList)

listExp :: MParser (Either String Expression)
listExp = do
  symbol "["
  exp <- (M.optional ((M.try consList) <|> (M.try enumeratedList)))
  symbol "]"
  return (getOrElse exp (Right (ListExp EmptyList)))

stringExp :: MParser Val
stringExp = M.between (symbol "'") (symbol "'") (StringVal <$> (M.manyTill M.printChar (M.lookAhead "'")))

integer :: MParser Val
integer = do
  v <- M.some M.digitChar
  return (IntVal v)

atom :: MParser Val
atom = M.between (M.optional M.space) (M.optional M.space) parser
  where
    parser = do
       fst <- firstChar
       rest <- M.many nonFirstChar
       return (AtomVal (fst:rest))
      where
       firstChar = M.char '_' <|> M.upperChar
       nonFirstChar = M.alphaNumChar

rule :: MParser (Either [String] Statement)
rule = do
  name <- identifier
  traceM ("Identifier parsed " ++ (show name))
  args <- (parens (M.sepBy atom (symbol ",")))

  traceM ("Arguments parsed: " ++ (show args))
  (body :: Maybe (Either [String] Expression)) <- M.optional $ do
    void $ symbol ":-"
    traceM ("Parsed smiley")
    predicates <- M.sepBy (do
      exp <- expression
      traceM ("Expression parsed: " ++ (show exp))
      return exp) (symbol "," <|> symbol ";")
    return (foldl (\l ->
      \vv ->
        case vv of
          (Right v) -> case l of
            Left lv -> Left lv
            Right lv -> (Right (LogicalAndOp lv v))
          (Left v) -> case l of
            Left lv -> Left (v:lv)
            Right _ -> Left (v:[])
      ) ((Right (LiteralExp (BoolVal True))) :: (Either [String] Expression)) predicates)
  return (case body of
      Just (Left errs) -> Left errs
      Just (Right b) -> Right (RuleStmt name (reverse args) (Just b))
      Nothing -> Right (RuleStmt name (reverse args) Nothing))

program :: String -> MParser (Either [String] Program)
program name = do
  result <- (M.sepEndBy1 rule (symbol "."))
  let statements = (foldl (\l -> \r ->
          case l of
            (Right lv) ->
              case r of
                Right rv -> (Right (rv:lv))
                Left rv -> (Left (rv))
            (Left lv) ->
              case r of
                Right rv -> (Left lv)
                Left rv -> (Left (rv ++ lv))) (Right []) result)
  return (fmap (\stmts -> (Program name (reverse stmts))) statements)

someFunc :: IO ()
someFunc = M.parseTest (program "test-program") "fact(A) :- factD('A'  ,   'B',   A). fact(A):-W+W,[X,A],[X|[Y|[]]],not D,fact(D,fact(C)),!Z."

