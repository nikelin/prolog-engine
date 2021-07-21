{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections     #-}
{-# LANGUAGE BangPatterns       #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE RecordWildCards    #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Lib
    ( answerQuery, testParsing
    ) where

import qualified Data.HashMap.Strict as H (HashMap, insert, lookup, empty, fromList, union)

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

data Statement = RuleStmt String [Expression] (Maybe Expression)
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
boolean = M.try ( M.string "True"  >> return (BoolVal True)  )
           <|> M.try ( M.string "False" >> return (BoolVal False) )

sc :: MParser ()
sc = L.space
  M.space1                         -- (2)
  (L.skipLineComment "//")       -- (3)
  (L.skipBlockComment "/*" "*/") -- (4)

symbol :: Text -> MParser Text
symbol = L.symbol sc

parens :: MParser a -> MParser a
parens = M.between (symbol "(") (symbol ")")

identifier :: Bool -> MParser String
identifier capitalize = M.between (M.optional M.space) (M.optional M.space) parser
  where
    parser = do
       fst <- firstChar
       rest <- M.many nonFirstChar
       let result = fst:rest
       return result
      where
       firstChar = M.char '_' <|> (case capitalize of
         True -> M.upperChar
         False -> M.letterChar)
       nonFirstChar = M.alphaNumChar

unaryOperator :: MParser Operator
unaryOperator = (M.chunk "-" *> (return OpMin)) <|>
    (symbol "not" *> (return OpNot)) <|>
    (symbol "!" *> (return OpNot))

binaryOperator :: MParser Operator
binaryOperator = unaryOperator <|>
    (symbol "*" *> (return OpMult)) <|>
    (symbol "+" *> (return OpAdd)) <|>
    (symbol "/" *> (return OpDiv)) <|>
    (symbol ">" *> (return OpCompGt)) <|>
    (symbol "<" *> (return OpCompLt)) <|>
    (symbol ">=" *> (return OpCompLte)) <|>
    (symbol "<=" *> (return OpCompGte)) <|>
    (symbol "=\\=" *> (return OpNotEq)) <|>
    (symbol "==" *> (return OpEq)) <|>
    (symbol "and" *> (return OpAnd)) <|>
    (symbol "or" *> (return OpOr))

binaryOperation :: MParser (Either String Expression)
binaryOperation = do
  left <- (expression1 True)
  op <- (fmap Right binaryOperator)
  right <- (expression1 True)
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
  op <- unaryOperator
  exp <- (expression1 True)
  return (exp >>= (\right -> (case op of
    OpMin -> Right (ArithNegOp right)
    OpNot -> Right (LogicalNotOp right)
    otherwise -> (Left ("operator cannot be in an unary position: " ++ show(op))))))

termExp :: MParser (Either String Expression)
termExp = do
  name <- (identifier False)
  traceM ("TermExp " ++ (show name))
  argsList <- (parens (M.sepBy1 expression (symbol ",")))
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
  v <- M.choice [(fmap Right integer), (fmap Right stringExp), (fmap Right atom)]
  return (fmap (\vf -> LiteralExp vf) v)

expression :: MParser (Either String Expression)
expression = expression1 False

expression1 :: Bool -> MParser (Either String Expression)
expression1 isSubExpression
  | isSubExpression == False = do
      op <- listExp <|> M.try unaryOperation  <|> M.try termExp <|> M.try binaryOperation <|> variableExp <|> literalExp
      traceM ("Result: " ++ (show op))
      return op
  | otherwise = do
      op <- M.try listExp <|> M.try (parens unaryOperation)  <|> M.try termExp <|> M.try (parens binaryOperation) <|> variableExp <|> literalExp
      traceM ("Result (sub-expression): " ++ (show op))
      return op

consList :: MParser (Either String Expression)
consList = do
  head <- expression
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
        ) (Right []) (reverse items))
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
       firstChar = M.lowerChar
       nonFirstChar = M.alphaNumChar

variableExp :: MParser (Either String Expression)
variableExp = do
  result <- (M.between (M.optional M.space) (M.optional M.space) (identifier True))
  return (Right (VarExp result))

rule :: MParser (Either String Statement)
rule = do
  name <- (identifier False)
  args <- (parens (M.sepBy expression (symbol ",")))
  let argsv = (foldl (\l ->
        \r ->
          case l of
              Right lv ->
                case r of
                  Right rv -> Right (rv:lv)
                  Left rv -> Left rv
              Left lv ->
                case r of
                  Right _ -> Left lv
                  Left rv -> Left (rv ++ lv)) (Right []) args)
  (body :: Maybe (Either String Expression)) <- M.optional $ do
    void $ symbol ":-"
    predicates <- M.sepBy1 (do
      exp <- expression
      return exp) (M.optional (symbol "," <|> symbol ";"))
    return (foldl (\l ->
      \vv ->
        case vv of
          (Right v) ->
            case l of
              Left lv -> Left lv
              Right lv -> (Right (LogicalAndOp lv v))
          (Left v) ->
            case l of
              Left lv -> Left (lv ++ v)
              Right _ -> Left v
      ) ((Right (LiteralExp (BoolVal True))) :: (Either String Expression)) predicates)
  (symbol ".")
  return (case argsv of
    Right argsvv ->
      (case body of
            Just (Left errs) -> Left errs
            Just (Right b) -> Right (RuleStmt name (reverse argsvv) (Just b))
            Nothing -> Right (RuleStmt name (reverse argsvv) Nothing))
    Left errs -> Left errs)


program :: String -> MParser (Either String Program)
program name = do
  result <- (M.many rule)
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

listVariables :: Expression -> [String]
listVariables (VarExp n) = [n]
listVariables (ListExp EmptyList) = []
listVariables (ListExp (EnumeratedList xs)) = foldl (++) [] (fmap (\v -> listVariables v) xs)
listVariables (ListExp (ConsList head tail)) = (listVariables head) ++ (listVariables tail)
listVariables (TermExp _ args) = foldl (++) [] (fmap (\v -> listVariables v) args)

unify' :: Expression -> Expression -> Bool
unify' (VarExp _) (VarExp _) = False
unify' (VarExp _) (LiteralExp _) = True
unify' (LiteralExp _) (VarExp _) = True
unify' (LiteralExp left) (LiteralExp right) = left == right
unify' (TermExp tname1 args1) (TermExp tname2 args2)
  | tname1 /= tname2 = False
  | (length args1) /= (length args2) = False
  | otherwise =
    (and (fmap (\arg -> (unify' (fst arg) (snd arg))) (zip args1 args2)))

unify :: [Statement] -> Expression -> Either [String] Bool
unify [] expr = Right False  -- throw exception here
unify stms expr = Right (aux stms expr)
  where
    aux [] expr = True -- check
    aux ((RuleStmt name args _):xs) expr =
      (unify' (TermExp name args) expr) && (aux xs expr)

solve :: [Statement] -> Expression -> Either [String] Bool
solve statements expr = do
  let variables = listVariables expr
  traceM ("Variables extracted: " ++ (show variables))
  result <- unify statements expr
  return result

testParsing :: IO ()
testParsing = M.parseTest (program "test-program") "fact(A) :- factD('A'  ,   'B',   A). fact(A):-W+(W+Z),[X,A],[X|[Y|[]]],not D,fact(D,fact(C)),!Z."

answerQuery :: IO ()
answerQuery = putStrLn (show $ do
  program <- M.runParser (program "test-program") "" "fact(a). fact(b). factC(A) :- factD('A'  ,   'B',   A). factD(A):-W+W,[X,A],[X|[Y|[]]],not D,fact(D,fact(C)),!Z."
  expression <- M.runParser (expression) "" "fact(A)"
  let result = (do
      (Program _ stmts) <- program
      expr <- expression
      return (solve stmts expr))
  return result)



