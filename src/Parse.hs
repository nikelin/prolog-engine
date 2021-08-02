{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections     #-}
{-# LANGUAGE BangPatterns       #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE RecordWildCards    #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Parse (program, expression, rule) where
  import qualified Data.HashMap.Strict as H (HashMap, insert, fromListWith, lookup, empty, fromList, toList, union, unionWith)

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
  import Control.Monad (void, sequence)

  import Core
  import Data.Maybe (fromMaybe)

  type MParser = Parsec Void Text

  whitespace :: MParser ()
  whitespace = do
    void $ M.spaceChar
    return ()

  boolean :: MParser Val
  boolean = ( symbol "True"  >> return (BoolVal True)  )
             <|> ( symbol "False" >> return (BoolVal False) )

  sc :: MParser ()
  sc = L.space
    M.space1
    (L.skipLineComment "//")
    (L.skipBlockComment "/*" "*/")

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
         nonFirstChar = M.alphaNumChar <|> M.char '_'

  unaryOperator :: MParser Operator
  unaryOperator = (M.chunk "-" *> (return OpMin)) <|>
      (symbol "not" *> (return OpNot))

  binaryOperator :: MParser Operator
  binaryOperator = unaryOperator <|>
      (symbol "*" *> (return OpMult)) <|>
      (symbol "+" *> (return OpAdd)) <|>
      (symbol "/" *> (return OpDiv)) <|>
      (symbol ">" *> (return OpCompGt)) <|>
      (symbol "<" *> (return OpCompLt)) <|>
      (symbol ">=" *> (return OpCompLte)) <|>
      (symbol "<=" *> (return OpCompGte)) <|>
      (symbol "!=" *> (return OpNotEq)) <|>
      (symbol "==" *> (return OpEq)) <|>
      (symbol "and" *> (return OpAnd)) <|>
      (symbol "or" *> (return OpOr))

  binaryOperation :: MParser (Either String Expression)
  binaryOperation = do
    left <- (expression1 True)
    void $ M.space
    op <- (fmap Right binaryOperator)
    void $ M.space
    right <- (expression1 True)
    return (do
      l <- left
      r <- right
      o <- op
      return (BinaryExpression o l r))

  unaryOperation :: MParser (Either String Expression)
  unaryOperation = do
    op <- unaryOperator
    exp <- (expression1 True)
    return (fmap (\v -> UnaryExpression op v) exp)

  termExp :: MParser (Either String Expression)
  termExp = do
    name <- (identifier False)
    argsList <- (parens (M.sepBy expression (symbol ",")))
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
    v <- M.choice [(fmap Right boolean), (fmap Right integer), (fmap Right stringExp), (fmap Right atom)]
    return (fmap (\vf -> LiteralExp vf) v)

  expression :: MParser (Either String Expression)
  expression = expression1 False

  expression1 :: Bool -> MParser (Either String Expression)
  expression1 isSubExpression
    | isSubExpression == False = do
        op <- M.try binaryOperation <|> listExp <|> cutExp <|> M.try unaryOperation  <|> M.try termExp <|> M.try literalExp <|> variableExp
        return op
    | otherwise = do
        op <- M.try listExp <|> cutExp <|> M.try (parens unaryOperation)  <|> M.try termExp <|> M.try (parens binaryOperation) <|> M.try literalExp <|> variableExp
        return op

  cutExp :: MParser (Either String Expression)
  cutExp = do
    symbol "!"
    return (Right CutOperatorExp)

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
    return (NumVal (read v:: Int))

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

  consult :: MParser (Either String Statement)
  consult = do
    void $ symbol "consult"
    resource <- parens (M.between (symbol "'") (symbol "'") (M.manyTill M.printChar (M.lookAhead "'")))
    symbol "."
    return (Right (ConsultStmt resource))

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
      let cutExpPredicates = foldl (\l ->
            (\r ->
              r >>= (\rv ->
                (fmap (\lv ->
                  case rv of
                    CutOperatorExp ->
                      case lv of
                         (head:tail) ->
                            ((CutExp head) : tail)
                    _ -> (rv:lv)
                  ) l))
            )) (Right []) predicates
      return (fmap (\vb ->
        (foldl (\l -> \r -> (BinaryExpression OpAnd r l)) (LiteralExp (BoolVal True)) vb)) cutExpPredicates)
    (symbol ".")
    (M.many (symbol "\n" <|> symbol "\r"))
    return (case argsv of
      Right argsvv ->
        (case body of
              Just (Left errs) -> Left errs
              Just (Right b) -> Right (RuleStmt name (reverse argsvv) (Just b))
              Nothing -> Right (RuleStmt name (reverse argsvv) Nothing))
      Left errs -> Left errs)


  program :: String -> MParser (Either String Program)
  program name = do
    result <- (M.many ((M.try consult) <|> rule) )
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
