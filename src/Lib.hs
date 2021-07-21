{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections     #-}
{-# LANGUAGE BangPatterns       #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE RecordWildCards    #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Lib
    ( answerQuery, answerQuery1, testParsing
    ) where

import qualified Data.HashMap.Strict as H (HashMap, insert, lookup, empty, fromList, toList, union)

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
           IntVal Int |
           FloatVal Float |
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

data Exception = UnknownVariableException String
            | UnexpectedExpression Expression
            | WrongUnaryOperationContext Operator Expression
            | WrongBinaryOperationContext Operator Expression Expression
            | UnsupportedListTypeException Operator Expression Expression
          deriving (Show, Eq)

data Expression = VarExp String |
                  TermExp String [Expression] |
                  LiteralExp Val |
                  ClosureExpr String [Expression] Expression |
                  ListExp List |
                  UnaryExpression Operator Expression |
                  BinaryExpression Operator Expression Expression
                  deriving (Show, Eq)

data Statement = RuleStmt String [Expression] (Maybe Expression)
                 deriving (Show, Eq)

data Program = Program String [Statement]
                  deriving (Show, Eq)

type MParser = Parsec Void Text

type Subst = (String, Expression)
type Env = H.HashMap String Expression

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
    return (BinaryExpression o l r))

unaryOperation :: MParser (Either String Expression)
unaryOperation = do
  op <- unaryOperator
  exp <- (expression1 True)
  return (fmap (\v -> UnaryExpression op v) exp)

termExp :: MParser (Either String Expression)
termExp = do
  name <- (identifier False)
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
  v <- M.choice [(fmap Right integer), (fmap Right float), (fmap Right stringExp), (fmap Right atom)]
  return (fmap (\vf -> LiteralExp vf) v)

expression :: MParser (Either String Expression)
expression = expression1 False

expression1 :: Bool -> MParser (Either String Expression)
expression1 isSubExpression
  | isSubExpression == False = do
      op <- listExp <|> M.try unaryOperation  <|> M.try termExp <|> M.try binaryOperation <|> variableExp <|> literalExp
      return op
  | otherwise = do
      op <- M.try listExp <|> M.try (parens unaryOperation)  <|> M.try termExp <|> M.try (parens binaryOperation) <|> variableExp <|> literalExp
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

float :: MParser Val
float = do
  m <- M.some M.digitChar
  symbol "."
  e <- M.some M.digitChar
  return (FloatVal (read (m ++ "." ++ e) :: Float))

integer :: MParser Val
integer = do
  v <- M.some M.digitChar
  return (IntVal (read v :: Int))

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
              Right lv -> (Right (BinaryExpression OpAnd lv v))
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

unify' :: Env -> [Subst] -> Expression -> Expression -> (Bool, [Subst])
unify' _ _ _ (ClosureExpr _ _ _) = (False, [])
unify' env subst (VarExp n1) (VarExp n2) =
  case (H.lookup n1 env) of
    Just n1v ->
      case (H.lookup n2 env) of
          Just n2v ->
            (n1v == n2v, [])
          Nothing ->
            (False, [])
    Nothing -> (False, [])
unify' env subst (VarExp n) l @ (LiteralExp _) =
  case H.lookup n env of
     Just nv -> (nv == l, [])
     Nothing -> (False, [])

unify' env subst t @ (TermExp _ _) (VarExp n) = (True, (n, t):subst)
unify' env subst v @ (LiteralExp _) (VarExp n) = (True, (n, v):subst)
unify' env subst (LiteralExp left) (LiteralExp right) = (left == right, [])
unify' env subst (ClosureExpr cn closure_args body) term @ (TermExp tn args)
  | cn == tn =
    case (trace "Unifying closure and term" (unify' env subst term (TermExp cn closure_args))) of
      (True, new_subst) ->
        let
          updated_env = (H.union (H.fromList new_subst) env)
        in
          trace ("Substitution in lambda " ++ (show new_subst)) (unify updated_env subst body)
      (False, _) -> (False, [])
  | otherwise = (False, [])
unify' env subst (TermExp tname1 args1) (TermExp tname2 args2)
  | tname1 /= tname2 = (trace ("Name mismatch" ++ (show tname1) ++ (show tname2)))((False, []))
  | (length args1) /= (length args2) = (False, [])
  | otherwise =
    (foldl (\l ->
        (\r ->
          if (fst l) && (fst r) then
            (True, (snd l) ++ (snd r))
          else
            (False, []))
        ) (True, []) (fmap (\arg -> (unify' env subst (fst arg) (snd arg))) (zip args1 args2)))
unify' a b c d = trace ("Unexpected input" ++ (show a) ++ " " ++ (show b) ++ " " ++ (show c) ++ " " ++ (show d)) (False, [])

unify :: Env -> [Subst] -> Expression -> (Bool, [Subst])
unify env subst expr @ (TermExp name _) =
  case (H.lookup name env) of
    Just v ->
      (unify' env subst v expr)
    Nothing ->
      (False, [])
unify env _ expr =
  case (eval env expr) of
    Right v -> (True, [])
    Left e -> (False, [])

solve :: [Statement] -> Expression -> Either [String] [Subst]
solve statements expr = (case result of
  (False, _) -> (Left ["unification faled"])
  (True, substList) -> Right substList)
    where
      closures = (map (\v -> case v of
         (RuleStmt n args (Just body)) -> (n, (ClosureExpr n args body))
         (RuleStmt n args Nothing) -> (n, (TermExp  n args))) statements)
      env = (H.fromList closures)
      result = (unify env [] expr)


evalStmt :: Env -> Statement -> Either Exception Expression
evalStmt env (RuleStmt n args (Just body)) = Right (ClosureExpr n args body)
evalStmt env (RuleStmt n args Nothing) = Right (TermExp n args)

eval :: Env -> Expression -> Either Exception Expression
eval _ v @ (LiteralExp _) = Right v
eval env (VarExp n) = case (H.lookup n env) of
  Just res -> (eval env res)
  Nothing -> Left (UnknownVariableException n)

eval env (UnaryExpression op operand) =
  (eval env operand) >>= (\v ->
    case v of
      l @ (LiteralExp (IntVal v)) ->
        case op of
          OpMin -> Right (LiteralExp (IntVal (-1 * v)))
          OpAdd -> Right (LiteralExp (IntVal (if v > 0 then v else -1 * v)))
          _ -> (Left (WrongUnaryOperationContext op l))
      l @ (LiteralExp (BoolVal v)) ->
        case op of
          OpNot -> Right (LiteralExp (BoolVal (not v)))
          _ -> (Left (WrongUnaryOperationContext op l))
      _ ->
        (Left (WrongUnaryOperationContext op operand))
  )

eval env (BinaryExpression op left right) =
  (eval env left) >>= (\l ->
    (eval env right) >>= (\r ->
      case (l, r) of
        (le @ (LiteralExp (IntVal lv)), ze @ (LiteralExp (IntVal rv))) ->
          case op of
            OpAdd ->
              (Right (LiteralExp (IntVal (lv + rv))))
            OpMin ->
              (Right (LiteralExp (IntVal (lv - rv))))
            OpMult ->
              (Right (LiteralExp (IntVal (lv * rv))))
            OpDiv ->
              (Right (LiteralExp (IntVal (lv `div` rv))))
            OpCompLt ->
              (Right (LiteralExp (BoolVal (lv < rv))))
            OpCompGt ->
              (Right (LiteralExp (BoolVal (lv > rv))))
            OpCompGte ->
              (Right (LiteralExp (BoolVal (lv >= rv))))
            OpCompLte ->
              (Right (LiteralExp (BoolVal (lv <= rv))))
            OpEq ->
              (Right (LiteralExp (BoolVal (lv == rv))))
            OpNotEq ->
              (Right (LiteralExp (BoolVal (lv /= rv))))
            _ ->
              (Left (WrongBinaryOperationContext op le ze))
        (le @ (LiteralExp (StringVal lv)), ze @ (LiteralExp (StringVal rv))) ->
          case op of
            OpAdd ->
              (Right (LiteralExp (StringVal (lv ++ rv))))
            OpNot ->
              (Right (LiteralExp (BoolVal (lv /= rv))))
            OpEq ->
              (Right (LiteralExp (BoolVal (lv == rv))))
            _ ->
              (Left (WrongBinaryOperationContext op le ze))
        (le @ (LiteralExp (BoolVal lv)), ze @ (LiteralExp (BoolVal rv))) ->
          case op of
            OpAnd ->
              (Right (LiteralExp (BoolVal (lv && rv))))
            OpOr ->
              (Right (LiteralExp (BoolVal (lv || rv))))
            OpEq ->
              (Right (LiteralExp (BoolVal (lv == rv))))
            OpNotEq ->
              (Right (LiteralExp (BoolVal (lv /= rv))))
            _ ->
              (Left (WrongBinaryOperationContext op le ze))
        (le @ (ListExp lv), ze @ (ListExp zv)) ->
          let
            result = case (lv,zv) of
              ((EnumeratedList elems1), (EnumeratedList elems2)) -> Right (elems1, elems2)
              ((EnumeratedList elems), EmptyList) -> Right (elems, [])
              (EmptyList, (EnumeratedList elems)) -> Right ([], elems)
              (EmptyList, EmptyList) -> Right ([], [])
              _ -> Left (UnsupportedListTypeException op le ze)
          in (case (result, op) of
            ((Left e), _) -> (Left e)
            (Right (left, right), OpAdd) ->
              (Right (ListExp (EnumeratedList (left ++ right))))
            _ ->
              (Left (WrongBinaryOperationContext op le ze)))
        (le @ (ListExp lv), ze @ (LiteralExp zv)) ->
          (case (result, op) of
            (Right lst, OpAdd)  ->
              (Right (ListExp (EnumeratedList ((LiteralExp zv):lst))))
            _ ->
              (Left (WrongBinaryOperationContext op le ze)))
          where
            result = (case lv of
              (EnumeratedList elems1) -> (Right elems1)
              EmptyList -> (Right [])
              _ -> (Left (UnsupportedListTypeException op le ze)))
        (le @ (LiteralExp lv), ze @ (LiteralExp zv)) ->
          case op of
            OpEq -> (Right (LiteralExp (BoolVal (lv == zv))))
            OpNotEq -> (Right (LiteralExp (BoolVal (lv /= zv))))
        _ ->
          trace ("Wrong binary operation: " ++ (show (WrongBinaryOperationContext op l r)))(Left (WrongBinaryOperationContext op l r))
    )
  )

eval env (TermExp n args) =
    let
      argsv = (foldl (\l ->
        (\r ->
          case l of
            Right lv ->
              case r of
                Right rv ->
                  Right (rv:lv)
                Left rv ->
                  Left rv
            Left lv -> Left lv)) (Right []) (fmap (\v -> (eval env v)) args))
    in
      (case argsv of
        Right v -> Right (TermExp n v)
        Left e -> Left e)

eval env (ListExp EmptyList) = Right (ListExp EmptyList)

eval env (ListExp (EnumeratedList xs)) =
  let
    args = (fmap (\v -> (eval env v)) xs)
    result = (foldl (\l ->
        (\r ->
          case l of
            Right lv ->
              case r of
                Right rv -> Right (rv:lv)
                Left rv -> Left rv
            Left lv -> Left lv
        )) (Right []) args)
  in
    (case result of
      Right elems -> Right (ListExp (EnumeratedList elems))
      Left e -> Left e)


eval env (ListExp (ConsList head tail)) = do
  headv <- (eval env head)
  tailv <- (eval env tail)
  return (ListExp (ConsList headv tailv))

eval env unexpected =
  trace ("Unexpected input to the eval(x, y): " ++ (show unexpected)) (Left (UnexpectedExpression unexpected))

testParsing :: IO ()
testParsing = M.parseTest (program "test-program") "fact(A) :- factD('A'  ,   'B',   A). fact(A):-W+(W+Z),[X,A],[X|[Y|[]]],not D,fact(D,fact(C)),!Z."

answerQuery1 :: IO ()
answerQuery1 = do
  query <- getLine
  putStrLn (show $ do
    program <- M.runParser (program "test-program") "" "fact(a). man(b, fact(a, b)). fact(a, b). fact(b). factC(A) :- factD('A'  ,   'B',   A). factD(A):-W+W,[X,A],[X|[Y|[]]],not D,fact(D,fact(C)),!Z."
    expression <- (M.runParser (expression) "" (pack query))
    let result = (do
        (Program _ stmts) <- program
        expr <- expression
        return (solve stmts expr))
    return result)

answerQuery :: IO ()
answerQuery = putStrLn (show $ do
  program <- M.runParser (program "test-program") "" "fact(a). man(b, fact(a, b)). fact(a, b). fact(b). factC(A) :- factD('A'  ,   'B',   A). factD(A):-W+W,[X,A],[X|[Y|[]]],not D,fact(D,fact(C)),!Z."
  expression <- M.runParser (expression) "" "man(A, fact(a, X))"
  let result = (do
      (Program _ stmts) <- program
      expr <- expression
      return (solve stmts expr))
  return result)



