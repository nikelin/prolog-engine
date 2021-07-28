{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections     #-}
{-# LANGUAGE BangPatterns       #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE RecordWildCards    #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Core (Val(AtomVal, IntVal, FloatVal, StringVal, BoolVal),
            Identifier,
            Operator(OpAdd, OpMin, OpMult, OpDiv, OpAnd, OpOr, OpCompLt, OpCompLte, OpCompGt, OpCompGte, OpEq, OpNotEq, OpNot),
            List(ConsList, EnumeratedList, EmptyList),
            Exception(UnknownVariableException, UnexpectedExpression, WrongBinaryOperationContext, WrongUnaryOperationContext),
            Expression(ExceptionExpression, VarExp, TermExp, LiteralExp, CutExp, ClosureExpr, ListExp, UnaryExpression, BinaryExpression),
            Statement(RuleStmt),
            Program(Program),
            isCompOp, compareOp, binaryLogicalOp, isBinaryLogicalOp, listVariables, getOrElse) where

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
                    CutExp |
                    ClosureExpr String [Expression] Expression |
                    ListExp List |
                    UnaryExpression Operator Expression |
                    BinaryExpression Operator Expression Expression |
                    ExceptionExpression Exception
                    deriving (Show, Eq)

  instance Ord Val where
      (IntVal s1) `compare` (IntVal s2) = s1 `compare` s2
      (FloatVal s1) `compare` (FloatVal s2) = s1 `compare` s2
      (BoolVal s1) `compare` (BoolVal s2) = s1 `compare` s2
      (StringVal s1) `compare` (StringVal s2) = s1 `compare` s2
      (AtomVal _) `compare` (AtomVal _) = GT

  data Statement = RuleStmt String [Expression] (Maybe Expression)
                   deriving (Show, Eq)

  data Program = Program String [Statement]
                    deriving (Show, Eq)

  isCompOp :: Operator -> Bool
  isCompOp op
    | op == OpCompGt = True
    | op == OpCompLt = True
    | op == OpCompGte = True
    | op == OpCompLte = True
    | op == OpEq = True
    | op == OpNotEq = True
    | otherwise = False

  isBinaryLogicalOp :: Operator -> Bool
  isBinaryLogicalOp op
    | op == OpAnd = True
    | op == OpOr = True
    | otherwise = False

  binaryLogicalOp :: Operator -> Expression -> Expression -> Expression
  binaryLogicalOp op le @ (LiteralExp (BoolVal left)) re @ (LiteralExp (BoolVal right))
    | op == OpAnd = (LiteralExp (BoolVal (left && right)))
    | op == OpOr = (LiteralExp (BoolVal (left || right)))
  compareOp :: Operator -> Expression -> Expression -> Expression
  compareOp op le @ (LiteralExp left) re @ (LiteralExp right)
    | op == OpEq = (LiteralExp (BoolVal (left == right)))
    | op == OpNotEq = (LiteralExp (BoolVal (left /= right)))
    | op == OpCompLte = (LiteralExp (BoolVal (left <= right)))
    | op == OpCompGte = (LiteralExp (BoolVal (left >= right)))
    | op == OpCompGt = (LiteralExp (BoolVal (left > right)))
    | op == OpCompLt = (LiteralExp (BoolVal (left < right)))

  listVariables :: Expression -> [String]
  listVariables (VarExp n) = [n]
  listVariables (ListExp EmptyList) = []
  listVariables (ListExp (EnumeratedList xs)) = foldl (++) [] (fmap (\v -> listVariables v) xs)
  listVariables (ListExp (ConsList head tail)) = (listVariables head) ++ (listVariables tail)
  listVariables (TermExp _ args) = foldl (++) [] (fmap (\v -> listVariables v) args)

  getOrElse::Maybe a -> a -> a
  getOrElse (Just v) d = v
  getOrElse Nothing d  = d

