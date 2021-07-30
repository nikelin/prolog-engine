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
            Expression(ExceptionExpression, VarExp, TermExp, LiteralExp, CutOperatorExp, CutExp, ClosureExpr, ListExp, UnaryExpression, BinaryExpression),
            Statement(RuleStmt, ConsultStmt),
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
                    CutOperatorExp |
                    CutExp Expression |
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

  data Statement = ConsultStmt String |
                   RuleStmt String [Expression] (Maybe Expression)
                   deriving (Show, Eq)

  data Program = Program String [Statement]
                    deriving (Show, Eq)

--  instance Show Operator where
--    show (OpAnd) = "&&"
--    show (OpNot) = "!"
--    show (OpNotEq) = "!="
--    show (OpOr) = "||"
--    show (OpCompLt) = "<"
--    show (OpCompGt) = ">"
--    show (OpCompGte) = ">="
--    show (OpCompLte) = "<="
--    show (OpEq) = "=="
--    show (OpMin) = "-"
--    show (OpDiv) = "/"
--    show (OpAdd) = "+"
--    show (OpMult) = "*"

--  instance Show Expression where
--    show (VarExp n) = n
--    show (TermExp n args) = (n ++ "(" ++ ((fmap (\v -> ((show v) ++ ",")) args) >>= id) ++ ")")
--    show (ClosureExpr n args body) = (n ++ "(" ++ ((fmap show args) >>= id) ++ ") :- " ++ (show body))
--    show CutOperatorExp = "!"
--    show (CutExp exp) = "!(" ++ (show exp) ++ ")"
--    show (LiteralExp v) = (show v)
--    show (ListExp (EnumeratedList xs)) = show xs
--    show (ListExp (ConsList head tail)) = ("[" ++ (show head ) ++ " | " ++ (show tail) ++ "]")
--    show (UnaryExpression op exp) = (show op) ++ (show exp)
--    show (BinaryExpression op left right) = (show left) ++ " " ++ (show op) ++ " " ++ (show right)
--    show (ExceptionExpression e) = "exception " ++ (show e)

  instance Ord Expression where
      compare l r = compare (show l) (show r)

--  instance Show Val where
--    show (BoolVal v) = show v
--    show (IntVal v) = show v
--    show (StringVal v) = v

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
  listVariables (LiteralExp _) = []
  listVariables (CutExp exp) = listVariables exp
  listVariables (ExceptionExpression _) = []
  listVariables CutOperatorExp = []
  listVariables (ClosureExpr _ _ _) = []
  listVariables (VarExp n) = [n]
  listVariables (UnaryExpression _ left) = (listVariables left)
  listVariables (BinaryExpression _ left right) = (listVariables left) ++ (listVariables right)
  listVariables (ListExp EmptyList) = []
  listVariables (ListExp (EnumeratedList xs)) = foldl (++) [] (fmap (\v -> listVariables v) xs)
  listVariables (ListExp (ConsList head tail)) = (listVariables head) ++ (listVariables tail)

  listVariables (TermExp _ args) = foldl (++) [] (fmap (\v -> listVariables v) args)

  getOrElse::Maybe a -> a -> a
  getOrElse (Just v) d = v
  getOrElse Nothing d  = d

