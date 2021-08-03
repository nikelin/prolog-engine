{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections     #-}
{-# LANGUAGE BangPatterns       #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE RecordWildCards    #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Unify(solve, processInstructions, unify, eval) where
  import qualified Data.HashMap.Strict as H (HashMap, unions, insert, fromListWith, lookup, empty, fromList, toList, union, unionWith)
  import qualified Data.Set as S
  import qualified Data.List as LS
  import Core
  import Debug.Trace
  import System.IO
  import Parse
  import Text.Megaparsec (Parsec)
  import qualified Text.Megaparsec as M
  import qualified Text.Megaparsec.Error
  import qualified Text.Megaparsec.Char as M
  import qualified Text.Megaparsec.Char.Lexer as L
  import Data.Text (strip, unpack, Text, pack)
  import Control.Monad (sequence)
  import Data.Maybe (fromMaybe)

  type Subst = (String, Expression)
  type Substs = [Subst]
  type VarScope = S.Set String
  type TermId = String
  type TermEnv = H.HashMap TermId [Expression]
  type EvalEnv = H.HashMap String Expression

  termId :: String -> Int -> TermId
  termId name argc = name ++ "/" ++ (show argc)

  genSym :: [Expression] -> [(Subst, Subst)]
  genSym xs = aux 0 xs []
    where
      aux n [] ys = reverse ys
      aux n (x:xs) ys =
        case x of
          VarExp varn ->
            let
              newsym = varn ++ show n
            in
              (aux (n + 1) xs (((varn, VarExp varn), (newsym, VarExp (newsym))):ys))

  filterScope :: Substs -> VarScope -> Substs
  filterScope subst scope = (
      LS.filter (\sol -> (fst sol) `elem` scope) (subst))

  -- Performs α-conversion on a given closure body (expression) applying
  -- using a substitutions list on every variable occurrence within the context of a closure.
  -- As we can't have nested closures in Prolog, we can disregard complexities associated
  -- with multi-level closures α-conversion.
  updateReferences :: Substs -> Expression -> Expression
  updateReferences subst (CutExp exp) = (CutExp (updateReferences subst exp))
  updateReferences _ expr @ (LiteralExp _) = expr
  updateReferences subst (BinaryExpression op left right) =
    (BinaryExpression op (updateReferences subst left) (updateReferences subst right))
  updateReferences subst (UnaryExpression op operand) =
    (UnaryExpression op (updateReferences subst operand))
  updateReferences _ CutOperatorExp = CutOperatorExp
  updateReferences subst (ListExp (EnumeratedList elems)) =
    (ListExp (EnumeratedList (fmap (\v -> updateReferences subst v) elems)))
  updateReferences subst (ListExp (ConsList head tail)) =
    (ListExp (ConsList (updateReferences subst head) (updateReferences subst tail)))
  updateReferences subst (TermExp n args) =
    (TermExp n (fmap (\arg -> updateReferences subst arg) args))
  updateReferences _ expr @ (ClosureExpr _ _ _) = expr

  updateReferences subst exp @ (VarExp n) =
    case (LS.find (\v -> (fst v) == n) subst) of
      Just elem -> (snd elem)
      Nothing -> exp


  -- Performs unification between two given expressions, returns a set of solutions where each contains a set of substitutions
  -- which when applied to one side of the unification problem produce the desired outcome.
  unifyPair :: Bool -> TermEnv -> Substs -> Expression -> Expression -> (Bool, [Substs])
  unifyPair incut _ _ _ expr @ (ClosureExpr _ _ _) = (False, [])

  unifyPair incut env subst (ListExp _) (ListExp EmptyList) = (True, [])
  unifyPair incut env subst (ListExp EmptyList) (ListExp _) = (True, [])

  unifyPair incut env subst l @ (ListExp (EnumeratedList (head:tail))) (ListExp (ConsList head2 tail2)) =
    case unifyPair incut env subst head head2 of
      (True, results) ->
        let
          (tailFlag, tailResults) = (unifyPair incut env subst (ListExp (EnumeratedList tail)) tail2)
        in
          (tailFlag, tailResults ++ results)
      dif -> dif

  unifyPair incut env subst l @ (ListExp (ConsList head tail)) (ListExp (EnumeratedList (head2:tail2))) =
    case unifyPair incut env subst head head2 of
      (True, results) ->
        let
          (tailFlag, tailResults) = (unifyPair incut env subst tail (ListExp (EnumeratedList tail2)))
        in
          (tailFlag, tailResults ++ results)
      dif -> dif

  unifyPair incut env subst l @ (ListExp (EnumeratedList xs)) (ListExp (EnumeratedList ys)) =
    foldl (\(lstate, lresults) ->
      (\(left, right) ->
        case (unifyPair incut env subst left right) of
          (False, _) -> (lstate, lresults)
          (True, results) -> (True, lresults ++ results)
      )) (False, []) (zip xs ys)

  unifyPair incut env subst l @ (ListExp _) (VarExp n2) = (True, [[(n2, l)]])

  unifyPair incut env subst l @ (VarExp n1) (VarExp n2) = (True, [])
  unifyPair incut env subst (VarExp n) l @ (LiteralExp n1) = (True, [])

  unifyPair incut env subst t @ (TermExp _ _) (VarExp n) = (True, [[(n, t)]])
  unifyPair incut env subst v @ (LiteralExp _) (VarExp n) = (True, [[(n, v)]])
  unifyPair incut env subst (LiteralExp left) (LiteralExp right) = (left == right, [])
  unifyPair incut env subst (ExceptionExpression _) _ = (False, [])
  unifyPair incut env subst _ (ExceptionExpression _) = (False, [])

  -- This unification serves as a sort of 'invocation' for the closure term.
  --
  -- Closure arguments are going to be replaced by either values or placeholders from the input term, in the latter case
  -- we will also have to update closure's body as otherwise we are going to face incorrect naming issues.
  unifyPair incut env subst lambda @ (ClosureExpr cn closure_args body) term @ (TermExp tn args)
    | cn == tn =
      let
        symbolsTable = (genSym closure_args)
        symbols = (fmap (\sym -> ((fst (fst sym)), (snd (snd sym)))) symbolsTable)
        closureArgsScoped = fmap (\arg -> (updateReferences symbols arg)) closure_args
        backSubst = (fmap (\sym -> ((fst (snd sym)), ((fst (fst sym)), (snd (fst sym))))) symbolsTable)
        backSubstRefs = (LS.map (\s -> (fst s, (snd (snd s)))) backSubst)
        variables = listVariables term
      in
        (case (unifyPair incut env subst term (TermExp cn closureArgsScoped)) of
          (True, new_subst) ->
            let
              invokeClosure = (\(r, (lu, ls)) ->
                let
                  updatedBody = (updateReferences symbols body)
                in
                  (case (eval incut S.empty r env updatedBody) of
                    Right evalResult ->
                      (let
                        eligibleSolutions = (filter (\sol ->
                            -- making sure that the resulting value is 'truthy' (i.e. unifiable to True)
                            (case (unifyPair incut env subst (LiteralExp (BoolVal True)) (snd sol)) of
                              (r, _) -> r)
                          ) evalResult)
                        solutions = (fmap (\v -> (fst v)) eligibleSolutions)
                      in
                        (True, (solutions ++ ls)))
                    Left e -> (lu, ls)))
              solutions = case new_subst of
                [] -> invokeClosure([], (True, []))
                _ -> (foldl (\l -> (\r -> invokeClosure(r, l))) (True, []) new_subst)
              backSubResult = (fmap (\sol ->
                (LS.filter (\v ->
                     (fst v) `elem` variables
                  ) (LS.map (\(solKey, solExpr) ->
                    let
                      newKey = case LS.find (\v -> (fst v) == solKey) backSubst of
                        Just elem -> (fst (snd elem))
                        Nothing -> solKey
                    in
                      (newKey, (updateReferences backSubstRefs solExpr))
                  ) sol))) (snd solutions))
            in
              (fst solutions, backSubResult)
          (False, _) -> trace ("Unable to unify closure and term " ++ (show term)) (False, []))
    | otherwise = (False, [])

  unifyPair incut env subst term1 @ (TermExp tname1 args1) term2 @ (TermExp tname2 args2)
    | tname1 /= tname2 = ((False, []))
    | (length args1) /= (length args2) = (False, [])
    | otherwise =
      (foldl (\l ->
        (\r ->
          if (fst l) && (fst r) then
            let
              argSolutions = [(foldl (\l -> (\r -> (l ++ r))) [] ((snd l) ++ (snd r)))]
            in
              (True, argSolutions)
          else
            (False, []))
        ) (True, []) (fmap (\arg -> (unifyPair incut env subst (fst arg) (snd arg))) (zip args1 args2)))
  unifyPair _ a b c d = trace ("Unexpected input" ++ (show a) ++ " " ++ (show b) ++ " " ++ (show c) ++ " " ++ (show d)) (False, [])

  -- Performs unification for a given term against the global execution environment.
  -- Returns a set of solutions to the unification problem in form of [(A, 10), (B, 20)] where
  -- (A, 10) and (B, 20) are target substitutions.
  unify :: TermEnv -> Substs -> Expression -> (Bool, [Substs])
  unify env subst (CutExp expr) = unify' True env subst expr
  unify env subst expr = unify' False env subst expr

  unify' :: Bool -> TermEnv -> Substs -> Expression -> (Bool, [Substs])
  unify' _ env subst (CutExp expr) = unify' True env subst expr
  unify' incut env subst expr @ (TermExp name args) =
    let
      termId' = (termId name (length args))
      variables = (listVariables expr)
    in
      (case (H.lookup termId' env) of
        Just v ->
          let
            solutions = (foldl (\(lu, lsols) ->
              (\r ->
                (case r of
                  (True, rsubst) ->
                    (True, ((filter(\v -> (not ((length v) == 0))) rsubst) ++ lsols))
                  (False, _) ->
                    (if lu then lu else False, lsols))
              )) (True, []) (reverse (foldl (\l -> (\term ->
                if (length l) > 0 && incut then l
                else ( (unifyPair incut env subst term expr):l)
              )) [] v)))
            in
              solutions
        Nothing ->
          trace ("Term was not found:" ++ (show termId')) (False, []))

  unify' incut env subst expr =
    (case (eval incut S.empty subst env expr) of
      Right sols -> (True, fmap (\v ->  (fst v)) sols )
      Left e -> (False, []))

  applySubs :: Substs -> Expression -> [Expression]
  applySubs subs expression =
    (case expression of
      (VarExp n) ->
        let
          matchingSubst = (LS.map (\s ->
              (snd s)
            ) (LS.filter (\v -> (fst v) == n) subs))
        in
          if (not ((length matchingSubst) == 0)) then matchingSubst
          else [expression]
      _ -> [expression])

  --- Evaluates expression producing either exception or a set of solutions where each solution consists of:
  --- - substitution results
  --- - reduced expression (only vals or non-reducable var/closure expressions)
  --- eval :: Variables Scope -> Substitutions -> Terms Env -> Expression To Evaluate -> Evaluation result
  eval :: Bool -> VarScope -> Substs -> TermEnv -> Expression -> Either Exception [(Substs, Expression)]

  eval _ _ _ _ v @ (LiteralExp _) = Right [([], v)]

  eval _ _ subst termEnv v @ (VarExp n) =
    if (length subst) == 0 then (Right [([], v)])
    else
      case (LS.find (\v -> (fst v) == n) subst) of
        Just elem -> Right [([], (snd elem))]
        Nothing -> (Right [([], v)])

  eval _ parentScope subst termEnv (CutExp exp) = eval True parentScope subst termEnv exp

  eval incut parentScope subst termEnv exp @ (UnaryExpression op left) =
    (let
         closureScope = S.union (listVariables exp) parentScope
       in
         (fmap (\solution ->
            (fmap (\(subst, value) ->
              let
                updatedVal = case op of
                  OpMin -> unaryArithOp op value
                  OpNot -> unaryLogicalOp op value
              in (subst, updatedVal)) solution)
         ) (eval incut closureScope subst termEnv left)))

  eval incut parentScope subst termEnv exp @ (BinaryExpression op left right) =
    let
      closureScope = S.union (listVariables exp) parentScope
      leftSolsEither = (eval incut closureScope subst termEnv left)
    in
      case leftSolsEither of
        Right leftSolsList ->
          let
            -- short-circuiting evaluation
            eligibleSolutions =
              (filter (\leftSol ->
                  case (op, leftSol) of
                    (OpAnd, (_, exp)) -> isTruthy exp
                    _ -> True
                ) leftSolsList)
            result = leftSolsList >>= (\leftSol ->
              if (op == OpOr && isTruthy (snd leftSol)) then
                -- Short circuiting the right branch
                [leftSol]
              else
                  case (eval incut closureScope (subst ++ (fst leftSol)) termEnv right) of
                    Right rightSolsList ->
                      (fmap (\rightSol ->
                          let
                            (leftSolSubst, leftExpr) = leftSol
                            (rightSolSubst, rightExpr) = rightSol
                            evaluationResult = (case (leftExpr, rightExpr) of
                              (LiteralExp leftVal, LiteralExp rightVal) ->
                                if (isCompOp op) then
                                  (compareOp op leftExpr rightExpr)
                                else if (isBinaryLogicalOp op) then
                                  (binaryLogicalOp op leftExpr rightExpr)
                                else if (isBinaryArithOp op) then
                                  (binaryArithOp op leftExpr rightExpr)
                                else
                                  (ExceptionExpression (WrongBinaryOperationContext op leftExpr rightExpr))
                              (leftVal, rightVal) ->
                                trace ("Unexpected pair of values: " ++ (show leftVal) ++ " " ++ (show rightVal)) (ExceptionExpression (WrongBinaryOperationContext op leftExpr rightExpr)))
                          in
                            (leftSolSubst ++ rightSolSubst, evaluationResult)
                        ) rightSolsList)
                    Left exception -> trace("Exception intercepted, swallowing - " ++ (show exception)) []
              )
          in
            Right result
        Left e -> Left e

  eval incut parentScope subst termEnv exp @ (TermExp n args) =
    let
      closureScope = S.union (listVariables exp) parentScope
      evaluatedArgs = sequence ((fmap (\arg ->
          (fmap (\solutions ->
            (arg, (fmap (\sol -> (snd sol)) solutions))
          ) (eval incut parentScope subst termEnv arg)
        )) args))
      merged = fmap (\mv ->
        let
          argsEval = map (\v -> (applySubs subst v)) (map (\v -> (fst v)) mv)
          newTerms = map (\av -> TermExp n av) (sequence argsEval)
          unifiedTerms = (filter (\unified -> (fst (snd unified))) (map (\term -> (term, unify' incut termEnv subst term)) newTerms))
          resultTerms = (unifiedTerms >>= (\sol ->
            let
              unifySubst = (snd (snd sol))
            in
              fmap (\v -> (v, (LiteralExp (BoolVal True)))) unifySubst
            ))
        in resultTerms) evaluatedArgs
    in merged

  eval _ _ _ _ unexpected =
    trace ("Unexpected input to the eval(x, y): " ++ (show unexpected)) (Left (UnexpectedExpression unexpected))

  processInstructions :: [Statement] -> IO (Either [String] [Statement])
  processInstructions [] = return (Right [])
  processInstructions (stmt:xs) = case stmt of
    (ConsultStmt resource) ->
      (do
        result <- (do
          handle <- openFile resource ReadMode
          contents <- hGetContents handle
          return (M.runParser (program resource) "" (pack contents)))
        res <- (case result of
            (Right (Right (Program _ newstms))) ->
              fmap (\v -> fmap (\vr -> newstms ++ vr) v ) (processInstructions xs)
            Left e ->
              return (Left (["consult() failed to load instructions from the file: " ++ (show resource)]))
          )
        return res)
    _ ->
      fmap (\v ->
        fmap (\results ->
          (stmt:results)
        ) v) (processInstructions xs)

  solve :: [Statement] -> Expression -> IO (Either [String] [Substs])
  solve statements expr =
    fmap (\stms -> aux stms) (processInstructions statements)
      where
        aux (Left ex) = Left ex
        aux (Right []) = Left ["No statements provided"]
        aux (Right stms) =
            if(unifies) then
              Right substitutions
            else
              Left ["Unification failed"]
          where
            closures = (map (\v -> case v of
               (RuleStmt n args (Just body)) -> ((termId n (length args)), [(ClosureExpr n args body)])
               (RuleStmt n args Nothing) -> ((termId n (length args)), [(TermExp n args)])) stms)
            termEnv = (H.fromListWith (++) closures)
            variables = listVariables expr
            (unifies, substs) = (unify termEnv [] expr)
            substitutions = (fmap (\sub -> filterScope sub variables) substs)

