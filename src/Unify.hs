{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections     #-}
{-# LANGUAGE BangPatterns       #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE RecordWildCards    #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Unify(solve) where
  import qualified Data.HashMap.Strict as H (HashMap, unions, insert, fromListWith, lookup, empty, fromList, toList, union, unionWith)
  import Core
  import Debug.Trace

  import Control.Monad (sequence)

  type Subst = (String, Expression)
  type TermId = String
  type TermEnv = H.HashMap TermId [Expression]
  type EvalEnv = H.HashMap String Expression

  termId :: String -> Int -> TermId
  termId name argc = name ++ "/" ++ (show argc)

  -- Performs unification between two given expressions, returns a set of solutions where each contains a set of substitutions
  -- which when applied to one side of the unification problem produce the desired outcome.
  unify' :: TermEnv -> [Subst] -> Expression -> Expression -> (Bool, [[Subst]])
  unify' _ _ _ expr @ (ClosureExpr _ _ _) = trace ("Unable to unify expression" ++ (show expr)) (False, [])
  unify' env subst (VarExp n1) (VarExp n2) = (True, [[]]) -- cannot unify outside of a closure context
  unify' env subst (VarExp n) l @ (LiteralExp _) = (True, [[(n, l)]]) -- cannot unify outside of a closure context
  unify' env subst exp @ (BinaryExpression _ _ _) term @ (TermExp n args) =
    trace ("Evaluating binary expression " ++ (show exp)) (case (eval subst env H.empty exp) of
      Right solutions ->
        (foldl (\(unifies, lred) ->
          (\(rsubst, rexpr) ->
            case (trace ("Unifying term and binary expression: " ++ (show n) ++ " expr: " ++ (show exp)) (unify env rsubst rexpr)) of
              (True, nsols) ->
                (True, nsols ++ lred)
              (False, _) -> (unifies, lred)
          )) (True, [[]]) solutions)
      Left e ->
        trace ("Unable to unify bin-exp and term-exp: " ++ (show exp) ++ " termexp " ++ (show term) ++ ", reason: " ++ (show e)) (False, []))

  unify' env subst t @ (TermExp _ _) (VarExp n) = (True, [[(n, t)]])
  unify' env subst v @ (LiteralExp _) (VarExp n) = (True, [[(n, v)]])
  unify' env subst (LiteralExp left) (LiteralExp right) = (left == right, [[]])
  unify' env subst (ClosureExpr cn closure_args body) term @ (TermExp tn args)
    | cn == tn =
      case (trace ("Unifying closure and term: body " ++ (show body) ++ " term " ++ (show term)) (unify' env subst term (TermExp cn closure_args))) of
        (True, new_subst) ->
          trace ("Unified " ++ (show new_subst) ++ ", subst: " ++ (show subst)) (foldl (\(lu, ls) ->
            (\r ->
              trace ("Processing solution " ++ (show r)) (let
                updated_env = (H.fromList r)
              in
                trace ("Substitution in lambda " ++ (show new_subst) ++ ", continue evaluation on " ++ (show body)) (case (eval r env updated_env body) of
                  Right solutions ->
                    let
                      eval_subst = (fmap (\v -> (fst v)) solutions)
                    in
                      (True, (mappend eval_subst ls))
                  Left e -> trace ("Evaluation failed due to: " ++ (show e)) (lu, ls)))
          )) (True, []::[[Subst]]) new_subst)
        (False, _) -> trace ("Unable to unify closure and term " ++ (show term)) (False, [])
    | otherwise = (False, [])

  unify' env subst term1 @ (TermExp tname1 args1) term2 @ (TermExp tname2 args2)
    | tname1 /= tname2 = (trace ("Name mismatch" ++ (show tname1) ++ (show tname2)))((False, []))
    | (length args1) /= (length args2) = trace ("Args length mismatch" ++ (show tname1)) (False, [])
    | otherwise =
      trace ("Unifying two terms: term1= " ++ (show term1) ++ " and " ++ (show term2)) (foldl (\l ->
          (\r ->
            if (fst l) && (fst r) then
              (True, (snd l) ++ (snd r))
            else
              (False, []))
          ) (True, []) (fmap (\arg -> trace ("Attempting to unify" ++ (show (fst arg)) ++ " " ++ (show (snd arg))) (unify' env subst (fst arg) (snd arg))) (zip args1 args2)))
  unify' a b c d = trace ("Unexpected input" ++ (show a) ++ " " ++ (show b) ++ " " ++ (show c) ++ " " ++ (show d)) (False, [])

  -- Performs unification for a given term against the global execution environment.
  -- Returns a set of solutions to the unification problem in form of (1, [(A, 10), (B, 20)]) where 1
  -- is the number of a solution and  (A, 10) and (B, 20) are target substitutions.
  unify :: TermEnv -> [Subst] -> Expression -> (Bool, [[Subst]])
  unify env subst expr @ (TermExp name args) =
    let
      termId' = (termId name (length args))
    in
      (case (H.lookup termId' env) of
        Just v ->
          trace ("Resolved expressions for termID: " ++ (show termId') ++ ": " ++ show(v)) (foldl (\(lu, lsols) ->
            (\r ->
              case (trace ("Unification result: " ++ (show r)) r) of
                (True, rsubst) ->
                  (True, rsubst ++ lsols)
                (False, _) ->
                  (if lu then lu else False, lsols)
            )) (True, []) (fmap (\term -> (unify' env subst term expr)) v))
        Nothing ->
          trace ("Term was not found:" ++ (show termId')) (False, []))

  unify env subst expr =
    trace ("Unification for expression: " ++ (show expr)) (case (eval subst env H.empty expr) of
      Right sols -> (True, fmap (\v ->  (fst v)) sols )
      Left e -> trace ("Expression evaluation failed: " ++ (show e)) (False, []))

  applySubs :: [Subst] -> Expression -> [Expression]
  applySubs subs expression =
    trace ("Applying substitutions in: " ++ (show expression) ++ " subs: " ++ (show subs)) (case expression of
      (VarExp n) ->
        let
          matchingSubst = (map (\s ->
              (snd s)
            ) (filter (\v -> (fst v) == n) subs))
        in
          case (matchingSubst) of
            xs @ (_:_) -> xs
            _ -> [expression]
      _ -> [expression])

  --- Evaluates expression producing either exception or a set of solutions where each solution consists of:
  --- - substitution results
  --- - reduced expression (only vals or non-reducable var/closure expressions)
  eval :: [Subst] -> TermEnv -> EvalEnv -> Expression -> Either Exception [([Subst], Expression)]

  eval _ _ _ v @ (LiteralExp _) = Right [([], v)]

  eval subst termEnv env v @ (VarExp n) =
      case subst of
        [] -> trace ("No substitutions to proceed with the evaluation: " ++ (show n)) (Right [([], v)])
        _ ->
          trace ("Evaluating the variable " ++ (show n) ++ " against " ++ (show subst)) (case (map (\v -> (snd v)) (filter (\v -> (fst v) == n) subst)) of
            [] -> Right [([], v)]
            (x:_) -> Right [([], x)])

  eval subst termEnv env (BinaryExpression op left right) =
    case trace ("Left operand evaluation: " ++ (show left) ++ " " ++ (show subst))  (eval subst termEnv env left) of
      Right leftSol ->
        let
          result = (sequence (fmap (\(sub, expr) ->
            trace ("Right operand evaluation: " ++ (show right)) (eval (subst ++ sub) termEnv env right)) leftSol))
          rightSols = fmap (\v -> v >>= id) result
          result2 = (fmap (\rightSol ->
            (fmap (\(left, right) ->
              if (isCompOp op) then
                case (left, right) of
                  ((lsub, le @ (LiteralExp _)), (rsub, re @ (LiteralExp _))) ->
                    trace("LiteralExp vs LiteralExp" ++ (show le) ++ " " ++ (show re)) ([], (compareOp op le re))
                  ((lsub, le), (rsub, re @ (TermExp n args))) ->
                    trace("LiteralExp vs LiteralExp" ++ (show le) ++ " " ++ (show re)) ([], (compareOp op le re))
                  ((lsub, le), (rsub, re)) ->
                    trace ("Unsupported comparison: " ++ (show le) ++ " " ++ (show re) ++ " " ++ (show (lsub ++ rsub))) ([], (ExceptionExpression (WrongBinaryOperationContext op le re)))
              else if (isBinaryLogicalOp op) then
                case (left, right) of
                   ((lsub, le @ (LiteralExp _)), (rsub, re @ (LiteralExp _))) ->
                      trace("LiteralExp vs LiteralExp" ++ (show le) ++ " " ++ (show re)) (lsub ++ rsub, (binaryLogicalOp op le re))
                   ((_, le), (_, re)) ->
                      ([], (ExceptionExpression (WrongBinaryOperationContext op le re)))
              else
                case (left, right) of
                  ((lsub, vl @ (LiteralExp _)), (rsub, vr @ (LiteralExp _))) ->
                    trace("LiteralExp vs LiteralExp" ++ (show vl) ++ " " ++ (show vr)) ([], vl)
                  ((_, le), (_, re)) ->
                    ([], (ExceptionExpression (WrongBinaryOperationContext op le re)))
            ) (zip leftSol rightSol))) rightSols)
        in (trace ("Evaluation result: " ++ (show result2)) (result2))
      Left e -> Left e

  eval subst termEnv env (TermExp n args) =
    let
      r2 = sequence ((fmap (\arg ->
          (fmap (\solutions ->
            (arg, (fmap (\sol -> (snd sol)) solutions))
          ) (eval subst termEnv env arg)
        )) args))
      merged = trace ("Resolved arguments " ++ (show r2)) (case r2 of
        Right mv ->
          let
            argsEval = map (\v -> trace ("Substitutions: " ++ (show $ applySubs subst v)) (applySubs subst v)) (map (\v -> (fst v)) mv)
            newTerms = map (\av -> TermExp n av) (sequence argsEval)
            unifiedTerms = trace ("Original args list: " ++ (show args) ++ ", substituted: " ++ (show argsEval)) (
              filter (\unified -> (fst (snd unified))) (map (\term -> (term, unify termEnv subst term)) newTerms))
            resultTerms = unifiedTerms >>= (\sol ->
              let
                unifySubst = (snd (snd sol))
              in
                fmap (\v -> (v, (fst sol))) unifySubst
              )
            result = trace ("Applying substitutions on " ++ (show mv) ++ " substitutions: " ++ (show subst)) (resultTerms)
          in Right result
        Left e -> Left e)
    in
      merged

  eval _ _ _ unexpected =
    trace ("Unexpected input to the eval(x, y): " ++ (show unexpected)) (Left (UnexpectedExpression unexpected))

  solve :: [Statement] -> Expression -> Either [String] [[Subst]]
  solve statements expr = (case result of
    (False, _) -> (Left ["unification failed"])
    (True, substList) -> Right substList)
      where
        closures = (map (\v -> case v of
           (RuleStmt n args (Just body)) -> ((termId n (length args)), [(ClosureExpr n args body)])
           (RuleStmt n args Nothing) -> ((termId n (length args)), [(TermExp n args)])) statements)
        termEnv = (H.fromListWith (++) closures)
        result = unify termEnv [] expr
