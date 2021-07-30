{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections     #-}
{-# LANGUAGE BangPatterns       #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE RecordWildCards    #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Unify(solve, processInstructions, eval) where
  import qualified Data.HashMap.Strict as H (HashMap, unions, insert, fromListWith, lookup, empty, fromList, toList, union, unionWith)
  import qualified Data.Set as S
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
  type Subst = (String, Expression)
  type Substs = S.Set Subst
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

  filterScope :: Substs -> [String] -> Substs
  filterScope subst scope = (
      S.filter (\sol -> (fst sol) `elem` scope) (subst))

  -- Performs α-conversion on a given closure body (expression) applying
  -- using a substitutions list on every variable occurrence within the context of a closure.
  -- As we can't have nested closures in Prolog, we can disregard complexities associated
  -- with multi-level closures α-conversion.
  updateReferences :: Substs -> Expression -> Expression
  updateReferences subst (CutExp exp) = (updateReferences subst exp)
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
  updateReferences _ expr @ (ClosureExpr _ _ _) = expr  -- fortunately, it is impossible to use functions as a
                                                        -- value in Prolog
  updateReferences subst exp @ (VarExp n) =
    case (S.lookupIndex n (S.map (\v -> (fst v)) subst)) of
      Just idx -> (snd (S.elemAt idx subst))
      Nothing -> exp


  -- Performs unification between two given expressions, returns a set of solutions where each contains a set of substitutions
  -- which when applied to one side of the unification problem produce the desired outcome.
  unify' :: Bool -> TermEnv -> Substs -> Expression -> Expression -> (Bool, [Substs])
  unify' incut _ _ _ expr @ (ClosureExpr _ _ _) = (False, [])
  unify' incut env subst l @ (VarExp n1) (VarExp n2) = (True, [S.singleton (n2, VarExp n1)]) -- cannot unify outside of a closure context
  unify' incut env subst (VarExp n) l @ (LiteralExp _) = (True, []) -- cannot unify outside of a closure context
  unify' incut env subst exp @ (BinaryExpression _ _ _) term @ (TermExp n args) =
    (case (eval subst env exp) of
      Right solutions ->
        (foldl (\(unifies, lred) ->
          (\(rsubst, rexpr) ->
            case (unify False env rsubst rexpr) of
              (True, nsols) ->
                (True, nsols ++ lred)
              (False, _) -> (unifies, lred)
          )) (True, []) solutions)
      Left e ->
        trace ("Unable to unify bin-exp and term-exp: " ++ (show exp) ++ " termexp " ++ (show term) ++ ", reason: " ++ (show e)) (False, []))

  unify' incut env subst t @ (TermExp _ _) (VarExp n) = (True, [S.singleton (n, t)])
  unify' incut env subst v @ (LiteralExp _) (VarExp n) = (True, [S.singleton (n, v)])
  unify' incut env subst (LiteralExp left) (LiteralExp right) = (left == right, [])

  -- This unification serves as a sort of 'invocation' for the closure term.
  --
  -- Closure arguments are going to be replaced by either values or placeholders from the input term, in the latter case
  -- we will also have to update closure's body as otherwise we are going to face incorrect naming issues.
  unify' incut env subst lambda @ (ClosureExpr cn closure_args body) term @ (TermExp tn args)
    | cn == tn =
      let
        symbolsTable = (genSym closure_args)
        symbols = S.fromList (fmap (\sym -> ((fst (fst sym)), (snd (snd sym)))) symbolsTable)
        closureArgsScoped = fmap (\arg -> (updateReferences symbols arg)) closure_args
        backSubst = S.fromList (fmap (\sym -> ((fst (snd sym)), (snd (fst sym)))) symbolsTable)
      in
        (case (unify' incut env subst term (TermExp cn closureArgsScoped)) of
          (True, new_subst) ->
            let
              invokeClosure = (\(r, (lu, ls)) ->
                let
                  updatedBody = (updateReferences symbols body)
                in
                  (case (eval r env updatedBody) of
                    Right solutions ->
                      let
                        eval_subst = (fmap (\v -> (fst v)) solutions)
                      in
                        (True, (mappend eval_subst ls))
                    Left e -> trace ("Evaluation failed due to: " ++ (show e)) (lu, ls)))
              solutions = case new_subst of
                [] -> invokeClosure(S.empty, (True, []))
                _ -> (foldl (\l -> (\r -> invokeClosure(r, l))) (True, []) new_subst)
              backSubResult = (fmap (\sol -> (S.map (\nsub -> (fst nsub, (updateReferences backSubst (snd nsub)))) sol)) (snd solutions))
            in
              (fst solutions, backSubResult)
          (False, _) -> trace ("Unable to unify closure and term " ++ (show term)) (False, []))
    | otherwise = (False, [])

  unify' incut env subst term1 @ (TermExp tname1 args1) term2 @ (TermExp tname2 args2)
    | tname1 /= tname2 = ((False, []))
    | (length args1) /= (length args2) = (False, [])
    | otherwise =
      (foldl (\l ->
        (\r ->
          if (fst l) && (fst r) then
            (True, (snd l) ++ (snd r))
          else
            (False, []))
        ) (True, []) (fmap (\arg -> (unify' incut env subst (fst arg) (snd arg))) (zip args1 args2)))
  unify' _ a b c d = trace ("Unexpected input" ++ (show a) ++ " " ++ (show b) ++ " " ++ (show c) ++ " " ++ (show d)) (False, [])

  -- Performs unification for a given term against the global execution environment.
  -- Returns a set of solutions to the unification problem in form of [(A, 10), (B, 20)] where
  -- (A, 10) and (B, 20) are target substitutions.
  unify :: Bool -> TermEnv -> Substs -> Expression -> (Bool, [Substs])
  unify incut env subst expr @ (TermExp name args) =
    let
      termId' = (termId name (length args))
    in
      (case (H.lookup termId' env) of
        Just v ->
          (foldl (\(lu, lsols) ->
            (\r ->
              (case r of
                (True, rsubst) ->
                  (True, trace ("Unification " ++ (show v) ++ " against " ++ (show expr)) (rsubst ++ lsols))
                (False, _) ->
                  (if lu then lu else False, lsols))
            )) (True, []) (fmap (\term -> (unify' False env subst term expr)) v))
        Nothing ->
          trace ("Term was not found:" ++ (show termId')) (False, []))

  unify _ env subst (CutExp expr) =
    unify True env subst expr

  unify _ env subst expr =
    (case (eval subst env expr) of
      Right sols -> (True, fmap (\v ->  (fst v)) sols )
      Left e -> trace ("Expression evaluation failed: " ++ (show e)) (False, []))

  applySubs :: Substs -> Expression -> [Expression]
  applySubs subs expression =
    (case expression of
      (VarExp n) ->
        let
          matchingSubst = (S.map (\s ->
              (snd s)
            ) (S.filter (\v -> (fst v) == n) subs))
        in
          if (not (S.null matchingSubst)) then (S.toList matchingSubst)
          else [expression]
      _ -> [expression])

  --- Evaluates expression producing either exception or a set of solutions where each solution consists of:
  --- - substitution results
  --- - reduced expression (only vals or non-reducable var/closure expressions)
  eval :: Substs -> TermEnv -> Expression -> Either Exception [(Substs, Expression)]

  eval _ _ v @ (LiteralExp _) = Right [(S.empty, v)]

  eval subst termEnv v @ (VarExp n) =
    if (S.null subst) then (Right [(S.empty, v)])
    else
      case (S.lookupIndex n (S.map (\v -> (fst v)) subst)) of
        Just idx -> Right [(S.empty, (snd (S.elemAt idx subst)))]
        Nothing -> Right [(S.empty, v)]

  eval subst termEnv exp @ (BinaryExpression op left right) =
    let
      closureScope = listVariables exp
    in
      (case (eval subst termEnv left) of
          Right leftSol ->
            let
              rightSols = fmap (\v -> v >>= id) (sequence (fmap (\(sub, expr) ->
                (eval (S.union subst sub) termEnv right)) leftSol))
              evaluationResult = (fmap (\rightSol ->
                leftSol >>= (\left ->
                  (fmap (\right ->
                    let
                      expr =
                        if (isCompOp op) then
                          case (left, right) of
                            ((_, le @ (LiteralExp _)), (rsub, re @ (LiteralExp _))) ->
                              (compareOp op le re)
                            ((_, le), (_, re @ (TermExp n args))) ->
                              (compareOp op le re)
                            ((_, le), (_, re)) ->
                              (ExceptionExpression (WrongBinaryOperationContext op le re))
                        else if (isBinaryLogicalOp op) then
                          case (left, right) of
                             ((_, le @ (LiteralExp _)), (rsub, re @ (LiteralExp _))) ->
                                (binaryLogicalOp op le re)
                             ((_, le), (_, re)) ->
                                (ExceptionExpression (WrongBinaryOperationContext op le re))
                        else
                          case (left, right) of
                            ((_, vl @ (LiteralExp _)), (_, vr @ (LiteralExp _))) ->
                              vl
                            ((_, le), (_, re)) ->
                              (ExceptionExpression (WrongBinaryOperationContext op le re))
                    in
                      (case (left, right) of
                        ((lsub, _), (rsub, _)) ->
                          (scopedSubstitutions, expr)
                            where
                              scopedSubstitutions = filterScope (S.union lsub rsub) closureScope)
                  ) rightSol)
                )) rightSols)
            in evaluationResult
          Left e -> Left e)

  eval subst termEnv (TermExp n args) =
    let
      r2 = sequence ((fmap (\arg ->
          (fmap (\solutions ->
            (arg, (fmap (\sol -> (snd sol)) solutions))
          ) (eval subst termEnv arg)
        )) args))
      merged = (case r2 of
        Right mv ->
          let
            argsEval = map (\v -> (applySubs subst v)) (map (\v -> (fst v)) mv)
            newTerms = map (\av -> TermExp n av) (sequence argsEval)
            unifiedTerms = (filter (\unified -> (fst (snd unified))) (map (\term -> (term, unify False termEnv subst term)) newTerms))
            resultTerms = (unifiedTerms >>= (\sol ->
              let
                unifySubst = (snd (snd sol))
              in
                fmap (\v -> (v, (LiteralExp (BoolVal True)))) unifySubst
              ))
          in Right (trace ("eval term: " ++ (show resultTerms)) resultTerms)
        Left e -> Left e)
    in merged

  eval _ _ unexpected =
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
            (unifies, substs) = (unify False termEnv S.empty expr)
            substitutions = (fmap (\sub -> filterScope sub variables) substs)

