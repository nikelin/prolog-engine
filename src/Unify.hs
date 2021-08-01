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

  type Subst = (String, Expression)
  type Substs = S.Set Subst
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
      S.filter (\sol -> (fst sol) `elem` scope) (subst))

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
    case (S.lookupIndex n (S.map (\v -> (fst v)) subst)) of
      Just idx -> (snd (S.elemAt idx subst))
      Nothing -> exp


  -- Performs unification between two given expressions, returns a set of solutions where each contains a set of substitutions
  -- which when applied to one side of the unification problem produce the desired outcome.
  unify'' :: Bool -> TermEnv -> Substs -> Expression -> Expression -> (Bool, [Substs])
  unify'' incut _ _ _ expr @ (ClosureExpr _ _ _) = (False, [])
  unify'' incut env subst l @ (VarExp n1) (VarExp n2) = (True, [])
  unify'' incut env subst (VarExp n) l @ (LiteralExp n1) = (True, [])
  unify'' incut env subst exp @ (BinaryExpression _ _ _) term @ (TermExp n args) =
    (case (eval S.empty subst env exp) of
      Right solutions ->
--        (True, (map (\sol -> (fst sol)) solutions))
        (foldl (\(unifies, lred) ->
          (\(rsubst, rexpr) ->
            (case (unify env rsubst rexpr) of
              (True, nsols) ->
                (True, nsols ++ lred)
              (False, _) -> (unifies, lred)
          ))) (True, []) solutions)
      Left e ->
        trace ("Unable to unify bin-exp and term-exp: " ++ (show exp) ++ " termexp " ++ (show term) ++ ", reason: " ++ (show e)) (False, []))

  unify'' incut env subst t @ (TermExp _ _) (VarExp n) = (True, [S.singleton (n, t)])
  unify'' incut env subst v @ (LiteralExp _) (VarExp n) = (True, [S.singleton (n, v)])
  unify'' incut env subst (LiteralExp left) (LiteralExp right) = (left == right, [])
  unify'' incut env subst (ExceptionExpression _) _ = (False, [])
  unify'' incut env subst _ (ExceptionExpression _) = (False, [])

  -- This unification serves as a sort of 'invocation' for the closure term.
  --
  -- Closure arguments are going to be replaced by either values or placeholders from the input term, in the latter case
  -- we will also have to update closure's body as otherwise we are going to face incorrect naming issues.
  unify'' incut env subst lambda @ (ClosureExpr cn closure_args body) term @ (TermExp tn args)
    | cn == tn =
      let
        symbolsTable = (genSym closure_args)
        symbols = S.fromList (fmap (\sym -> ((fst (fst sym)), (snd (snd sym)))) symbolsTable)
        closureArgsScoped = fmap (\arg -> (updateReferences symbols arg)) closure_args
        backSubst = S.fromList (fmap (\sym -> ((fst (snd sym)), ((fst (fst sym)), (snd (fst sym))))) symbolsTable)
        backSubstRefs = (S.map (\s -> (fst s, (snd (snd s)))) backSubst)
        variables = listVariables term
      in
        (case (unify'' incut env subst term (TermExp cn closureArgsScoped)) of
          (True, new_subst) ->
            let
              invokeClosure = (\(r, (lu, ls)) ->
                let
                  updatedBody = (updateReferences symbols body)
                in
                  (case (eval S.empty r env updatedBody) of
                    Right evalResult ->
                      (let
                        eligibleSolutions = (filter (\sol ->
                            -- making sure that the resulting value is 'truthy' (i.e. unifiable to True)
                            case (unify'' True env subst (LiteralExp (BoolVal True)) (snd sol)) of
                              (r, _) -> r
                          ) evalResult)
                        solutions = (fmap (\v -> (fst v)) eligibleSolutions)
                      in
                        (True, (mappend solutions ls)))
                    Left e -> (lu, ls)))
              solutions = case new_subst of
                [] -> invokeClosure(S.empty, (True, []))
                _ -> (foldl (\l -> (\r -> invokeClosure(r, l))) (True, []) new_subst)
              backSubResult = (fmap (\sol ->
                (S.filter (\v ->
                     (fst v) `elem` variables
                  ) (S.map (\(solKey, solExpr) ->
                    let
                      newKey = case S.lookupIndex solKey (S.map (\v -> (fst v)) backSubst) of
                        Just idx -> (fst (snd (S.elemAt idx backSubst)))
                        Nothing -> solKey
                    in
                      (newKey, (updateReferences backSubstRefs solExpr))
                  ) sol))) (snd solutions))
            in
              (fst solutions, backSubResult)
          (False, _) -> trace ("Unable to unify closure and term " ++ (show term)) (False, []))
    | otherwise = (False, [])

  unify'' incut env subst term1 @ (TermExp tname1 args1) term2 @ (TermExp tname2 args2)
    | tname1 /= tname2 = ((False, []))
    | (length args1) /= (length args2) = (False, [])
    | otherwise =
      (foldl (\l ->
        (\r ->
          if (fst l) && (fst r) then
            let
              argSolutions = [(foldl (\l -> (\r -> (S.union l r))) S.empty ((snd l) ++ (snd r)))]
            in
              (True, argSolutions)
          else
            (False, []))
        ) (True, []) (fmap (\arg -> (unify'' False env subst (fst arg) (snd arg))) (zip args1 args2)))
  unify'' _ a b c d = trace ("Unexpected input" ++ (show a) ++ " " ++ (show b) ++ " " ++ (show c) ++ " " ++ (show d)) (False, [])

  -- Performs unification for a given term against the global execution environment.
  -- Returns a set of solutions to the unification problem in form of [(A, 10), (B, 20)] where
  -- (A, 10) and (B, 20) are target substitutions.
  unify :: TermEnv -> Substs -> Expression -> (Bool, [Substs])
  unify env subst (CutExp expr) = unify' True env subst expr
  unify env subst expr = unify' False env subst expr

  unify' :: Bool -> TermEnv -> Substs -> Expression -> (Bool, [Substs])
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
                    (True, (
                      (filter(\v -> (not (S.null v))) rsubst) ++ lsols))
                  (False, _) ->
                    (if lu then lu else False, lsols))
              )) (True, []) (reverse (foldl (\l -> (\term ->
                if (length l) > 0 && incut then l
                else ((unify'' False env subst term expr):l)
              )) [] v)))
            in
              solutions
        Nothing ->
          trace ("Term was not found:" ++ (show termId')) (False, []))

  unify' _ env subst expr =
    (case (eval S.empty subst env expr) of
      Right sols -> (True, fmap (\v ->  (fst v)) sols )
      Left e -> (False, []))

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
  --- eval :: Variables Scope -> Substitutions -> Terms Env -> Expression To Evaluate -> Evaluation result
  eval :: VarScope -> Substs -> TermEnv -> Expression -> Either Exception [(Substs, Expression)]

  eval _ _ _ v @ (LiteralExp _) = Right [(S.empty, v)]

  eval _ subst termEnv v @ (VarExp n) =
    if (S.null subst) then (Right [(S.empty, v)])
    else
      case (S.lookupIndex n (S.map (\v -> (fst v)) subst)) of
        Just idx -> trace ("Resolved " ++ (show v) ++ " in the current closure context")  Right [(S.empty, (snd (S.elemAt idx subst)))]
        Nothing -> trace ("Unable to resolve " ++ (show v) ++ " in the current closure context: " ++ (show subst)) (Right [(S.empty, v)])

  eval parentScope subst termEnv exp @ (UnaryExpression op left) =
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
         ) (eval closureScope subst termEnv left)))

  eval parentScope subst termEnv exp @ (BinaryExpression op left right) =
    (let
      closureScope = S.union (listVariables exp) parentScope
    in
      (eval closureScope subst termEnv left) >>= (\leftSol ->
        let
          rightSols = fmap (\v -> v >>= id) (sequence (fmap (\(sub, expr) ->
            (eval closureScope (S.union sub subst) termEnv right)) leftSol))
          evaluationResult = (fmap (\rightSol ->
            (fmap (\(left, right) ->
              (let
                expr =
                  if (isCompOp op) then
                    case (trace ("Left: " ++ (show left) ++ ", right: " ++ (show right))) (left, right) of
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
                    (S.union lsub rsub, expr)))
            ) (zip leftSol rightSol)) ) rightSols)
        in evaluationResult))

  eval parentScope subst termEnv exp @ (TermExp n args) =
    let
      closureScope = S.union (listVariables exp) parentScope
      evaluatedArgs = sequence ((fmap (\arg ->
          (fmap (\solutions ->
            (arg, (fmap (\sol -> (snd sol)) solutions))
          ) (eval parentScope subst termEnv arg)
        )) args))
      merged = fmap (\mv ->
        let
          argsEval = map (\v -> (applySubs subst v)) (map (\v -> (fst v)) mv)
          newTerms = map (\av -> TermExp n av) (sequence argsEval)
          unifiedTerms = (filter (\unified -> (fst (snd unified))) (map (\term -> (term, unify termEnv subst term)) newTerms))
          resultTerms = (unifiedTerms >>= (\sol ->
            let
              unifySubst = (snd (snd sol))
            in
              fmap (\v -> (v, (LiteralExp (BoolVal True)))) unifySubst
            ))
        in resultTerms) evaluatedArgs
    in merged

  eval parentScope termEnv subst (CutExp exp) = eval parentScope termEnv subst exp

  eval _ _ _ unexpected =
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
            (unifies, substs) = (unify termEnv S.empty expr)
            substitutions = (fmap (\sub -> filterScope sub variables) substs)

