Prolog Engine (CS421 - Summer '21)
-----
- Author: Cyril Karpenko <kyrylok2@illinois.edu>
- Date: Aug/01/2020
- Source code repository: https://gitlab.com/cyrilkarpenko/prolog-engine

### Project structure

The source code of the project stored in the `src/` folder and split into three core modules:
- `Core.hs`: ADTs and core functions on them.
- `Parse.hs`: Data structures and functions directly related to language parsing activities.
- `Unify.hs`: Everything related to the unification engine allowing the majority of all operations provided by the language; 
  consists of functions related to the terms unification and those responsible for the evaluation of expressions.
  
There are also a number of tests defined in the `test/` folder 

### Overview

*Prolog Engine* - is a minimalistic implementation of a Prolog-like programming language written entirely in Haskell.

Its main features are:
- Support for boolean and exploratory queries against facts and rules defined in the input program declarations.
- Ability to load external definitions stored on the file system using `consult/1`.
- Rich support for data types and various operations on their values, including:
  - Atoms
  - Variables 
  - Terms (when used as a value `fact(A)`)
  - Cons-lists (i.e. `[Head|Tail]`)
  - Enumerated lists (i.e. `[1, 2, 3, 4, 5]`) 
  - Boolean 
  - Numeric types: `Int`, `Float`
  - Strings

The language allows following operations over its data types:
- Unary operations
  - Logical negation: `(!) :: Bool -> Bool`
  - Arithmetic negation: `(-) :: Int -> Int`
- Binary operations
  - Logical conjunction: `(and) :: Bool -> Bool -> Bool`
  - Logical disjunction: `(or) :: Bool -> Bool -> Bool`
  - Comparison operations:
    - `(>) :: Ord a -> a -> a -> Bool`
    - `(<) :: Ord a -> a -> a -> Bool`
    - `(>=) :: Ord a -> a -> a -> Bool`
    - `(<=) :: Ord a -> a -> a -> Bool`
    - `(==) :: Ord a -> a -> a -> Bool`
    - `(!=) :: Ord a -> a -> a -> Bool`
  - Arithmetic operations:
    - Addition: `(+) :: Numeric a -> a -> a -> a`
    - Multiplication: `(*) :: Numeric a -> a -> a -> a`
    - Division: `(/) :: Numeric a -> a -> a -> a`

## Implementation

The implementation of a syntax parser is based on capabilities provided by `megaparsec` library, language's AST consists
of three structural parts:
- Statements: `RuleStm` for high level definitions which is used for both rules and facts (a missing body part).
- Expressions: 
  - `(UnaryExpression op exp)` - a representation for an operation **op** of a single argument **exp**.
  - `(BinaryExpression op left right)` - a representation of an operation **op** of two arguments **left** and **right**.
  - `(TermExp name [Expression])` - a reference to a term **name** and a list of argument values. 
  - `CutExp` - denotes a cut operator `!`
  - `CutOperationExp` - a representation for a term within a given rule to which cut operator was applied (i.e. `t(X) :- f(X), !.`) 
- Values:  
  ```
  data Val = AtomVal String |
      IntVal Int |
      FloatVal Float |
      StringVal String |
      BoolVal Bool
      deriving (Show, Eq)
  ```
  

