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
  - Numeric types: `Int`
  - Strings

The language allows following operations over its data types:
- Unary operations
  - Logical negation: `(!) :: Bool -> Bool`
  - Arithmetic negation: `(-) :: Int -> Int`
- Binary operations
  - Logical conjunction: `(and) :: Truthy -> Truthy -> Bool`
  - Logical disjunction: `(or) :: Truthy -> Truthy -> Bool`
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

### Syntax

Below is the rules describing syntax for expression and values supported by the language:
```
<alpha-num-char> = [a-zA-Z0-9]
<unary-operator> ::= '-' | 'not'

<binary-operator> ::= '+' | '*' | '/' |                          # arith operators 
                   '==' | '!=' | '<=' | '>=' | '<' | '>' |      # comparison operations
                   'and' | 'or'                                 # logical operator

<cons-list> ::= <expression-1> '|' <expression-1>

<enumerated-list> ::= <expression-1> ',' <expression-1> | <expression-1>

<list-elements> ::= <cons-list> | <enumerated-list> | '' 
<list> ::= '[' <listExpElements> ']'

<unary-operation> ::= <unary-operator> <expression-2>

<binary-operation> ::= <expression-2> <binary-operator> <expression-2>

<cut> ::= '!'

<integer> ::= <digit>
<digit> ::= [0-9]<digit> | ""

<boolean> ::= 'True' | 'False'
<atom> ::= <atom-first-char><atom-nonfirst-char>
<atom-first-char> ::= [a-z]
<atom-nonfirst-char> ::= [a-zA-Z0-9]<atom-non-first-char>

<literal> ::= <boolean> | <integer> | <string> | <atom>

<term> ::= <term-identifier> '(' <term-args> ')' 

<term-identifier> ::= <identifier-first-char><identifier-nonfirst-char>
<term-identifier-first-char> ::= [a-zA-Z_]
<term-identifier-nonfirst-char> ::= <alpha-num-char><identifier-nonfirst-char> | '' 

<term-args> ::= <expression-1> ',' <term-args> | <expression-1>

<variable> ::= <identifier-first-char><identifier-nonfirst-char>
<variable-first-char> ::= [A-Z_]
<variable-nonfirst-char> ::= <alpha-num-char><variable-nonfirst-char> | '' 

<expression-1> ::= <binary-operation> | <list> | <cut> | <unary-operation> | <term> | <literal> | <variable>
# An expression which is nested in some other binary or unary expression
<expression-2> ::= <list> | <cut> | '(' <unary-operation> ')' | <term> | '(' <binary-operation> ')' | <literal> | <variable>
```

Additionally, there are three extra rules which are describing statements. Statements are not expressions themselves but still they are being 
used by the parser to load the source code of the program that will be used by the user to query against:
```
<program> ::= <rule-statement><program> | <consult-statement><program>

<rule-statement> ::= <term-identifier> '(' <term-args> ')'<rule-statement-body>
<rule-statement-body> ::= ':-' <expression> '.' | ''

<consult-statement> ::= 'consult(' <single-quote> <consult-resource-path> <single-quote> ').'
 
 <single-quote> ::= '\''
```

### Unification 

In order to answer a user's query, the interpreter uses a unification procedure which for a given input is trying to: 
- Evaluate all expressions reducing them to literals or references 
- Decide whether the given input is satisfiable under the current environment scope (i.e. there is a solution that matches the defined criteria)
- Substitute variables provided as part of the given input with matching values defined in the current environment

### REPL


### Working examples

#### Example 1: Ancestry example - Siblings

The code of the `ancestry_1.prolog`:
```
parent(michael, josh).
parent(michael, stephen).
parent(michael, jessicah).

siblings(X, S) :- 
  parent(Y, X),
  parent(Y, S),
  S != X.
```

REPL commands to execute the example scenario:
```
repl>> :open "ancestry_1.prolog"
repl *ancestry_1.prolog> siblings(josh, Y)
? - True

Y = stephen
Y = jessicah

repl *ancestry_1.prolog> siblings(josh, jessica)
? - True

repl *ancestry_1.prolog> siblings(X, S)
? - True
(X = josh, S=stephen)
(X = josh, S=jessicah) 
```

### Known Issues / Scope for Improvement
- There seems to be an issue in the alpha-conversion algorithm for closures which is preventing correct unification in terms with dependent
  variable pairs which are named differently to the term represented by closure. I.e.:
  ```
    siblings(X, S) :- 
       parent(Y, X),
       parent(Y, S),
       S != X.
    
    ?- siblings(X, P)     # doesn't work correctly
    ?- siblings(X, S)     # works correctly
  ```
- There is no syntactic shape enforcement for const-lists:
  - Valid: `[H|T]`
  - Valid: `[X|[Y|T]]`
  - Also valid, unfortunately: `[H|(term name)]`
- There could be more control provided to the user when it comes to type conversion especially during arithmetic operations.
- It is impossible under the current implementation to have any persistent state between runs of `unify` / `solve`.
- If I had more time, I would try to merge definitions of `unify` and `eval` under a single `unify` construct.
