module Main
    where

import Data.Either
import Test.HUnit

import ERP

-- Helpers.
-----------

makeListOfTests :: (Eq a, Show a) => [a] -> [a] -> [Test]
makeListOfTests actual expected =
    if length actual == length expected
    then zipWith (~?=) actual expected
    else error "makeListOfTests: both lists should be the same length!"

-- Constraint solver tests.
---------------------------

constraintsActual :: [String]
constraintsActual = map (either id showConstraintSet . unify) allTests
    where
      allTests =
          [
           [(STBase "X", STInt),(STBase "Y", STFun (STBase "X") (STBase "X"))],
           [(STFun STInt STInt, STFun (STBase "X") (STBase "Y"))],
           [(STInt, STFun (STInt) (STBase "Y"))],
           [(STBase "Y", STFun STInt (STBase "Y"))],
           [],
           [(STFun (STBase "x_0") (STBase "x_0"), STFun (STBase "x_1") STInt)],
           [(STFun (STBase "x_0") (STBase "x_0"), STFun STInt (STBase "x_1"))],
           [(STStr,STInt),(STInt,STInt)]
          ]

constraintsExpected :: [String]
constraintsExpected =
    [
     "{(Y = int -> int), (X = int)}",
     "{(Y = int), (X = int)}",
     "Unsolvable constraints",
     "Unsolvable constraints",
     "{}",
     "{(x_1 = int), (x_0 = x_1)}",
     "{(x_1 = int), (x_0 = int)}",
     "Unsolvable constraints"
    ]

constraintsTests :: [Test]
constraintsTests = makeListOfTests constraintsActual constraintsExpected

-- Shared test data for inference and evaluation tests.
-------------------------------------------------------

astTests :: [AST]
astTests = [
 (app (lambda (var "x") (var "x")) (int 1)),
 (lambda (var "x") (var "x")),
 (lambda (var "x") (plus (var "x") (var "x"))),
 (plus (str "abc") (int 2)),
 (lambda (var "y")
  (lambda (var "x") (plus (var "y") (var "x")))),
 (lambda (var "x") (str "abc")),
 (lambda (var "y") (lambda (var "x") (str "abc"))),
 (lambda (var "a") (lambda (var "z")
                    (lambda (var "y") (lambda (var "x") (int 42))))),
 (lambda (var "x") (concatStr (var "x") (var "x"))),
 (let_ [("f", (int 1)), ("f", (int 2))]
  (plus (var "f") (var "f"))),
 (let_ [("f", (lambda (var "x") (var "x")))]
  (tuple [(app (var "f") (str "abc")),
          (app (var "f") (str "abc"))])),
 (let_ [("f", (lambda (var "x") (var "x")))]
  (tuple [(app (var "f") (str "abc")),
          (app (var "f") (int 1))])),
 (builtinApp "plus" [(int 1), (int 2), (int 3)]),
 (app (var "fst") (tuple [(int 1), (int 2), (int 3)])),
 (app (var "fst") (tuple [(int 1), (int 2)])),
 (app (var "snd") (tuple [(int 1), (str "2")])),
 (tuple [(app (var "snd")
          (tuple [(int 7), (str "8")])),
         (app (var "fst")
          (tuple [(bool True), (bool False)]))]),
 (let_ [("f", (lambda (var "x") (var "x")))]
           (tuple [(app (var "f") (int 1)),
                   (app (var "f") (bool True))])),
 (tuple [(length_ (list [(int 1), (int 2), (int 3)])),
         (length_ (list [(str "abc")]))]),

 (snd_ (tuple [(var "x"), (int 1)])),
 (let_ [("t", (tuple [(bool True), (str "aaa")]))]
  (tuple [(snd_ (var "t")), (fst_ (var "t"))])),

 (tuple [(int 6), (str "abc")]),
 (tuple [(lambda (var "x") (var "x")), (str "abc")]),

 (list [(int 1), (int 2), (int 3)]),
 (list [(int 1), (int 2), (str "abc")]),

 (concatStr (str "answer: ")
  (intToStr (plus (int 35) (int 7)))),
 (let_ [("f", (lambda (var "x") (var "x")))]
  (app (var "f") (int 1))),
 (builtinApp "plus" [(int 1), (int 2)]),
 (let_ [("f", (app (builtin "plus") (int 1)))] (app (var "f") (int 22))),
 (app (lambda (var "x") (snd_ (var "x"))) (tuple [(int 1), (bool False)])),
 (map_ (lambda (var "x") (plus (var "x") (int 64))) (list [(int 1), (int 2)])),
 (filter_ (app (var "strEq") (str "abc"))
              (list [(str "abc"), (str "def"), (str "abc")])),
 (reduce (lambda (var "x") (lambda (var "y") (plus (var "x") (var "y"))))
             (int 0) (list [(int 1), (int 2), (int 3)])),
 (reduce (var "plus") (int 993) (list [(int 1), (int 2), (int 3)])),
 (app (app (lambda (var "x") (lambda (var "y")
                              (plus (var "x") (var "y")))) (int 1)) (int 2)),
 (boolEq (bool True) (app (lambda (var "x") (var "x")) (bool True))),
 (intEq (int 23) (int 23)),
 (strEq (str "abc") (str "abc")),
 (var "id"),
 (map_ (var "id") (list [(int 1), (int 2), (int 3)])),
 (ifThenElse (bool True) (str "abc") (str "bcd")),
 (ifThenElse (str "abc") (str "abc") (str "bcd")),
 (ifThenElse (strEq (str "abc") (str "bcd")) (bool True) (int 1)),
 (ifThenElse (strEq (str "abc") (str "bcd"))
                 (bool True) (app (var "id") (bool False))),
 (concatMap_ (lambda (var "x") (list [(var "x")]))
                 (list [(int 1), (int 2), (int 3)])),
 (concatMap_ (var "id") (list [(int 1), (int 2), (int 3)])),
 (query [("o", "owners"), ("a", "accounts")]
  [(intEq (snd_ (var "o")) (fst_ (var "a")))]
  [(fst_ (var "o")), (snd_ (var "a"))]),
 (reduce (var "plus") (int 0)
  (map_ (var "fst") (query [("a", "accounts")] [] [(snd_ (var "a")), (fst_ (var "a"))])))
    ]

-- Type inference tests.
------------------------

inferenceActual :: [String]
inferenceActual = map (either id showType . typecheck) astTests

inferenceExpected :: [String]
inferenceExpected =
    [
     "int",
     "x_0 -> x_0",
     "int -> int",
     "Unsolvable constraints",
     "int -> int -> int",
     "x_0 -> string",
     "x_0 -> x_1 -> string",
     "x_0 -> x_1 -> x_2 -> x_3 -> int",
     "string -> string",
     "Conflicting definitions in let-expression!",
     "(string, string)",
     "(string, int)",
     "Unsolvable constraints",
     "Unsolvable constraints",
     "int",
     "string",
     "(string, bool)",
     "(int, bool)",
     "(int, int)",
     "Unknown variable 'x'!",
     "(string, bool)",
     "(int, string)",
     "(x_0 -> x_0, string)",
     "[int]",
     "Unsolvable constraints",
     "string",
     "int",
     "int",
     "int",
     "bool",
     "[int]",
     "[string]",
     "int",
     "int",
     "int",
     "bool",
     "bool",
     "bool",
     "a -> a",
     "[int]",
     "string",
     "Unsolvable constraints",
     "Unsolvable constraints",
     "bool",
     "[int]",
     "Unsolvable constraints",
     "[(string, int)]",
     "int"
    ]

inferenceTests :: [Test]
inferenceTests = makeListOfTests inferenceActual inferenceExpected

-- Evaluator tests.
-------------------

evaluationActual :: [String]
evaluationActual = map (either id showValue . interpret) astTests

evaluationExpected :: [String]
evaluationExpected =
    [
     "1",
     "(\\x -> AVar \"x\")",
     "(\\x -> AApp (AApp (ABuiltin \"plus\") (AVar \"x\")) (AVar \"x\"))",
     "The value is not an integer!",
     "(\\y -> AAbs (AVar \"x\") (AApp (AApp (ABuiltin \"plus\") (AVar \"y\")) (AVar \"x\")))",
     "(\\x -> AStr \"abc\")",
     "(\\y -> AAbs (AVar \"x\") (AStr \"abc\"))",
     "(\\a -> AAbs (AVar \"z\") (AAbs (AVar \"y\") (AAbs (AVar \"x\") (AInt 42))))",
     "(\\x -> AApp (AApp (ABuiltin \"concatStr\") (AVar \"x\")) (AVar \"x\"))",
     "Conflicting definitions in let-expression!",
     "(\"abc\", \"abc\")",
     "(\"abc\", 1)",
     "Can't perform application!",
     "The tuple must have 2 elements!",
     "1",
     "\"2\"",
     "(\"8\", True)",
     "(1, True)",
     "(3, 1)",
     "Variable 'x' not found in the environment!",
     "(\"aaa\", True)",
     "(6, \"abc\")",
     "((\\x -> AVar \"x\"), \"abc\")",
     "[1, 2, 3]",
     "Heterogeneous lists are not allowed!",
     "\"answer: 42\"",
     "1",
     "3",
     "23",
     "False",
     "[65, 66]",
     "[\"abc\", \"abc\"]",
     "6",
     "999",
     "3",
     "True",
     "True",
     "True",
     "(built-in function \"id\")",
     "[1, 2, 3]",
     "\"abc\"",
     "The value is not a boolean!",
     "1",
     "False",
     "[1, 2, 3]",
     "The value is not a list!",
     "[(\"name1\", 23), (\"name2\", 56), (\"name3\", 100)]",
     "179"
    ]

evaluationTests :: [Test]
evaluationTests = makeListOfTests evaluationActual evaluationExpected

-- Entry point.
---------------

main :: IO ()
main = runTestTT allTests >> return ()
    where
      allTests = TestList (constraintsTests ++
                           inferenceTests ++ evaluationTests)
