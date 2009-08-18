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
      allTests = [constraints0, constraints1, constraints2, constraints3,
                  constraints4, constraints5, constraints6, constraints7]

      constraints0 = [(STBase "X", STInt),
                      (STBase "Y", STFun (STBase "X") (STBase "X"))]
      constraints1 = [(STFun STInt STInt,
                       STFun (STBase "X") (STBase "Y"))]
      constraints2 = [(STInt, STFun (STInt) (STBase "Y"))]
      constraints3 = [(STBase "Y", STFun STInt (STBase "Y"))]
      constraints4 = []
      constraints5 = [(STFun (STBase "x_0") (STBase "x_0"),
                       STFun (STBase "x_1") STInt)]
      constraints6 = [(STFun (STBase "x_0") (STBase "x_0"),
                       STFun STInt (STBase "x_1"))]
      constraints7 = [(STStr,STInt),(STInt,STInt)]

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

-- Type inference tests.
------------------------

inferenceActual :: [String]
inferenceActual = map (either id showType . typecheck) allTests
    where
      allTests = [
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
       (lambda (var "x") (append (var "x") (var "x"))),
       (let_ [("f", (int 1)), ("f", (int 2))]
        (plus (var "f") (var "f"))),
       (let_ [("f", (lambda (var "x") (var "x")))]
        (tuple [(app (var "f") (str "abc")),
                (app (var "f") (str "abc"))])),
       (let_ [("f", (lambda (var "x") (var "x")))]
        (tuple [(app (var "f") (str "abc")),
                (app (var "f") (int 1))])),
       (builtin "plus" [(int 1), (int 2), (int 3)]),
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
       (tuple [(myLength (list [(int 1), (int 2), (int 3)])),
               (myLength (list [(str "abc")]))]),
       (mySnd (tuple [(var "x"), (int 1)])),
       (let_ [("t", (tuple [(bool True), (str "aaa")]))]
        (tuple [(mySnd (var "t")), (myFst (var "t"))]))
        ]

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
     "(string, bool)"
    ]

inferenceTests :: [Test]
inferenceTests = makeListOfTests inferenceActual inferenceExpected

-- Evaluator tests.
-------------------

evaluationActual :: [String]
evaluationActual = map (either id showValue . interpret) allTests
    where
      allTests = [
       (tuple [(int 6), (str "abc")]),
       (tuple [(lambda (var "x") (var "x")), (str "abc")]),
       (list [(int 1), (int 2), (int 3)]),
       (list [(int 1), (int 2), (str "abc")]),
       (append (str "answer: ")
        (intToString (plus (int 35) (int 7)))),
       (let_ [("f", (lambda (var "x") (var "x")))]
                 (app (var "f") (int 1))),
       (builtin "plus" [(int 1), (int 2)]),
       (tuple [(myLength (list [(int 1), (int 2), (int 3)])),
               (myLength (list [(str "abc")]))]),
       (let_ [("t", (tuple [(bool True), (str "aaa")]))]
        (tuple [(mySnd (var "t")), (myFst (var "t"))]))
        ]


evaluationExpected :: [String]
evaluationExpected =
    [
     "(6, \"abc\")",
     "((\\x -> AVar \"x\"), \"abc\")",
     "[1, 2, 3]",
     "Heterogeneous lists are not allowed!",
     "\"answer: 42\"",
     "1",
     "3",
     "(3, 1)",
     "(\"aaa\", True)"
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
