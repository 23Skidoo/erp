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
      allTests = [inference0, inference1, inference2, inference3,
                  inference4, inference5, inference6, inference7,
                  inference8, inference9, inference10, inference11,
                  inference12
                 ]

      inference0 = (app (lambda (var "x") (var "x")) (int 1))
      inference1 = (lambda (var "x") (var "x"))
      inference2 = (lambda (var "x") (plus (var "x") (var "x")))
      inference3 = (plus (str "abc") (int 2))
      inference4 = (lambda (var "y")
                    (lambda (var "x") (plus (var "y") (var "x"))))
      inference5 = (lambda (var "x") (str "abc"))
      inference6 = (lambda (var "y") (lambda (var "x") (str "abc")))
      inference7 =  (lambda (var "a")
                     (lambda (var "z")
                      (lambda (var "y") (lambda (var "x") (int 42)))))
      inference8 = (lambda (var "x") (append (var "x") (var "x")))
      inference9 = (let_ [("f", (int 1)), ("f", (int 2))]
                             (plus (var "f") (var "f")))
      inference10 = (let_ [("f", (lambda (var "x") (var "x")))]
                     (tuple [(app (var "f") (str "abc")),
                             (app (var "f") (str "abc"))]))
      inference11 = (let_ [("f", (lambda (var "x") (var "x")))]
                            (tuple [(app (var "f") (str "abc")),
                                    (app (var "f") (int 1))]))
      inference12 = (builtin "plus" [(int 1), (int 2), (int 3)])

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

     -- TOFIX: this must be (string, int) after let-polymorphism lands.
     "Unsolvable constraints",
     "Unsolvable constraints"
    ]

inferenceTests :: [Test]
inferenceTests = makeListOfTests inferenceActual inferenceExpected

-- Evaluator tests.
-------------------

evaluationActual :: [String]
evaluationActual = map (either id showValue . evaluate) allTests
    where
      allTests = [eval1, eval2, eval3, eval4, eval5, eval6, eval7]

      eval1 = (tuple [(int 6), (str "abc")])
      eval2 = (tuple [(lambda (var "x") (var "x")), (str "abc")])
      eval3 = (list [(int 1), (int 2), (int 3)])
      eval4 = (list [(int 1), (int 2), (str "abc")])
      eval5 = (append (str "answer: ")
               (intToString (plus (int 35) (int 7))))
      eval6 = (let_ [("f", (lambda (var "x") (var "x")))]
                        (app (var "f") (int 1)))
      eval7 = (builtin "plus" [(int 1), (int 2)])

evaluationExpected :: [String]
evaluationExpected =
    [
     "(6, \"abc\")",
     "((\\x -> AVar \"x\"), \"abc\")",
     "[1, 2, 3]",
     "Heterogeneous lists are not allowed!",
     "\"answer: 42\"",
     "1",
     "3"
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
