module Test
    where

import ERP

-- Constraint solver tests.
---------------------------

-- Y = int -> int ; X = int.
testConstraints1 :: ConstraintSet
testConstraints1 = [(STBase "X", STInt),
                    (STBase "Y", STFun (STBase "X") (STBase "X"))]

-- Y = int; X = int.
testConstraints2 :: ConstraintSet
testConstraints2 = [(STFun STInt STInt,
                     STFun (STBase "X") (STBase "Y"))]

-- xfail
testConstraints3 :: ConstraintSet
testConstraints3 = [(STInt, STFun (STInt) (STBase "Y"))]

-- xfail
testConstraints4 :: ConstraintSet
testConstraints4 = [(STBase "Y", STFun STInt (STBase "Y"))]

-- [].
testConstraints5 :: ConstraintSet
testConstraints5 = []

-- x_1 -> int; x_0 -> x_1.
testConstraints6 :: ConstraintSet
testConstraints6 = [(STFun (STBase "x_0") (STBase "x_0"),
                     STFun (STBase "x_1") STInt)]

-- x_1 -> int; x_0 -> int.
testConstraints7 :: ConstraintSet
testConstraints7 = [(STFun (STBase "x_0") (STBase "x_0"),
                     STFun STInt (STBase "x_1"))]

-- xfail.
testConstraints8 :: ConstraintSet
testConstraints8 = [(STStr,STInt),(STInt,STInt)]

-- Type inference tests.
------------------------

-- int.
testInference1 :: AST
testInference1 = (app (lambda (var "x") (var "x")) (int 1))

-- x -> x.
testInference2 :: AST
testInference2 = (lambda (var "x") (var "x"))

-- int -> int.
testInference3 :: AST
testInference3 = (lambda (var "x") (plus (var "x") (var "x")))

-- xfail.
testInference4 :: AST
testInference4 = (plus (str "abc") (int 2))

-- int -> int -> int.
testInference5 :: AST
testInference5 = (lambda (var "y") (lambda (var "x") (plus (var "y") (var "x"))))

-- x -> string.
testInference6 :: AST
testInference6 = (lambda (var "x") (str "abc"))

-- x -> y -> string.
testInference7 :: AST
testInference7 = (lambda (var "y") (lambda (var "x") (str "abc")))

-- x -> y -> z -> a -> int.
testInference8 :: AST
testInference8 =  (lambda (var "a")  (lambda (var "z")
                                     (lambda (var "y") (lambda (var "x") (int 42)))))

-- string -> string.
testInference9 :: AST
testInference9 = (lambda (var "x") (append (var "x") (var "x")))

-- Evaluator tests.
-------------------

-- (6, "abc").
testEvaluation1 :: AST
testEvaluation1 = (tuple [(int 6), (str "abc")])

-- xfail.
testEvaluation2 :: AST
testEvaluation2 = (tuple [(lambda (var "x") (var "x")), (str "abc")])

-- {1, 2, 3}.
testEvaluation3 :: AST
testEvaluation3 = (list [(int 1), (int 2), (int 3)])

-- xfail.
testEvaluation4 :: AST
testEvaluation4 = (list [(int 1), (int 2), (str "abc")])

-- "answer: 42".
testEvaluation5 :: AST
testEvaluation5 = (append (str "answer: ")
                   (intToString (plus (int 35) (int 7))))
