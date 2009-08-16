module Test
    where

import ERP

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
