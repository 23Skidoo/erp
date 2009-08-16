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
