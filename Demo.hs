module Demo
    where

import ERP

simpleApp :: AST
simpleApp = (app (lambda (var "x") (var "x")) (int 2))

simpleStuck :: AST
simpleStuck = (var "x")
