module Demo
    where

import ERP

-- Interpreter.
simpleApp :: AST
simpleApp = (app (lambda (var "x") (var "x")) (int 2))

simpleStuck :: AST
simpleStuck = (var "x")

-- Typechecker.

simpleType1 :: AST
simpleType1 = (concatStr (str "answer: ") (intToStr (plus (int 35) (int 7))))

simpleType2 :: AST
simpleType2 = (map_ (app (var "plus") (int 64)) (list [(int 1), (int 2)]))

-- Queries.
simpleQuery :: AST
simpleQuery =  (query [("o", "owners"), ("a", "accounts")]
                [(intEq (snd_ (var "o")) (fst_ (var "a")))]
                [(fst_ (var "o")), (snd_ (var "a"))])

simpleReduce :: AST
simpleReduce =  (reduce (var "plus") (int 0)
                 (query [("a", "accounts")] [] [(snd_ (var "a"))]))
