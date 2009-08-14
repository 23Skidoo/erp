module Erp
   where

import Data.Maybe
import Data.Map as M

-- Parser.
----------
data AST = AStr String | AInt Integer | AVar String | AAbs AST AST | AApp AST AST
           deriving (Eq, Show)

type ParseResult = Either String AST

parse :: String -> ParseResult
parse = undefined

-- Typechecker.
---------------
data Type = TString | TInt | TFun Type Type
            deriving (Eq, Show)

type TypecheckResult = Either String Type

typecheck :: AST -> Either String Type
typecheck = undefined

-- Interpreter.
---------------
data Value = VStr String | VInt Integer | VAbs String AST
             deriving (Eq, Show)

type Environment = M.Map String Value
type EvalResult  = Either String Value

interpret :: AST -> EvalResult
interpret e = interpret' e emptyEnvironment

emptyEnvironment :: Environment
emptyEnvironment = M.empty

-- (lambda (var "x") (var "x")) (int 2)
interpret' :: AST -> Environment -> EvalResult
interpret' (AStr s) _ = Right (VStr s)
interpret' (AInt i) _ = Right (VInt i)
interpret' (AVar n) env =
    case M.lookup n env
    of Just v  -> Right v
       Nothing -> Left ("Variable '"
                        ++ n ++
                        "' not found in the environment!")
interpret' (AAbs v b) _ =
    case v of
      AVar x -> Right (VAbs x b)
      _      -> Left "Unknown value in the abstraction parameter list!"
interpret' (AApp f e) env =
    case interpret' f env of
      Right (VAbs v b) ->
          case interpret' e env of
            Right arg  -> interpret' b (M.insert v arg env)
            l@(Left _) -> l
      l@(Left _)       -> l
      _                -> Left "Can't perform application!"


-- "Syntax sugar".

str :: String -> AST
str s = AStr s

int :: Integer -> AST
int i = AInt i

var :: String -> AST
var n = AVar n

lambda :: AST -> AST -> AST
lambda v a = AAbs v a

app :: AST -> AST -> AST
app f e = AApp f e
