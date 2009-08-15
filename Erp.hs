module Erp
   where

import Data.Maybe
import Data.Map as M

-- Parser.
----------
data AST = ABool Bool | AInt Integer | AStr String
         | AVar String | AAbs AST AST | AApp AST AST
           deriving (Eq, Show)

type ParseResult = Either String AST

parse :: String -> ParseResult
parse = undefined

-- Typechecker.
---------------
-- TODO: tuples, sets
data SimpleType = STBool | STInt | STString | STFun SimpleType SimpleType | STBase String
                  deriving (Eq, Show)

data TypeScheme = TSVar SimpleType | TSForAll String TypeScheme

data Type = TSimple SimpleType | TScheme TypeScheme

type TypecheckResult = Either String Type

typecheck :: AST -> TypecheckResult
typecheck = undefined

-- Interpreter.
---------------
data Value = VBool Bool | VInt Integer | VStr String | VAbs String AST
             deriving (Eq, Show)

type Environment = M.Map String Value
type EvalResult  = Either String Value

interpret :: AST -> EvalResult
interpret e = interpret' e emptyEnvironment

emptyEnvironment :: Environment
emptyEnvironment = M.empty

interpret' :: AST -> Environment -> EvalResult
interpret' (ABool b) _  = Right (VBool b)
interpret' (AStr s) _   = Right (VStr s)
interpret' (AInt i) _   = Right (VInt i)
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

bool :: Bool -> AST
bool b = ABool b

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
