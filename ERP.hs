module ERP
   where

import Control.Monad.Error
import Data.Maybe
import Data.Map as M

-- Parser.
----------
data AST = ABool Bool | AInt Integer | AStr String
         | AVar String | AAbs AST AST | AApp AST AST
         | APlus AST AST
           deriving (Eq, Show)

type ParseResult = Either String AST

parse :: String -> ParseResult
parse = undefined

-- Typechecker.
---------------
-- Types.
-- TODO: tuples, sets
data SimpleType = STBool | STInt | STStr
                | STFun SimpleType SimpleType | STBase String
                  deriving (Eq, Show)

data TypeScheme = TSVar SimpleType | TSForAll String TypeScheme
                  deriving (Eq, Show)

data Type = TSimple SimpleType | TScheme TypeScheme
            deriving (Eq, Show)

showSimpleType :: SimpleType -> String
showSimpleType STBool = "bool"
showSimpleType STInt = "int"
showSimpleType STStr = "string"
showSimpleType (STFun a b) = showSimpleType a ++ " -> " ++ showSimpleType b
showSimpleType (STBase s) = s

showTypeScheme :: TypeScheme -> String
showTypeScheme (TSVar st) = showSimpleType st
showTypeScheme (TSForAll s ts) = "A" ++ s ++ "." ++ showTypeScheme ts

showType :: Type -> String
showType (TSimple st) = showSimpleType st
showType (TScheme ts) = showTypeScheme ts

-- Internals.
type Constraint = (Type, Type)

type ConstraintSet = [Constraint]

type TypingContext = M.Map String SimpleType

emptyTypingContext :: TypingContext
emptyTypingContext = M.empty

type Sym = String
type SymGen = () -> NextSym
data NextSym = NextSym (Sym, SymGen)

gensym :: SymGen
gensym = let f x u = NextSym ("x_" ++ show x, f (x+1))
         in f 0

typecheck' :: AST -> TypingContext -> TypecheckResult
typecheck' (ABool _) _      = Right (TSimple STBool)
typecheck' (AInt _) _       = Right (TSimple STInt)
typecheck' (AStr _) _       = Right (TSimple STStr)
typecheck' (AVar n) ctx     =
    case M.lookup n ctx of
      Just t -> Right (TSimple t)
      Nothing -> Left ("Unknown variable '" ++ n ++ "'!")

typecheck' (AAbs (AVar v) b) ctx   = case typecheck' b (M.insert v (STBase "x") ctx)
                                     of Right (TSimple t) -> Right (TSimple (STFun (STBase "x") t))
                                        l -> l
typecheck' (AApp e1 e2) ctx = undefined
typecheck' _ _ = Left "Can't typecheck!"

-- Client interface.
type TypecheckResult = Either String Type

typecheck :: AST -> TypecheckResult
typecheck ast = typecheck' ast emptyTypingContext

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

toVInt (VInt i) = Right i
toVInt _        = Left "The value is not an integer!"

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
interpret' (APlus e1 e2) env =
    do i1 <- toVInt =<< interpret' e1 env
       i2 <- toVInt =<< interpret' e2 env
       return (VInt (i1 + i2))
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

plus :: AST -> AST -> AST
plus e1 e2 = APlus e1 e2
