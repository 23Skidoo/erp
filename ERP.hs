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

symgen :: SymGen
symgen = let f x () = NextSym ("x_" ++ show x, f (x+1))
         in f 0

data TypingInfo = TypingInfo {
      ctx:: TypingContext,
      gens:: SymGen, constrs:: ConstraintSet }

emptyTypingInfo :: TypingInfo
emptyTypingInfo = TypingInfo { ctx = emptyTypingContext,
                               gens = symgen, constrs = []}

gensym :: TypingInfo -> (Sym, TypingInfo)
gensym ti = let NextSym (sym, ngens) = gens ti ()
            in (sym, ti { gens = ngens })

lookupCtx :: String -> TypingInfo -> Maybe SimpleType
lookupCtx n ti = M.lookup n (ctx ti)

insertCtx :: String -> SimpleType -> TypingInfo -> TypingInfo
insertCtx k v ti = ti { ctx = M.insert k v (ctx ti) }

insertConstr :: Constraint -> TypingInfo -> TypingInfo
insertConstr c ti = let oldconstrs = constrs ti
                    in ti { constrs = (c:oldconstrs) }

insertConstrs :: [Constraint] -> TypingInfo -> TypingInfo
insertConstrs cs ti = let oldconstrs = constrs ti
                      in ti { constrs = (cs ++ oldconstrs) }

simpleType :: (SimpleType, TypingInfo) -> Either a (Type, TypingInfo)
simpleType (t, ti) = Right (TSimple t, ti)

type TypecheckResult = Either String (Type, TypingInfo)

typecheck' :: AST -> TypingInfo -> TypecheckResult
typecheck' (ABool _) ti = simpleType (STBool , ti)
typecheck' (AInt  _) ti = simpleType (STInt  , ti)
typecheck' (AStr  _) ti = simpleType (STStr  , ti)
typecheck' (AVar n) ti =
    case lookupCtx n ti of
      Just t -> Right ((TSimple t), ti)
      Nothing -> Left ("Unknown variable '" ++ n ++ "'!")

typecheck' (AAbs (AVar v) b) ti =
    case typecheck' b (insertCtx v (STBase sym) nti)
    of Right ((TSimple t), _) -> Right (TSimple (STFun (STBase sym) t), nti)
       l -> l
    where
      (sym, nti) = gensym ti

typecheck' (APlus e1 e2) ti =
    do (t1, _) <- typecheck' e1 ti
       (t2, _) <- typecheck' e2 ti
       let newti = insertConstrs [(t1, TSimple STInt),
                                  (t2, TSimple STInt)] ti
       return (TSimple STInt, newti)
typecheck' (AApp _ _) _  = undefined
typecheck' _ _           = Left "Can't typecheck!"

-- Client interface.

typecheck :: AST -> String
typecheck ast = case typecheck' ast emptyTypingInfo
                of Left l -> error l
                   Right (t, _) -> showType t

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

fromVInt :: Value -> Either String Integer
fromVInt (VInt i) = Right i
fromVInt _        = Left "The value is not an integer!"

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
    do i1 <- getInt e1
       i2 <- getInt e2
       return (VInt (i1 + i2))
    where
      getInt e = fromVInt =<< interpret' e env
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
