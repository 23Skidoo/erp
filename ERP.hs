module ERP
   where

import Control.Arrow ((***))
import Control.Monad.Error
import Data.List (foldl')
import Data.Maybe
import qualified Data.Map as M

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
data SimpleType = STBool | STInt | STStr
                | STFun SimpleType SimpleType | STBase String
                  deriving (Eq, Show)

data TypeScheme = TSVar SimpleType | TSForAll String TypeScheme
                  deriving (Eq, Show)

data Type = TSimple SimpleType | TScheme TypeScheme
            deriving (Eq, Show)

-- Type pretty-printing.
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

-- Unification.
type Constraint = (SimpleType, SimpleType)

type ConstraintSet = [Constraint]

type Substitution = ConstraintSet

mergeSubstitutions :: Substitution -> Substitution -> Substitution
mergeSubstitutions s1 s2 = s1 ++ s2

substituteTypeVariableWithType :: (SimpleType -> SimpleType
                                   -> SimpleType -> SimpleType)
substituteTypeVariableWithType (STBase n) nt old = doSubstitute old
    where
      doSubstitute (STBase s) | (s == n) = nt
      doSubstitute (STFun ta tb) = (STFun (doSubstitute ta) (doSubstitute tb))
      doSubstitute x = x
substituteTypeVariableWithType _ _ _ =
    error ("The first argument to " ++
              "'substituteVariableWithType' should be a type variable!")

applySubstitution :: Substitution -> SimpleType -> SimpleType
applySubstitution ss t = foldl' (\ot (v, nt) ->
                                     substituteTypeVariableWithType v nt ot)
                         t (reverse ss)

substituteInConstraintSet :: (SimpleType -> SimpleType ->
                              ConstraintSet -> ConstraintSet)
substituteInConstraintSet tv nt = map (\c -> subst' c)
    where
      subst'' = substituteTypeVariableWithType tv nt
      subst' = subst'' *** subst''

occursIn :: SimpleType -> SimpleType -> Bool
occursIn (STBase n) tT = o tT
    where
      o (STBase n1) = n1 == n
      o (STFun a b) = o a || o b
      o _ = False
occursIn _ _ = error "The first argument to occursIn should be a type variable!"

notOccursIn :: SimpleType -> SimpleType -> Bool
notOccursIn x t = not . occursIn x $ t

recUnify:: SimpleType -> SimpleType -> ConstraintSet -> ConstraintSet
recUnify s t = unify . substituteInConstraintSet s t

unify :: ConstraintSet -> Substitution
unify [] = []
unify ((s,t):cs) | s == t = unify cs

unify ((s@(STBase _), t):cs) | s `notOccursIn` t = ncs
                             where
                               ncs' = recUnify s t cs
                               ncs  = ncs' ++ [(s, t)]

unify ((s, t@(STBase _)):cs) | t `notOccursIn` s = ncs
                             where
                               ncs' = recUnify t s cs
                               ncs  = ncs' ++ [(t, s)]

unify ((STFun s1 s2, STFun t1 t2):cs) = unify ncs
    where
      ncs = cs ++ [(s1, t1), (s2, t2)]

unify ((_, _):_) = error "Unsolvable constraints"


-- Typing context.
type TypingContext = M.Map String SimpleType

emptyTypingContext :: TypingContext
emptyTypingContext = M.empty

lookupCtx :: String -> TypingContext -> Maybe SimpleType
lookupCtx n ctx = M.lookup n ctx

insertCtx :: String -> SimpleType -> TypingContext -> TypingContext
insertCtx k v ctx = M.insert k v ctx

-- Symbol generator.
type Sym = String
type SymGen = () -> NextSym
data NextSym = NextSym (Sym, SymGen)

symgen :: SymGen
symgen = let f x () = NextSym ("x_" ++ show x, f (x+1))
         in f 0

-- Typing info : gensym + constraint set.
data TypingInfo = TypingInfo {
      gens:: SymGen, constrs:: ConstraintSet }

emptyTypingInfo :: TypingInfo
emptyTypingInfo = TypingInfo { gens = symgen, constrs = []}

-- Helper functions for working with TypingInfo.
gensym :: TypingInfo -> (Sym, TypingInfo)
gensym ti = let NextSym (sym, ngens) = gens ti ()
            in (sym, ti { gens = ngens })

insertConstr :: Constraint -> TypingInfo -> TypingInfo
insertConstr c ti = let oldconstrs = constrs ti
                    in ti { constrs = (c:oldconstrs) }

insertConstrs :: [Constraint] -> TypingInfo -> TypingInfo
insertConstrs cs ti = let oldconstrs = constrs ti
                      in ti { constrs = (cs ++ oldconstrs) }

type TypecheckResult = Either String (Type, TypingInfo)

simpleType :: (SimpleType, TypingInfo) -> Either a (Type, TypingInfo)
simpleType (t, ti) = Right (TSimple t, ti)

typecheck' :: AST -> TypingInfo -> TypingContext -> TypecheckResult
typecheck' (ABool _) ti _ = simpleType (STBool , ti)
typecheck' (AInt  _) ti _ = simpleType (STInt  , ti)
typecheck' (AStr  _) ti _ = simpleType (STStr  , ti)

typecheck' (AVar n) ti ctx =
    case lookupCtx n ctx of
      Just t -> Right ((TSimple t), ti)
      Nothing -> Left ("Unknown variable '" ++ n ++ "'!")

typecheck' (AAbs (AVar v) b) ti ctx =
    case typecheck' b nti (insertCtx v varType ctx)
    of Right ((TSimple t), nti2) -> Right (TSimple funType, nti2)
           where
             funType = (STFun varType t)
             --newFunType = applySubstitution (constrs nti2) funType
       l -> l
    where
      (sym, nti) = gensym ti
      varType = STBase sym

typecheck' (APlus e1 e2) ti ctx =
    do (t1, ti1) <- getSimpleType e1 ti ctx
       (t2, ti2) <- getSimpleType e2 ti1 ctx
       let newti = insertConstrs [(t1, STInt),
                                  (t2, STInt)] ti2
       return (TSimple STInt, newti)
    where
      getSimpleType e ti' ctx' = typecheck' e ti' ctx' >>= getSimpleType'

      getSimpleType' (TSimple t, ti') = return (t, ti')
      getSimpleType' _ = fail "One of plus's operands is not a simple type"

typecheck' (AApp _ _) _ _  = undefined
typecheck' _ _ _           = Left "Can't typecheck!"

-- Client interface.

typecheck :: AST -> String
typecheck ast =
    case typecheck' ast emptyTypingInfo emptyTypingContext
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
