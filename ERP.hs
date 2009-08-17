module ERP
   where

import Control.Arrow ((***))
import Control.Monad.Error
import Data.List (foldl', intersperse)
import Data.Maybe
import qualified Data.Map as M

-- Parser.
----------
data AST = ABool Bool | AInt Integer | AStr String
         | AVar String | AAbs AST AST | AApp AST AST
         | ATuple [AST] | AList [AST]
         | APlus AST AST | AAppend AST AST | AIntToString AST
           deriving (Eq, Show, Ord)

type ParseResult = Either String AST

parse :: String -> ParseResult
parse = undefined

-- Typechecker.
---------------
-- Types.
data SimpleType = STBool | STInt | STStr
                | STList SimpleType | STTuple [SimpleType]
                | STFun SimpleType SimpleType | STBase String
                  deriving (Eq, Show)

data TypeScheme = TSVar SimpleType | TSForAll String TypeScheme
                  deriving (Eq, Show)

data Type = TSimple SimpleType | TScheme TypeScheme
            deriving (Eq, Show)

-- Type pretty-printing.
showSimpleType :: SimpleType -> String
showSimpleType STBool        = "bool"
showSimpleType STInt         = "int"
showSimpleType STStr         = "string"
showSimpleType (STList st)   = "[" ++ (showSimpleType st) ++ "]"
showSimpleType (STTuple sts) = ("(" ++ (concat . intersperse ", "
                                        . map showSimpleType $ sts) ++ ")")
showSimpleType (STFun a b)   = showSimpleType a ++ " -> " ++ showSimpleType b
showSimpleType (STBase s)    = s

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
    error ("The first argument to 'substituteVariableWithType' " ++
           "should be a type variable!")

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
occursIn _ _ = error ("The first argument to 'occursIn' " ++
                      "should be a type variable!")

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

unify ((STList s1, STList s2):cs) = unify ncs
    where
      ncs = cs ++ [(s1, s2)]

unify ((STTuple els1, STTuple els2):cs) = unify ncs
    where
      ncs = cs ++ (zipWith (,) els1 els2)

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

unifyConstrs :: TypingInfo -> TypingInfo
unifyConstrs ti = ti { constrs = unifiedConstrs }
    where
      unifiedConstrs = unify . constrs $ ti

inferType :: TypingInfo -> SimpleType -> Type
inferType ti t = TSimple (applySubstitution (constrs ti) t)

type TypecheckResult = Either String (Type, TypingInfo)
type SimpleTypecheckResult = Either String (SimpleType, TypingInfo)

simpleType :: (SimpleType, TypingInfo) -> Either a (Type, TypingInfo)
simpleType (t, ti) = Right (TSimple t, ti)

getSimpleType :: AST -> TypingInfo -> TypingContext -> SimpleTypecheckResult
getSimpleType e ti ctx = do (t, nti) <- typecheck' e ti ctx
                            st <- extractSimpleType t
                            return (st, nti)

extractSimpleType :: (Monad m) => Type -> m SimpleType
extractSimpleType (TSimple t) = return t
extractSimpleType _           = fail "One of plus's operands is not a simple type"

type SimpleTypecheckListResult = Either String ([SimpleType], TypingInfo)

getSimpleTypes :: [AST] -> TypingInfo ->
                  TypingContext -> SimpleTypecheckListResult
getSimpleTypes [] ti _ = Right ([], ti)
getSimpleTypes (x:xs) ti ctx =
    do (t1, nti) <- getSimpleType x ti ctx
       (ts, nti2) <- getSimpleTypes xs nti ctx
       return (t1:ts, nti2)

newTypeVariable :: TypingInfo -> (SimpleType, TypingInfo)
newTypeVariable ti = (STBase sym, nti)
    where
      (sym, nti) = gensym ti

typecheck' :: AST -> TypingInfo -> TypingContext -> TypecheckResult
typecheck' (ABool _) ti _ = simpleType (STBool , ti)
typecheck' (AInt  _) ti _ = simpleType (STInt  , ti)
typecheck' (AStr  _) ti _ = simpleType (STStr  , ti)

typecheck' (AList [])  ti _ = simpleType (STList newVar, nti)
    where
      (newVar, nti) = newTypeVariable ti

typecheck' (AList els) ti ctx =
    do (simpleEls, nti) <- getSimpleTypes els ti ctx
       let (newVar, nti2) = newTypeVariable nti
       let listConstrs = zipWith (,) (newVar:simpleEls) simpleEls
       let nti3 = insertConstrs listConstrs nti2
       let nti4 = unifyConstrs nti3
       elType <- extractSimpleType . inferType nti4 $ newVar
       simpleType (STList elType , nti4)

typecheck' (ATuple []) ti _ = simpleType (STTuple [newVar], nti)
    where
      (newVar, nti) = newTypeVariable ti

typecheck' (ATuple els) ti ctx =
    do (simpleEls, nti) <- getSimpleTypes els ti ctx
       simpleType (STTuple simpleEls, nti)

typecheck' (AVar n) ti ctx =
    case lookupCtx n ctx of
      Just t -> Right ((TSimple t), ti)
      Nothing -> Left ("Unknown variable '" ++ n ++ "'!")

typecheck' (AAbs (AVar v) b) ti ctx =
    case typecheck' b nti (insertCtx v varType ctx)
    of Right ((TSimple t), nti2) -> Right (newFunType, nti3)
           where
             funType = (STFun varType t)
             nti3 = unifyConstrs nti2
             newFunType = inferType nti3 funType
       l -> l
    where
      (varType, nti) = newTypeVariable ti

typecheck' (APlus e1 e2) ti ctx =
    do (t1, ti1) <- getSimpleType e1 ti ctx
       (t2, ti2) <- getSimpleType e2 ti1 ctx
       let newti = insertConstrs [(t1, STInt),
                                  (t2, STInt)] ti2
       let newti2 = unifyConstrs newti
       return ((TSimple STInt), newti2)

typecheck' (AAppend e1 e2) ti ctx =
    do (t1, ti1) <- getSimpleType e1 ti ctx
       (t2, ti2) <- getSimpleType e2 ti1 ctx
       let newti = insertConstrs [(t1, STStr),
                                  (t2, STStr)] ti2
       let newti2 = unifyConstrs newti
       return ((TSimple STStr), newti2)

typecheck' (AIntToString e1) ti ctx =
    do (t1, ti1) <- getSimpleType e1 ti ctx
       let newti = insertConstrs [(t1, STInt)] ti1
       let newti2 = unifyConstrs newti
       return ((TSimple STStr), newti2)

typecheck' (AApp f a) ti ctx  =
    do (tf, ti1) <- getSimpleType f ti ctx
       (ta, ti2) <- getSimpleType a ti1 ctx
       let (retType, ti3) = newTypeVariable ti2
       let newConstr = (tf, STFun ta retType)
       let ti4 = insertConstr newConstr ti3
       let ti5 = unifyConstrs ti4
       return (inferType ti5 retType, ti5)
typecheck' _ _ _           = Left "Can't typecheck!"

-- Client interface.

typecheck :: AST -> String
typecheck ast =
    case typecheck' ast emptyTypingInfo emptyTypingContext
    of Left l -> error l
       -- Laziness can be so much fun sometimes...
       Right (t, ti) -> constrs ti `seq` showType t

-- Interpreter.
---------------
data Value = VBool Bool | VInt Integer | VStr String | VAbs String AST
           | VList [Value] | VTuple [Value]
             deriving (Eq, Show, Ord)

-- Are runtime 'types' of these values equal?
isEqualV :: Value -> Value -> Bool
isEqualV (VBool _) (VBool _)         = True
isEqualV (VInt _) (VInt _)           = True
isEqualV (VStr _) (VStr _)           = True
isEqualV (VTuple els1) (VTuple els2) = and . zipWith isEqualV els1 $ els2
isEqualV (VList l1) (VList l2)       = sameType l1 && sameType l2
    where
      headType = head l1
      sameType = and . map (isEqualV headType)

-- We assume that the typecheck worked here.
isEqualV (VAbs _ _) (VAbs _ _)       = True
isEqualV _ _                         = False

type Environment = M.Map String Value
type EvalResult  = Either String Value

emptyEnvironment :: Environment
emptyEnvironment = M.empty

fromVInt :: Value -> Either String Integer
fromVInt (VInt i) = Right i
fromVInt _        = Left "The value is not an integer!"

fromVStr :: Value -> Either String String
fromVStr (VStr i) = Right i
fromVStr _        = Left "The value is not an string!"

interpret' :: Environment -> AST -> EvalResult
interpret' _ (ABool b)  = Right (VBool b)
interpret' _ (AStr s)   = Right (VStr s)
interpret' _ (AInt i)   = Right (VInt i)
interpret' env (AVar n) =
    case M.lookup n env
    of Just v  -> Right v
       Nothing -> Left ("Variable '"
                        ++ n ++
                        "' not found in the environment!")
interpret' env (AList els) =
    do { values <- sequence . map (interpret' env) $ els;
         let valList = VList values
         in if isEqualV valList valList
            then return valList
            else fail ("Heterogeneous lists are not allowed!") }

interpret' env (ATuple els) = do values <- sequence . map (interpret' env) $ els;
                                 return . VTuple $ values

interpret' env (APlus e1 e2) =
    do i1 <- getInt e1
       i2 <- getInt e2
       return (VInt (i1 + i2))
    where
      getInt e = fromVInt =<< interpret' env e

interpret' env (AAppend e1 e2) =
    do s1 <- getStr e1
       s2 <- getStr e2
       return (VStr (s1 ++ s2))
    where
      getStr e = fromVStr =<< interpret' env e

interpret' env (AIntToString e1) =
    do i1 <- getInt e1
       return (VStr (show i1))
    where
      getInt e = fromVInt =<< interpret' env e

interpret' _ (AAbs v b) =
    case v of
      AVar x -> Right (VAbs x b)
      _      -> Left "Unknown value in the abstraction parameter list!"
interpret' env (AApp f e) =
    case interpret' env f of
      Right (VAbs v b) ->
          case interpret' env e of
            Right arg  -> interpret' (M.insert v arg env) b
            l@(Left _) -> l
      l@(Left _)       -> l
      _                -> Left "Can't perform application!"

-- Client interface.
interpret :: AST -> EvalResult
interpret e = interpret' emptyEnvironment e

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

append :: AST -> AST -> AST
append e1 e2 = AAppend e1 e2

intToString :: AST -> AST
intToString e1 = AIntToString e1

list :: [AST] -> AST
list e = AList e

tuple :: [AST] -> AST
tuple e = ATuple e
