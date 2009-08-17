module ERP
   where

import Control.Arrow ((***))
import Control.Monad.Error
import Data.List (foldl', intersperse)
import Data.Maybe
import qualified Data.Map as M

-- Parser.
----------
type Binding = (String, AST)

data AST = ABool Bool | AInt Integer | AStr String
         | AVar String | AAbs AST AST | AApp AST AST
         | ATuple [AST] | AList [AST]
         | ALet [Binding] AST
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

showConstraint :: Constraint -> String
showConstraint (t1, t2) = ("(" ++ showSimpleType t1 ++ " = "
                           ++ showSimpleType t2 ++ ")")

showConstraintSet :: ConstraintSet -> String
showConstraintSet s = "{" ++ (concat . intersperse ", " . map showConstraint $ s) ++ "}"

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

type UnifyResult = Either String Substitution

recUnify:: SimpleType -> SimpleType -> ConstraintSet -> UnifyResult
recUnify s t = unify . substituteInConstraintSet s t

unify :: ConstraintSet -> UnifyResult
unify [] = return []
unify ((s,t):cs) | s == t = unify cs

unify ((s@(STBase _), t):cs)
    | s `notOccursIn` t = do ncs' <- recUnify s t cs
                             let ncs = ncs' ++ [(s, t)]
                             return ncs

unify ((s, t@(STBase _)):cs)
    | t `notOccursIn` s = do ncs' <- recUnify t s cs
                             let ncs = ncs' ++ [(t, s)]
                             return ncs

unify ((STFun s1 s2, STFun t1 t2):cs) = unify ncs
    where
      ncs = cs ++ [(s1, t1), (s2, t2)]

unify ((STList s1, STList s2):cs) = unify ncs
    where
      ncs = cs ++ [(s1, s2)]

unify ((STTuple els1, STTuple els2):cs) = unify ncs
    where
      ncs = cs ++ (zipWith (,) els1 els2)

unify ((_, _):_) = fail "Unsolvable constraints"


-- Typing context.
type TypingContext = M.Map String Type

emptyTypingContext :: TypingContext
emptyTypingContext = M.empty

lookupCtxST :: String -> TypingContext -> Maybe SimpleType
lookupCtxST n ctx = M.lookup n ctx >>= extractSimpleType

lookupCtxTS :: String -> TypingContext -> Maybe TypeScheme
lookupCtxTS n ctx = M.lookup n ctx >>= extractTypeScheme

insertCtxST :: String -> SimpleType -> TypingContext -> TypingContext
insertCtxST k v ctx = M.insert k (TSimple v) ctx

insertCtxTS :: String -> TypeScheme -> TypingContext -> TypingContext
insertCtxTS k v ctx = M.insert k (TScheme v) ctx

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

newTypeVariable :: TypingInfo -> (SimpleType, TypingInfo)
newTypeVariable ti = (STBase sym, nti)
    where
      (sym, nti) = gensym ti

insertConstr :: Constraint -> TypingInfo -> TypingInfo
insertConstr c ti = let oldconstrs = constrs ti
                    in ti { constrs = (c:oldconstrs) }

insertConstrs :: [Constraint] -> TypingInfo -> TypingInfo
insertConstrs cs ti = let oldconstrs = constrs ti
                      in ti { constrs = (cs ++ oldconstrs) }

unifyConstrs :: TypingInfo -> Either String TypingInfo
unifyConstrs ti = do unifiedConstrs <- unify . constrs $ ti
                     return $ ti { constrs = unifiedConstrs }

inferType :: TypingInfo -> SimpleType -> Type
inferType ti t = TSimple (applySubstitution (constrs ti) t)

simpleType :: (SimpleType, TypingInfo) -> Either a (Type, TypingInfo)
simpleType (t, ti) = Right (TSimple t, ti)

type SimpleTypecheckResult = Either String (SimpleType, TypingInfo)

-- Typecheck the expression, and fail if it doesn't have a simple type.
getSimpleType :: AST -> TypingInfo -> TypingContext -> SimpleTypecheckResult
getSimpleType e ti ctx = do (t, nti) <- typecheck' e ti ctx
                            st <- extractSimpleType t
                            return (st, nti)

-- Given a Type, return the underlying SimpleType or fail.
extractSimpleType :: (Monad m) => Type -> m SimpleType
extractSimpleType (TSimple t) = return t
extractSimpleType t           = fail ("The type " ++ (show t) ++
                                      "is not a simple type")

-- Given a Type, return the underlying TypeScheme or fail.
extractTypeScheme :: (Monad m) => Type -> m TypeScheme
extractTypeScheme (TScheme t) = return t
extractTypeScheme t           = fail ("The type " ++ (show t) ++
                                      "is not a type scheme")

type SimpleTypecheckListResult = Either String ([SimpleType], TypingInfo)

-- Given a list of expressions, typecheck them using getSimpleType.
getSimpleTypes :: [AST] -> TypingInfo ->
                  TypingContext -> SimpleTypecheckListResult
getSimpleTypes [] ti _ = Right ([], ti)
getSimpleTypes (x:xs) ti ctx =
    do (t1, nti) <- getSimpleType x ti ctx
       (ts, nti2) <- getSimpleTypes xs nti ctx
       return (t1:ts, nti2)

type TypecheckResult = Either String (Type, TypingInfo)
type BindingTypes = [(String, Type)]
type InferTypesOfBindingsResult = Either String (TypingInfo, BindingTypes)

-- The main typechecking function.
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
       nti4 <- unifyConstrs nti3
       elType <- extractSimpleType . inferType nti4 $ newVar
       simpleType (STList elType , nti4)

typecheck' (ATuple []) ti _ = simpleType (STTuple [newVar], nti)
    where
      (newVar, nti) = newTypeVariable ti

typecheck' (ATuple els) ti ctx =
    do (simpleEls, nti) <- getSimpleTypes els ti ctx
       simpleType (STTuple simpleEls, nti)

typecheck' (AVar n) ti ctx =
    case lookupCtxST n ctx of
      Just t -> Right ((TSimple t), ti)
      Nothing -> Left ("Unknown variable '" ++ n ++ "'!")

typecheck' (AAbs (AVar v) b) ti ctx =
    do let (varType, nti) = newTypeVariable ti
       (t, nti2) <- getSimpleType b nti (insertCtxST v varType ctx)
       nti3 <- unifyConstrs nti2
       let funType = (STFun varType t)
       let newFunType = inferType nti3 funType
       Right (newFunType, nti3)

typecheck' (AApp f a) ti ctx  =
    do (tf, ti1) <- getSimpleType f ti ctx
       (ta, ti2) <- getSimpleType a ti1 ctx
       let (retType, ti3) = newTypeVariable ti2
       let newConstr = (tf, STFun ta retType)
       let ti4 = insertConstr newConstr ti3
       ti5 <- unifyConstrs ti4
       return (inferType ti5 retType, ti5)

typecheck' (ALet [] body) ti ctx = typecheck' body ti ctx

typecheck' (ALet bindings body) ti ctx  =
    do check_bindings bindings
       (nti, binding_types) <- inferTypesOfBindings bindings ti
       let newctx = foldl' (\m e -> uncurry M.insert e m) ctx binding_types
       typecheck' body nti newctx
    where

      inferTypesOfBindings :: [Binding] ->
                              TypingInfo -> InferTypesOfBindingsResult
      inferTypesOfBindings [] ti' = Right (ti', [])
      inferTypesOfBindings ((n, v):xs) ti' =
          do (t, nti) <- typecheck' v ti' ctx
             -- generalize t
             (nti2, rest) <- inferTypesOfBindings xs nti
             return (nti2, (n, t):rest)

      -- Check that there are no identically-named bindings.
      check_bindings :: (Monad m) => [Binding] -> m Bool
      check_bindings [] = return True
      check_bindings ((n, _):bs) =
          if hasEqual n bs
          then fail "Conflicting definitions in let-expression!"
          else return True

      -- Helper function for check_bindings.
      hasEqual :: String -> [Binding] -> Bool
      hasEqual _ []                       = False
      hasEqual n ((n1, _):bs) | n == n1   = True
                              | otherwise = hasEqual n bs


-- TODO: replace by 'builtin'.
typecheck' (APlus e1 e2) ti ctx =
    do (t1, ti1) <- getSimpleType e1 ti ctx
       (t2, ti2) <- getSimpleType e2 ti1 ctx
       let newti = insertConstrs [(t1, STInt),
                                  (t2, STInt)] ti2
       newti2 <- unifyConstrs newti
       simpleType (STInt, newti2)

typecheck' (AAppend e1 e2) ti ctx =
    do (t1, ti1) <- getSimpleType e1 ti ctx
       (t2, ti2) <- getSimpleType e2 ti1 ctx
       let newti = insertConstrs [(t1, STStr),
                                  (t2, STStr)] ti2
       newti2 <- unifyConstrs newti
       simpleType (STStr, newti2)

typecheck' (AIntToString e1) ti ctx =
    do (t1, ti1) <- getSimpleType e1 ti ctx
       let newti = insertConstrs [(t1, STInt)] ti1
       newti2 <- unifyConstrs newti
       simpleType (STStr, newti2)

typecheck' _ _ _           = Left "Can't typecheck!"

-- Client interface.

typecheck :: AST -> Either String Type
typecheck ast =
    do (t, _) <- typecheck' ast emptyTypingInfo emptyTypingContext
       return t

typecheck_pretty :: AST -> String
typecheck_pretty ast =
    case typecheck' ast emptyTypingInfo emptyTypingContext
    of Left l -> error l
       -- Laziness can be so much fun sometimes...
       Right (t, ti) -> constrs ti `seq` showType t

-- Interpreter.
---------------
data Value = VBool Bool | VInt Integer | VStr String | VAbs String AST
           | VList [Value] | VTuple [Value]
             deriving (Eq, Show, Ord)

showValueList :: [Value] -> String
showValueList = concat . intersperse ", " . map showValue

showValue :: Value -> String
showValue (VBool b)  = show b
showValue (VInt i)   = show i
showValue (VStr s)   = show s
showValue (VList l)  = "[" ++ showValueList l ++ "]"
showValue (VTuple l) = "(" ++ showValueList l ++ ")"
showValue (VAbs v b) = ("(\\" ++ v ++ " -> " ++ show b ++ ")")

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

interpret' env (ALet [] body) = interpret' env body

interpret' env (ALet ((name, val):xs) body) =
    do valEval <- interpret' env val
       let newEnv = (M.insert name valEval env)
       interpret' newEnv (ALet xs body)

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

evaluate :: AST -> EvalResult
evaluate = interpret

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

let_ :: [(String, AST)] -> AST -> AST
let_ bindings body = ALet bindings body
