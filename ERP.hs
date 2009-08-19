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
         | AIfThenElse AST AST AST
         | ABuiltin String
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

-- "Syntax sugar" for type schemes.
forAllTS :: [String] -> SimpleType -> TypeScheme
forAllTS [] t     = TSVar t
forAllTS (x:xs) t = TSForAll x (forAllTS xs t)

-- Apply f to all type variable nodes in the given simple type.
mapSTVars :: (SimpleType -> SimpleType) -> SimpleType -> SimpleType
mapSTVars f t@(STBase _)   = f t
mapSTVars f (STFun ta tb)  = (STFun (mapSTVars f ta) (mapSTVars f tb))
mapSTVars f (STList te)    = STList . mapSTVars f $ te
mapSTVars f (STTuple elts) = STTuple . map (mapSTVars f) $ elts
mapSTVars _ STBool         = STBool
mapSTVars _ STStr          = STStr
mapSTVars _ STInt          = STInt

-- A fold over all type variables in the type tree.
foldSTVars :: (SimpleType -> a -> a) -> a -> SimpleType -> a
foldSTVars f v t@(STBase _)     = f t v
foldSTVars f v (STFun ta tb)    = foldSTVars f (foldSTVars f v ta) tb
foldSTVars f v (STList te)      = foldSTVars f v te
foldSTVars _ v (STTuple [])     = v
foldSTVars f v (STTuple (x:xs)) = foldSTVars f (foldSTVars f v (STTuple xs)) x
foldSTVars _ v STBool           = v
foldSTVars _ v STStr            = v
foldSTVars _ v STInt            = v

-- Given a type variable, return its name.
extractTVName :: (Monad m) => SimpleType -> m String
extractTVName (STBase s) = return s
extractTVName t          = fail ("The type " ++ show t ++ "must be a type variable!")

-- Type pretty-printing.
showSimpleType :: SimpleType -> String
showSimpleType STBool        = "bool"
showSimpleType STInt         = "int"
showSimpleType STStr         = "string"
showSimpleType (STList st)   = "[" ++ (showSimpleType st) ++ "]"
showSimpleType (STTuple sts) = ("(" ++ (concat . intersperse ", "
                                        . map showSimpleType $ sts) ++ ")")
showSimpleType (STFun f@(STFun _ _) a)
    = "(" ++ showSimpleType f ++ ") -> " ++ showSimpleType a
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

-- Given a type variable n, a type nt, and a type old, substitute all
-- occurences of n in old for nt.
substituteTypeVariableWithType :: (SimpleType -> SimpleType
                                   -> SimpleType -> SimpleType)
substituteTypeVariableWithType (STBase n) nt old = mapSTVars doSubstitute old
    where
      doSubstitute ot@(STBase s) | (s == n)  = nt
                                 | otherwise = ot
      doSubstitute x  = x

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

unify ((STTuple els1, STTuple els2):cs)
    | length els1 == length els2 = unify ncs
    where
      ncs = cs ++ (zipWith (,) els1 els2)

unify ((_, _):_) = fail "Unsolvable constraints"

-- Typing context.
type TypingContext = M.Map String Type

-- Default typing context, pre-populated with types of built-in functions.
defaultTypingContext :: TypingContext
defaultTypingContext = M.fromList builtinTypes
    where
      builtinTypes = builtinSimpleTypes ++ builtinTypeSchemes

      builtinSimpleTypes = map (id *** (TSimple)) builtinSimpleTypes'
      builtinSimpleTypes' =
          [
           ("id", STFun (STBase "a") (STBase "a")),
           ("boolEq", STFun STBool (STFun STBool STBool)),
           ("intEq", STFun STInt (STFun STInt STBool)),
           ("strEq", STFun STStr (STFun STStr STBool)),
           ("concat", STFun STStr (STFun STStr STStr)),
           ("intToString", STFun STInt STStr),
           ("plus", STFun STInt (STFun STInt STInt))
          ]

      builtinTypeSchemes = map (id *** (TScheme)) builtinTypeSchemes'
      builtinTypeSchemes' =
          [
           ("fst",    forAllTS ["a", "b"] simpleFstType),
           ("snd",    forAllTS ["a", "b"] simpleSndType),
           ("length", forAllTS ["a"] simpleLengthType),
           ("map",    forAllTS ["a", "b"] simpleMapType),
           ("reduce", forAllTS ["a", "b"] simpleReduceType),
           ("filter", forAllTS ["a"] simpleFilterType),
           ("concatMap", forAllTS ["a", "b"] simpleConcatMapType)
          ]
      simpleFstType    = STFun (STTuple [STBase "a", STBase "b"]) (STBase "a")
      simpleSndType    = STFun (STTuple [STBase "a", STBase "b"]) (STBase "b")
      simpleLengthType = STFun (STList (STBase "a")) STInt

      -- (a -> b) -> [a] -> [b]
      simpleMapType = STFun (STFun (STBase "a") (STBase "b"))
                      (STFun (STList (STBase "a")) (STList (STBase "b")))

      -- (a -> b -> a) -> a -> [b] -> a
      simpleReduceType = STFun (STFun (STBase "a")
                                (STFun (STBase "b") (STBase "a")))
                         (STFun (STBase "a")
                          (STFun (STList (STBase "b")) (STBase "a")))

      -- (a -> bool) -> [a] -> [a]
      simpleFilterType = STFun (STFun (STBase "a") STBool)
                         (STFun (STList (STBase "a")) (STList (STBase "a")))

      -- (a -> [b]) -> [a] -> [b]
      simpleConcatMapType = STFun (STFun (STBase "a") (STList (STBase "b")))
                            (STFun (STList (STBase "a")) (STList (STBase "b")))



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

-- Create a new type variable.
newTypeVariable :: TypingInfo -> (SimpleType, TypingInfo)
newTypeVariable ti = (STBase sym, nti)
    where
      (sym, nti) = gensym ti

-- Create n new type variables
newTypeVariables :: Int -> TypingInfo -> ([SimpleType], TypingInfo)
newTypeVariables m ti = newTypeVariables' m ti []
    where
      newTypeVariables' 0 ti' acc = (acc, ti')
      newTypeVariables' n ti' acc = let (st, nti) = newTypeVariable ti'
                                    in newTypeVariables' (n-1) nti (acc ++ [st])

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

-- Given a type scheme, instantiate it with fresh type variables.
instantiateTypeScheme :: TypeScheme -> TypingInfo -> TypecheckResult
instantiateTypeScheme ts ti =
    do let st = underlyingSimpleType ts
       let (subst, nti) = typeSchemeToSubstitution ts ti []
       return (TSimple . applySubstitution subst $ st, nti)

-- Get the underlying simple type from a type scheme.
underlyingSimpleType :: TypeScheme -> SimpleType
underlyingSimpleType (TSVar st) = st
underlyingSimpleType (TSForAll _ ts) = underlyingSimpleType ts

-- Given a type scheme, extract the assumed substitution.
typeSchemeToSubstitution :: TypeScheme -> TypingInfo
                         -> Substitution -> (Substitution, TypingInfo)
typeSchemeToSubstitution (TSVar _) ti s = (s, ti)
typeSchemeToSubstitution (TSForAll x ts) ti s
    = let (tv, nti) = newTypeVariable ti
      in typeSchemeToSubstitution ts nti ((STBase x, tv):s)

-- Given a type, try to generalize all remaining free type variables (with
-- regard to context).
generalizeType :: Type -> TypingInfo -> TypingContext -> TypecheckResult
generalizeType ts@(TScheme _) ti _ = return (ts, ti)
generalizeType (TSimple st) ti ctx =
    do let freeTypeVariables = foldSTVars doGeneralize [] st
       let (newVars, nti) = newTypeVariables (length freeTypeVariables) ti
       let subst = zipWith (,) freeTypeVariables newVars
       let nst = applySubstitution subst st
       newTypeVariableNames <- mapM extractTVName newVars
       return (TScheme . forAllTS newTypeVariableNames $ nst, nti)
    where
       doGeneralize :: SimpleType -> [SimpleType] -> [SimpleType]
       doGeneralize st'@(STBase n) lst | notInContext n = st':lst
       doGeneralize _ lst = lst

       notInContext :: String -> Bool
       notInContext = not . (flip M.member) ctx

-- Check that there are no identically-named bindings in the list.
checkBindings :: (Monad m) => [Binding] -> m Bool
checkBindings [] = return True
checkBindings ((n, _):bs) =
    if hasEqual n bs
    then fail "Conflicting definitions in let-expression!"
    else return True
    where

      hasEqual :: String -> [Binding] -> Bool
      hasEqual _ []                       = False
      hasEqual n' ((n1, _):bs') | n' == n1   = True
                                | otherwise = hasEqual n bs'

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
      Nothing -> case lookupCtxTS n ctx of
                   Just ts -> instantiateTypeScheme ts ti
                   Nothing -> fail ("Unknown variable '" ++ n ++ "'!")

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
    do checkBindings bindings
       (nti, binding_types) <- inferTypesOfBindings bindings ti
       let newctx = M.union (M.fromList binding_types) ctx
       typecheck' body nti newctx
    where

      inferTypesOfBindings :: [Binding] ->
                              TypingInfo -> InferTypesOfBindingsResult
      inferTypesOfBindings [] ti' = Right (ti', [])
      inferTypesOfBindings ((n, v):xs) ti' =
          do (t, nti) <- typecheck' v ti' ctx
             (gent, nti2) <- generalizeType t nti ctx
             (nti3, rest) <- inferTypesOfBindings xs nti2
             return (nti3, (n, gent):rest)

typecheck' (AIfThenElse cond br1 br2) ti ctx =
    do (tcond, nti) <- getSimpleType cond ti ctx
       (tbr1, nti1) <- getSimpleType br1 nti ctx
       (tbr2, nti2) <- getSimpleType br2 nti1 ctx
       let ifConstrs = [(tcond, STBool), (tbr1, tbr2)]
       let nti3 = insertConstrs ifConstrs nti2
       nti4 <- unifyConstrs nti3
       return (inferType nti4 tbr1, nti4)

typecheck' (ABuiltin name) ti ctx = typecheck' (AVar name) ti ctx

typecheck' _ _ _           = Left "Can't typecheck!"

-- Client interface.

typecheck :: AST -> Either String Type
typecheck ast =
    do (t, _) <- typecheck' ast emptyTypingInfo defaultTypingContext
       return t

printType :: AST -> IO ()
printType ast =
    case typecheck' ast emptyTypingInfo defaultTypingContext
    of Left l -> fail l
       Right (t, _) -> do let s = showType t
                          putStrLn s
-- Interpreter.
---------------

type EvalResult = Either String Value
type Environment = M.Map String Value
type BuiltinFun = ([Value] -> Environment -> EvalResult)

data Value = VBool Bool | VInt Integer | VStr String
           | VClosure String Environment AST
           | VList [Value] | VTuple [Value]
           | VBuiltin String BuiltinFun [Value] Int

instance Eq Value where
    (==) = isEqualV

instance Show Value where
    show = showValue

showValueList :: [Value] -> String
showValueList = concat . intersperse ", " . map showValue

showValue :: Value -> String
showValue (VBool b)  = show b
showValue (VInt i)   = show i
showValue (VStr s)   = show s
showValue (VList l)  = "[" ++ showValueList l ++ "]"
showValue (VTuple l) = "(" ++ showValueList l ++ ")"
showValue (VClosure v _ b) = ("(\\" ++ v ++ " -> " ++ show b ++ ")")
showValue (VBuiltin n _ args _) =
    let baseName = "(built-in function \"" ++ n ++ "\")"
    in if (length args) > 0
       then baseName ++ " partially applied to " ++ show args
       else baseName

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

isEqualV (VBuiltin b1 _ _ _) (VBuiltin b2 _ _ _) = (b1 == b2)
isEqualV (VClosure _ _ _) (VClosure _ _ _)       = False
isEqualV _ _                                     = False

-- Helper functions that extract underlying values from the Value type.

fromVBool :: Value -> Either String Bool
fromVBool (VBool b) = Right b
fromVBool _         = Left "The value is not a boolean!"

fromVInt :: Value -> Either String Integer
fromVInt (VInt i) = Right i
fromVInt _        = Left "The value is not an integer!"

fromVStr :: Value -> Either String String
fromVStr (VStr i) = Right i
fromVStr _        = Left "The value is not an string!"

fromVTuple :: Value -> Either String [Value]
fromVTuple (VTuple l) = Right l
fromVTuple _          = Left "The value is not an tuple!"

fromVList :: Value -> Either String [Value]
fromVList (VList l) = Right l
fromVList _         = Left "The value is not a list!"

-- Return a closure that we can apply with applyClosure.
fromClosure :: Value -> Either String Value
fromClosure c@(VClosure _ _ _)   = Right c
fromClosure b@(VBuiltin _ _ _ _) = Right b
fromClosure _                    = Left "The value is not a function!"

-- Default environment, pre-populated with builtin functions.
defaultEnvironment :: Environment
defaultEnvironment = M.fromList defaultBindings
    where
      defaultBindings :: [(String, Value)]
      defaultBindings = map (uncurry makeBuiltin) defaultBindings'

      defaultBindings' = [ ("boolEq", 2), ("intEq", 2),
                           ("strEq", 2), ("id", 1),
                           ("concat", 2), ("intToString", 1),
                           ("plus", 2), ("fst", 1),
                           ("snd", 1), ("length", 1),
                           ("map", 2), ("reduce", 3),
                           ("filter", 2), ("concatMap", 2)
                         ]

makeBuiltin :: String -> Int -> (String, Value)
makeBuiltin name argsReq = let f = builtinFun name
                           in (name, (VBuiltin name f [] argsReq))

builtinFun :: String -> BuiltinFun
builtinFun name args env

    | name == "id" =
        do checkArgs 1
           return firstArg

    | name == "boolEq" =
        do checkArgs 2
           b1 <- fromVBool firstArg
           b2 <- fromVBool secondArg
           return . VBool $ b1 == b2

    | name == "intEq" =
        do checkArgs 2
           i1 <- fromVInt firstArg
           i2 <- fromVInt secondArg
           return . VBool $ i1 == i2

    | name == "strEq" =
        do checkArgs 2
           s1 <- fromVStr firstArg
           s2 <- fromVStr secondArg
           return . VBool $ s1 == s2

    | name == "plus" =
        do checkArgs 2
           i1 <- fromVInt firstArg
           i2 <- fromVInt secondArg
           return . VInt $ i1 + i2

    | name == "concat" =
        do checkArgs 2
           s1 <- fromVStr firstArg
           s2 <- fromVStr secondArg
           return . VStr $ s1 ++ s2

    | name == "intToString" =
        do checkArgs 1
           i <- fromVInt firstArg
           return . VStr $ show i

    | name == "fst" =
        do checkArgs 1
           l <- fromVTuple firstArg
           checkTupleLength l
           return . head $ l

    | name == "snd" =
        do checkArgs 1
           l <- fromVTuple firstArg
           checkTupleLength l
           return . head . tail $ l

    | name == "length" =
        do checkArgs 1
           l <- fromVList firstArg
           return . VInt . toInteger . length $ l

    | name == "map" =
        do checkArgs 2
           f <- fromClosure firstArg
           l <- fromVList secondArg
           ret <- mapM (applyClosure env f) l
           return . VList $ ret

    | name == "concatMap" =
        do checkArgs 2
           f <- fromClosure firstArg
           l <- fromVList secondArg
           ret <- mapM (applyClosure env f) l
           ret2 <- mapM fromVList ret
           return . VList $ concat ret2

    | name == "reduce" =
        do checkArgs 3
           f <- fromClosure firstArg
           let v = secondArg
           l <- fromVList thirdArg
           let foldFun = (\s e -> do cl1 <- applyClosure env f s
                                     applyClosure env cl1 e)
           ret <- foldM foldFun v l
           return ret

    | name == "filter" =
        do checkArgs 2
           f <- fromClosure firstArg
           l <- fromVList secondArg
           let filterFun = (\e -> fromVBool =<< applyClosure env f e)
           ret <- filterM filterFun l
           return . VList $ ret

    | otherwise = fail "Unknown builtin!"

    where
      checkArgs argsNeeded =
          if argsGiven == argsNeeded
          then return True
          else fail ("'" ++ name ++ "' takes " ++ show argsNeeded ++
                     " arguments, but was called with " ++ show argsGiven ++ "!")

      checkTupleLength l =
          when (length l /= 2) (fail "The tuple must have 2 elements!")

      argsGiven = length args
      firstArg  = head $ args
      secondArg = head . tail $ args
      thirdArg  = head . tail . tail $ args

-- Given a closure and a value, apply the former to the latter, and return the
-- result.
applyClosure :: Environment -> Value -> Value -> EvalResult
applyClosure _ (VClosure v e b) arg = interpret' (M.insert v arg e) b

applyClosure env (VBuiltin n bf args argsRequired) arg =
    do let newArgs = args ++ [arg]
       if length newArgs == argsRequired
           then bf newArgs env
           else return (VBuiltin n bf newArgs argsRequired)

applyClosure _ _ _  = Left "Can't perform application!"

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

interpret' env (ALet [] body) = interpret' env body
interpret' env (AIfThenElse cond br1 br2)
    = do cond' <- fromVBool =<< interpret' env cond
         if cond'
             then interpret' env br1
             else interpret' env br2

interpret' env (ALet bindings body) =
    do checkBindings bindings
       vals <- mapM (interpret' env) (map snd bindings)
       let letEnv = M.fromList . zipWith (,) (map fst bindings) $ vals
       let newEnv = (M.union letEnv env)
       interpret' newEnv body

interpret' env (AAbs v b) =
    case v of
      AVar x -> return (VClosure x env b)
      _      -> fail "Unknown value in the abstraction parameter list!"

interpret' env (AApp f e) =
    do fun <- interpret' env f
       arg <- interpret' env e
       applyClosure env fun arg

interpret' env (ABuiltin n) = interpret' env (AVar n)

-- Client interface.
interpret :: AST -> EvalResult
interpret e = interpret' defaultEnvironment e

interpret_pretty :: AST -> String
interpret_pretty e = case interpret e
                     of (Right v)  -> showValue v
                        (Left err) -> error err

evaluate :: AST -> IO ()
evaluate ast = do let output = interpret_pretty ast
                  putStrLn output

printResult :: AST -> IO ()
printResult = evaluate

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

let_ :: [(String, AST)] -> AST -> AST
let_ bindings body = ALet bindings body

ifThenElse :: AST -> AST -> AST -> AST
ifThenElse cond br1 br2 = AIfThenElse cond br1 br2

list :: [AST] -> AST
list e = AList e

tuple :: [AST] -> AST
tuple e = ATuple e

builtin :: String -> AST
builtin = ABuiltin

builtinApp :: String -> [AST] -> AST
builtinApp n args = foldl' AApp (builtin n) args

id_ :: AST -> AST
id_ x = builtinApp "id" [x]

boolEq :: AST -> AST -> AST
boolEq b1 b2 = builtinApp "boolEq" [b1, b2]

intEq :: AST -> AST -> AST
intEq i1 i2 = builtinApp "intEq" [i1, i2]

strEq :: AST -> AST -> AST
strEq s1 s2 = builtinApp "strEq" [s1, s2]

plus :: AST -> AST -> AST
plus e1 e2 = builtinApp "plus" [e1, e2]

concat_ :: AST -> AST -> AST
concat_ e1 e2 = builtinApp "concat" [e1, e2]

intToString :: AST -> AST
intToString e1 = builtinApp "intToString" [e1]

length_ :: AST -> AST
length_ e1 = builtinApp "length" [e1]

fst_ :: AST -> AST
fst_ e1 = builtinApp"fst" [e1]

snd_ :: AST -> AST
snd_ e1 = builtinApp "snd" [e1]

reduce :: AST -> AST -> AST -> AST
reduce f v l = builtinApp "reduce" [f, v, l]

map_ :: AST -> AST -> AST
map_ f l = builtinApp "map" [f, l]

filter_ :: AST -> AST -> AST
filter_ f l = builtinApp "filter" [f, l]

concatMap_ :: AST -> AST -> AST
concatMap_ f l = builtinApp "concatMap" [f, l]
