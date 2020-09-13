module AlgorithmW where 

import Data.Maybe (fromMaybe)
import qualified Data.Map as Map
import qualified Data.Set as Set 

import Control.Monad.Error 
import Control.Monad.Reader (runReaderT, ReaderT)
import Control.Monad.State (put, get, runStateT, runState, StateT)

import qualified Text.PrettyPrint as PP 
import Data.Set ((\\))

data Exp = EVar String 
         | ELit Lit 
         | EApp Exp Exp 
         | EAbs String Exp
         | ELet String Exp Exp 
         deriving (Eq, Ord, Show)

data Lit = LInt Integer
         | LBool Bool 
         deriving (Eq, Ord, Show)

data Type = TVar String 
          | TInt 
          | TBool 
          | TFun Type Type  
          deriving (Eq, Ord)

data Scheme = Scheme [String] Type 

type Subst = Map.Map String Type 

instance Show Type where 
    show (TVar t) = t
    show TInt = "int"
    show TBool = "bool"
    show (TFun a b) = "(" ++ show a ++ "->" ++ show b ++ ")" 

nullSubst :: Subst 
nullSubst = Map.empty

composeSubst :: Subst -> Subst -> Subst
composeSubst s1 s2 = Map.map (apply s1) s2 `Map.union` s1 

class Types a where 
    ftv :: a -> Set.Set String 
    apply :: Subst -> a -> a

instance Types Type where 
    ftv (TVar n)   = Set.singleton n
    ftv TInt       = Set.empty 
    ftv TBool      = Set.empty
    ftv (TFun a b) = Set.union (ftv a) (ftv b)

    apply s (TVar n)   = fromMaybe (TVar n) (Map.lookup n s)  
    apply s (TFun a b) = TFun (apply s a) (apply s b)
    apply s t          = t

instance Types Scheme where 
    ftv (Scheme vars t) = ftv t \\ Set.fromList vars
    apply s (Scheme vars t) = Scheme vars (apply s' t)
        where s' = foldr Map.delete s vars

instance Show Scheme where 
    show (Scheme vars t) = "forall " ++ v ++ show t
        where v = foldr (\x s -> x  ++ ". " ++ s) "" vars 

instance Types a => Types [a] where 
    apply s = map (apply s)
    ftv = foldr (Set.union . ftv) Set.empty

-- make a pr to F# lint on fusing maps and folds 
-- Type environments, called Γ in the text, are mappings from term variables to their respective type schemes.
newtype TypeEnv = TypeEnv (Map.Map String Scheme)

remove :: TypeEnv -> String -> TypeEnv
remove (TypeEnv env) var = TypeEnv (Map.delete var env)

instance Types TypeEnv where 
    ftv (TypeEnv env) = ftv (Map.elems env)
    apply s (TypeEnv env) = TypeEnv (Map.map (apply s) env)

generalize :: TypeEnv -> Type -> Scheme 
generalize env t = Scheme vars t
    where vars = Set.toList (ftv t \\ ftv env) 

data TIEnv = TIEnv{}
data TIState = TIState{tiSupply :: Int,
                       tiSubst  :: Subst}

type TI a = ErrorT String (ReaderT TIEnv (StateT TIState IO)) a 

runTI :: TI a -> IO (Either String a, TIState)
runTI t = do 
    (res, st) <- runStateT (runReaderT (runErrorT t) initTIEnv) initTIState 
    return (res, st)
 where initTIEnv = TIEnv{}
       initTIState = TIState{ tiSupply = 0, tiSubst = Map.empty}

newTypVar :: String -> TI Type
newTypVar prefix = do 
    s <- get 
    put s{tiSupply = tiSupply s + 1} 
    return (TVar (prefix ++ show (tiSupply s)))

instantiate :: Scheme -> TI Type
instantiate (Scheme vars t) = do    
    nvars <- mapM (const newTypVar "a") vars
    let s = Map.fromList (zip vars nvars)
    return $ apply s t

-- unification
mgu :: Type -> Type -> TI Subst 
mgu (TFun l r) (TFun l' r') = do
    s1 <- mgu l l'
    s2 <- mgu (apply s1 r) (apply s1 r')
    return (s1 `composeSubst` s2)
mgu (TVar u) t = varBind u t
mgu t (TVar u) = varBind u t
mgu TInt TInt = return nullSubst
mgu TBool TBool = return nullSubst 
mgu t1 t2 = throwError $ "types do not unify" ++ show t1 ++ "vs. " ++ show t2

varBind :: String -> Type -> TI Subst
varBind u t 
    | t == TVar u = return nullSubst
    | u `Set.member` ftv t = throwError $ "occur checks fails: " ++ u ++ "vs. " ++ show t
    | otherwise = return (Map.singleton u t)


tiLit :: TypeEnv -> Lit -> TI (Subst, Type)
tiLit _ (LInt _) = return (nullSubst, TInt)
tiLit _ (LBool _) = return (nullSubst, TBool)

ti :: TypeEnv -> Exp -> TI (Subst, Type)
ti (TypeEnv env) (EVar n) = 
    case Map.lookup n env of 
        Nothing -> throwError $ "unbound variable: " ++ n
        Just sigma -> do 
            t <- instantiate sigma
            return (nullSubst, t)
ti env (ELit l) = tiLit env l
ti env (EAbs n e) = do
    tv <- newTypVar "a"
    let TypeEnv env' = remove env n
    let env'' = TypeEnv (env' `Map.union` Map.singleton n (Scheme [] tv))
    (s1, t1) <- ti env'' e
    return (s1, TFun (apply s1 tv) t1)
ti env (EApp e1 e2) = do 
    tv <- newTypVar "a"
    (s1, t1) <- ti env e1
    (s2, t2) <- ti (apply s1 env) e2 
    s3 <- mgu (apply s2 t1) (TFun t2 tv) 
    return (s3 `composeSubst` s2 `composeSubst` s1 `composeSubst` s1, apply s3 tv) 
ti env (ELet x e1 e2) = do 
    (s1, t1) <- ti env e1 
    let TypeEnv env' = remove env x
    let t' = generalize (apply s1 env) t1
    let env'' = TypeEnv (Map.insert x t' env')
    (s2, t2) <- ti (apply s1 env'') e2
    return (s1 `composeSubst` s2, t2)

typeInference :: Map.Map String Scheme -> Exp -> TI Type 
typeInference env e = do 
    (s, t) <- ti (TypeEnv env) e
    return (apply s t)


-- tests 
e0 = ELet "id" (EAbs "x" (EVar "x")) (EVar "id")
e1 = ELet "id" (EAbs "x" (EVar "x")) (EApp (EVar "id") (EVar "id"))
e2 = ELet "id" (EAbs "x" (ELet "y" (EVar "x") (EVar "y"))) (EApp (EVar "id") (EVar "id"))
e3 = ELet "id" (EAbs "x" (ELet "y" (EVar "x") (EVar "y"))) (EApp (EApp (EVar "id") (EVar "id")) (ELit (LInt 2)))
e4 = ELet "id" (EAbs "x" (EApp (EVar "x") (EVar "x"))) (EVar "id")
e5 = EAbs "m" (ELet "y" (EVar "m") (ELet "x" (EApp (EVar "y") (ELit (LBool True))) (EVar "x")))



test :: Exp -> IO ()
test e = do 
    (res, _) <- runTI (typeInference Map.empty e)
    case res of 
        Left err -> putStrLn $ "error: " ++ err
        Right t -> putStrLn $ show e ++ " :: " ++ show t 