module AlgorithmW  where 

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
         deriving (Eq, Ord)

data Lit = LInt Integer
         | LBool Bool 
         deriving (Eq, Ord)

data Type = TVar String 
          | TInt 
          | TBool 
          | TFun Type Type  
          deriving (Eq, Ord)

data Scheme = Scheme [String] Type 

type Subst = Map.Map String Type 

instance Show Type where 

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
    apply s (Scheme vars t) = Scheme vars (apply (foldr Map.delete s vars) t)


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