module AlgorithmW  where 

import Data.Maybe (fromMaybe)
import qualified Data.Map as Map
import qualified Data.Set as Set 

import Control.Monad.Error 
import Control.Monad.Reader ()
import Control.Monad.State ()

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

nullSubst :: Subst 
nullSubst = Map.empty

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