-- | 这是其中一种实现方式的代码框架。你可以参考它，或用你自己的方式实现，只要按需求完成 evalValue :: Program -> Result 就行。
module EvalValue where

import AST
import Control.Monad.State
import qualified Data.Map as Map
import Debug.Trace

data Value
  = VBool Bool
  | VInt Int
  | VChar Char
  | VExpr Expr [(String, Value)]
  | VData String [Value]
  deriving (Show, Eq)

data Context = Context { -- 可以用某种方式定义上下文，用于记录变量绑定状态
                      value :: Maybe Value,
                      valueMap :: Map.Map String Value,
                      funcMap:: Map.Map String Expr } deriving (Show, Eq)

type ContextState a = StateT Context Maybe a

getBool :: Expr -> ContextState Bool
getBool e = do
  ev <- eval e
  case ev of
    VBool b -> return b
    _ -> lift Nothing

evalAnd :: Expr -> Expr -> ContextState Bool
evalAnd e1 e2 = do
  ev1 <- getBool e1
  case ev1 of
    False -> return False
    True -> getBool e2

evalOr :: Expr -> Expr -> ContextState Bool
evalOr e1 e2 = do
  ev1 <- getBool e1
  case ev1 of
    True -> return True
    False -> getBool e2

getInt :: Expr -> ContextState Int
getInt e = do
  ev <- eval e 
  case ev of
    VInt i -> return i 
    _ -> lift Nothing

getCal :: Expr -> Expr -> Integer -> ContextState Int
getCal e1 e2 operation = do
  VInt ev1 <- eval e1
  VInt ev2 <- eval e2
  case operation of
    0 -> return (ev1 + ev2)
    1 -> return (ev1 - ev2)
    2 -> return (ev1 * ev2)
    3 -> return (ev1 `div` ev2)
    4 -> return (ev1 `mod` ev2)

isSameType :: Value -> Value -> ContextState Bool
isSameType v1 v2 = do
  case v1 of
    VInt _ -> case v2 of 
      VInt _ -> return True 
      _ -> lift Nothing
    VBool _ -> case v2 of 
      VBool _ -> return True 
      _ -> lift Nothing
    VChar _ -> case v2 of 
      VChar _ -> return True 
      _ -> lift Nothing
    
isSameValueType :: Value -> Value -> ContextState Bool
isSameValueType v1 v2 = do
  case v1 of
    VInt _ -> case v2 of 
      VInt _ -> return True 
      _ -> lift Nothing
    VChar _ -> case v2 of 
      VChar _ -> return True 
      _ -> lift Nothing

getEq :: Expr -> Expr -> ContextState Bool
getEq e1 e2 = do
  ev1 <- eval e1
  ev2 <- eval e2
  isSameType ev1 ev2 >> if ev1 == ev2 then return True else return False

getNeq :: Expr -> Expr -> ContextState Bool
getNeq e1 e2 = do
  ev1 <- eval e1
  ev2 <- eval e2
  isSameType ev1 ev2 >> if ev1 == ev2 then return False else return True

getOrd :: Expr -> Expr -> Integer -> ContextState Bool
getOrd e1 e2 operation = do
  ev1 <- eval e1
  ev2 <- eval e2
  isSameValueType ev1 ev2 >> case operation of
    0 -> case ev1 of 
      VInt v1 -> let VInt v2 = ev2 in if v1 < v2 then return True else return False
      VChar v1 -> let VChar v2 = ev2 in if v1 < v2 then return True else return False
    1 -> case ev1 of 
      VInt v1 -> let VInt v2 = ev2 in if v1 > v2 then return True else return False
      VChar v1 -> let VChar v2 = ev2 in if v1 > v2 then return True else return False
    2 -> case ev1 of 
      VInt v1 -> let VInt v2 = ev2 in if v1 <= v2 then return True else return False
      VChar v1 -> let VChar v2 = ev2 in if v1 <= v2 then return True else return False
    3 -> case ev1 of 
      VInt v1 -> let VInt v2 = ev2 in if v1 >= v2 then return True else return False
      VChar v1 -> let VChar v2 = ev2 in if v1 >= v2 then return True else return False

addValue :: Value -> ContextState Value -> ContextState Value
addValue v c = do
  ctx <- get
  put (Context {value = Just v, valueMap = (valueMap ctx), funcMap = funcMap ctx})
  result <- c
  put ctx
  return result

addVars :: [(String,Value)] -> ContextState Value -> ContextState Value
addVars ((n, v):xs) c = do
  ctx <- get
  put (Context {value = (value ctx), valueMap = Map.insert n v (valueMap ctx), funcMap = funcMap ctx})
  result <- addVars xs c
  put ctx
  return result
addVars [] c = c

matchPattern' :: [Value] -> [Pattern] -> ContextState Bool
matchPattern' [] [] = return True
matchPattern' _ [] = return False
matchPattern' [] _ = return False
matchPattern' (v:vs) (p:ps) = do
  b <- matchPattern v p
  if b == True
  then matchPattern' vs ps
  else return False

matchPattern :: Value -> Pattern -> ContextState Bool
matchPattern v p = do
  ctx <- get
  case v of
    VInt vv -> case p of
                PIntLit pv -> do
                  if vv == pv
                  then return True
                  else return False
                PVar s -> do
                  put (Context (value ctx) (Map.insert s v (valueMap ctx)) (funcMap ctx))
                  return True
                _ -> do
                  return False
    VChar vv -> case p of
                  PCharLit pv -> do
                    if vv == pv
                    then return True
                    else return False
                  PVar s -> do
                    put (Context (value ctx) (Map.insert s v (valueMap ctx)) (funcMap ctx))
                    return True
                  _ -> do
                    return False
    VBool vv -> case p of
                  PBoolLit pv -> do
                    if vv == pv
                    then return True
                    else return False
                  PVar s -> do
                    put (Context (value ctx) (Map.insert s v (valueMap ctx)) (funcMap ctx))
                    return True
                  _ -> do
                    return False
    VData s vs -> case p of
                    PData ps pats -> do
                      if s == ps
                      then matchPattern' vs pats
                      else return False
                    PVar ss -> do
                      put (Context (value ctx) (Map.insert ss v (valueMap ctx)) (funcMap ctx))
                      return True
                    _ -> do
                      return False

evalPattern :: Value -> [(Pattern, Expr)] -> ContextState Value
evalPattern _ [] = lift Nothing
evalPattern v (p:ps) = do
  ctx <- get
  b <- matchPattern v (fst p)
  case b of
    True -> do
      result <- eval (snd p)
      put ctx
      return result
    False -> do
      put ctx
      evalPattern v ps
 
evalEs :: [Expr] -> ContextState [Value]
evalEs [] = return []
evalEs (e:es) = do
  ev <- eval e
  esv <- evalEs es
  return (ev:esv)

eval :: Expr -> ContextState Value
eval (EBoolLit b) = return $ VBool b
eval (EIntLit i) = return $ VInt i 
eval (ECharLit c) = return $ VChar c
eval (ENot e) = getBool e >>= \b -> return (VBool $ not b)
eval (EAnd e1 e2) = (evalAnd e1 e2) >>= \b -> return (VBool b)
eval (EOr e1 e2) = (evalOr e1 e2) >>= \b -> return (VBool b)
eval (EAdd e1 e2) = (getCal e1 e2 0) >>= \b -> return (VInt b)
eval (ESub e1 e2) = (getCal e1 e2 1) >>= \b -> return (VInt b)
eval (EMul e1 e2) = (getCal e1 e2 2) >>= \b -> return (VInt b)
eval (EDiv e1 e2) = (getCal e1 e2 3) >>= \b -> return (VInt b)
eval (EMod e1 e2) = (getCal e1 e2 4) >>= \b -> return (VInt b)

eval (EEq e1 e2) = (getEq e1 e2) >>= \b -> return (VBool b)
eval (ENeq e1 e2) = (getNeq e1 e2) >>= \b -> return (VBool b)

eval (ELt e1 e2) = (getOrd e1 e2 0) >>= \b -> return (VBool b)
eval (EGt e1 e2) = (getOrd e1 e2 1) >>= \b -> return (VBool b)
eval (ELe e1 e2) = (getOrd e1 e2 2) >>= \b -> return (VBool b)
eval (EGe e1 e2) = (getOrd e1 e2 3) >>= \b -> return (VBool b)

eval (EIf e1 e2 e3) = do
  ev1 <- eval e1
  case ev1 of
    VBool v1 -> if v1 then eval e2 else eval e3
    _ -> lift Nothing

eval (ELambda (pn, pt) e) = do
  ctx <- get
  case (value ctx) of
    Nothing -> return $ VExpr (ELambda (pn, pt) e) []
    Just v -> do
      put (Context {value = Nothing, valueMap = (valueMap ctx), funcMap = funcMap ctx})
      tmpctx <- get
      put (Context {value = (value tmpctx), valueMap = Map.insert pn v (valueMap tmpctx), funcMap = funcMap tmpctx})
      result <- eval e
      put tmpctx
      case result of
        VExpr expr vars -> return (VExpr expr ((pn, v):vars))
        _ -> return result


eval (ELet (n, e1) e2) = do
  ev1 <- eval e1
  ctx <- get
  put (Context {value = (value ctx), valueMap = Map.insert n ev1 (valueMap ctx), funcMap = funcMap ctx})
  result <- eval e2
  put ctx
  return result

eval (ELetRec f (x, tx) (e1, ty) e2) = do 
  function <- eval (ELambda (x, tx) e1)
  ctx <- get
  put (Context {value = (value ctx), valueMap = Map.insert f function (valueMap ctx), funcMap = funcMap ctx})
  result <- eval e2
  put ctx
  trace (show result) $ return result
  
eval (EVar n) = do
  ctx <- get
  case ((valueMap ctx) Map.!? n) of 
    Just t -> return t
    _ -> case (funcMap ctx) Map.!? n of
      Just t -> eval t
      _ -> lift Nothing 

eval (EApply e1 e2) = do
  VExpr ex1 vars <- eval e1
  ev2 <- eval e2
  result <- addVars vars (addValue ev2 (eval ex1))
  case result of
    VExpr expr var -> return (VExpr expr (vars ++ var))
    _ -> return result

eval (ECase e pe) = do
  ev <- eval e
  result <- evalPattern ev pe
  return result

eval (EData con es) = do
  vs <- evalEs es
  return $ VData con vs

initFunc :: [ADT] -> Map.Map String Expr -> Map.Map String Expr
initFunc adts map = foldl ins map adts
  where
    ins map (ADT t s) = foldl inslam map s
      where
        inslam map (s, ts) = Map.insert s (lsm ts 1 (lamexp s (length ts))) map
          where
            lsm [] _ exp = exp
            lsm (t:ts) k exp = lsm ts (k+1) (ELambda (show k, t) exp)
            lamexp s n = EData s [EVar (show (n + 1 - x)) | x <- [1..n]]

evalProgram :: Program -> Maybe Value
evalProgram (Program adts body) = evalStateT (eval body) $
  Context {value=Nothing, valueMap=Map.fromList [], funcMap = initFunc adts (Map.fromList[])} -- 可以用某种方式定义上下文，用于记录变量绑定状态

evalValue :: Program -> Result
evalValue p = case evalProgram p of
  Just (VBool b) -> RBool b
  Just (VInt i) -> RInt i
  Just (VChar c) -> RChar c
  _ -> RInvalid
