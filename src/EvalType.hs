-- | 这是其中一种实现方式的代码框架。你可以参考它，或用你自己的方式实现，只要按需求完成 evalType :: Program -> Maybe Type 就行。
module EvalType where

import AST
import Control.Monad.State
import qualified Data.Map as Map

data Context = Context { -- 可以用某种方式定义上下文，用于记录变量绑定状态
  getVars :: Map.Map String Type
                       }
  deriving (Show, Eq)

type ContextState a = StateT Context Maybe a

isBool :: Expr -> ContextState Type
isBool e = do
  et <- eval e
  case et of
    TBool -> return TBool
    _ -> lift Nothing

isInt :: Expr -> ContextState Type
isInt e = do 
  et <- eval e 
  case et of
    TInt -> return TInt
    _ -> lift Nothing


isChar :: Expr -> ContextState Type
isChar e = do 
  et <- eval e 
  case et of
    TChar -> return TChar
    _ -> lift Nothing


isValue :: Expr -> Expr -> ContextState Type
isValue e1 e2 = do 
  et1 <- eval e1 
  case et1 of
    TChar -> isChar e2 >> return TChar
    TInt -> isInt e2 >> return TInt
    _ -> lift Nothing


isSameType :: Expr -> Expr -> ContextState Type
isSameType e1 e2 = do
  et1 <- eval e1
  case et1 of
    TChar -> isChar e2 >> return TBool
    TInt -> isInt e2 >> return TBool
    TBool -> isBool e2 >> return TBool
    _ -> lift Nothing


eval :: Expr -> ContextState Type
eval (EBoolLit _) = return TBool
eval (EIntLit _) = return TInt
eval (ECharLit _) = return TChar
eval (ENot e) = isBool e >> return TBool
eval (EAnd e1 e2) = isBool e1 >> isBool e2 >> return TBool
eval (EOr e1 e2) = isBool e1 >> isBool e2 >> return TBool
eval (EAdd  e1 e2) = isInt e1 >> isInt e2 >> return TInt
eval (ESub  e1 e2) = isInt e1 >> isInt e2 >> return TInt
eval (EMul  e1 e2) = isInt e1 >> isInt e2 >> return TInt
eval (EDiv  e1 e2) = isInt e1 >> isInt e2 >> return TInt
eval (EMod  e1 e2) = isInt e1 >> isInt e2 >> return TInt
eval (EEq  e1 e2) = isSameType e1 e2
eval (ENeq  e1 e2) = isSameType e1 e2
eval (ELt  e1 e2) = isValue e1 e2 >> return TBool
eval (EGt  e1 e2) = isValue e1 e2 >> return TBool
eval (EGe  e1 e2) = isValue e1 e2 >> return TBool
eval (ELe  e1 e2) = isValue e1 e2 >> return TBool
eval (EIf  e1 e2 e3) = isBool e1 >> isSameType e2 e3 >> eval e2
eval (ELambda (pn, pt) e) = do
  ctx <- get
  put (Context $ Map.insert pn pt (getVars ctx))
  res <- eval e
  put ctx
  return (TArrow pt res)
eval (ELet (n, e1) e2) = do
  ctx <- get
  t <- eval e1
  put (Context $ Map.insert n t (getVars ctx))
  res <- eval e2
  put ctx
  return res 
eval (ELetRec f (x, tx) (e1, ty) e2) = do 
  ctx <- get
  put (Context $ (Map.insert x tx $ Map.insert f (TArrow tx ty) (getVars ctx)))
  tmp <- eval e1
  put ctx
  if tmp == ty then do
    ctx <- get
    put (Context $ Map.insert f (TArrow tx ty) (getVars ctx))
    res <- eval e2
    put ctx
    return res
  else lift Nothing
eval (EVar s) = do
  ctx <- get 
  case (getVars ctx) Map.!? s of
    Just x -> return x
    _ -> lift Nothing
eval (EApply e1 e2) = do
  et1 <- eval e1
  et2 <- eval e2
  case et1 of
    TArrow x y -> if x == et2 then return y else lift Nothing
    _ -> lift Nothing
eval _ = undefined


evalType :: Program -> Maybe Type
evalType (Program adts body) = evalStateT (eval body) $
  Context (Map.fromList []) -- 可以用某种方式定义上下文，用于记录变量绑定状态
