module MMachine where

data Type = IntTy | BoolTy | FunTy Type Type
          deriving (Eq, Show)

data Expr = Num Int
          | Lit Bool
          | Plus Expr Expr
          | Minus Expr Expr
          | Less Expr Expr
          | Equal Expr Expr
          | Divide Expr Expr
          | If Expr Expr Expr
          | Apply Expr Expr
          | Recfun Type Type (Expr -> Expr -> Expr)
          | Tag String -- just for printing
          | TypeTag Type -- just for typechecking

data Value = IntV Int | BoolV Bool | FunV (Expr -> Expr -> Expr)

isAtom :: Expr -> Bool
isAtom (Num _) = True
isAtom (Lit _) = True
isAtom (Recfun _ _ _) = True
isAtom _ = False

step :: Expr -> Expr
step (Plus (Num a) (Num b)) = Num (a + b)
step (Plus (Num a) b) = Plus (Num a) (step b)
step (Plus a b) = Plus (step a) b
step (Minus (Num a) (Num b)) = Num (a - b)
step (Minus (Num a) b) = Minus (Num a) (step b)
step (Minus a b) = Minus (step a) b
step (Less (Num a) (Num b)) = Lit (a < b)
step (Less (Num a) b) = Less (Num a) (step b)
step (Less a b) = Less (step a) b
step (Equal (Num a) (Num b)) = Lit (a == b)
step (Equal (Num a) b) = Equal (Num a) (step b)
step (Equal a b) = Equal (step a) b
step (Divide (Num a) (Num b)) = Num (a `div` b)
step (Divide (Num a) b) = Divide (Num a) (step b)
step (Divide a b) = Divide (step a) b
step (If (Lit True) t e) = t
step (If (Lit False) t e) = e
step (If b t e) = If (step b) t e
step (Apply rec@(Recfun _ _ f) e2)
  | isAtom e2 = f rec e2
  | otherwise = Apply rec (step e2)
step (Apply e1 e2) = Apply (step e1) e2

runStep :: Expr -> Expr
runStep e
  | isAtom e  = e
  | otherwise = runStep (step e)

eval :: Expr -> Value
eval (Num n) = IntV n
eval (Lit b) = BoolV b
eval (Less a b) = let
    IntV x = eval a
    IntV y = eval b
 in BoolV (x < y)
eval (Equal  a b) = let
    IntV x = eval a
    IntV y = eval b
 in BoolV (x == y)
eval (Plus a b) = let
    IntV x = eval a
    IntV y = eval b
 in IntV (x + y)
eval (If c t e) = let
    BoolV b = eval c
 in if b then eval t else eval e
eval (Recfun _ _ f) = FunV f
eval (Apply a b) = let
    FunV f = eval a
    arg    = eval b
 in eval (f (uneval (FunV f)) (uneval arg))

uneval :: Value -> Expr
uneval (IntV n) = Num n
uneval (BoolV b) = Lit b
uneval (FunV abs) = Recfun undefined undefined abs

prettyValue :: Value -> String
prettyValue = prettyPrint 0 . uneval

run :: Expr -> Value
run e = eval e

typeCheck :: Expr -> Type
typeCheck (Num n) = IntTy
typeCheck (Lit b) = BoolTy
typeCheck (Plus e1 e2) = case (typeCheck e1, typeCheck e2) of
                           (IntTy, IntTy) -> IntTy
                           _ -> error "type error"
typeCheck (Minus e1 e2) = case (typeCheck e1, typeCheck e2) of
                           (IntTy, IntTy) -> IntTy
                           _ -> error "type error"
typeCheck (Divide e1 e2) = case (typeCheck e1, typeCheck e2) of
                           (IntTy, IntTy) -> IntTy
                           _ -> error "type error"
typeCheck (Less e1 e2) = case (typeCheck e1, typeCheck e2) of
                           (IntTy, IntTy) -> BoolTy
                           _ -> error "type error"
typeCheck (Equal e1 e2) = case (typeCheck e1, typeCheck e2) of
                           (IntTy, IntTy) -> BoolTy
                           (BoolTy, BoolTy) -> BoolTy
                           _ -> error "type error"
typeCheck (If c t e) = case (typeCheck c, typeCheck t, typeCheck e) of
    (BoolTy, tt, te) -> if tt == te then tt else error "Branches have different types"
    _ -> error "if condition should be bool"
typeCheck (Apply e1 e2) = case (typeCheck e1, typeCheck e2) of
    (FunTy t1 t2, t1') -> if t1 == t1' then t2
                                       else error "Argument doesn't match function"
    _ -> error "Can't apply a non-function"
typeCheck (Recfun t1 t2 f) =
    if typeCheck (f (TypeTag (FunTy t1 t2)) (TypeTag t1)) == t2 then
        FunTy t1 t2
    else
        error "Function body doesn't match type signature"
typeCheck (TypeTag t) = t

prettyPrint :: Int -> Expr -> String
prettyPrint _ (Num n) = show n
prettyPrint n (Lit b) = show b
prettyPrint n (Plus e1 e2) = "(" ++ prettyPrint n e1 ++ " + " ++ prettyPrint n e2 ++ ")"
prettyPrint n (Minus e1 e2) = "(" ++ prettyPrint n e1 ++ " - " ++ prettyPrint n e2 ++ ")"
prettyPrint n (Less e1 e2) = "(" ++ prettyPrint n e1 ++ " < " ++ prettyPrint n e2 ++ ")"
prettyPrint n (Equal e1 e2) = "(" ++ prettyPrint n e1 ++ " == " ++ prettyPrint n e2 ++ ")"
prettyPrint n (Divide e1 e2) = "(" ++ prettyPrint n e1 ++ " / " ++ prettyPrint n e2 ++ ")"
prettyPrint n (If ec e1 e2)
   = "(if " ++ prettyPrint n ec
  ++ " then " ++ prettyPrint n e1
  ++ " else " ++ prettyPrint n e2
  ++ ")"
prettyPrint n (Apply e1 e2) = "(" ++ prettyPrint n e1 ++ " " ++ prettyPrint n e2 ++ ")"
prettyPrint n (Recfun t1 t2 f)
    = "(recfun " ++ funName
      ++ " :: (" ++ prettyPrintTy t1 ++ " -> " ++ prettyPrintTy t2 ++ ") "
      ++ argName ++ " = " ++ prettyPrint (n + 2) (f (Tag funName) (Tag argName))
      ++ ")"
  where
   funName = "f" ++ show n
   argName = "x" ++ show (n + 1)
prettyPrint n (Tag s) = s

prettyPrintTy :: Type -> String
prettyPrintTy IntTy = "Int"
prettyPrintTy BoolTy = "Bool"
prettyPrintTy (FunTy a b) = "(" ++ prettyPrintTy a ++ " -> " ++ prettyPrintTy b ++ ")"

divByFive :: Expr
divByFive = Recfun IntTy IntTy (\f x ->
       If (Less x (Num 5))
          (Num 0)
          (Plus (Num 1) (Apply f (Minus x (Num 5)))))

avg :: Expr
avg = Recfun IntTy (FunTy IntTy IntTy) (\f x ->
        Recfun IntTy IntTy (\f' y ->
            Divide (Plus x y) (Num 2)))