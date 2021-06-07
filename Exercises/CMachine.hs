module CMachine where

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

data Frame = PlusF1 Expr | PlusF2 Value
           | MinusF1 Expr | MinusF2 Value
           | LessF1 Expr | LessF2 Value
           | EqualF1 Expr | EqualF2 Value
           | DivideF1 Expr | DivideF2 Value
           | IfF Expr Expr
           | ApplyF1 Expr | ApplyF2 Value

type Stack = [Frame]

data State = (:>) Stack Expr
           | (:<) Stack Value

step :: State -> State
step (s :> Plus e1 e2) = (PlusF1 e2 : s) :> e1
step ((PlusF1 e2 : s) :< v1) = (PlusF2 v1 : s) :> e2
step ((PlusF2 (IntV v1) : s) :< (IntV v2)) = s :< IntV (v1 + v2)
step (s :> Minus e1 e2) = (MinusF1 e2 : s) :> e1
step ((MinusF1 e2 : s) :< v1) = (MinusF2 v1 : s) :> e2
step ((MinusF2 (IntV v1) : s) :< (IntV v2)) = s :< IntV (v1 - v2)
step (s :> Divide e1 e2) = (DivideF1 e2 : s) :> e1
step ((DivideF1 e2 : s) :< v1) = (DivideF2 v1 : s) :> e2
step ((DivideF2 (IntV v1) : s) :< (IntV v2)) = s :< IntV (v1 `div` v2)
step (s :> Less e1 e2) = (LessF1 e2 : s) :> e1
step ((LessF1 e2 : s) :< v1) = (LessF2 v1 : s) :> e2
step ((LessF2 (IntV v1) : s) :< (IntV v2)) = s :< BoolV (v1 < v2)
step (s :> Equal e1 e2) = (EqualF1 e2 : s) :> e1
step ((EqualF1 e2 : s) :< v1) = (EqualF2 v1 : s) :> e2
step ((EqualF2 (IntV v1) : s) :< (IntV v2)) = s :< BoolV (v1 == v2)
step ((EqualF2 (BoolV v1) : s) :< (BoolV v2)) = s :< BoolV (v1 == v2)
step (s :> Num n) = s :< IntV n
step (s :> If ec et ee) = (IfF et ee : s) :> ec
step ((IfF et ee : s) :< BoolV True) = s :> et
step ((IfF et ee : s) :< BoolV False) = s :> ee
step (s :> Recfun _ _ abs) = s :< FunV abs
step (s :> Apply e1 e2) = (ApplyF1 e2:s) :> e1
step ((ApplyF1 e2:s) :< fv) = (ApplyF2 fv:s) :> e2
step ((ApplyF2 )(FunV abs:s) :< v) = s :> abs (uneval (FunV abs)) (uneval v)

uneval :: Value -> Expr
uneval (IntV n) = Num n
uneval (BoolV b) = Lit b
uneval (FunV abs) = Recfun undefined undefined abs

prettyValue :: Value -> String
prettyValue = prettyPrint 0 . uneval

run :: Expr -> Value
run e = let
    initialState = [] :> e
    loop :: State -> Value
    loop ([] :< v) = v
    loop s = loop (step s)
  in loop initialState


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

dec :: Int -> Int
dec y = if (y > 0) then dec (y-1) else y

divByF :: Int -> Int
divByF x = if (x < 5) then 0 else (1 + divByF (x - 5))