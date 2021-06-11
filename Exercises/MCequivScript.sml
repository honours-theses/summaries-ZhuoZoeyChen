open HolKernel Parse boolLib bossLib;

val _ = new_theory "MCequiv";

Datatype:
	type = IntTy | BoolTy | FunTy type type
End

(*
Datatype:
	expr =  Num num | Lit bool
		  | Plus expr expr | Minus expr expr
          | Less expr expr | Equal expr expr
          | Divide expr expr | If expr expr expr
          | Apply expr expr
          | Lam
          | Var num
          | Recfun type type (expr -> expr -> expr)
End
*)

Datatype:
	expr =  Lit bool | Equal expr expr
		  | If expr expr expr
          | Apply expr expr
          | Lam expr
          | Var num
End

val _ = export_rewrites ["expr_size_def"]

(*
  -----------------
  --- M Machine ---
  -----------------
*)

Definition isAtom:
(*	(isAtom (Num _) ⇔ T) ∧ *)
	(isAtom (Lit _) ⇔ T) ∧
(*	isAtom (Recfun _ _ _) ∧ *)
	(isAtom (Var _) ⇔ T) ∧
	(isAtom (Lam _) ⇔ T) ∧
	(isAtom _ ⇔ F)
End

Definition isVar:
	(isVar (Var _) ⇔ T) ∧
	(isVar _ ⇔ F)
End

(*
Definition M_step:
	M_step (Plus (Num a) (Num b)) = Num (a + b) ∧
	M_step (Plus (Num a) b) = Plus (Num a) (M_step b) ∧
	M_step (Plus a b) = Plus (M_step a) b ∧
	M_step (Minus (Num a) (Num b)) = Num (a - b) ∧
	M_step (Minus (Num a) b) = Minus (Num a) (M_step b) ∧
	M_step (Minus a b) = Minus (M_step a) b ∧
	M_step (Less (Num a) (Num b)) = Lit (a < b) ∧
	M_step (Less (Num a) b) = Less (Num a) (M_step b) ∧
	M_step (Less a b) = Less (M_step a) b ∧
	M_step (Equal (Num a) (Num b)) = Lit (a = b) ∧
	M_step (Equal (Num a) b) = Equal (Num a) (M_step b) ∧
	M_step (Equal a b) = Equal (M_step a) b ∧
	M_step (Divide (Num a) (Num b)) = Num (a `div` b) ∧
	M_step (Divide (Num a) b) = Divide (Num a) (M_step b) ∧
	M_step (Divide a b) = Divide (M_step a) b ∧
	M_step (If (Lit True) t e) = t ∧
	M_step (If (Lit False) t e) = e ∧
	M_step (If b t e) = If (M_step b) t e ∧
		M_step (Apply rec@(Recfun _ _ f) e2)
	  | isAtom e2 = f rec e2
	  | otherwise = Apply rec (M_step e2)  ∧
	M_step (Apply e1 e2) = Apply (M_step e1) e2
End
*)

Definition subst:
	subst e1 e2 n = if (isAtom e1 ∧ ¬(isVar e1)) then e1 else case e1 of
		Equal a b => Equal (subst a e2 n) (subst b e2 n)
	  | If g a b => If (subst g e2 n) (subst a e2 n) (subst b e2 n)
	  | Apply a b => Apply (subst a e2 n) (subst b e2 n)
	  | Lam e => Lam (subst e e2 (n+1))
	  | Var m => if (n = m) then e2 else (Var m)
End


Definition M_step:
(*	M_step (Plus (Num a) (Num b)) = Num (a + b) ∧
	M_step (Plus (Num a) b) = Plus (Num a) (M_step b) ∧
	M_step (Plus a b) = Plus (M_step a) b ∧
	M_step (Minus (Num a) (Num b)) = Num (a - b) ∧
	M_step (Minus (Num a) b) = Minus (Num a) (M_step b) ∧
	M_step (Minus a b) = Minus (M_step a) b ∧
	M_step (Less (Num a) (Num b)) = Lit (a < b) ∧
	M_step (Less (Num a) b) = Less (Num a) (M_step b) ∧
	M_step (Less a b) = Less (M_step a) b ∧
	M_step (Equal (Num a) (Num b)) = Lit (a = b) ∧
	M_step (Equal (Num a) b) = Equal (Num a) (M_step b) ∧
	M_step (Equal a b) = Equal (M_step a) b ∧
	M_step (Divide (Num a) (Num b)) = Num (a `div` b) ∧
	M_step (Divide (Num a) b) = Divide (Num a) (M_step b) ∧
	M_step (Divide a b) = Divide (M_step a) b ∧ *)
	M_step (Equal (Lit a) (Lit b)) = Lit (a = b) ∧
	M_step (Equal (Lit a) b) = Equal (Lit a) (M_step b) ∧
	M_step (Equal a b) = Equal (M_step a) b ∧
	M_step (If (Lit True) t e) = t ∧
	M_step (If (Lit False) t e) = e ∧
	M_step (If b t e) = If (M_step b) t e ∧
	(M_step (Apply (Lam e) e2) =
		if isAtom e2 then
			subst e e2 0
		else
			Apply (Lam e) (M_step e2))	∧
	M_step (Apply e1 e2) = Apply (M_step e1) e2
(*	M_step (Apply rec@(Recfun _ _ f) e2)
	  | isAtom e2 = f rec e2
	  | otherwise = Apply rec (M_step e2)  ∧
	M_step (Apply e1 e2) = Apply (M_step e1) e2
*)
End

Theorem equal_step_size:
	∀e1 e2. expr_size (M_step (Equal e1 e2)) < expr_size e1 + (expr_size e2 + 1)
Proof
	Cases_on `e1` >>
QED

Definition run_M_step:
	run_M_step e =
		if isAtom e
			then e
		else run_M_step (M_step e)
End
Termination
	WF_REL_TAC `measure expr_size` >>
	Induct_on `e` >> rw[isAtom]
	>- (rename [`expr_size (M_step (Equal e1 e2)) < _`] >>
		rw[] >> Cases_on `e1` >> Cases_on `e2` >> rw[M_step])
End

(*
Datatype:
	M_machine = <|
		Q: state set;
		I: state set;
		F: state set;
		tr: state -> state
	|>
End
*)

(*
Definition subst:
	subst e [] _ = e ∧
	subst (Num n) (x1, y1)::t rec_subed = if (n == x1) then (subst (Num y1) t) else (subst (Num n) t) ∧
	subst (Lit n) (x1, y1)::t rec_subed = if (n == x1) then (subst (Lit y1) t) else (subst (Lit n) t) ∧
	subst (Plus e1 e2) lst rec_subed = Plus (subst e1 lst) (subst e2 lst) rec_subed ∧
	subst (If e1 e2 e3) lst rec_subed = If (subst e1 lst) (subst e2 lst) (subst e3 lst) rec_subed ∧
	subst (Apply e1 e2) lst rec_subed = Apply (subst e1 lst) (subst e2 lst) rec_subed ∧

	subst (Recfun f x e) (x1, y1)::t rec_subed = if (not rec_subed) then subst (subst e [(x1, y1)] true) t false
End
*)

(*
Definition M_rules:
	M_rules M (Num n) = IntV n ∧
	M_rules M (Lit b) = BoolV b ∧
	(M_rules M e1 e1' ⇒
		(	M_rules M (Plus e1 e2) (Plus e1' e2) ∧
			M_rules M (If e1 e2 e3) (If e1' e2 e3) ∧
			M_rules M (Apply e1 e2) (Apply e1' e2) ∧
			M_rules M (Apply (Recfun f x e) e1) (Apply (Recfun f x e) e1')
		)) ∧
	(M_rules M (If (Lit True) e2 e3) e2) ∧
			M_rules M (If (Lit False) e2 e3) e3 ∧
	(v ∈ M.F ⇒ M_rules M (Apply (Recfun f x e) v) (subst e [(x, v), (f, Recfun f x e)] false))
End
*)


(*
  -----------------
  --- C Machine ---
  -----------------
*)

Datatype:
	value = IntV int | BoolV bool | FunV (expr -> expr -> expr)
End

Datatype:
	frame =  PlusF1 expr | PlusF2 value
           | MinusF1 expr | MinusF2 value
           | LessF1 expr | LessF2 value
           | EqualF1 expr | EqualF2 value
           | DivideF1 expr | DivideF2 value
           | IfF expr expr
           | ApplyF1 expr | ApplyF2 value
End

Datatype:
	stack = [frame]
End

Datatype:
 State = Push Stack expr | Eval Stack value
End

Definition step:
	step (Push s Plus e1 e2) = Push (PlusF1 e2 : s) e1 ∧
	step (Eval (PlusF1 e2 : s) v1) = Push (PlusF2 v1 : s) EqualF2 ∧
	step (Eval (PlusF2 (IntV v1) : s) (IntV v2)) = Eval s IntV (v1 + v2)
	step (Push s Minus e1 e2) = Push (MinusF1 e2 : s) e1
	step (Eval (MinusF1 e2 : s) v1) = Push (MinusF2 v1 : s) e2
	step (Eval (MinusF2 (IntV v1) : s) (IntV v2)) = Eval s IntV (v1 - v2)
	step (Push s Divide e1 e2) = Push (DivideF1 e2 : s) e1
	step (Eval (DivideF1 e2 : s) v1) = Push (DivideF2 v1 : s) e2
	step (Eval (DivideF2 (IntV v1) : s) (IntV v2)) = Eval s IntV (v1 `div` v2)
	step (Push s Less e1 e2) = Push (LessF1 e2 : s) e1
	step (Eval (LessF1 e2 : s) v1) = Push (LessF2 v1 : s) e2
	step (Eval (LessF2 (IntV v1) : s) (IntV v2)) = Eval s BoolV (v1 < v2)
	step (Push s Equal e1 e2) = Push (EqualF1 e2 : s) e1
	step (Eval (EqualF1 e2 : s) v1) = Push (EqualF2 v1 : s) e2
	step (Eval (EqualF2 (IntV v1) : s) (IntV v2)) = Eval s BoolV (v1 == v2)
	step (Eval (EqualF2 (BoolV v1) : s) (BoolV v2)) = Eval s BoolV (v1 == v2)
	step (Push s Num n) = Eval s IntV n
	step (Push s If ec et ee) = Push (IfF et ee : s) ec
	step (Eval (IfF et ee : s) BoolV True) = Push s et
	step (Eval (IfF et ee : s) BoolV False) = Push s ee
	step (Push s Recfun _ _ abs) = Eval s FunV abs
	step (Push s Apply e1 e2) = Push (ApplyF1 e2:s) e1
	step (Eval (ApplyF1 e2:s) fv) = Push (ApplyF2 fv:s) e2
	step (Eval (ApplyF2 (FunV abs):s) v) = Push s abs (uneval (FunV abs)) (uneval v)
End

Definition uneval:
	uneval :: value -> expr
	uneval (IntV n) = Num n
	uneval (BoolV b) = Lit b
	uneval (FunV abs) = Recfun undefined undefined abs
End

prettyvalue :: value -> String
prettyvalue = prettyPrint 0 . uneval

run :: expr -> value
run e = let
    initialState = [] :> e
    loop :: State -> value
    loop ([] :< v) = v
    loop s = loop (step s)
  in loop initialState

val _ = export_theory ()