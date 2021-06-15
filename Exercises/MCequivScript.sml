open HolKernel Parse boolLib bossLib;
open basicSizeTheory;

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
          | Lam type expr
          | Var num
          | Recfun type type (expr -> expr -> expr)
End
*)

Datatype:
	expr =  Lit bool | Equal expr expr
		  | If expr expr expr
          | Apply expr expr
          | Lam type expr (* TODO: could change type to expr using typetag *)
          | Var type num (* TODO: remove type here and add a context that carries the mapping from the variables/numbers to their types *)
          | TypeTag type
End

val _ = export_rewrites ["expr_size_def"]

(*
  -----------------
  --- M Machine ---
  -----------------
*)

Definition isVal:
	(isVal (Lit _) ⇔ T)
End

Definition isAtom:
(*	(isAtom (Num _) ⇔ T) ∧ *)
	(isAtom (Lit _) ⇔ T) ∧
(*	isAtom (Recfun _ _ _) ∧ *)
	(isAtom (Var _ _) ⇔ T) ∧
	(isAtom (Lam _ _ _) ⇔ T) ∧
	(isAtom _ ⇔ F)
End

Theorem non_atoms_not_isAtom[simp]:
	¬(isAtom (Equal e1 e2)) ∧
	¬(isAtom (If e1 e2 e3)) ∧
	¬(isAtom (Apply e1 e2))
Proof
	simp[isAtom]
QED

(*
Theorem litIsAtom[simp]:
	isAtom (Lit a)
Proof
	simp[isAtom]
QED

Theorem varIsAtom[simp]:
	isAtom (Var a)
Proof
	simp[isAtom]
QED
*)


Definition isVar:
	(isVar (Var _ _) ⇔ T) ∧
	(isVar _ ⇔ F)
End

Theorem non_var_not_isVar[simp]:
	¬(isVar (Equal e1 e2)) ∧
	¬(isVar (If e1 e2 e3)) ∧
	¬(isVar (Apply e1 e2)) ∧
	¬(isVar (Lam t1 t2 e1)) ∧
	¬(isVar (Lit b))
Proof
	rw[isVar]
QED

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
(* TODO: use Lit directly *)
	subst e1 e2 n = if (isVal e1) then e1 else case e1 of
		Equal a b => Equal (subst a e2 n) (subst b e2 n)
	  | If g a b => If (subst g e2 n) (subst a e2 n) (subst b e2 n)
	  | Apply a b => Apply (subst a e2 n) (subst b e2 n)
	  | Lam t1 t2 e => Lam t1 t2 (subst e e2 (n+1))
	  | Var t m => if (n = m) then e2 else (Var t m)
End

(* (\x (\y. xy)) (Var 0) *)
(* TODO:
	1. check capture avoiding substitution
	2. check higher order abstract syntax *)

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
	M_step (Lit e) = Lit e ∧
	M_step (Var t v) = Var t v ∧
	M_step (Lam t1 t2 e) = Lam t1 t2 e ∧
	M_step (Equal (Lit a) (Lit b)) = Lit (a = b) ∧
(*	M_step (Equal (Lit a) (Lam b)) = Lit False ∧
	M_step (Equal (Lit a) (Var t b)) = Lit False ∧ *)
	M_step (Equal (Lit a) b) = Equal (Lit a) (M_step b) ∧
(*	M_step (Equal (Lam a) (Lit b) = Lit False *)
	M_step (Equal a b) = Equal (M_step a) b ∧
	M_step (If (Lit True) t e) = t ∧
	M_step (If (Lit False) t e) = e ∧
	M_step (If b t e) = If (M_step b) t e ∧
	(M_step (Apply (Lam t1 t2 e) e2) =
		if isAtom e2 then
			subst e e2 0
		else
			Apply (Lam t1 t2 e) (M_step e2))	∧
	M_step (Apply e1 e2) = Apply (M_step e1) e2
(*	M_step (Apply rec@(Recfun _ _ f) e2)
	  | isAtom e2 = f rec e2
	  | otherwise = Apply rec (M_step e2)  ∧
	M_step (Apply e1 e2) = Apply (M_step e1) e2
*)
End

(* TODO *)
(*
	e = M_step (Equal e1 e2) ==>
	?b. e = Lit b \/
	?e2'. e = ...
*)

Theorem M_step_equal_bool_or_equal:
∀e1 e2. (∃b. M_step (Equal e1 e2) = Lit b) ∨
		(∃e2'. M_step (Equal e1 e2) = Equal e1 e2') ∨
		(∃e1'. M_step (Equal e1 e2) = Equal e1' e2)
Proof
	ho_match_mp_tac M_step_ind >> rw[M_step] >>
	Cases_on `e2` >> rw[M_step]
QED

(* TODO; check isabelle/hol: induct cases gives all theorems like above *)

Theorem equal_step_size:
	∀e1 e2. expr_size (M_step (Equal e1 e2)) < expr_size e1 + (expr_size e2 + 1)
Proof
	Cases_on `e1` >>
QED

(*
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
		rw[] >> Cases_on `e1` >> Cases_on `e2` >> fs[M_step, bool_size_def]
		>- ())
End
*)

(* need to progress + preservation *)

(* expr -> SOME type *)
Definition typeCheck:
(*	typeCheck (Num n) = IntTy ∧ *)
	typeCheck (Lit b) = SOME BoolTy ∧
(*	typeCheck (Plus e1 e2) = case (typeCheck e1, typeCheck e2) of
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
	                           _ -> error "type error" *)
	(typeCheck (Equal e1 e2) = case (typeCheck e1, typeCheck e2) of
	                        (*   (IntTy, IntTy) -> BoolTy *)
	                         |  (SOME BoolTy, SOME BoolTy) => SOME BoolTy
	                         |  _ => NONE (* error "type error" *)) ∧
	(typeCheck (If c t e) = case (typeCheck c, typeCheck t, typeCheck e) of
	   | (SOME BoolTy, tt, te) => if tt = te then tt else NONE (* error "Branches have different types" *)
	   | _ => NONE (* error "if condition should be bool" *)) ∧
	(typeCheck (Apply e1 e2) = case (typeCheck e1, typeCheck e2) of
	   | (SOME (FunTy t1 t2), SOME t1') => if t1 = t1' then (SOME t2)
	                                  else NONE (* error "Argument doesn't match function" *)
	   | _ => NONE) ∧ (* error "Can't apply a non-function" *)
	typeCheck (Lam t1 t2 e) = SOME (FunTy t1 t2) ∧ (* error "Function body doesn't match type signature" *)
	typeCheck (Var t n) = SOME t ∧
	typeCheck (TypeTag t) = SOME t
End


Theorem typeCheck_equal_bool_or_none:
∀e1 e2.	typeCheck (Equal e1 e2) = SOME BoolTy ∨
		typeCheck (Equal e1 e2) = NONE
Proof
	rw[] >> Cases_on `typeCheck e1` >> Cases_on `typeCheck e2` >> gs[typeCheck]
	>> Cases_on `x` >> gs[] >> Cases_on `x'` >> gs[]
QED

Theorem M_progress:
	∀e t. typeCheck e = SOME t ⇒ isAtom e ∨ ∃e'. M_step e = e'
Proof
	rw[M_step]
QED

Theorem M_preservation:
	∀e e' t. typeCheck e = SOME t ∧ M_step e = e' ⇒ typeCheck e' = SOME t
Proof
	Induct_on `e` >> rw[M_step] >> rw[]
	>- (Cases_on `e` >> Cases_on `e'` >> rw[M_step]
		>- rw[typeCheck]
		>- (fs[typeCheck] >> Cases_on `typeCheck e` >> Cases_on `typeCheck e0` >> gs[]
			>- (Cases_on `x` >> gs[])
			>> Cases_on `x` >> gs[] >> Cases_on `x'` >> gs[] >>
			Cases_on `t''` >> gs[]
			>- (rename [`typeCheck (M_step (Equal e1 e2)) = SOME IntTy`] >>
				`(∃b. M_step (Equal e1 e2) = Lit b) ∨
			     (∃e2'. M_step (Equal e1 e2) = Equal e1 e2') ∨
			      ∃e1'. M_step (Equal e1 e2) = Equal e1' e2`
			      	by metis_tac[M_step_equal_bool_or_equal]
			    >- fs[typeCheck] >> gs[]
		    	>> rename [`typeCheck (Equal a b) = SOME IntTy`] >>
		        `typeCheck (Equal a b) = SOME BoolTy ∨ typeCheck (Equal a b) = NONE`
		        	by metis_tac[typeCheck_equal_bool_or_none] >> fs[])
			>> rename [`typeCheck (M_step (Equal e1 e2)) = SOME (FunTy t1 t2)`] >>
			`(∃b. M_step (Equal e1 e2) = Lit b) ∨
		     (∃e2'. M_step (Equal e1 e2) = Equal e1 e2') ∨
		      ∃e1'. M_step (Equal e1 e2) = Equal e1' e2`
			      	by metis_tac[M_step_equal_bool_or_equal]
			>- fs[typeCheck] >> gs[]
	    	>> rename [`typeCheck (Equal a b) = SOME (FunTy t1 t2)`] >>
	        `typeCheck (Equal a b) = SOME BoolTy ∨ typeCheck (Equal a b) = NONE`
	        	by metis_tac[typeCheck_equal_bool_or_none] >> fs[])
		>- ()
		)
QED

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