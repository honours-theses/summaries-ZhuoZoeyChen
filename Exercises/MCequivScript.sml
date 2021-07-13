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
          | Lam expr expr
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

Definition isVal:
	(isVal (Lit _) ⇔ T)
End

Definition isAtom:
(*	(isAtom (Num _) ⇔ T) ∧ *)
	(isAtom (Lit _) ⇔ T) ∧
(*	isAtom (Recfun _ _ _) ∧ *)
	(isAtom (Var _) ⇔ T) ∧
	(isAtom (Lam _) ⇔ T) ∧
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
	(isVar (Var _) ⇔ T) ∧
	(isVar _ ⇔ F)
End

Theorem non_var_not_isVar[simp]:
	¬(isVar (Equal e1 e2)) ∧
	¬(isVar (If e1 e2 e3)) ∧
	¬(isVar (Apply e1 e2)) ∧
	¬(isVar (Lam e1)) ∧
	¬(isVar (Lit b))
Proof
	rw[isVar]
QED


Definition shift_up_one:
	shift_up_one e = case e of
		  Var m => Var (m+1)
		| _ => e
End

Definition shift_down_one_bounded:
	shift_down_one_bounded e = case e of
		  Var m => if (m > 0) then Var (m-1) else e
		| _ => e
End


Definition subst:
	subst e1 e2 n = case e1 of
		Lit b => Lit b
	  | Equal a b => Equal (subst a e2 n) (subst b e2 n)
	  | If g a b => If (subst g e2 n) (subst a e2 n) (subst b e2 n)
	  | Apply a b => Apply (subst a e2 n) (subst b e2 n)
	  | Lam e => Lam (subst e (shift_up_one e2) (n+1))
	  | Var m => if (n = m) then e2 else (Var m)
End

(* (\x (\y. xy)) (Var 0) *)
(* (\. (\. (Var 1) (Var 0)))) (Var 0) *)


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
	M_step (Divide a b) = Divide (M_step a) b ∧
*)

(*	M_step (Apply rec@(Recfun _ _ f) e2)
	  | isAtom e2 = f rec e2
	  | otherwise = Apply rec (M_step e2)  ∧
	M_step (Apply e1 e2) = Apply (M_step e1) e2
*)

Inductive M_step_inductive:
	(∀e. M_step_inductive (Lit e) (Lit e)) ∧
	(∀v. M_step_inductive (Var v) (Var v)) ∧
	(∀e. M_step_inductive (Lam e) (Lam e)) ∧
	(∀a b. M_step_inductive (Equal (Lit a) (Lit b)) (Lit (a = b))) ∧
	(∀a b b'.
		M_step_inductive b b'
		⇒ M_step_inductive (Equal (Lit a) b) (Equal (Lit a) b')) ∧
	(∀a b a'.
		M_step_inductive a a'
		⇒ M_step_inductive (Equal a b) (Equal a' b)) ∧
	(∀t e. M_step_inductive (If (Lit True) t e) t) ∧
	(∀t e. M_step_inductive (If (Lit False) t e) e) ∧
	(∀b t e b'.
		M_step_inductive b b'
		⇒ M_step_inductive (If b t e) (If b' t e)) ∧
	(∀e e2.
		isAtom e2
		⇒ M_step_inductive (Apply (Lam e) e2)
						   (shift_down_one_bounded (subst e (shift_up_one e2) 0))) ∧
	(∀e e2 e2'.
		M_step_inductive e2 e2'
		⇒ M_step_inductive (Apply (Lam e) e2) (Apply (Lam e) e2')) ∧
	(∀e1 e2 e1'.
		M_step_inductive e1 e1'
		⇒ M_step_inductive (Apply e1 e2) (Apply e1' e2))
End


(* TODO *)
(*
	e = M_step (Equal e1 e2) ==>
	?b. e = Lit b \/
	?e2'. e = ...
*)

(*
Theorem M_step_equal_bool_or_equal:
∀e1 e2. (∃b. M_step (Equal e1 e2) = Lit b) ∨
		(∃e2'. M_step (Equal e1 e2) = Equal e1 e2') ∨
		(∃e1'. M_step (Equal e1 e2) = Equal e1' e2)
Proof
	ho_match_mp_tac M_step_ind >> rw[M_step] >>
	Cases_on `e2` >> rw[M_step]
QED
*)

(*
Theorem equal_step_size:
	∀e1 e2. expr_size (M_step (Equal e1 e2)) < expr_size e1 + (expr_size e2 + 1)
Proof
	Cases_on `e1` >>
QED
*)

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


(*	typeCheck (Num n) = IntTy ∧ *)
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
	                           _ -> error "type error"
*)

Inductive typeChecking:
	(∀Γ b. typeChecking Γ (Lit b) BoolTy) ∧
	(∀Γ n. (n < LENGTH Γ) ⇒ typeChecking Γ (Var n) (EL n Γ)) ∧
	(∀Γ e1 e2.
	    typeChecking Γ e1 BoolTy ∧
	     typeChecking Γ e2 BoolTy
		 ⇒ typeChecking Γ (Equal e1 e2) BoolTy) ∧
	(∀Γ b t e tt.
	    typeChecking Γ b BoolTy ∧
	    typeChecking Γ t tt ∧
	    typeChecking Γ e tt
		⇒ typeChecking Γ (If b t e) tt) ∧
	(∀Γ e1 e2 t1 t2.
		typeChecking Γ e1 (FunTy t1 t2) ∧
		typeChecking Γ e2 t1
		⇒ typeChecking Γ (Apply e1 e2) t2) ∧
	(∀Γ e t1 t2.
	    typeChecking (t1::Γ) e t2 (* extend Γ and prove e has type t2 *)
		⇒ (typeChecking Γ (Lam e) (FunTy t1 t2)))
End

(* Γ, x:t1 |- s:t2 *)
(* Γ |- \x. s : FunTy t1 t2 *)

(*
Theorem typeCheck_equal_bool_or_none:
∀Γ e1 e2.	typeCheck Γ (Equal e1 e2) = SOME BoolTy ∨
			typeCheck Γ (Equal e1 e2) = NONE
Proof
	rw[] >> Cases_on `typeCheck Γ e1` >> Cases_on `typeCheck Γ e2` >> gs[typeCheck]
	>> Cases_on `x` >> gs[] >> Cases_on `x'` >> gs[]
QED
*)

(*
Theorem M_progress:
	∀Γ e t. typeCheck Γ e = SOME t ⇒ isAtom e ∨ ∃e'. M_step e = e'
Proof
	rw[M_step]
QED
*)

Theorem M_progress:
	∀Γ e t. typeChecking Γ e t ⇒ isAtom e ∨ ∃e'. M_step_inductive e = e'
Proof
	rw[M_step_inductive_rules]
QED

(*
Theorem M_preservation:
	∀Γ e e' t. typeCheck Γ e = SOME t ∧ M_step e = e' ⇒ typeCheck Γ e' = SOME t
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
*)

Theorem lit_m_step_lit:
	∀b e. M_step_inductive (Lit b) e ⇒ e = Lit b
Proof
	Induct_on `M_step_inductive` >> gs[]
QED

Theorem var_m_step_var:
	∀n e. M_step_inductive (Var n) e ⇒ e = Var n
Proof
	Induct_on `M_step_inductive` >> gs[]
QED

Theorem lam_m_step_lam:
	∀e e'. M_step_inductive (Lam e) e' ⇒ e' = (Lam e)
Proof
	Induct_on `M_step_inductive` >> gs[]
QED

Theorem m_step_equal:
	∀e1 e2 e.
		M_step_inductive (Equal e1 e2) e
			⇒ ((∃b. e = Lit b) ∨
			   (∃e2'. M_step_inductive e2 e2' ∧ e = Equal e1 e2') ∨
			   (∃e1'. M_step_inductive e1 e1' ∧ e = Equal e1' e2))
Proof
	Induct_on `M_step_inductive` >> gs[]
QED

Theorem m_step_if:
	∀b t e tt.
		M_step_inductive (If b t e) tt
			⇒ ( tt = t ∨
				tt = e ∨
			   (∃b'. M_step_inductive b b' ∧ tt = (If b' t e)))
Proof
	Induct_on `M_step_inductive` >> gs[]
QED

Theorem m_step_apply:
	∀e1 e2 e.
		M_step_inductive (Apply e1 e2) e
			⇒ ((isAtom e2 ∧ ∃t le. e1 = Lam le ∧ e = shift_down_one_bounded (subst le (shift_up_one e2) 0)) ∨
			   (∃e2'. M_step_inductive e2 e2' ∧ e = Apply e1 e2') ∨
			   (∃e1'. M_step_inductive e1 e1' ∧ e = Apply e1' e2))
Proof
	Induct_on `M_step_inductive` >> gs[]
QED

Theorem type_lam_impl_type_e:
	∀Γ e t1 t2.
		typeChecking Γ (Lam e) (FunTy t1 t2) ⇒
	    typeChecking (t1::Γ) e t2
Proof
	Induct_on `typeChecking` >> gs[]
QED

Theorem typeChecking_var:
	(∀Γ n. (n < LENGTH Γ) ⇒ typeChecking Γ (Var n) (EL n Γ)) ∧
Proof
QED

Theorem subst_reserves_type:
	∀Γ e t1 t2 e2.
		typeChecking (t1::Γ) e t2 ∧ typeChecking Γ e2 t1 ⇒ isAtom e2 ⇒
		typeChecking Γ (shift_down_one_bounded (subst e (shift_up_one e2) 0)) t2
Proof
	Induct_on `typeChecking` >> rw[]
	>- rw[subst, typeChecking_rules, shift_down_one_bounded]
	>- (rw[subst, typeChecking_rules, shift_up_one, shift_down_one_bounded]
		>- (Cases_on `e2` >> rw[])
		>> `n - 1 < LENGTH Γ` by (Induct_on `Γ` >> simp[])
		>> `typeChecking Γ (Var (n - 1)) (EL (n - 1) Γ)` by simp[typeChecking_rules]
		>> Cases_on `n` >> gs[])
	>- (rw[shift_up_one, shift_down_one_bounded, Once subst, typeChecking_rules]
		>> Cases_on `e2` >> rw[Once subst] >> )
QED

Theorem M_preservation_2:
	∀Γ e e' t. typeChecking Γ e t ∧ M_step_inductive e e' ⇒ typeChecking Γ e' t
Proof
	Induct_on `typeChecking` >> rw[M_step_inductive_rules, typeChecking_rules]
	>- metis_tac[lit_m_step_lit, typeChecking_rules]
	>- metis_tac[var_m_step_var, typeChecking_rules]
	>- (drule m_step_equal >> metis_tac[typeChecking_rules])
	>- (drule m_step_if >> metis_tac[typeChecking_rules])
	>- (rename[`M_step_inductive (Apply e1 e2) e`] >>
		drule m_step_apply >> rw[]
		>- (rename [`typeChecking Γ (Lam e) (FunTy t1 t2)`] >>
			drule type_lam_impl_type_e >> rw[] >>
			)
		>> metis_tac[typeChecking_rules])
	>> metis_tac[lam_m_step_lam, typeChecking_rules]
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