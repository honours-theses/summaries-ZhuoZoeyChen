open HolKernel Parse boolLib bossLib;
open arithmeticTheory;
open listTheory;
open PrelimsTheory;

val _ = new_theory "L";

(* ------------------
	      CBV LC
   ------------------ *)

Datatype:
	term = var num | app term term | lam term
End

(*
Coercion app : term >-> Funclass.
Coercion var : nat >-> term .

Notation "(λ  s )" := (lam s) (right associativity, at level 0).

Inductive abstraction : term -> Prop := isAbstraction s : abstraction (lam s).
Hint Constructors abstraction.

Instance term_eq_dec : eq_dec term.
Proof.
  intros s t; unfold dec; repeat decide equality.
Defined.
*)

Inductive abstraction:
	∀s. abstraction (lam s)
End

(* ------------------
	  Substitution
   ------------------ *)

Definition subst:
	subst s k u =
		case s of
			| var n => if (n = k) then u else (var n)
			| app s t => app (subst s k u) (subst t k u)
			| lam s => lam (subst s (SUC k) u)
End

(* ------------------
	   Reduction
   ------------------ *)


(* Reserved Notation "s  '≻L'  t" (at level 70). *)

Inductive stepL:
	(∀s t. stepL (app (lam s) (lam t)) (subst s 0 (lam t))) ∧
	(∀s t t'. stepL t t' ⇒ stepL (app (lam s) t) (app (lam s) t')) ∧
	(∀s s' t. stepL s s' ⇒ stepL (app s t) (app s' t))
End

(*
Notation "(≻L)" := stepL (at level 0).*)
(* workaround to prefere "x ≻ y" over "(≻) x y"*) (* Notation "s '≻L' t" := 0. *)
(*Notation "s '≻L' t" := (stepL s t).
*)

(*
Canonical Structure L_ARS := {| ARS_X := term ; ARS_R := stepL |}.

Hint Constructors stepL.
*)


Theorem stepL_funct:
	functional (stepL)
Proof
	rw[functional] >> pop_assum mp_tac >> qid_spec_tac `y'` >> pop_assum mp_tac >>
	MAP_EVERY qid_spec_tac [`y`, `x`] >> ho_match_mp_tac stepL_strongind >> rw[]
	>- (gvs[Once stepL_cases] >> gvs[Once stepL_cases])
	>- (pop_assum (strip_assume_tac o PURE_ONCE_REWRITE_RULE[stepL_cases]) >>
		gvs[] >> gvs[Once stepL_cases] >> gvs[Once stepL_cases])
	>> pop_assum (strip_assume_tac o PURE_ONCE_REWRITE_RULE[stepL_cases]) >> gvs[] >>
	qpat_x_assum `stepL (lam _) _` (strip_assume_tac o PURE_ONCE_REWRITE_RULE[stepL_cases]) >>
	gvs[]
QED

(*
Fixpoint redL s : option term :=
  match s with
  |  app (lam s) (lam t) => Some (subst s 0 (lam t))
  |  app (lam s) t => try t':= redL t in Some ((lam s) t')
  |  app s t => try s':= redL s in Some (s' t)
  | _ => None
  end.
*)
(*
Notation "'try' x ':='  t 'in' u":=
  (match t with Some x => u | None => None end)
    (at level 200, right associativity).
*)

Definition redL:
	redL s =
		case s of
			| app (lam s) (lam t) => SOME (subst s 0 (lam t))
			| app (lam s) t =>
				(case (redL t) of
					| SOME t' => SOME (app (lam s) t')
					| NONE => NONE)
			| app s t =>
				(case (redL s) of
					| SOME s' => SOME (app s' t)
					| NONE => NONE)
			| _ => NONE
End

Theorem stepL_computable:
	stepFunction stepL redL
Proof
	simp[stepFunction] >> ho_match_mp_tac redL_ind >> rw[] >> Cases_on `x`
	>- rw[redL, Once stepL_cases]
	>- (rw[] >> Cases_on `t`
		>- (rw[redL, Once stepL_cases] >> rw[redL, Once stepL_cases])
		>- (rw[Once redL] >> Cases_on `redL (app t' t0')` >> fs[] >> rw[Once stepL_cases])
		>> fs[] >> rw[] >> rw[Once redL] >> Cases_on `t0`
		>- (rw[redL, Once stepL_cases] >> rw[redL, Once stepL_cases])
		>- (fs[] >> rw[] >> Cases_on `redL (app t t0')`  >>
			fs[] >> rw[Once stepL_cases] >> rw[Once stepL_cases])
		>> fs[] >> rw[Once stepL_cases])
	>> rw[Once redL, Once stepL_cases]
QED

(*
Theorem stepL_computable: 
	stepFunction stepL redL 
Proof 
	simp[stepFunction] >>   ho_match_mp_tac redL_ind >>   rw[] >> 
	rw[Once redL] >>   rpt(BasicProvers.PURE_TOP_CASE_TAC >> gvs[]) >> 
	gvs[AllCaseEqs()] >>   rw[Once stepL_cases] >>   rw[Once stepL_cases] 
QED
*)

(* ------------------------------------
	   Bound & Closedness for Terms
   ------------------------------------ *)

Inductive boundL:
	(∀k n. n < k ⇒ boundL (var n) k) ∧
	(∀k s t. boundL s k ∧ boundL t k ⇒ boundL (app s t) k) ∧
	(∀k s. boundL s (SUC k) ⇒ boundL (lam s) k)
End

Definition closedL:
	closedL s = boundL s 0
End

(* ------------------
	   Reduction
   ------------------ *)

Inductive stuck:
	(∀x. stuck (var x)) ∧
	(∀s t. stuck s ⇒ stuck (app s t)) ∧
	(∀s t. stuck t ⇒ stuck (app (lam s) t) )
End

Theorem L_trichotomy:
	exactlyOneHolds
		[reducible stepL s
		 ; abstraction s
		 ; stuck s]
Proof
	rw[exactlyOneHolds] >> Cases_on `reducible stepL s` >> rw[noneHolds]
	>- fs[reducible, Once stepL_cases, Once abstraction_cases]
	>- (fs[reducible] >> pop_assum mp_tac >> MAP_EVERY qid_spec_tac [`x'`, `s`] >>
		ho_match_mp_tac stepL_strongind >> rw[]
		>- (rw[Once stuck_cases] >> rw[Once stuck_cases])
		>- (rw[Once stuck_cases] >> rw[Once stuck_cases])
		>> fs[Once stepL_cases] >> rw[Once stuck_cases])
	>> Cases_on `abstraction s` >> rw[]
	>- fs[Once abstraction_cases, Once stuck_cases] >>
	fs[reducible] >> Induct_on `s` >> rw[]
	>- gvs[Once stepL_cases, Once stuck_cases]
	>- (simp[Once stuck_cases] >>
		qpat_x_assum `∀x. ¬stepL _ _` (strip_assume_tac o ONCE_REWRITE_RULE[stepL_cases]) >>
		fs[] >> Cases_on `s` >> gvs[]
		>- rw[Once stuck_cases]
		>- fs[Once abstraction_cases]
		>> fs[Once abstraction_cases] >> rw[] >> Cases_on `∃s. s' = lam s` >> fs[] >>
		gvs[] >> metis_tac[])
	>> fs[Once abstraction_cases]
QED

Theorem stuck_normal:
	stuck s ⇒ ¬reducible stepL s
Proof
	`exactlyOneHolds
		[reducible stepL s
		 ; abstraction s
		 ; stuck s]` by simp[L_trichotomy] >>
	fs[exactlyOneHolds, noneHolds]
QED

val _ = export_theory ()

