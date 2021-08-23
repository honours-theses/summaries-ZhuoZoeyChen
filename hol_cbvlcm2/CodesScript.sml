open HolKernel Parse boolLib bossLib;
open arithmeticTheory;
open listTheory;
open PrelimsTheory;
open ProgramsTheory;

val _ = new_theory "Codes";

(* ---------------------
    	   Codes
   --------------------- *)

Datatype:
  Com = retC | varC num | appC | lamC 'a
End

(*

Inductive Com PA:= retC| varC (n:nat) | appC | lamC (p:PA).
Arguments retC {_}.
Arguments varC {_} _.
Arguments lamC {_} _.
Arguments appC {_}.
*)

Type Code = ``:('a Com) list``;

Type PA = ``:num``;

Datatype:
	code =
		<|
    	   phi  : 'b -> 'a -> ('a Com) option;
    	   inc  : 'a -> 'a
    	|>
End

(*
Datatype:
	code =
		<|
    	   phi  : Com list -> num -> Com option;
    	   inc  : num -> num
    	|>
End
*)

Definition codeImpl:
	codeImpl =
		<|	phi := (λC p.
		      case (nth_error p C) of
		      | SOME (lamC k) => SOME (lamC (p+k))
		      | SOME c => SOME c
		      | NONE => NONE);
		    inc := (λp. p+1)
		|>
End

(*
Class code :=
  {
    Code:Type;
    PA:Type;
    φ : Code -> PA -> option (Com PA);
    inc : PA -> PA;
  }.

Coercion φ : Code >-> Funclass.
Notation "# p" := (inc p) (at level 0, format "'#' p").
*)

(* Reserved Notation "p ≫p_ C P" (at level 70,C at level 0, format "p '≫p_' C P"). *)

(* Code -> PA -> Pro -> Prop *)
(* Code -> num -> Pro -> Prop *)
Inductive representsPro:
[~Ret:]
	(∀p.
		codeImpl.phi C p = SOME retC ⇒
		representsPro C p retT) ∧
[~Var:]
	(∀p P x.
		codeImpl.phi C p = SOME (varC x) ∧ representsPro C (codeImpl.inc p) P ⇒
		representsPro C p (varT x P)) ∧
[~Lam:]
	(∀p q P Q.
		codeImpl.phi C p = SOME (lamC q) ∧ representsPro C (codeImpl.inc p) P ∧
		representsPro C q Q ⇒
		representsPro C p (lamT Q P)) ∧
[~App:]
	(∀p P.
		codeImpl.phi C p = SOME appC ∧ representsPro C (codeImpl.inc p) P ⇒
		representsPro C p (appT P))
End

(*
Inductive representsPro {codeImpl : code} (C:Code) : PA -> Pro -> Prop :=
| representsProRet p:
    C p = Some retC -> p ≫p_C retT
| representsProVar p P x:
    C p = Some (varC x) -> #p ≫p_C P -> p ≫p_C varT x P
| representsProLam p q P Q:
    C p = Some (lamC q) -> #p ≫p_C P -> q ≫p_C Q -> p ≫p_C lamT Q P
| representsProApp p P:
    C p = Some appC -> #p ≫p_C P -> p ≫p_C appT P
where "p ≫p_ C P" := (representsPro C p P).
*)

Theorem representsPro_functional:
	functional (representsPro C)
Proof
	simp[functional] >> Induct_on `representsPro` >> rw[] (* 4 *)
	>- (fs[Once representsPro_cases] >> fs[])
    >> pop_assum mp_tac >> rw[Once representsPro_cases]
QED

(*
Definition codeImpl:
	codeImpl =
		<|
		    phi := (λC p.
		      case (nth_error p C) of
		      | SOME (lamC k) => SOME (lamC (p+k))
		      | SOME c => SOME c
		      | NONE => NONE);
		    inc := (λp. p+1)
		|>
End
*)

(*
Instance codeImpl: code:=
  {
    PA := nat;
    Code := list (Com nat);
    φ C p:=
      match C.[p] return option (Com nat) with
      | Some (lamC k) => Some (lamC (p+k))
      | Some c => Some c
      | None => None
      end;
    inc p:= p+1
  }.
*)

(* (P:Pro) : list (Com nat) :=*)
Definition psi:
	psi P =
	    case P of
	    | retT => [retC]
	    | appT P => appC::psi P
	    | varT x P => varC x::psi P
	    | lamT Q P =>
		      let cP = psi P in
		      lamC (1 + LENGTH cP)::cP++psi Q
End

Theorem fetch_correct':
	∀C1 C2 P. representsPro (C1++(psi P)++C2) (LENGTH C1) P
Proof
	Induct_on `P`
	>- (rw[Once representsPro_cases, codeImpl, AllCaseEqs()] >>
		`LENGTH C1 ≤ LENGTH C1` by rw[LESS_EQ_REFL] >>
		drule nth_error_app2 >> rw[] >>
		`nth_error (LENGTH C1) (C1 ⧺ (psi retT ⧺ C2)) = nth_error 0 (psi retT ⧺ C2)`
			by fs[] >> fs[APPEND_ASSOC] >> rw[nth_error, psi])
	>- (rw[Once representsPro_cases, codeImpl, AllCaseEqs()]
		>- (`LENGTH C1 ≤ LENGTH C1` by rw[LESS_EQ_REFL] >>
			drule nth_error_app2 >> rw[] >>
			`nth_error (LENGTH C1) (C1 ⧺ (psi (varT n P) ⧺ C2)) =
			 nth_error 0 (psi (varT n P) ⧺ C2)` by fs[] >>
			fs[APPEND_ASSOC] >> rw[nth_error, Once psi])
		>> rw[Once psi] >>
		`representsPro ((C1 ++ [varC n]) ⧺ psi P ⧺ C2) (LENGTH (C1 ++ [varC n])) P`
			by fs[] >> fs[] >>
		`C1 ⧺ [varC n] ⧺ psi P ⧺ C2 = C1 ⧺ varC n::psi P ⧺ C2`
			suffices_by metis_tac[] >> rw[])
	>- (rw[Once representsPro_cases, codeImpl, AllCaseEqs()]
		>- (`LENGTH C1 ≤ LENGTH C1` by rw[LESS_EQ_REFL] >>
			drule nth_error_app2 >> rw[] >>
			`nth_error (LENGTH C1) (C1 ⧺ (psi (appT P) ⧺ C2)) =
			 nth_error 0 (psi (appT P) ⧺ C2)` by fs[] >>
			fs[APPEND_ASSOC] >> rw[nth_error, Once psi])
		>> rw[Once psi] >>
		`representsPro ((C1 ++ [appC]) ⧺ psi P ⧺ C2) (LENGTH (C1 ++ [appC])) P`
			by fs[] >> fs[] >>
		`C1 ⧺ [appC] ⧺ psi P ⧺ C2 = C1 ⧺ appC::psi P ⧺ C2`
			suffices_by metis_tac[] >> rw[])
	>> rw[Once representsPro_cases, codeImpl, AllCaseEqs()] >> rw[PULL_EXISTS] >>
	qexists_tac `LENGTH (psi P') + 1` >> rw[] >> rw[Once psi]
	>- (`LENGTH C1 ≤ LENGTH C1` by rw[LESS_EQ_REFL] >>
		drule nth_error_app2 >> rw[] >>
		`nth_error (LENGTH C1) (C1 ⧺ (lamC (LENGTH (psi P') + 1)::(psi P' ⧺ psi P) ⧺ C2)) =
		 nth_error 0 (lamC (LENGTH (psi P') + 1)::(psi P' ⧺ psi P) ⧺ C2)`
		 	by fs[] >> fs[APPEND_ASSOC] >>
		rw[nth_error])
	>- (`representsPro ((C1 ⧺ [lamC (LENGTH (psi P') + 1)]) ⧺ psi P' ⧺ (psi P ⧺ C2))
					   (LENGTH (C1 ⧺ [lamC (LENGTH (psi P') + 1)]))
					   P'` by fs[] >> fs[] >>
		`C1 ⧺ [lamC (LENGTH (psi P') + 1)] ⧺ psi P' ⧺ psi P ⧺ C2 =
		 C1 ⧺ lamC (LENGTH (psi P') + 1)::(psi P' ⧺ psi P) ⧺ C2`
		 	suffices_by metis_tac[] >> rw[])
	>> `representsPro ((C1 ⧺ lamC (LENGTH (psi P') + 1) :: psi P') ⧺ psi P ⧺ C2)
					   (LENGTH (C1 ⧺ lamC (LENGTH (psi P') + 1) :: psi P'))
					   P` by fs[] >> fs[ADD1] >>
	`C1 ⧺ lamC (LENGTH (psi P') + 1)::psi P' ⧺ psi P ⧺ C2 =
	 C1 ⧺ lamC (LENGTH (psi P') + 1)::(psi P' ⧺ psi P) ⧺ C2`
	 	suffices_by metis_tac[] >> rw[]
QED

Theorem fetch_correct:
	∀P. representsPro (psi P) 0 P
Proof
	rw[] >>
	`representsPro ([]++(psi P)++[]) (LENGTH ([]: num Com list)) P`
		by metis_tac[fetch_correct'] >>
	fs[]
QED

val _ = export_theory ()
