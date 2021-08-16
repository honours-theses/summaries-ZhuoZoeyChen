open HolKernel Parse boolLib bossLib;
open PrelimsTheory;
open ProgramsTheory;

val _ = new_theory "Codes";

(* ---------------------
    	   Codes
   --------------------- *)

Datatype:
  Com = retC | varC num | appC | lamC num
End

(*

Inductive Com PA:= retC| varC (n:nat) | appC | lamC (p:PA).
Arguments retC {_}.
Arguments varC {_} _.
Arguments lamC {_} _.
Arguments appC {_}.
*)

Datatype:
	code =
		<| Code : Com list;
		   PA   : num;
    	   phi  : Com list -> num -> Com option;
    	   inc  : num -> num
    	|>
End

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
		codeImpl.phi C p = SOME (lamC q) ∧ representsPro C (codeImpl.inc p) P ∧ representsPro C q Q ⇒
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
	Induct_on ``
QED

(*
Lemma fetch_correct' C1 C2 P:
  length C1 ≫p_(C1++ψ P++C2) P.
Proof.
  induction P in C1,C2|-*;cbn.
  -econstructor; cbn. rewrite nth_error_app2. 2:omega. rewrite <- minus_n_n. reflexivity.
  -econstructor;cbn.
   +rewrite nth_error_app2. 2:omega. rewrite <- minus_n_n. reflexivity.
   +specialize IHP with (C1:=C1++[varC n]) (C2:=C2). rewrite app_assoc_reverse in IHP.
    autorewrite with list in IHP. exact IHP.
  -econstructor;cbn.
   +rewrite nth_error_app2. 2:omega. rewrite <- minus_n_n. reflexivity.
   +specialize IHP with (C1:=C1++[appC]) (C2:=C2). rewrite app_assoc_reverse in IHP.
    autorewrite with list in IHP. exact IHP.
  -econstructor;cbn.
   +rewrite nth_error_app2. 2:omega. rewrite <- minus_n_n. reflexivity.
   +autorewrite with list.
    cbn. specialize IHP2 with (C1:=C1++[lamC (1+ | ψ P2 |)])
                              (C2:=ψ P1++C2).
    rewrite app_assoc_reverse in IHP2.
    autorewrite with list in IHP2. cbn in *. exact IHP2.
   +specialize IHP1 with (C1:=C1++lamC (1+ |ψ P2|)
                                :: ψ P2)
                         (C2:=C2).
    autorewrite with list in *. cbn in *. exact IHP1.
Qed.
Lemma fetch_correct P :
  0 ≫p_(ψ P) P.
Proof.
  specialize fetch_correct' with (C1:=[]) (C2:=[]) (P:=P) as H.
  cbn in H. setoid_rewrite app_nil_r in H. eassumption.
Qed.
*)

val _ = export_theory ()
