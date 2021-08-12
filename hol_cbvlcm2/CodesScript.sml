open HolKernel Parse boolLib bossLib;
open PrelimsTheory;
open ProgramsTheory;

val _ = new_theory "Codes";

(* ---------------------
    	   Codes
   --------------------- *)

(*

Inductive Com PA:= retC| varC (n:nat) | appC | lamC (p:PA).
Arguments retC {_}.
Arguments varC {_} _.
Arguments lamC {_} _.
Arguments appC {_}.

Class code :=
  {
    Code:Type;
    PA:Type;
    φ : Code -> PA -> option (Com PA);
    inc : PA -> PA;
  }.

Coercion φ : Code >-> Funclass.
Notation "# p" := (inc p) (at level 0, format "'#' p").

Reserved Notation "p ≫p_ C P" (at level 70,C at level 0, format "p '≫p_' C P").

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

Lemma representsPro_functional {codeImpl: code} (C:Code):
  functional (representsPro C).
Proof.
  intros p P P' H. induction H in P'|-*; inversion 1;try congruence;f_equal;eauto;try congruence. replace q0 with q in * by congruence. eauto.
Qed.
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

Fixpoint ψ (P:Pro) : list (Com nat) :=
    match P with
    | retT => [retC]
    | appT P => appC::ψ P
    | varT x P => varC x::ψ P
    | lamT Q P =>
      let cP := ψ P in
      lamC (1 + length cP)::cP++ψ Q
    end.

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
