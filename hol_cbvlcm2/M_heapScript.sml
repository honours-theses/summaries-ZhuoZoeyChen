open HolKernel Parse boolLib bossLib;
open PrelimsTheory RefinementsTheory LTheory ProgramsTheory;
open ClosuresTheory M_closTheory CodesTheory;
open HeapsTheory;

val _ = new_theory "M_heaps";

(* ---------------------
        Heap Machine
   --------------------- *)

(*
Section Lin.
  Variable codeImpl:code.
  Variable heapImpl:heap PA.

  Variable C: Code.

  Notation "(≫C_ H )" := (representsClos C H) (at level 0, format "'(≫C_' H ')'").
  Notation "g ≫C_ H e" := (representsClos C H g e) (at level 70,H at level 0, format "g '≫C_' H e").
  Notation "a ≫E_ H E" := (representsEnv C H a E) (at level 70,H at level 0, format "a '≫E_' H E").

  (* stackStack and Heap *)
  Definition state := (list HC * list HC *Heap)%type.

  Hint Transparent state.

  Reserved Notation "σ ≻H_ l σ'" (at level 70, l at level 0,format "σ '≻H_' l σ'").

  Inductive stepH : label -> state -> state -> Prop :=
  | step_nil p a T V H:
      C p = Some retC ->
      ((p,a)::T,V,H) ≻H_τ (T,V,H)
  | step_load p a x e T V H:
      C p = Some (varC x) ->
      H.[a,x] = Some e ->
      ((p,a)::T,V,H) ≻H_τ ((inc p,a)::T,e::V,H)
  | step_pushVal p q a T V H:
      C p = Some (lamC q) ->
      ((p,a)::T,V,H) ≻H_τ ((inc p,a)::T,(q,a)::V,H)
  | step_beta a b b' g p q H H' T V:
      C p = Some (appC)
      -> put H g b = (H',b')
      -> ((p,a)::T,g::(q,b)::V,H) ≻H_β ((q,b')::(inc p,a)::T,V,H')
  where "σ ≻H_ l σ'" := (stepH l σ σ').

  Notation "(≻H_ l )" := (stepH l) (at level 0, format "'(≻H_' l ')'").
  (* workaround to prefere "x ≻ y" over "(≻) x y"*) Notation "σ ≻H_ l σ'" := 0.
  Notation "σ ≻H_ l σ'" := (stepH l σ σ').
  Notation "σ ≻H σ'" := (any stepH σ σ') (at level 70).
  Notation "(≻H)" := (any stepH) (at level 0).

  Canonical Structure heap_machine := {| M_rel := stepH |}.

  Hint Constructors stepH.

  Inductive repsHC : state -> stateC -> Prop :=
  | representsC H T V T' V': Forall2 (≫C_H) T T' -> Forall2 (≫C_H) V V' -> repsHC (T,V,H) (T',V').

  Hint Constructors repsHC.
  Notation "(≫HC)" := (repsHC) (at level 0).
  Notation "ψ '≫HC' π" := (repsHC ψ π) (at level 70).

  Hint Constructors repsHC.

  Ltac inv_Mheap :=
    repeat
      lazymatch goal with
      | [H:_ ≫C_ _ _ |-_] => inv H
      | [H:Forall2 _ (_::_) _ |- _] => inv H
      | [H:Forall2 _ _ (_::_) |- _] => inv H
      | [H:Forall2 _ _ [] |- _] => inv H
      | [H:_ ≫p_ _ _, eq : φ ?C ?a = Some _|- _] =>
        (inv H;rewrite eq in *;
         match goal with
         | [eq' : Some (_)=Some (_) |- _ ] => inv eq'
            end
         ;[])
      | [H:_ ≫p_ _ retT |- _] => inv H
      | [H:_ ≫p_ _ (lamT _ _) |- _] => inv H
      | [H:_ ≫p_ _ (varT _ _) |- _] => inv H
      | [H:_ ≫p_ _ (appT _) |- _] => inv H
      end.

  Lemma step_simulation π π' ψ l:
    π ≫HC ψ -> π ≻H_l π' -> exists ψ', π' ≫HC ψ' /\ ψ ≻C_l ψ'.
  Proof.
    intros rep R.
    inv R; inv rep; inv_Mheap.
    2:edestruct lookup_unlinedEnv with (C:=C) as (?&?&?); [now eassumption..|inv_Mheap].
    all:eexists;split;[|now eauto 10].
    all:split;repeat apply Forall2_cons;
      eauto 8 using Forall2_cons,representsEnv_extend,representsClos_extend,Forall2_impl,HR1,HR2.
  Qed.
  Lemma reducible_red π ψ:
    π ≫HC ψ -> reducible (≻C) ψ -> reducible (≻H) π.
  Proof.
    intros rep (ψ'&?&R). inv R; inv rep; inv_Mheap.
    2:edestruct nth_error_unlinedEnv as (?&?&?);[eassumption..|inv_Mheap].
    4:edestruct (put H (p,a) a0) eqn:eq.
    all:now eexists _,_;econstructor; eassumption.
  Qed.
  Lemma heap_clos_refinement :
    refinement_M (≫HC).
  Proof.
    split.
    -apply reducible_red.
    -eauto using step_simulation.
  Qed.
  Lemma compile_heap_clos p a H P:
    p ≫p_C P ->
    a ≫E_H [] ->
    ([(p,a)],[],H) ≫HC ([P/[]],[]).
  Proof.
    intros repP repE. eauto.
  Qed.

  Definition repsHL := rcomp (≫HC) (≫CL).
  Notation "(≫HL)" := (repsHL) (at level 0).
  Notation "ψ ≫HL s" := (repsHL ψ s) (at level 70).

  Lemma heap_L_refinement :
    refinement_ARS (≫HL).
  Proof.
    eapply composition;eauto using heap_clos_refinement, clos_L_refinement.
  Qed.
  Lemma compile_heap_L p a H s:
    closedL s ->
    p ≫p_C γ s retT ->
    a ≫E_H [] ->
    ([(p,a)],[],H) ≫HL s.
  Proof.
    unfold repsHL in *.
    intros repP repE. eexists;split.
    -apply compile_heap_clos. all:eassumption.
    -apply compile_clos_L. assumption.
  Qed.
End Lin.*)