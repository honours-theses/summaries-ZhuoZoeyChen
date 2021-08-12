open HolKernel Parse boolLib bossLib;
open arithmeticTheory;
open listTheory;
open relationTheory;
open PrelimsTheory;
open RefinementsTheory;
open LTheory;
open ProgramsTheory;
open ClosuresTheory;
open M_stackTheory;

val _ = new_theory "M_clos";

(* ---------------------
     Closure Machine
   --------------------- *)

Type stateC = ``:Clo list # Clo list``;

(* label -> stateC -> stateC -> Prop:= *)
(*
	Reserved Notation "σ ≻C_ l σ'" (at level 70, l at level 0,format "σ '≻C_' l σ'").
*)
Inductive stepC:
	(∀E T V. stepC (τ: label) (closC retT E::T,V) (T,V)) ∧
	(∀P E x V p T.
    	nth_error x E = SOME p ⇒
    	stepC τ (closC (varT x P) E::T,V) (closC P E::T,p::V)) ∧
	(∀P Q E T V.
    	stepC τ (closC (lamT Q P) E ::T,V) (closC P E::T,closC Q E::V)) ∧
	(∀P E T e Q F V.
    	stepC β (closC (appT P) E :: T,e :: closC Q F ::V) (closC Q (e::F) :: closC P E :: T,V))
End
(*
	"σ ≻C_ l σ'" := (stepC l σ σ').
	Notation "(≻C_ l )" := (stepC l) (at level 0, format "'(≻C_' l ')'").
*)
(* Notation "σ ≻C_ l σ'" := 0.
Notation "σ ≻C_ l σ'" := (stepC l σ σ').
Notation "(≻C)" := (any stepC) (at level 0).

Notation "σ ≻C σ'" := (any stepC σ σ') (at level 70).

Canonical Structure clos_machine := {| M_rel := stepC |}.

Hint Constructors stepC.*)

Definition closedSC:
	closedSC (Ts, V) = (Forall (λx. boundC x 0) Ts ∧ Forall (λx. boundC x 1) V)
End

Definition repsCS:
	repsCS (C:stateC) (S:stateS) =
		(case C of
			(Ts, V) => (closedSC (Ts, V) ∧ (MAP (deltaC 0) Ts, MAP (deltaC 1) V) = S))
End

(*
Notation "(≫CS)" := (repsCS) (at level 0).
Notation "π ≫CS σ" := (repsCS π σ) (at level 70).
*)

(* Fact 31 *)
Theorem repsCS_functional:
  functional repsCS
Proof
  rw[functional, repsCS] >>
  Cases_on `x` >> fs[]
QED

Theorem cbound_cons:
  ∀P e E.
    boundC (closC P E) 1 ⇒
    boundC e 1 ⇒
    boundC (closC P (e::E)) 0
Proof
  rw[Once boundC_cases] >> rw[Once boundC_cases]
  >- rw[ADD1]
  >- rw[]
  >> metis_tac[]
QED

(* Fact 32 *)
Theorem reducibility:
  ∀Ts V.
    reducible (any stepS) (MAP (deltaC 0) Ts, MAP (deltaC 1) V) ⇒
    reducible (any stepC) (Ts, V)
Proof
  rw[reducible, any, Once stepS_cases, Once stepC_cases]
  >- (Cases_on `Ts` >> fs[] >>
      Cases_on `V` >> fs[] >>
      Cases_on `t'` >> fs[] >>
      gvs[] >> Cases_on `h` >> fs[Once deltaC] >>
      fs[Once substPl] >>
      Cases_on `P'` >> fs[]
      >- (Cases_on `nth_error n (MAP (λa. deltaC 1 a) l)` >> fs[])
      >> fs[Once substPl] >>
      Cases_on `P0` >> fs[] >> rw[] >> Cases_on `h''` >> rw[])
  >- (Cases_on `Ts` >> gvs[Once deltaC] >>
      Cases_on `h` >> fs[Once substPl] >>
      Cases_on `P'` >> fs[] >>
      Cases_on `nth_error n (MAP (λa. deltaC 1 a) l)` >> fs[] >>
      gvs[] >> metis_tac[nth_error_Some_lt, nth_error_lt_Some, LENGTH_MAP])
  >> Cases_on `Ts` >> gvs[Once deltaC] >>
  Cases_on `h` >> gvs[Once substPl] >>
  Cases_on `P` >> fs[] >>
  Cases_on `nth_error n (MAP (λa. deltaC 1 a) l)` >> fs[]
QED

(*
Ltac inv_closed_clos :=
  repeat
    match goal with
    | [H:closedSC (_,_) |- _] => inv H
    | [H:Forall _ (_::_) |- _] => inv H
    | [H:_/_ <C _|- _] => inv H
    | [H:lamT _ _ <P _ |- _] => inv H
    | [H:varT _ _<P _ |- _] => inv H
    | [H:appT _<P _ |- _] => inv H
    end.
*)

(* Fact 33 *)
Theorem closedSC_preserved:
  ∀Ts V T' V'.
    closedSC (Ts, V) ⇒
    (any stepC (Ts, V) (T', V')) ⇒
    closedSC (T', V')
Proof
  rw[closedSC, any]
  >- (fs[Once stepC_cases] >> gvs[]
      >- fs[Once Forall_cases]
      >- (fs[Once Forall_cases] >> fs[Once boundC_cases] >>
          fs[Once boundP_cases])
      >- (fs[Once Forall_cases] >> fs[Once boundC_cases] >>
          fs[Once boundP_cases])
      >> fs[Once Forall_cases] >> rw[]
      >- (pop_assum mp_tac >> rw[Once Forall_cases] >>
          metis_tac[cbound_cons])
      >> rw[Once Forall_cases] >>
      fs[Once boundC_cases] >> fs[Once boundP_cases])
  >> fs[Once stepC_cases] >> gvs[]
  >- (fs[Once Forall_cases] >> rw[]
      >- (qpat_x_assum `boundC _ _` mp_tac >> rw[Once boundC_cases] >>
          metis_tac[nth_error_SOME_in_H])
      >- rw[Once Forall_cases]
      >- (qpat_x_assum `boundC (closC (varT x P) E) 0` mp_tac >> rw[Once boundC_cases] >>
          metis_tac[nth_error_SOME_in_H])
      >> rw[Once Forall_cases])
  >- (fs[Once Forall_cases] >> rw[]
      >- (fs[Once boundC_cases] >> fs[Once boundP_cases] >> gvs[] >>
          Cases_on `Q` >> rw[]
          >- fs[Once boundP_cases]
          >- (qpat_x_assum `boundP (varT n P0) (SUC (LENGTH E))` mp_tac >>
              rw[Once boundP_cases, ADD1])
          >- (qpat_x_assum `boundP (appT P0) (SUC (LENGTH E))` mp_tac >>
              rw[Once boundP_cases, ADD1])
          >> qpat_x_assum `boundP (lamT P0 P1) (SUC (LENGTH E))` mp_tac >>
          rw[Once boundP_cases, ADD1])
      >- rw[Once Forall_cases]
      >- (qpat_x_assum `boundC (closC (lamT Q P) E) 0` mp_tac >> rw[Once boundC_cases] >>
          rw[Once boundC_cases] >> fs[Once boundP_cases] >>
          Cases_on `Q` >> rw[]
          >- fs[Once boundP_cases]
          >- (qpat_x_assum `boundP (varT n P0) (SUC (LENGTH E))` mp_tac >>
              rw[Once boundP_cases, ADD1])
          >- (qpat_x_assum `boundP (appT P0) (SUC (LENGTH E))` mp_tac >>
              rw[Once boundP_cases, ADD1])
          >> qpat_x_assum `boundP (lamT P0 P1) (SUC (LENGTH E))` mp_tac >>
          rw[Once boundP_cases, ADD1])
      >> rw[Once Forall_cases])
  >> pop_assum mp_tac >> simp[Once Forall_cases] >> rw[Once Forall_cases]
QED

(* Fact 34 *)
Theorem tau_simulation:
  ∀Ts V T' V'.
    stepC τ (Ts, V) (T', V') ⇒
    stepS τ (MAP (deltaC 0) Ts, MAP (deltaC 1) V) (MAP (deltaC 0) T', MAP (deltaC 1) V')
Proof
  rw[Once stepC_cases, Once stepS_cases] >> rw[]
  >- rw[Once deltaC, Once substPl]
  >- (rw[Once deltaC, Once substPl] >> rw[] >>
      drule(INST_TYPE [beta |-> ``:Pro``] map_nth_error) >> rw[] >>
      `nth_error x (MAP (λa. deltaC 1 a) E) = SOME ((λa. deltaC 1 a) p)`
        by metis_tac[] >>
      Cases_on `nth_error x (MAP (λa. deltaC 1 a) E)` >> rw[] >>
      rw[EQ_SYM_EQ] >> rw[Once deltaC])
  >> rw[Once deltaC, Once substPl] >> rw[]
  >> rw[EQ_SYM_EQ] >> rw[Once deltaC]
QED

(* Fact 35 *)
Theorem beta_simulation:
  ∀Ts V T' V'.
    closedSC (Ts, V) ⇒
    stepC β (Ts, V) (T', V') ⇒
    stepS β (MAP (deltaC 0) Ts, MAP (deltaC 1) V) (MAP (deltaC 0) T', MAP (deltaC 1) V')
Proof
  rw[closedSC, Once stepC_cases, Once stepS_cases] >> rw[]
  >- (rw[Once deltaC, Once substPl] >>
      rw[EQ_SYM_EQ] >> rw[Once deltaC])
  >> rw[Once deltaC] >> rw[EQ_SYM_EQ, Once deltaC] >> rw[EQ_SYM_EQ] >>
  `Forall (λx. boundP x 1) (MAP (λa. deltaC 1 a) F')`
    suffices_by rw[substPl_cons, ADD1] >>
  pop_assum mp_tac >> simp[Once Forall_cases] >> rw[Once Forall_cases] >>
  qpat_x_assum `boundC (closC _ _) _` mp_tac >> rw[Once boundC_cases] >>
  `Forall (λx. boundC x 1) F'` by fs[Forall_forall] >>
  irule Forall_map >> rw[] >>
  pop_assum mp_tac >> Induct_on `Forall`  >> rw[]
  >- rw[Once Forall_cases]
  >> rw[Once Forall_cases] >> metis_tac[translateC_boundP]
QED

(* Theorem 36: Closure Machine to Naive Stack Machine *)
Theorem clos_stack_refinement:
  refinement_M repsCS (stepC (τ:label)) (stepC β) (stepS τ) (stepS β)
Proof
  rw[refinement_M, repsCS] >> Cases_on `a` >> fs[]
  >- (rename [`reducible (stepC τ ∪ᵣ stepC β) (Ts,V)`] >>
      `reducible (any stepS) (MAP (deltaC 0) Ts,MAP (deltaC 1) V) ⇒
       reducible (any stepC) (Ts,V)`
        by rw[reducibility] >>
      fs[reducible, any, RUNION] >> rw[] >>
      rfs[PULL_EXISTS] >>
      first_x_assum drule >> rw[] >>
      fs[Once stepC_cases] >> rw[]
      >- metis_tac[]
      >- metis_tac[]
      >- metis_tac[]
      >> rw[Once stepC_cases])
  >- (Cases_on `a'` >> fs[] >> rw[]
      >- metis_tac[any, closedSC_preserved]
      >> metis_tac[tau_simulation])
  >> Cases_on `a'` >> fs[] >> rw[]
  >- metis_tac[any, closedSC_preserved]
  >> metis_tac[beta_simulation]
QED

Theorem compile_clos_stack:
  ∀P.
    closedP P ⇒
    repsCS ([closC P []], []) ([P], [])
Proof
  rw[closedP, repsCS, closedSC] >> rw[Once Forall_cases]
  >- rw[Once boundC_cases]
  >- rw[Once Forall_cases]
  >> rw[Once deltaC] >> metis_tac[substPl_nil]
QED

Definition repsCL:
  repsCL = rcomp repsCS repsSL
End

(*
Notation "(≫CL)" := (repsCL) (at level 0).
Notation "π ≫CL s" := (repsCL π s) (at level 70).
*)

(*
Lemma repsCL_equiv T V s:
  (T,V) ≫CL s <-> closedL s /\ exists A, δV (map (δC 1) V) = Some A /\ δT (map (δC 0) T) A = Some s.
Proof.
  unfold repsCL,repsCS,repsSL. split.
  -intros (?&? <-&(A&?&?)). split. 2:eauto. admit.
  -intros (?&(A&?&?)). eexists;split. split. 2:reflexivity. 2:now cbn;eauto. admit.
Abort. *)

(* Theorem 36: Closure Machine to L *)
Theorem clos_L_refinement:
  refinement_ARS repsCL (stepC (τ:label)) (stepC β) stepL
Proof
  rw[repsCL, rcomp] >>
  metis_tac[composition, clos_stack_refinement, stack_L_refinement]
QED

Theorem compile_clos_L:
  ∀s. closedL s ⇒ repsCL ([closC (gamma s retT) []], []) s
Proof
  rw[closedL, repsCL, rcomp] >>
  qexists_tac `([gamma s retT],[])` >> rw[]
  >- (irule compile_clos_stack >> rw[closedP] >>
      irule bound_compile >> rw[Once boundP_cases])
  >> metis_tac[compile_stack_L]
QED

val _ = export_theory ()