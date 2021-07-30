open HolKernel Parse boolLib bossLib;
open arithmeticTheory;
open listTheory;
open PrelimsTheory;
open LTheory;
open RefinementsTheory;
open ProgramsTheory;

val _ = new_theory "Mstack";

Type States = ``:(Pro list) # (Pro list)``;

(* Reserved Notation "σ ≻S_ l σ'" (at level 70, l at level 0,format "σ '≻S_' l σ'"). *)

(* The original coq code had the labels as an argument.
   The label arguments are removed in this HOL implementation.
*)

(* τ | β *)

(* Ts (tasks) for control stack
   V (values) for argument stack*)
Inductive stepS:
  (∀P Q R Ts V. stepS β ((appT P)::Ts, R::Q::V) (substP Q 0 R::P::Ts, V)) ∧
  (∀P Q Ts V. stepS τ (lamT Q P::Ts, V) (P::Ts, Q::V)) ∧
  (∀Ts V. stepS τ (retT::Ts, V) (Ts, V))
End

(*
where "σ ≻S_ l σ'" := (stepS l σ σ').

Notation "(≻S_ l )" := (stepS l) (at level 0, format "'(≻S_' l ')'").
*）

(* workaround to prefere "x ≻ y" over "(≻) x y"*)

(*
Notation "σ ≻S_ l σ'" := 0.
Notation "σ ≻S_ l σ'" := (stepS l σ σ').
Notation "(≻S)" := (any stepS) (at level 0).
Notation "σ ≻S σ'" := (any stepS σ σ') (at level 70).

Canonical Structure stack_machine := {| M_rel := stepS |}.
*)

Theorem tau_functional:
  functional (stepS τ)
Proof
  simp[functional] >> Induct_on `stepS` >> rw[] (* 3 *)
  >> fs[Once stepS_cases]
QED

Theorem beta_functional:
  functional (stepS β)
Proof
  simp[functional] >> Induct_on `stepS` >> rw[] (* 3 *)
  >> fs[Once stepS_cases]
QED

Theorem stepS_functional:
  ∀l. functional (stepS l)
Proof
  simp[functional] >> Induct_on `stepS` >> rw[] (* 3 *)
  >> fs[Once stepS_cases]
QED

Theorem tau_terminating:
  ∀x. terminatesOn (stepS τ) x
Proof
  rw[Once terminatesOn_cases] >>
  PairCases_on `x` >> rename [`stepS τ (Ts,V) x'`] >>
  pop_assum mp_tac >> MAP_EVERY qid_spec_tac [`V`, `x'`] >>
  Induct_on `Ts`
  >- rw[Once stepS_cases]
  >> Induct_on `h` >>
  rw[Once stepS_cases, Once terminatesOn_cases] >> metis_tac[]
QED

Theorem beta_terminating:
  ∀x. terminatesOn (stepS β) x
Proof
  rw[Once terminatesOn_cases] >>
  PairCases_on `x` >> rename [`stepS β (Ts,V) x'`] >>
  pop_assum mp_tac >> MAP_EVERY qid_spec_tac [`Ts`, `x'`] >>
  Q.SUBGOAL_THEN `∃n. n = LENGTH V` strip_assume_tac >- metis_tac[] >>
  pop_assum mp_tac >> MAP_EVERY qid_spec_tac [`V`, `n`] >>
  ho_match_mp_tac COMPLETE_INDUCTION >> rw[] >>
  first_assum mp_tac >> PURE_REWRITE_TAC[Once stepS_cases] >>
  rw[Once terminatesOn_cases] >>
  first_x_assum (match_mp_tac o MP_CANON) >>
  first_x_assum (irule_at (Pos last)) >> rw[]
QED

(* decompilation function for control stacks
  type: L(Pro) -> L(term) -> O(L(term)) *)
Definition deltaT:
  deltaT Ts A =
    case Ts of
    | [] => SOME A
    | P::Ts' => case (delta P A) of
               | SOME A' => deltaT Ts' A'
               | _ => NONE
End

(* decompilation function for argument stacks
   tyep: L(Pro) → O(L(Term)) *)
Definition deltaV:
  deltaV V =
    case V of
    | [] => SOME []
    | P::V' => case (delta P [], deltaV V') of
               | (SOME [s], SOME A) => SOME (lam s::A)
               | _,_ => NONE
End

Definition repsSL:
  repsSL (Ts,V) s =
    ∃A. deltaV V = SOME A ∧ deltaT Ts A = SOME [s]
End

(*
Notation "(≫SL)" := (repsSL) (at level 0).
Notation "σ ≫SL s" := (repsSL σ s) (at level 70).
*)

Theorem repsSL_functional:
  functional repsSL
Proof
  simp[functional] >> rw[] >>
  PairCases_on `x` >> fs[repsSL] >> gvs[]
QED

Theorem repsSL_computable:
  computable repsSL
Proof
  simp[computable] >>
  qexists_tac `(λ(Ts, V). case (deltaV V) of
                          | SOME A => (case (deltaT Ts A) of
                                       | SOME [s] => (SOME s)
                                       | _ => NONE)
                          | NONE => NONE)` >>
  rw[stepFunction] >> PairCases_on `x` >>
  rw[repsSL] >>
  Cases_on `deltaV x1` >> rw[] >>
  Cases_on `deltaT x0 x` >> rw[] >>
  Cases_on `x'` >> rw[] >>
  Cases_on `t` >> rw[]
QED

(* Only in code, to prettify reasoning *)
Theorem decompileTask_inv:
  ∀P Ts A B.
    deltaT (P::Ts) A = SOME B ⇒
    ∃A'. delta P A = SOME A' ∧ deltaT Ts A' = SOME B
Proof
  rw[Once deltaT] >> Cases_on `delta P A` >> fs[]
QED

(* Only in code, to prettify reasoning *)
Theorem decompileTask_step:
  ∀P A A' Ts.
    delta P A = SOME A' ⇒ deltaT (P::Ts) A = deltaT Ts A'
Proof
  rw[Once deltaT]
QED

(* Only in code, to prettify reasoning *)
Theorem decompileArg_inv:
  ∀P V A.
    deltaV (P::V) = SOME A ⇒
    ∃s A'. A = (lam s)::A' ∧ delta P [] = SOME [s] ∧ deltaV V = SOME A'
Proof
  rw[Once deltaV] >> Cases_on `delta P []` >> fs[] >>
  Cases_on `x` >> fs[] >>
  Cases_on `deltaV V` >> fs[] >>
  Cases_on `t` >> fs[]
QED


(* Only in code, to prettify reasoning *)
Theorem decompileArg_step:
  ∀P s A V.
    delta P [] = SOME [s] ⇒
    deltaV V = SOME A ⇒
    deltaV (P::V) = SOME (lam s::A)
Proof
  rw[] >> rw[Once deltaV]
QED

Theorem tau_simulation:
  ∀Ts V s T' V'.
    repsSL (Ts,V) s ⇒
    stepS τ (Ts,V) (T',V') ⇒
    repsSL (T',V') s
Proof
  rw[repsSL] >> fs[Once stepS_cases]
  >- (qpat_x_assum `deltaT Ts A = SOME [s]` mp_tac >>
      rw[Once deltaT] >> fs[Once delta] >>
      Cases_on `delta Q []` >> fs[] >>
      Cases_on `x` >> fs[] >>
      Cases_on `t` >> fs[] >>
      Cases_on `delta P (lam h ::A)` >> fs[] >>
      rw[Once deltaV, Once deltaT])
  >> qpat_x_assum `deltaT Ts A = SOME [s]` mp_tac >>
  rw[Once deltaT] >> fs[Once delta]
QED

Theorem decompileArg_abstractions:
  ∀V A. deltaV V = SOME A ⇒ Forall abstraction A
Proof
  ho_match_mp_tac deltaV_ind >> rw[] >>
  pop_assum mp_tac >> rw[Once deltaV] >>
  Cases_on `V` >> fs[]
  >- rw[Once Forall_cases, abstraction_cases]
  >> Cases_on `delta h []` >> fs[] >>
  Cases_on `x` >> fs[] >>
  Cases_on `t` >> fs[]
  >- (fs[Once deltaV] >> Cases_on `t'` >> fs[] >>
      rw[] >> rw[Once Forall_cases, abstraction_cases])
  >> Cases_on `deltaV (h''::t'')` >> fs[] >> rw[] >>
  Cases_on `t'` >> fs[] >> rw[] >>
  rw[Once Forall_cases, abstraction_cases]
QED


(* Here should be two lemmas only shown in the paper *)

(*
Lemma substP_rep_subst Q s R t A:
  Q ≫P s ->
  R ≫P t ->
  δ (substP Q 0 R) A = Some (subst s 0 (lam t)::A).
Proof.
  intros ? ?.
  change A with ([]++A) at 1.
  erewrite decompile_append with (A':=[_]). reflexivity.
  apply substP_rep_subst' with (A:=[]) (B:=[s]). all:eassumption.
Qed.
Reserved Notation "s '≻Ls' t" (at level 70).

Inductive stepLs : list term -> list term -> Prop :=
|stepL_here s t A : s ≻L t -> Forall abstraction A -> s::A ≻Ls t::A
|stepLs_there s A B : A ≻Ls B -> s::A ≻Ls s::B
where "A '≻Ls' B" := (stepLs A B).

Hint Constructors stepLs.

Only in Coq
Lemma stepLs_singleton_inv s B:
  [s] ≻Ls B -> exists t, B = [t] /\ s ≻L t.
Proof.
  inversion_clear 1. eauto. easy.
Qed.
Ltac invAll :=
  repeat
    match goal with
      H: δT (_::_,_) _|- _ => inv H
    | H: δV (_::_) _ |- _=> inv H
    | H: δV _ (_::_) |- _=> inv H
    | H: Forall _ (_::_) |- _ => inv H
    | H : abstraction _ |- _ => inv H
    end.

Lemma stepLs_decomp P A A' B:
  A ≻Ls A' -> δ P A = Some B ->
  exists B', B ≻Ls B' /\ δ P A' = Some B'.
Proof.
  revert A' B. functional induction (δ P A). all:try congruence.
  all:intros A' B R repP.
  -inv repP. eauto.
  -eauto.
  -cbn. rewrite e0. eauto.
  -repeat (match goal with [ H: (_::_) ≻Ls _ |- _ ] => inv H end).
   all:invAll.
   all:eauto.
Qed.
Lemma stepLs_decompileTask T A A1 B:
  A ≻Ls A1 ->
  δT T A = Some B ->
  exists B', B ≻Ls B' /\ δT T A1 = Some B'.
Proof.
  revert A1 B. functional induction (δT T A);try congruence.
  all:intros A1 B1 R eq.
  -cbn. inv eq. eauto.
  -edestruct stepLs_decomp as (?&?&repP). 1,2:eassumption.
   rewrite (decompileTask_step _ repP). eauto.
Qed.
Lemma beta_simulation (σ σ':_) s:
  σ ≻S_β σ' -> σ ≫SL s ->
  exists s', σ' ≫SL s' /\ s ≻L s'.
Proof.
  destruct σ as (T0,V0), σ' as (T',V').
  intros red (A0&repV'&repT0V0).
  inversion red as [P Q R T V eql| |]. subst T0 V0 T' V'. clear eql.
  apply decompileArg_inv in repV' as (u&?&eqA0&repD&repV').
  apply decompileArg_inv in repV' as (t&A&->&repR&repV). subst A0.
  apply decompileTask_inv in repT0V0 as (A1&repPA0&repTA1).
  cbn in repPA0.
  edestruct stepLs_decompileTask with (B:=[s]) (A:=(lam t) (lam u) :: A) (T:=P::T) as (B&redB&repB).
  -eauto using decompileArg_abstractions.
  -rewrite (decompileTask_step _ repPA0). trivial.
  -apply stepLs_singleton_inv in redB as (s'&->&red').
   exists s'. split.
   unfold repsSL.
   exists A. split. tauto.
   rewrite <- repB. apply decompileTask_step.
   apply substP_rep_subst. all:tauto.
Qed.
Inductive stuckLs : list term -> Prop :=
  stuckLsHere s A : Forall abstraction A -> stuck s -> stuckLs (s::A)
| stuckLsThere s A : stuckLs A -> stuckLs (s::A).

Hint Constructors stuck stuckLs.

Lemma stuck_decompile A B P:
  stuckLs A -> δ P A = Some B -> stuckLs B.
Proof.
  functional induction (δ P A);try congruence;cbn;intros H eq.
  -apply IHo. all:eauto.
  -apply IHo0. all:eauto.
  -apply IHo.
   all:repeat match goal with
                H : stuckLs (_::_) |- _ => inv H
              | H: Forall _ (_::_) |- _ => inv H
              | H: abstraction _ |- _ => inv H
              end.
   all:eauto.
Qed.
Lemma stuck_decompileTask T A B:
  stuckLs A -> δT T A = Some B -> stuckLs B.
Proof.
  revert B. functional induction (δT T A);try congruence. intros B ? ?.
  eapply stuck_decompile in e0. all:eauto.
Qed.
Lemma stateS_trichotomy T V s:
  (T,V) ≫SL s ->
  reducible (≻S) (T,V)
  \/ (exists P s', (T,V)=([],[P]) /\ s = lam s' /\ P ≫P s')
  \/ (exists x P T', T = varT x P::T' /\ stuck s).
Proof.
  intros (A&H1&H2). destruct T as [|[] T]; functional inversion H2;subst.
  -right. left. functional inversion H1;subst. functional inversion H4;subst. eauto 10.
  -left. eauto.
  - right. right. cbn in H4. apply stuck_decompile in H4. 2:now eauto using decompileArg_abstractions.
    eapply stuck_decompileTask in H7. 2:assumption. inv H7; now eauto.
  -left. functional inversion H4;subst. functional inversion H1;subst. functional inversion H6;subst. eauto.
  -left. eauto.
Qed.
Lemma reducible_red conf s:
  conf ≫SL s -> reducible (≻L) s -> reducible (≻S) conf.
Proof.
  destruct conf as (T,V). intros H1 R. apply stateS_trichotomy in H1 as [H1|[(?&?&[= -> ->]&->&H1)|(?&?&?&->&H1)]].
  -assumption.
  -destruct R as (?&R). inv R.
  -edestruct stuck_normal. all:eassumption.
Qed.
Lemma stack_L_refinement:
  refinement_ARS (≫SL).
Proof.
  repeat (apply conj); cbn. 2:intros [] [].
  all:eauto using reducible_red, tau_simulation,beta_simulation,tau_terminating.
Qed.
Lemma compile_stack_L s:
  ([γ s retT],[]) ≫SL s.
Proof.
  exists []. split. tauto. cbn. rewrite decompile_correct'. tauto.
Qed.*)

val _ = export_theory ()
