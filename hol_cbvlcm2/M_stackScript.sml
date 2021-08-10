open HolKernel Parse boolLib bossLib;
open arithmeticTheory;
open listTheory;
open relationTheory;
open PrelimsTheory;
open LTheory;
open RefinementsTheory;
open ProgramsTheory;

val _ = new_theory "M_stack";

Type stateS = ``:(Pro list) # (Pro list)``;

(* Reserved Notation "σ ≻S_ l σ'" (at level 70, l at level 0,format "σ '≻S_' l σ'"). *)

(* The original coq code had the labels as an argument.
   The label arguments are removed in this HOL implementation.
*)

(* τ | β *)

(* Ts (tasks) for control stack
   V (values) for argument stack *)
Inductive stepS:
  (∀P Q R Ts V. stepS β ((appT P)::Ts, R::Q::V) (substP Q 0 R::P::Ts, V)) ∧
  (∀P Q Ts V. stepS τ (lamT Q P::Ts, V) (P::Ts, Q::V)) ∧
  (∀Ts V. stepS τ (retT::Ts, V) (Ts, V))
End

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

(* Fact 18 *)
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
(* Lemma 21 *)
Theorem substP_rep_subst:
  ∀Q R A s t.
    repsP Q s ⇒
    repsP R t ⇒
    delta (substP Q 0 R) A = SOME (subst s 0 (lam t)::A)
Proof
  rw[] >> qpat_x_assum `repsP Q s` mp_tac >> rw[repsP] >>
  drule_all substP_rep_subst' >> rw[] >>
  `delta (substP Q 0 R) [] = SOME [subst s 0 (lam t)]` by fs[] >>
  metis_tac[decompile_append, APPEND]
QED

(* Reserved Notation "s '≻Ls' t" (at level 70). *)

Inductive stepLs:
  (∀s t A. stepL s t ∧ Forall abstraction A ⇒ stepLs (s::A) (t::A)) ∧
  (∀s A B. stepLs A B ⇒ stepLs (s::A) (s::B))
End

(* Only in code *)
Theorem stepLs_singleton_inv:
  ∀s B. stepLs [s] B ⇒ ∃t. B = [t] ∧ stepL s t
Proof
  Induct_on `stepLs` >> rw[] >>
  fs[Once stepLs_cases]
QED

(* TODO *)
(*
Ltac invAll :=
  repeat
    match goal with
      H: δT (_::_,_) _|- _ => inv H
    | H: δV (_::_) _ |- _=> inv H
    | H: δV _ (_::_) |- _=> inv H
    | H: Forall _ (_::_) |- _ => inv H
    | H : abstraction _ |- _ => inv H
    end.
*)

(* Lemma 22 *)
Theorem stepLs_decomp:
  ∀P A A' B.
    stepLs A A' ⇒
    delta P A = SOME B ⇒
    ∃B'. stepLs B B' ∧ delta P A' = SOME B'
Proof
  ho_match_mp_tac delta_ind >> rw[] >>
  pop_assum mp_tac >> simp[Once delta] >>
  simp[AllCaseEqs()] >> rw[] (* 4 *)
  >- simp[Once delta]
  >- (simp[Once delta] >>
      pop_assum mp_tac >> rw[Once stepLs_cases])
  (* app *)
  >- (qpat_x_assum `stepLs (t::s::A'') A'` mp_tac >>
      rw[Once stepLs_cases]
      (* Lemma22(3):
           stepL t t'
           s::A = s'::A'
           s::A contains only abstractions
       *)
      >- (fs[Once Forall_cases, Once abstraction_cases] >>
          `stepL (app (lam s') t) (app (lam s') t')`
            by metis_tac[stepL_rules] >> rw[] >> gvs[] >>
          `stepLs (app (lam s') t::A'') (app (lam s') t'::A'')`
            by metis_tac[stepLs_rules] >>
          first_x_assum drule >> rw[] >> rw[Once delta])
      >> qpat_x_assum `stepLs (s::A'') B'` mp_tac >>
      rw[Once stepLs_cases]
      (* Lemma22(2):
            t = t'
            stepL s s'
            A = A'
            A contains only abstractions
       *)
      >- (rename [`stepL s s'`, `Forall abstraction A`] >>
          rw[Once delta] >> metis_tac[stepL_rules, stepLs_rules])
      (* Lemma22(1):
            t = t'
            s = s'
            stepL A A' *)
      >> rename [`stepLs A A'`] >>
      rw[Once delta] >> metis_tac[stepL_rules, stepLs_rules])
  (* lam *)
  >> rw[Once delta] >> first_x_assum drule >> rw[] >>
  metis_tac[stepL_rules, stepLs_rules]
QED

Theorem stepLs_decompileTask:
  ∀Ts A A1 B.
    stepLs A A1 ⇒
    deltaT Ts A = SOME B ⇒
    ∃B'. stepLs B B' ∧ deltaT Ts A1 = SOME B'
Proof
  ho_match_mp_tac deltaT_ind >> rw[] >>
  pop_assum mp_tac >> simp[Once deltaT] >>
  simp[AllCaseEqs()] >> rw[]
  >- simp[Once deltaT]
  >> first_x_assum drule >> rw[] >>
  `∃B'. stepLs A' B' ∧ delta P A1 = SOME B'`
    by metis_tac[stepLs_decomp] >>
  first_x_assum drule >> rw[] >>
  qexists_tac `B''` >> rw[] >>
  rw[Once deltaT]
QED

(* Fact 23 *)
Theorem beta_simulation:
  ∀ a a' s.
    stepS β a a' ⇒
    repsSL a s ⇒
    ∃s'. repsSL a' s' ∧ stepL s s'
Proof
  Induct_on `stepS` >> rw[] >>
  fs[repsSL, Once stepS_cases] >> gvs[] >>
  drule decompileArg_inv >> rw[] >>
  drule decompileArg_inv >> rw[] >> rw[] >>
  drule decompileTask_inv >> rw[] >>
  rename [`deltaV (R::Q::V) = SOME (lam t::lam u::A)`] >>
  qpat_x_assum `delta (appT P) (lam t::lam t'::A) = SOME A'` mp_tac >>
  rw[Once delta] >>
  drule decompileTask_step >> rw[] >>
  first_x_assum (qspecl_then [`Ts`] ASSUME_TAC) >> gvs[] >>
  `delta (substP Q 0 R) A = SOME (subst u 0 (lam t)::A)`
    by metis_tac[substP_rep_subst, repsP] >>
  `∀A1. stepLs (lam t::lam u::A) A1 ⇒
   deltaT (appT P::Ts) (lam t::lam u::A) = SOME [s] ⇒
   ∃B'. stepLs [s] B' ∧ deltaT (appT P::Ts) A1 = SOME B'`
      by metis_tac[stepLs_decompileTask] >> gvs[] >>
  pop_assum mp_tac >> rw[Once deltaT, Once delta] >>
  `stepL (app (lam u) (lam t)) (subst u 0 (lam t))`
    by metis_tac[stepL_cases] >>
  drule decompileArg_abstractions >> rw[] >> gvs[] >>
  `stepLs ((app (lam u) (lam t))::A) ((subst u 0 (lam t))::A)`
    by metis_tac[stepLs_rules] >>
  drule_all stepLs_decomp >> rw[] >> gvs[] >>
  drule_all stepLs_decompileTask >> rw[] >>
  drule stepLs_singleton_inv >> rw[] >>
  qexists_tac `t'`  >> rw[] >>
  drule decompileTask_step >> rw[] >>
  rw[Once deltaT]
QED

Inductive stuckLs:
  (∀s A. Forall abstraction A ∧ stuck s ⇒ stuckLs (s::A)) ∧
  (∀s A. stuckLs A ⇒ stuckLs (s::A))
End

(* Lemma 24 *)
Theorem stuck_decompile:
  ∀P A B.
    stuckLs A ⇒
    delta P A = SOME B ⇒
    stuckLs B
Proof
  ho_match_mp_tac delta_ind >> rw[] >>
  pop_assum mp_tac >> simp[Once delta] >>
  simp[AllCaseEqs()] >> rw[] >> rw[]
  >- fs[Once stuckLs_cases]
  >- (fs[Once stuckLs_cases] >>
      first_x_assum irule >> rw[] >>
      qpat_x_assum `stuckLs (t::s::A')` mp_tac >>
      rw[Once stuckLs_cases]
      >- (qpat_x_assum `Forall abstraction (s::A')` mp_tac >>
          rw[Once Forall_cases, Once stuck_cases, Once abstraction_cases])
      >> qpat_x_assum `stuckLs (s::A')` mp_tac >>
      rw[Once stuckLs_cases] >> rw[Once stuck_cases])
  >> metis_tac[stuckLs_cases]
QED

(* Lemma 25 *)
Theorem stuck_decompileTask:
  ∀Ts A B.
    stuckLs A ⇒
    deltaT Ts A = SOME B ⇒
    stuckLs B
Proof
  ho_match_mp_tac deltaT_ind >> rw[] >>
  pop_assum mp_tac >> simp[Once deltaT] >>
  simp[AllCaseEqs()] >> rw[] >> rw[] >>
  metis_tac[stuck_decompile]
QED

(* Fact 26. Trichotomy *)
Theorem stateS_trichotomy:
  ∀Ts V s.
    repsSL (Ts, V) s ⇒
    reducible (any stepS) (Ts, V)
    ∨ (∃P s'. (Ts, V) = ([], [P]) ∧ s = lam s' ∧ repsP P s')
    ∨ (∃x P T'. Ts = varT x P::T' ∧ stuck s)
Proof
  rw[repsSL, reducible, any] >> fs[Once deltaT] >>
  drule decompileArg_abstractions >> rw[] >>
  Cases_on `Ts` >> rw[]
  (* [] *)
  >- (rw[repsP] >>
      fs[Once deltaV] >> Cases_on `V` >> fs[] >>
      Cases_on `delta h []` >> fs[] >>
      Cases_on `x` >> fs[] >>
      Cases_on `deltaV t` >> fs[] >>
      Cases_on `t'` >> fs[] >> rw[] >>
      fs[Once deltaV] >>
      Cases_on `t` >> fs[] >>
      Cases_on `delta h'' []`  >> fs[] >>
      Cases_on `x` >> fs[] >>
      Cases_on `deltaV t'` >> fs[] >>
      Cases_on `t` >> fs[]) >>
  Cases_on `h` >> fs[]
  (* retT *)
  >- (fs[Once delta] >> rw[Once stepS_cases] >>
      Cases_on `delta P0 (var n::A)` >> fs[])
  (* varT *)
  >- (Cases_on `delta (varT n P0) A` >> fs[] >>
      fs[Once delta] >>
      `stuck (var n)` by rw[Once stuck_rules] >>
      `stuckLs (var n::A)` by rw[Once stuckLs_rules] >>
      drule_all stuck_decompile >> rw[] >>
      drule_all stuck_decompileTask >> rw[] >>
      pop_assum mp_tac >> rw[Once stuckLs_cases] >> rw[] >>
      pop_assum mp_tac >> rw[Once stuckLs_cases])
  (* appT *)
  >- (rw[Once stepS_cases] >>
      Cases_on `delta (appT P0) A` >> fs[] >>
      fs[Once deltaV] >>
      Cases_on `V` >> fs[]
      >- (Cases_on `delta (appT P0) A` >> fs[] >>
          rw[] >> fs[Once delta])
      >> Cases_on `delta h []` >> fs[] >>
      Cases_on `x'` >> fs[] >>
      Cases_on `deltaV t'` >> fs[] >>
      Cases_on `t''` >> fs[] >>
      fs[Once deltaV] >>
      Cases_on `t'` >> fs[] >>
      rw[] >> fs[Once delta])
  (* lamT *)
  >> rw[Once stepS_cases]
QED

(* Corollary 27. Progress *)
Theorem reducible_red:
  ∀conf s.
    repsSL conf s ⇒
    reducible stepL s ⇒
    reducible (any stepS) conf
Proof
  rw[] >> PairCases_on `conf` >>
  drule stateS_trichotomy >> rw[]
  >- fs[reducible, Once stepL_cases]
  >> drule stuck_normal >> rw[]
QED

(* Theorem 28. Naive Stack Machine to L *)
Theorem stack_L_refinement:
  refinement_ARS repsSL (stepS τ) (stepS β) stepL
Proof
  rw[refinement_ARS]
  >- (drule reducible_red >>
      rw[] >> fs[reducible, any] >>
      Cases_on `l` >> metis_tac[RUNION])
  >- (PairCases_on `a` >> PairCases_on `a'` >> metis_tac[tau_simulation])
  >- (PairCases_on `a` >> PairCases_on `a'` >> metis_tac[beta_simulation])
  >> metis_tac[tau_terminating]
QED

Theorem compile_stack_L:
  ∀s.
    repsSL ([gamma s retT], []) s
Proof
  rw[repsSL] >> qexists_tac `[]` >> rw[Once deltaV, Once deltaT] >>
  `delta (gamma s retT) [] = delta retT (s::[])`
    by metis_tac[decompile_correct] >> rw[Once delta, Once deltaT]
QED

val _ = export_theory ()