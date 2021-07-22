open HolKernel Parse boolLib bossLib;
open arithmeticTheory;
open listTheory;
open PrelimsTheory;
open relationTheory;

val _ = new_theory "Refinements";

Datatype:
	label = τ | β
End

Type tbrel = ``:label -> 'a -> 'a -> bool``;

Type rel = ``:'a -> 'a -> bool``;

Definition any:
	any R x y = ∃l. R (l:label) x y
End

(*
Structure Machine :=
  {
    M_A :> Type ;
    M_rel : τβ_rel M_A
  }.
Local Notation "(≻τ)" := (@M_rel _ τ).
Local Notation "a '≻τ' a'" := (@M_rel _ τ a a') (at level 40).
Local Notation "a '≻β' a'" := (@M_rel _ β a a') (at level 40).
*)

(*Definition M_any (A : Machine) (a a' : A) := (a ≻τ a' \/ a ≻β a').*)

(*
Canonical Structure Machine_ARS (A : Machine) : ARS :=
  {|
    ARS_X := A ;
    ARS_R := any (@M_rel A)
  |}.

Coercion Machine_ARS : Machine >-> ARS.
*)

(* Section absSim. *)

  (* Section refine_ARS.

    Variable X : ARS.
    Variable A : Machine.

    Variable refines: A -> X -> Prop.
    Notation "a ≫ x" := (refines a x) (at level 70). *)

Definition refinement_ARS:
  refinement_ARS (refs: 'a -> 'b -> bool) (Rt: 'a rel) (Rb: 'a rel) (Rx: 'b rel)  =
  	((∀a x. refs a x ∧ reducible Rx x ⇒ reducible (Rt ∪ᵣ Rb) a) ∧
     (∀a a' x. refs a x ∧ Rt a a' ⇒ refs a' x) ∧
  	 (∀a a' x. refs a x ∧ Rb a a' ⇒ (∃x'. refs a' x' ∧ Rx x x')) ∧
  	 (∀a x. refs a x ⇒ terminatesOn Rt a))
End
(*
    Definition refinement_ARS :=
      (forall a x, a ≫ x -> reducible (≻) x -> reducible (≻) a) /\
      (forall a a' x, a ≫ x -> a ≻τ a' -> a' ≫ x) /\
      (forall a a' x, a ≫ x -> a ≻β a' -> exists x', a' ≫ x' /\ x ≻ x') /\
      (forall a x, a ≫ x -> terminatesOn (≻τ) a).
*)
(*  End refine_ARS. *)

(* Section assume_refine.

    Variable A : Machine.
    Variable X : ARS.
    Notation "a ▷τ a'" := (@evaluates (Build_ARS (M_rel τ)) a a') (at level 40).

    Variable refines: A -> X -> Prop.
    Notation "a ≫ x" := (refines a x) (at level 70).

    Hypothesis refinement : refinement_ARS refines.

    Section Correctness.
      Variable a : A. Variable x : X.
      Hypothesis H : a ≫ x.
*)

Theorem upSim:
  ∀refs Rx Rt Rb a x a'.
    refinement_ARS refs Rt Rb Rx ⇒
    refs a x ⇒
    evaluates (Rt ∪ᵣ Rb) a a' ⇒
    (∃x'. refs a' x' ∧ evaluates Rx x x')
Proof
  rw[] >> pop_assum mp_tac >> pop_assum mp_tac >>
  MAP_EVERY qid_spec_tac [`x`, `a'`, `a`] >>
  Induct_on `evaluates` >> rw[]
  >- (fs[refinement_ARS] >> qexists_tac `x` >> rw[] >>
      simp[Once evaluates_cases] >> DISJ1_TAC >>
      CCONTR_TAC >> rw[] >> last_x_assum drule >> strip_tac >>
      first_x_assum drule >> rw[])
  >> fs[refinement_ARS] >> fs[RUNION]
  >- metis_tac[]
  >> `∃x'. refs a' x' ∧ Rx x x'` by metis_tac[] >>
  first_x_assum drule >> rw[] >> metis_tac[evaluates_cases]
QED

Theorem rightValue:
  ∀refs Rx Rt Rb a x a' x'.
    refinement_ARS refs Rt Rb Rx ⇒
    refs a x ⇒
    evaluates (Rt ∪ᵣ Rb) a a' ⇒
    refs a' x' ⇒
    functional refs ⇒
    evaluates Rx x x'
Proof
  rw[] >> drule_all upSim >> rw[] >>
  `x' = x''` by metis_tac[functional] >>
  gvs[]
QED

Theorem termination_propagates:
  ∀refs Rx Rt Rb a x.
    refinement_ARS refs Rt Rb Rx ⇒
    refs a x ⇒
    terminatesOn Rx x ⇒
    terminatesOn (Rt ∪ᵣ Rb) a
Proof
  Induct_on `terminatesOn` >>  rw[] >>
  rw[Once terminatesOn_cases] >>
  rename [`(Rt ∪ᵣ Rb) a a'`] >> reverse(fs[RUNION])
  >- (qhdtm_assum `refinement_ARS` mp_tac >> PURE_REWRITE_TAC[refinement_ARS] >> strip_tac >>
      first_x_assum(drule_then drule) >> strip_tac >>
      last_x_assum drule >> strip_tac >> first_x_assum (match_mp_tac o MP_CANON) >>
      goal_assum drule >> rw[])
  >> qhdtm_assum `refinement_ARS` mp_tac >> PURE_REWRITE_TAC[refinement_ARS] >> strip_tac >>
  `refs a' x` by metis_tac[] >> pop_assum mp_tac >>
  first_x_assum drule >>
  simp[Once terminatesOn_cases] >> strip_tac >>
  first_x_assum drule >> ntac 5 (pop_assum kall_tac) >>
  pop_assum mp_tac >> Induct_on `terminatesOn` >> rw[] >>
  rename [`terminatesOn (Rt ∪ᵣ Rb) a`] >> rw[Once terminatesOn_cases] >>
  rename [`(Rt ∪ᵣ Rb) a a'`] >> reverse(fs[RUNION])
  >- (qhdtm_assum `refinement_ARS` mp_tac >> PURE_REWRITE_TAC[refinement_ARS] >> strip_tac >>
      first_x_assum(drule_then drule) >> strip_tac >>
      last_x_assum drule >> strip_tac >> first_x_assum (match_mp_tac o MP_CANON) >>
      goal_assum drule >> rw[])
  >> metis_tac[refinement_ARS]
QED

Theorem evaluation_propagates:
  ∀refs Rx Rt Rb a x.
    refinement_ARS refs Rt Rb Rx ⇒
    refs a x ⇒
    terminatesOn Rx x ⇒
    computable (Rt ∪ᵣ Rb) ⇒
    (∃a'. evaluates (Rt ∪ᵣ Rb) a a')
Proof
  rw[] >> drule termination_propagates >> rw[] >>
  first_x_assum drule >> rw[] >>
  drule terminates_normalizes >> rw[] >>
  fs[normalizes]
QED

Theorem refinement_correctness: (* Fact6 *)
  ∀refs Rx Rt Rb a x.
    refinement_ARS refs Rt Rb Rx ⇒
    refs a x ⇒
    (* upSim *)
    (∀a'.
      evaluates (Rt ∪ᵣ Rb) a a' ⇒ ∃x'. refs a' x' ∧ evaluates Rx x x') ∧
    (* rightValue *)
    (∀a' x'.
      evaluates (Rt ∪ᵣ Rb) a a' ⇒
      refs a' x' ⇒
      functional refs ⇒
      evaluates Rx x x') ∧
    (* termination_propagates *)
    (terminatesOn Rx x ⇒ terminatesOn (Rt ∪ᵣ Rb) a) ∧
    (* evaluation_propagates *)
    (terminatesOn Rx x ⇒
     computable (Rt ∪ᵣ Rb) ⇒
     ∃a'. evaluates (Rt ∪ᵣ Rb) a a')
Proof
  metis_tac[upSim, rightValue, termination_propagates, evaluation_propagates]
QED

Theorem tau_evaluates_evaluates:
  ∀refs Rx Rt Rb a x a'.
  	refinement_ARS refs Rt Rb Rx ⇒
    refs a x ⇒
    ¬reducible Rx x ⇒
    evaluates Rt a a' ⇒
    evaluates (Rt ∪ᵣ Rb) a a'
Proof
  ntac 10 strip_tac >> qpat_x_assum (`refs a x`) mp_tac >>
  pop_assum mp_tac >>
  MAP_EVERY qid_spec_tac [`a`, `a'`, `x`] >>
  Induct_on `evaluates` >> rw[]
  >- (fs[refinement_ARS] >> simp[Once evaluates_cases] >>
      Cases_on `¬reducible (Rt ∪ᵣ Rb) a` >> rw[] >>
      pop_assum mp_tac >> rw[reducible, RUNION]
      >- gvs[reducible]
      >> `∃y. refs x' y ∧ Rx x y` by metis_tac[] >>
      gvs[reducible])
  >> fs[refinement_ARS] >> first_x_assum drule >> rw[] >>
  `refs a' x` by metis_tac[] >> first_x_assum drule >> rw[] >>
  rw[Once evaluates_cases] >> DISJ2_TAC >>
  qexists_tac `a'` >> rw[] >> rw[RUNION]
QED

Theorem evaluates_tau:
	∀refs Rx Rt Rb a x a' a''.
    refinement_ARS refs Rt Rb Rx ⇒
    refs a x ⇒
    evaluates Rt a a' ⇒
    evaluates (Rt ∪ᵣ Rb) a' a'' ⇒
    evaluates (Rt ∪ᵣ Rb) a a''
Proof
  ntac 9 strip_tac >>
  MAP_EVERY qid_spec_tac [`a''`, `a'`, `a`, `x`] >>
  Induct_on `evaluates` >> rw[] >> fs[refinement_ARS] >>
  `refs a' x` by metis_tac[] >>
  first_x_assum drule >> rw[] >>
  first_x_assum drule >> rw[] >>
  rw[Once evaluates_cases] >> metis_tac[RUNION]
QED

Theorem tau_eval:
  ∀refs Rx Rt Rb a x a'.
    refinement_ARS refs Rt Rb Rx ⇒
    functional Rx ⇒
    computable Rt ⇒
    refs a x ⇒
    evaluates Rt a a' ⇒
    refs a' x
Proof
  ntac 10 strip_tac >>
  MAP_EVERY qid_spec_tac [`a'`, `a`, `x`] >>
  Induct_on `evaluates` >> rw[] >> fs[refinement_ARS] >>
  `refs a' x` by metis_tac[] >>
  metis_tac[]
QED

Theorem one_downSim:
  ∀refs Rx Rt Rb a x x'.
    refinement_ARS refs Rt Rb Rx ⇒
    functional Rx ⇒
    computable Rt ⇒
    refs a x ⇒
    Rx x x' ⇒
    ∃a' a''. evaluates Rt a a'' ∧ Rb a'' a' ∧ refs a' x'
Proof
  rw[] >> qhdtm_assum `refinement_ARS` mp_tac >>
  PURE_REWRITE_TAC[refinement_ARS] >> strip_tac >>
  fs[reducible] >>
  `terminatesOn Rt a` by metis_tac[] >>
  drule_all terminates_normalizes >> rw[] >>
  fs[normalizes] >> drule evaluates_irred >> rw[] >>
  rename[`evaluates Rt a a''`] >>
  drule_all tau_eval >> rw[] >>
  `∃a'. (Rt ∪ᵣ Rb) a'' a'` by metis_tac[] >> fs[RUNION]
  >- metis_tac[reducible]
  >> metis_tac[functional]
QED

Theorem downSim:
  ∀refs Rx Rt Rb a x x'.
    refinement_ARS refs Rt Rb Rx ⇒
    functional Rx ⇒
    computable Rt ⇒
    refs a x ⇒
    evaluates Rx x x' ⇒
    ∃a'. evaluates (Rt ∪ᵣ Rb) a a' ∧ refs a' x'
Proof
  ntac 10 strip_tac >>
  MAP_EVERY qid_spec_tac [`x'`, `x`, `a`] >>
  Induct_on `evaluates` >> rw[]
  >- (qhdtm_assum `refinement_ARS` mp_tac >>
      PURE_REWRITE_TAC[refinement_ARS] >> strip_tac >>
      first_x_assum drule >> rw[] >>
      drule_all terminates_normalizes >> rw[] >>
      fs[normalizes] >> rw[] >>
      drule_all tau_evaluates_evaluates >> rw[] >>
      rename [`evaluates (Rt ∪ᵣ Rb) a a'`] >>
      qexists_tac `a'` >> rw[] >>
      drule_all tau_eval >> rw[])
  >> drule_all one_downSim >> rw[] >>
  first_x_assum drule >> rw[] >>
  rename [`evaluates (Rt ∪ᵣ Rb) a' a1`] >>
  qexists_tac `a1` >> rw[] >>
  `evaluates (Rt ∪ᵣ Rb) a'' a1`
    by (rw[Once evaluates_cases] >>
        DISJ2_TAC >> qexists_tac `a'` >> rw[RUNION]) >>
  metis_tac[evaluates_tau]
QED

Theorem fact7:
  ∀refs Rx Rt Rb a x x'.
    refinement_ARS refs Rt Rb Rx ⇒
    functional Rx ⇒
    computable Rt ⇒
    refs a x ⇒
    (Rx x x' ⇒
     ∃a' a''. evaluates Rt a a'' ∧ Rb a'' a' ∧ refs a' x') ∧
    (evaluates Rx x x' ⇒
     ∃a'. evaluates (Rt ∪ᵣ Rb) a a' ∧ refs a' x')
Proof
  metis_tac[one_downSim, downSim]
QED

(*
  Section refine_M.

    Variable A : Machine.
    Variable B : Machine.

    Variable refines: A -> B -> Prop.
    Notation "a ≫ b" := (refines a b) (at level 70).
*)

(* refinement_M (refs: 'a -> 'b -> bool) (RtA: 'a rel) (RbA: 'a rel) (RtB: 'b rel) (RbB: 'b rel) *)
Definition refinement_M:
  refinement_M refs RtA RbA RtB RbB ⇔
  	(∀a b. refs a b ∧ reducible (RtB ∪ᵣ RbB) b ⇒ reducible (RtA ∪ᵣ RbA) a) ∧
  	(∀a a' b. refs a b ∧ RtA a a' ⇒ (∃b'. refs a' b' ∧ RtB b b')) ∧
  	(∀a a' b. refs a b ∧ RbA a a' ⇒ (∃b'. refs a' b' ∧ RbB b b'))
End

(* refsR: A -> B -> bool
   refsS: B -> X -> bool *)
Theorem composition:
  ∀refsR refsS RtA RbA RtB RbB Rx.
    refinement_M refsR RtA RbA RtB RbB ⇒
    refinement_ARS refsS RtB RbB Rx ⇒
  	refinement_ARS (λa c. (∃b. refsR a b ∧ refsS b c)) RtA RbA Rx
Proof
  rw[refinement_ARS, refinement_M]
  >- metis_tac[]
  >- metis_tac[]
  >- metis_tac[]
  >> first_x_assum drule >> rw[] >>
  ntac 9 (pop_assum mp_tac) >>
  MAP_EVERY qid_spec_tac [`refsR`, `RtB`, `RbB`, `RtA`, `RbA`, `refsS`, `a`,`b`,`c`,`Rx`] >>
  Induct_on `terminatesOn` >> rw[] >>
  rw[Once terminatesOn_cases] >> rename [`terminatesOn RtA a'`] >>
  `∃b'. refsR a' b' ∧ RtB b b'` by metis_tac[] >>
  last_x_assum drule >> rw[] >>
  `refsS b' c` by metis_tac[] >>
  ntac 8 (first_x_assum (drule_then assume_tac)) >> rw[]
QED

val _ = export_theory ()