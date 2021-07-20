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
  refinement_ARS (refs: 'a -> 'b -> bool) (Rx: 'b rel) (Rt: 'a rel) (Rb: 'a rel)  =
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
    refinement_ARS refs Rx Rt Rb ⇒
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
    refinement_ARS refs Rx Rt Rb ⇒
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
    refinement_ARS refs Rx Rt Rb ⇒
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

(*
      Lemma termination_propagates :
        terminatesOn (≻X) x -> terminatesOn (≻A) a.
      Proof.
        destruct refinement as (R1 & R2 & R3 & R4).
        intros N. induction N as [x wf H0] in a, H |- *.
        induction (R4 a x H).
        constructor. intros a' [ [] Hstep].
        - eauto.
        - eapply R3 in Hstep as (? & ? & ?); eauto.
      Qed.*)

Theorem evaluation_propagates:
  ∀refs Rx Rt Rb a x.
    refinement_ARS refs Rx Rt Rb ⇒
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

(*
      Lemma evaluation_propagates:
        terminatesOn (≻X) x -> computable (≻A) ->
        exists (a':A), a ▷ a'.
      Proof.
 intros Hter C. specialize Hter as Hter % termination_propagates % terminates_normalizes. all: eauto using evaluates.
      Qed.*)

Theorem refinement_correctness: (* Fact6 *)
  ∀refs Rx Rt Rb a x.
    refinement_ARS refs Rx Rt Rb ⇒
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
  	refinement_ARS refs Rx Rt Rb ⇒
    refs a x ⇒
    ¬reducible Rx x ⇒
    evaluates Rt a a' ⇒
    evaluates (Rt ∪ᵣ Rb) a a'
Proof
  rw[] >> pop_assum mp_tac >> qpat_x_assum (`refs a x`) mp_tac >> qid_spec_tac `a` >> qid_spec_tac `a'` >>
  Induct_on `evaluates` >> rw[]
  >- (fs[refinement_ARS] >> )
  >>
QED
(*
      Lemma tau_evaluates_evaluates a' : ~ reducible (≻X) x -> a ▷τ a' -> a ▷ a'.
      Proof.
        intros H2. destruct refinement as (R1 & R2 & R3 & R4). induction 1 as [a |] in x, H, H2 ; cbn in *.
        - econstructor. intros (? & [] & ?). eauto. destruct (R3 _ _ _ H H1) as (? & ? & ?). eauto.
        - econstructor. exists τ. eauto. eauto.
      Qed.*)

Theorem evaluates_tau:
	evaluates Rt a a' ⇒ (evaluates Ra a' a'') ⇒ evaluates Ra a a''
Proof
QED
(*
      Lemma evaluates_tau a' a'' : a ▷τ a' -> (evaluates (X := A) a' a'') -> a ▷ a''.
      Proof.
        induction 1 in a'', H; cbn in *.
        - eauto.
        - intros. eapply IHevaluates in H2.
          + econstructor. exists τ. eauto. eauto.
          + eapply refinement; eauto.
      Qed.*)
(*    End Correctness. *)

(*    Section top_down.
      Variable FN :functional (≻X).
      Variable C : computable (X:=A) (≻τ). *)

Theorem tau_eval:
	computable Rt ⇒ refinement a x ⇒ evaluates Rt a a' ⇒ refinement a' x
Proof
QED
(*
      Lemma tau_eval a x a' :
        a ≫ x -> a ▷τ a' -> a' ≫ x.
      Proof.
        intros H. destruct refinement as (R1 & R2 & R3 & R4).
        induction 1; eauto.
      Qed.*)

Theorem fact7:
	(refinement a x ∧ functional Rx ∧ computable Rt) ⇒
	((refinement a x ⇒ Rx x x' ⇒ ∃a' a''. evaluates Rt a a'' ∧ Rb a'' a' ∧ refinement a' x') ∧
	  refinement a x ⇒ evaluates Rx x x' ⇒ ∃a'. evaluates Ra a a' ∧ refinement a' x')
Proof
QED
(*
      Lemma one_downSim a x x' :
        a ≫ x -> x ≻ x' -> exists a' a'', a ▷τ a'' /\ a'' ≻β a' /\ a' ≫ x'.
      Proof.
        intros H H1. destruct refinement as (R1 & R2 & R3 & R4). cbn in *.
        destruct (@terminates_normalizes (Build_ARS (M_rel τ)) C _ (R4 _ _ H)) as [a'' H2].
        edestruct (R1 _ _ (tau_eval H H2)) as [a' [[] H3]]. eexists; eauto.
        - exists a', a''. edestruct evaluates_irred; eauto.
        - exists a',a''. repeat split; eauto. destruct (R3 _ _ _ (tau_eval H H2) H3) as (x'' & ? & H5).
          now rewrite (FN H1 H5).
      Qed.
      Lemma downSim a x x' :
      a ≫ x -> x ▷ x' -> exists a', a ▷ a' /\ a' ≫ x'.
    Proof.
      intros H H1. destruct refinement as (R1 & R2 & R3 & R4). induction H1 in a, H |- *; cbn in *;[intros|].
      - destruct (@terminates_normalizes (Build_ARS (M_rel τ)) C _ (R4 _ _ H)) as [a' H2].
        exists a'. split. eapply tau_evaluates_evaluates; eauto. eapply tau_eval; eauto.
      - destruct (one_downSim H H0) as (a' & a'' & ? & ? & ?). cbn in *.
        destruct (IHevaluates _ H4) as (a''' & ? & ?).
        exists a'''. split. eapply evaluates_tau; eauto. econstructor. exists β. eauto. eauto. eauto.
    Qed.
  End top_down.

  End assume_refine.
*)
(*
  Section refine_M.

    Variable A : Machine.
    Variable B : Machine.

    Variable refines: A -> B -> Prop.
    Notation "a ≫ b" := (refines a b) (at level 70).
*)

Definition refinement_M:
	(∀a b. refinement_M a b ⇒ reducible RB b ⇒ reducible RA a) ∧
	(∀a a' b. refinement_M a b ⇒ Rt a a' ⇒ ∃b' refinement_M a' b' ∧ Rt b b') ∧
	(∀a a' b. refinement_M a b ⇒ Rb a a' ⇒ ∃b'. refinement_M a' b' ∧ Rb b b')
End

(*
    Definition refinement_M :=
      (forall a b, a ≫ b -> reducible (≻) b -> reducible (≻) a) /\
      (forall a a' b, a ≫ b -> a ≻τ a' -> exists b', a' ≫ b' /\ b ≻τ b') /\
      (forall a a' b, a ≫ b -> a ≻β a' -> exists b', a' ≫ b' /\ b ≻β b').

  End refine_M.
*)

Theorem composition:
	refinement_M R ⇒ refinement S ⇒ refinement (∃b. R a b ∧ S b c)
Proof
QED
(*
  Lemma composition (A B : Machine) (X : ARS) (R : A -> B -> Prop) (S : B -> X -> Prop) :
    refinement_M R -> refinement_ARS S -> refinement_ARS (fun a c => exists b, R a b /\ S b c).
  Proof.
    intros (H & H0 & H1) (H2 & H3 & H4 & H5). do 3 try split; intros.
    - destruct H6 as (? & ? & ?). eauto.
    - destruct H6 as (? & ? & ?). destruct (H0 _ _ _ H6 H7) as (? & ? & ?). eauto.
    - destruct H6 as (? & ? & H8). destruct (H1 _ _ _ H6 H7) as (? & ? & H10).
      destruct (H4 _ _ _ H8 H10) as (? & ? & ?). eauto.
    - destruct H6 as (? & ? & H7). specialize (H5 _ _ H7).
      clear H7. induction H5 in a, H6. econstructor. intros ? H7.
      destruct (H0 _ _ _ H6 H7) as (? & ? & ?). eauto.
  Qed.
End absSim.
*)


val _ = export_theory ()