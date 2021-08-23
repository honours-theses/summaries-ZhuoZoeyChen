open HolKernel Parse boolLib bossLib;
open PrelimsTheory RefinementsTheory LTheory ProgramsTheory;
open ClosuresTheory M_closTheory CodesTheory;
open HeapsTheory;
open relationTheory;

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
*)

(* stackStack and Heap *)
Type state = ``:(('a HC) list # ('a HC) list # ('b Heap))``;

(* label -> state -> state -> Prop *)
(* "σ ≻H_ l σ'" := (stepH l σ σ'). *)
Inductive stepH:
[~nil:]
  (∀hImpl C p a T V H.
    codeImpl.phi C p = SOME retC ⇒
    stepH hImpl C τ ((p,a)::T,V,H) (T,V,H)) ∧
[~load:]
  (∀hImpl C p a x e T V H.
    codeImpl.phi C p = SOME (varC x) ∧
    lookup hImpl H a x = SOME e ⇒
    stepH hImpl C τ ((p,a)::T,V,H) ((codeImpl.inc p,a)::T,e::V,H)) ∧
[~pushVal:]
  (∀hImpl C p q a T V H.
    codeImpl.phi C p = SOME (lamC q) ⇒
    stepH hImpl C τ ((p,a)::T,V,H) ((codeImpl.inc p,a)::T,(q,a)::V,H)) ∧
[~beta:]
  (∀hImpl C a b b' g p q H H' T V.
    codeImpl.phi C p = SOME (appC) ∧
    hImpl.put H g b = (H',b') ⇒
    stepH hImpl C β ((p,a)::T,g::(q,b)::V,H) ((q,b')::(codeImpl.inc p,a)::T,V,H'))
End
(*
  Reserved Notation "σ ≻H_ l σ'" (at level 70, l at level 0,format "σ '≻H_' l σ'").

  Notation "(≻H_ l )" := (stepH l) (at level 0, format "'(≻H_' l ')'").*)
  (* Notation "σ ≻H_ l σ'" := 0.
  Notation "σ ≻H_ l σ'" := (stepH l σ σ').
  Notation "σ ≻H σ'" := (any stepH σ σ') (at level 70).
  Notation "(≻H)" := (any stepH) (at level 0).

  Canonical Structure heap_machine := {| M_rel := stepH |}.
*)

(* state -> stateC -> Prop *)
Inductive repsHC:
[representsC:]
  (∀hImpl C H T V T' V'.
    Forall2 (representsClos hImpl C H) T T' ∧
    Forall2 (representsClos hImpl C H) V V' ⇒
    repsHC hImpl C (T,V,H) (T',V'))
End

(*
Inductive repsHC : state -> stateC -> Prop :=
| representsC H T V T' V': Forall2 (≫C_H) T T' -> Forall2 (≫C_H) V V' -> repsHC (T,V,H) (T',V').

Hint Constructors repsHC.
Notation "(≫HC)" := (repsHC) (at level 0).
Notation "ψ '≫HC' π" := (repsHC ψ π) (at level 70).
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

Inductive representsClos:
[~C:]
  (∀hImpl p a P E.
    representsPro C p P ∧
    representsEnv hImpl C H a E ⇒
    representsClos hImpl C H (p,a) (closC P E))
End

Inductive representsEnv:
[~Nil:]
  (∀hImpl C H a. hImpl.get H a = SOME NONE ⇒ representsEnv hImpl C H a []) ∧
[~Cons:]
  (∀hImpl C H a b c p P F E.
         hImpl.get H a = SOME (SOME ((p, b), c)) ∧
         representsPro C p P ∧
         representsEnv hImpl C H b F ∧
         representsEnv hImpl C H c E ⇒
         representsEnv hImpl C H a ((closC P F)::E))
End

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

Theorem step_simulation:
  ∀hImpl C π π' ψ l.
    HR hImpl ⇒
    repsHC hImpl C π ψ ⇒
    stepH hImpl C l π π' ⇒
    ∃ψ'. repsHC hImpl C π' ψ' ∧ stepC l ψ ψ'
Proof
  rw[] >> PairCases_on `π` >> PairCases_on `ψ` >>
  PairCases_on `π'` >>
  qpat_x_assum `repsHC _ _ _ _` mp_tac >>
  rw[Once repsHC_cases] >>
  fs[Once stepH_cases] >> rw[] (* 4 *)
  >- (rw[Once repsHC_cases, PULL_EXISTS] >>
      qpat_x_assum `Forall2 _ (_::_) _` mp_tac >>
      rw[Once Forall2_cases] >>
      qexistsl_tac [`l'`, `ψ1`] >> rw[] >>
      rw[Once stepC_cases] >>
      qpat_x_assum `representsClos _ _ _ _ _` mp_tac >>
      rw[Once representsClos_cases] >>
      qpat_x_assum `representsPro _ _ _` mp_tac >>
      rw[Once representsPro_cases])
  >- (PairCases_on `e`  >>
      qpat_x_assum `Forall2 _ (_::_) _` mp_tac >>
      rw[Once Forall2_cases] >>
      qpat_x_assum `representsClos _ _ _ _ _` mp_tac >>
      rw[Once representsClos_cases] >>
      qpat_x_assum `representsPro _ _ _` mp_tac >>
      rw[Once representsPro_cases] >>
      drule_all lookup_unlinedEnv >> rw[] >>
      Cases_on `e` >>
      rename [`nth_error x E = SOME (closC P E0)`,
              `representsPro C (codeImpl.inc p) P0`] >>
      qexists_tac `(closC P0 E :: l', closC P E0 :: ψ1)` >>
      rw[] (* 2 *)
      (* repsHC *)
      >- (rw[Once repsHC_cases] >> (* 2 *)
          rw[Once Forall2_cases] >>
          rw[Once representsClos_cases])
      (* stepC *)
      >> rw[Once stepC_cases])
  >- (qpat_x_assum `Forall2 _ (_::_) _` mp_tac >>
      rw[Once Forall2_cases] >>
      qpat_x_assum `representsClos _ _ _ _ _` mp_tac >>
      rw[Once representsClos_cases] >>
      qpat_x_assum `representsPro _ _ _` mp_tac >>
      rw[Once representsPro_cases] >>
      rename [`representsPro C (codeImpl.inc p) P0`] >>
      qexists_tac `(closC P0 E :: l', closC Q E :: ψ1)` >>
      rw[] (* 2 *)
      (* repsHC *)
      >- (rw[Once repsHC_cases] >> (* 2 *)
          rw[Once Forall2_cases] >>
          rw[Once representsClos_cases])
      (* stepC *)
      >> rw[Once stepC_cases])
  >> pop_assum mp_tac >> rw[Once Forall2_cases] >>
  pop_assum mp_tac >> rw[Once Forall2_cases] >>
  qpat_x_assum `Forall2 _ (_::_) _` mp_tac >>
  rw[Once Forall2_cases] >>
  fs[HR, HR1, HR2] >>
  first_x_assum drule >> rw[] >>
  first_x_assum drule >> rw[] >>
  qpat_x_assum `representsClos hImpl C π2 g y` mp_tac >>
  rw[Once representsClos_cases] >>
  rename [`representsPro C p0 P`, `representsEnv hImpl C π2 a0 E`] >>
  qpat_x_assum `representsClos hImpl C π2 (q,b) y'` mp_tac >>
  rw[Once representsClos_cases] >>
  rename [`representsPro C q P0`, `representsEnv hImpl C π2 b E0`] >>
  qpat_x_assum `representsClos _ _ _ (p,a) _` mp_tac >>
  rw[Once representsClos_cases] >>
  rename [`representsPro C p P2`, `representsEnv hImpl C π2 a E1`] >>
  qpat_x_assum `representsPro C p P2` mp_tac >>
  rw[Once representsPro_cases] >>
  rename [`representsPro C (codeImpl.inc p) P2`] >>
  qexists_tac `(closC P0 (closC P E :: E0) :: (closC P2 E1) :: l', l'')` >>
  rw[] (* 2 *)
  (* repsHC *)
  >- (rw[Once repsHC_cases]
      >- (rw[Once Forall2_cases]
          >- (rw[Once representsClos_cases] >>
              rw[Once representsEnv_cases] >>
              metis_tac[representsEnv_extend])
          >> rw[Once Forall2_cases]
          >- (rw[Once representsClos_cases] >>
              metis_tac[representsEnv_extend])
          >> metis_tac[representsClos_extend, Forall2_impl])
      >> metis_tac[representsClos_extend, Forall2_impl])
  (* stepC *)
  >> rw[Once stepC_cases]
QED

(*
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
*)

Theorem reducible_red:
  ∀hImpl C π ψ.
    repsHC hImpl C π ψ ⇒
    reducible (any stepC) ψ ⇒
    reducible (any (stepH hImpl C)) π
Proof
  rw[Once repsHC_cases, Once stepC_cases, Once stepH_cases,
     reducible, any]
  >- (qpat_x_assum `Forall2 _ T' _` mp_tac >>
      rw[Once Forall2_cases] >>
      qexistsl_tac [`(l,V,H)`, `τ`] >> rw[] >>
      fs[Once representsClos_cases] >>
      fs[Once representsPro_cases])
  >- (qpat_x_assum `Forall2 _ T' _` mp_tac >>
      rw[Once Forall2_cases] >>
      fs[Once representsClos_cases] >>
      fs[Once representsPro_cases] >>
      metis_tac[nth_error_unlinedEnv])
  >- (qpat_x_assum `Forall2 _ T' _` mp_tac >>
      rw[Once Forall2_cases] >>
      fs[Once representsClos_cases] >>
      fs[Once representsPro_cases])
  >> qpat_x_assum `Forall2 _ T' _` mp_tac >>
  rw[Once Forall2_cases] >>
  fs[Once representsClos_cases] >>
  fs[Once representsPro_cases] >>
  qpat_x_assum `Forall2 _ V _` mp_tac >>
  rw[Once Forall2_cases] >>
  qpat_x_assum `Forall2 _ l' _` mp_tac >>
  rw[Once Forall2_cases] >>
  PairCases_on `x'` >> rw[] >>
  Cases_on `hImpl.put H x x'1` >> rw[]
QED

(*
Lemma reducible_red π ψ:
  π ≫HC ψ -> reducible (≻C) ψ -> reducible (≻H) π.
Proof.
  intros rep (ψ'&?&R). inv R; inv rep; inv_Mheap.
  2:edestruct nth_error_unlinedEnv as (?&?&?);[eassumption..|inv_Mheap].
  4:edestruct (put H (p,a) a0) eqn:eq.
  all:now eexists _,_;econstructor; eassumption.
Qed.
*)

Theorem heap_clos_refinement:
  HR hImpl ⇒
  refinement_M (repsHC hImpl C) (stepH hImpl C τ) (stepH hImpl C β) (stepC τ) (stepC β)
Proof
  rw[refinement_M]
  >- (drule reducible_red >> rw[] >>
      fs[reducible, any, RUNION]
      >- (`∃x' l. stepH hImpl C l a x'` by metis_tac[] >>
          Cases_on `l` >> metis_tac[])
      >> `∃x' l. stepH hImpl C l a x'` by metis_tac[] >>
      Cases_on `l` >> metis_tac[])
  >> metis_tac[step_simulation]
QED

(*
Lemma heap_clos_refinement :
  refinement_M (≫HC).
Proof.
  split.
  -apply reducible_red.
  -eauto using step_simulation.
Qed.
*)

Theorem compile_heap_clos:
  ∀hImpl C p a H P.
    representsPro C p P ⇒
    representsEnv hImpl C H a [] ⇒
    repsHC hImpl C ([(p,a)],[],H) ([closC P []],[])
Proof
  rw[repsHC_cases, Once Forall2_cases]
  >- rw[Once representsClos_cases]
  >> rw[Once Forall2_cases]
QED

Definition repsHL:
  repsHL hImpl C = rcomp (repsHC hImpl C ) repsCL
End

(*
Definition repsHL := rcomp (≫HC) (≫CL).
Notation "(≫HL)" := (repsHL) (at level 0).
Notation "ψ ≫HL s" := (repsHL ψ s) (at level 70).
*)

Theorem heap_L_refinement:
  HR hImpl ⇒
  refinement_ARS (repsHL hImpl C) (stepH hImpl C τ) (stepH hImpl C β) stepL
Proof
  rw[repsHL, rcomp] >>
  metis_tac[composition, heap_clos_refinement, clos_L_refinement]
QED

Theorem compile_heap_L:
  ∀hImpl C p a H s.
    closedL s ⇒
    HR hImpl ⇒
    representsPro C p (gamma s retT) ⇒
    representsEnv hImpl C H a [] ⇒
    repsHL hImpl C ([(p,a)],[],H) s
Proof
  rw[repsHL, rcomp] >>
  drule_all compile_heap_clos >> rw[] >>
  drule compile_clos_L >> rw[] >>
  metis_tac[]
QED

val _ = export_theory ()