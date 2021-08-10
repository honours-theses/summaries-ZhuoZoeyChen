open HolKernel Parse boolLib bossLib;
open arithmeticTheory;
open listTheory;
open PrelimsTheory;
open ProgramsTheory;

val _ = new_theory "Closures";

(* ------------------
        Closures
   ------------------ *)

(* A closure is a pair consisting of a program and an environment.
   An environment is a list of closures representing a delayed substitution.
*)
Datatype:
  Clo = closC Pro (Clo list)
End
val _ = export_rewrites ["Clo_size_def"]
(* With closures we can refine the naive stack machine
   so that no substitution operation is needed.
*)

(* ---------------------
     Substituion Lemmas
   --------------------- *)

(* substPl stands for parallel substitution operation*)
(* decompilation of closures into plain programs *)
(* W ranges over lists of programs *)
Definition substPl:
  substPl P k W =
    case P of
      retT => retT
    | varT n P =>
      (let P' = substPl P k W in
      if (k>n) then varT n P' else
        case (nth_error (n-k) W) of
          SOME Q => lamT Q P'
        | _ => varT n P')
    | lamT Q P => lamT (substPl Q (SUC k) W) (substPl P k W)
    | appT P => appT (substPl P k W)
End

(* Fact 29. (Parallel Substitution) *)

(* Fact 29.1 *)
Theorem substPl_nil:
  ∀P k. substPl P k [] = P
Proof
  Induct_on `P` >> rw[Once substPl, Once nth_error]
QED

(* Fact 29.2 *)
Theorem boundP_mono:
  ∀P k k'.
    boundP P k ⇒
    k <= k' ⇒
    boundP P k'
Proof
  Induct_on `boundP` >> rw[] >>
  rw[Once boundP_cases]
QED

(* Fact 29.3 *)
Theorem boundP_substP:
  ∀P Q k.
    boundP P k ⇒ substP P k Q = P
Proof
  Induct_on `boundP` >> rw[] >>
  rw[Once substP]
QED

(* Fact 29.4 *)
Theorem substPl_cons:
  ∀P k W Q.
    Forall (λx. boundP x 1) W ⇒
    substPl P k (Q::W) = substP (substPl P (SUC k) W) k Q
Proof
  Induct_on `P` >> rw[] (* 4 *)
  (* retT *)
  >- (rw[Once substPl] >> rw[Once substPl] >> rw[Once substP])
  (* varT *)
  >- (first_x_assum drule >> rw[] >>
      rw[Once substPl]
      >- (`substP (substPl (varT n P) (SUC k) W') k Q =
           varT n (substP (substPl P (SUC k) W') k Q)`
            suffices_by simp[] >>
          rw[Once substPl] >> rw[Once substP])
      >> fs[NOT_GREATER] >>
      Cases_on `nth_error (n − k) (Q::W')` >> rw[]
      >- (`substP (substPl (varT n P) (SUC k) W') k Q =
           varT n (substP (substPl P (SUC k) W') k Q)`
            suffices_by simp[] >> rw[Once substPl]
          >- (`LENGTH (Q::W') ≤ (n-k)` by fs[nth_error_NONE_lt] >>
              fs[ADD1])
          >> fs[NOT_GREATER] >> rw[] >>
          `LENGTH (Q::W') ≤ (n-k)` by fs[nth_error_NONE_lt] >>
          fs[ADD1] >> rw[] >>
          `LENGTH W' ≤ n - (k + 1)` by fs[] >>
          rw[nth_error_lt_NONE] >> rw[Once substP])
      >> `substP (substPl (varT n P) (SUC k) W') k Q =
          lamT x (substP (substPl P (SUC k) W') k Q)`
            suffices_by simp[] >> rw[Once substPl]
      >- (rw[Once substP] >> fs[ADD1] >> `k = n` by fs[] >>
          rw[] >> fs[] >> fs[nth_error])
      >> fs[NOT_GREATER, ADD1] >>
      drule nth_error_SOME_lemma >> rw[] >>
      rw[Once substP] >>
      drule nth_error_SOME_in_H >> rw[] >>
      drule_all Forall_MEM >> rw[] >>
      drule boundP_mono >> rw[] >>
      Cases_on `1 ≤ (SUC k)` >> rw[]
      >- (first_x_assum drule >> rw[] >> metis_tac[boundP_substP])
      >> fs[NOT_GREATER])
  (* appT *)
  >- (first_x_assum drule >> rw[] >>
      rw[Once substPl] >>
      `substP (substPl (appT P) (SUC k) W') k Q =
       appT (substP (substPl P (SUC k) W') k Q)`
        suffices_by simp[] >>
      rw[Once substPl] >> rw[Once substP])
  (* lamT *)
  >> first_x_assum drule >> rw[] >>
  rw[Once substPl] >>
  `substP (substPl (lamT P P') (SUC k) W') k Q =
   lamT (substP (substPl P (SUC (SUC k)) W') (SUC k) Q)
   (substP (substPl P' (SUC k) W') k Q)`
    suffices_by simp[] >>
  rw[Once substPl] >> rw[Once substP]
QED

(* Fact 29.5 *)
Theorem substP_boundP:
  ∀P k W.
    Forall (λx. boundP x 1) W ⇒
    boundP P (k + LENGTH W) ⇒
    boundP (substPl P k W) k
Proof
  Induct_on `P` >> rw[]
  >- (rw[Once substPl] >> fs[Once boundP_cases])
  >- (first_x_assum drule >> rw[] >>
      qpat_x_assum `boundP (varT n P) (k + LENGTH W')` mp_tac >>
      rw[Once boundP_cases] >>
      first_x_assum drule >> rw[] >>
      rw[Once substPl]
      >- rw[Once boundP_cases]
      >> fs[NOT_GREATER] >>
      `n - k < LENGTH W'` by fs[] >>
      Cases_on `nth_error (n − k) W'`
      >- (drule nth_error_lt_Some >> rw[])
      >> rw[] >> rw[Once boundP_cases] >>
      drule nth_error_SOME_in_H >> rw[] >>
      drule_all Forall_MEM >> rw[] >>
      drule boundP_mono >> rw[])
  >- (first_x_assum drule >> rw[] >>
      qpat_x_assum `boundP (appT P) (k + LENGTH W')` mp_tac >>
      rw[Once boundP_cases] >>
      first_x_assum drule >> rw[] >>
      rw[Once substPl] >> rw[Once boundP_cases])
  >> first_x_assum drule >> rw[] >>
  first_x_assum drule >> rw[] >>
  qpat_x_assum `boundP (lamT P P') (k + LENGTH W')` mp_tac >>
  rw[Once boundP_cases] >>
  first_x_assum drule >> rw[] >>
  rw[Once substPl] >> rw[Once boundP_cases] >>
  fs[ADD1]
QED

Definition deltaC:
  deltaC k (e: Clo) =
    case e of
      closC C E => substPl C k (MAP (deltaC 1) E)
Termination
  WF_REL_TAC `measure (λ(a, b). Clo_size b)` >> rw[] >>
  Induct_on `E` >> rw[]
  >- rw[]
  >> first_x_assum drule >> rw[]
End

(*
Definition deltaC:
  deltaC k (e: Clo) =
    (let (C, E) = e in
    substPl C k (MAP (deltaC 1) E))
End
*)

(*
Notation "P / E" := (closC P E).

Fixpoint δC k (e:Clo) :=
  let (C,E):=e in
  substPl C k (map (δC 1) E).
*)

(* Reserved Notation "P <C k" (at level 70). *)
Inductive boundC:
  ∀k P E. boundP P (k+LENGTH E) ∧ (∀e. MEM e E ⇒ boundC e 1) ⇒ boundC (closC P E) k
End

Theorem translateC_boundP_1:
  ∀e. boundC e 1 ⇒ boundP (deltaC 1 e) 1
Proof
  Induct >> rw[] >>
  rw[Once deltaC] >>
  irule substP_boundP >> rw[]
  >- (fs[Once boundC_cases] >>
      `∀y. MEM y (MAP (λa. deltaC 1 a) l) ⇒ (λx. boundP x 1) y`
        suffices_by rw[Forall_forall] >> rw[] >>
      `∃z. y = (λa. deltaC 1 a) z ∧ MEM z l`
        by metis_tac[MEM_MAP] >>
      first_x_assum drule >> rw[] >> )
  >> fs[Once boundC_cases]

  fs[Once boundC_cases] >> rw[] >>
  pop_assum mp_tac >> pop_assum mp_tac >>
  Induct_on `boundP` >> rw[]
  >- rw[Once deltaC, Once substPl, Once boundP_cases]
  >- (first_x_assum drule >> rw[] >>
      fs[Once deltaC] >> rw[Once substPl]
      >- rw[Once boundP_cases]
      >> fs[NOT_GREATER] >>
      Cases_on `nth_error (n − 1) (MAP (λa. deltaC 1 a) E)` >> rw[]
      >- (drule nth_error_NONE_lt >> rw[])
      >> rw[Once boundP_cases] >>
      drule nth_error_SOME_in_H >> rw[] >>
      fs[MEM_MAP] >> rw[] >>

    rw[Once deltaC, Once substPl, Once boundP_cases])

  Induct >> rw[] >> pop_assum mp_tac >>
  MAP_EVERY qid_spec_tac [`l`, `P`] >>
  Induct_on `l` >> rw[]
  >- (rw[Once deltaC, substPl_nil] >> fs[Once boundC_cases])
  >> fs[Once boundC_cases] >> rw[Once deltaC] >>
  rw[Once deltaC] >> Cases_on `h` >> rw[] >>

  pop_assum mp_tac >>

  rw[Once deltaC] >>

  Induct >> rw[] >>
  pop_assum mp_tac >>
  MAP_EVERY qid_spec_tac [`l`, `P`] >>
  Induct_on `l` >> rw[]
  >- (rw[Once deltaC, substPl_nil] >> fs[Once boundC_cases])
  >> rw[Once deltaC] >>
  irule substP_boundP >> rw[]
  >- (fs[Once boundC_cases] >>
      `∀y. MEM y (MAP (λa. deltaC 1 a) l) ⇒ (λx. boundP x 1) y`
        suffices_by rw[Forall_forall] >> rw[] >>
      `∃z. y = (λa. deltaC 1 a) z ∧ MEM z l`
        by metis_tac[MEM_MAP] >>
      first_x_assum drule >> rw[] >>)
  >> fs[Once boundC_cases]



QED

Theorem translateC_boundP:
  ∀e k. boundC e k ⇒ boundP (deltaC k e) k
Proof
  Induct_on `e`
  Cases_on `k` >> rw[]
  >- (fs[Once boundC_cases] >> rw[Once deltaC] >>

      )
  >>
  Induct >> rw[] >>
  fs[Once boundC_cases] >>
  rw[Once deltaC] >>
  irule substP_boundP >> rw[] >>
  `∀y. MEM y (MAP (λa. deltaC 1 a) l) ⇒ (λx. boundP x 1) y`
    suffices_by rw[Forall_forall] >> rw[] >>
  `∃z. y = (λa. deltaC 1 a) z ∧ MEM z l`
    by metis_tac[MEM_MAP] >> rw[] >>
  first_x_assum drule >> rw[] >>
  fs[Once boundC_cases] >> rw[] >>
  rw[Once deltaC] >>
  rw[Once substPl] >> Cases_on `P'` >> rw[]
  >- rw[Once boundP_cases]
  >- (rw[Once boundP_cases] >> )

  rw[Once deltaC] >> Cases_on `z` >> rw[] >>
  first_assum drule >>
  `boundP `
  simp[Once boundC_cases]
  strip_tac >>

first_x_assum drule >> rw[] >>
  boundP_substP
  pop_assum mp_tac >> rw[Once boundC_cases] >>

  rw[Once deltaC] >> Cases_on `z` >> rw[] >>





  rw[] >> first_x_assum drule >> rw[] >>
  rw[Once deltaC] >> Cases_on `z` >> rw[] >>
  rw[Once boundP_cases]
  `Forall (λx. boundP x 1) (MAP (λa. deltaC 1 a) l)`
    by (Induct_on `l` >> rw[]
        >- rw[Once Forall_cases]
        >> )
  rw[Once substPl] >>
  fs[Once boundC_cases] >>
  drule boundP_substP >> rw[] >>

  rw[Once boundP_cases]

  LENGTH_MAP
  Forall_forall
  MEM_MAP
QED

(*

Lemma translateC_boundP e k:
  e <C k -> δC k e <P k.
Proof.
  induction 1. cbn.
  apply substP_boundP. 2: now rewrite map_length. eapply Forall_forall.
  setoid_rewrite in_map_iff. intros ? (?&<-&?). eauto.
Qed.
*)

val _ = export_theory ()