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
(* Notation "P / E" := (closC P E). *)
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

(* Reserved Notation "P <C k" (at level 70). *)
Inductive boundC:
  ∀k P E. boundP P (k+LENGTH E) ∧ (∀e. MEM e E ⇒ boundC e 1) ⇒ boundC (closC P E) k
End

Theorem translateC_boundP:
  ∀e k. boundC e k ⇒ boundP (deltaC k e) k
Proof
  Induct_on `boundC` >>
  rw[] >> rw[Once deltaC] >>
  irule substP_boundP >> rw[Forall_forall,MEM_MAP] >>
  res_tac
QED

val _ = export_theory ()