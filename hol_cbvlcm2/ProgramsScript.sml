open HolKernel Parse boolLib bossLib;
open arithmeticTheory;
open listTheory;
open PrelimsTheory;
open LTheory;
open RefinementsTheory;

val _ = new_theory "Programs";

Datatype:
  Pro = retT | varT num Pro | appT Pro | lamT Pro Pro
End

(* Inductive Pro := retT | varT (n:nat) (P:Pro) | appT (P:Pro) | lamT (Q P:Pro). *)

(* compilation function γ : Ter → Pro → Pro
    translates terms into programs: *)
Definition gamma:
  gamma s P =
    case s of
      | var n => varT n P
      | app s t => gamma s (gamma t (appT P))
      | lam s => lamT (gamma s retT) P
End

(* Implicit Types A B : list term. *)

(* decompilation function δ P A of type Pro → L(Term) → O(L(Term))
    translates programs into terms *)
Definition delta:
  delta P A =
    case P of
    | retT => SOME A
    | varT n P => delta P (var n ::A)
    | lamT Q P =>
      (case (delta Q []) of
        | SOME [s] => delta P (lam s::A)
        | _ => NONE)
    | appT P =>
      (case A of
        | t::s::A => delta P (app s t::A)
        | _ => NONE)
End

(* Fact 10 *)
Theorem decompile_correct:
  ∀P A s. delta (gamma s P) A = delta P (s::A)
Proof
  Induct_on `s`
  >- (rw[Once gamma] >> rw[Once delta])
  >- (rw[Once gamma] >> rw[Once delta])
  >> rw[Once gamma] >> rw[Once delta] >> rw[Once delta]
QED

Definition repsP:
  repsP P s ⇔ delta P [] = SOME [s]
End

(* Definition repsP P s := δ P [] = Some [s].
Notation "P ≫P s" := (repsP P s ) (at level 70).
Notation "(>>P)" := repsP (at level 0).*)

(* Fact 11 *)
Theorem decompile_append:
  ∀P A A' B.
    delta P A = SOME A' ⇒ delta P (A ++ B) = SOME (A' ++ B)
Proof
  Induct_on `P` >> rw[]
  >- fs[Once delta]
  >- (gs[Once delta] >> first_x_assum drule >> rw[] >>
      simp[Once delta])
  >- (gs[Once delta] >> Cases_on `A` >> fs[] >>
      Cases_on `t` >> fs[] >> first_x_assum drule >> rw[] >>
      simp[Once delta])
  >> gs[Once delta] >>
  Cases_on `delta P []` >> fs[] >>
  Cases_on `x` >> fs[] >>
  simp[Once delta] >> Cases_on `t` >> gs[] >> rw[] >>
  first_x_assum drule >> rw[]
QED

(*Some lemmas to simplify reasoning*)

Theorem decompile_lamT_inv:
  ∀Q P A B.
    delta (lamT Q P) A = SOME B ⇒
    (∃s. delta Q [] = SOME [s] ∧ delta P (lam s::A) = SOME B)
Proof
  rw[Once delta] >> Cases_on `delta Q []` >> fs[] >>
  Cases_on `x` >> fs[] >> Cases_on `t` >> fs[]
QED

Definition substP:
  substP P k R =
    case P of
      retT => retT
    | varT n P =>
      if (n = k) then lamT R (substP P k R) else varT n (substP P k R)
    | lamT Q P => lamT (substP Q (SUC k) R) (substP P k R)
    | appT P => appT (substP P k R)
End

Theorem decompile_empty_A_empty:
  ∀P A. delta P A = SOME [] ⇒ A = []
Proof
  Induct_on `P` >> rw[] >> fs[]
  >- fs[Once delta]
  >- (pop_assum mp_tac >> rw[Once delta] >>
      first_x_assum (qspecl_then [`var n :: A`] ASSUME_TAC) >>
      first_x_assum drule >> rw[])
  >- (pop_assum mp_tac >> rw[Once delta] >>
      Cases_on `A` >> fs[] >>
      Cases_on `t` >> fs[] >>
      first_x_assum (qspecl_then [`app h' h::t'`] ASSUME_TAC) >>
      first_x_assum drule >> rw[])
  >> pop_assum mp_tac >> rw[Once delta] >>
  Cases_on `delta P []` >> rw[] >> fs[] >>
  Cases_on `x` >> rw[] >> fs[] >>
  Cases_on `t` >> rw[] >> fs[] >>
  `delta P' (lam h::A) = SOME [] ⇒ (lam h::A) = []` by metis_tac[] >>
  first_x_assum drule >> rw[]
QED

Theorem substP_rep_subst':
  ∀Q A R t B k R.
    repsP R t ⇒
    delta Q A = SOME B ⇒
    (delta (substP Q k R) (MAP (λs. subst s k (lam t)) A)
      = SOME (MAP (λs. subst s k (lam t)) B))
Proof
  ho_match_mp_tac delta_ind >> rw[repsP] >>
  pop_assum mp_tac >> simp[Once delta] >>
  simp[AllCaseEqs()] >> rw[]
  >- (simp[Once substP] >> fs[Once delta])
  >- (first_x_assum drule >> rw[] >>
      simp[Once substP] >> Cases_on `n = k` >> rw[]
      >- (simp[Once delta] >>
          first_x_assum (qspecl_then [`k`] ASSUME_TAC) >>
          fs[Once subst])
      >> simp[Once delta] >>
      first_x_assum (qspecl_then [`k`] ASSUME_TAC) >>
      pop_assum mp_tac >> rw[Once subst])
  >- (first_x_assum drule >> rw[] >>
      simp[Once substP] >> simp[Once delta] >>
      first_x_assum (qspecl_then [`k`] ASSUME_TAC) >>
      fs[Once subst])
  >> simp[Once substP, Once delta] >> gvs[] >>
  first_x_assum (qspecl_then [`t`] ASSUME_TAC) >>
  first_x_assum (drule_then assume_tac) >> gvs[] >>
  last_x_assum (qspecl_then [`t`] ASSUME_TAC) >>
  first_x_assum (drule_then assume_tac) >> gvs[] >>
  pop_assum mp_tac >> simp[Once subst]
QED

Inductive boundL:
  (∀k n. n < k ⇒ boundL (var n) k) ∧
  (∀k s t. boundL s k ∧ boundL t k ⇒ boundL (app s t) k) ∧
  (∀k s. boundL s (SUC k) ⇒ boundL (lam s) k)
End

Definition closedL:
  closedL s = boundL s 0
End

Inductive boundP:
  (∀k. boundP retT k) ∧
  (∀n k P. n < k ∧ boundP P k ⇒ boundP (varT n P) k) ∧
  (∀k Q P. boundP Q (SUC k) ∧ boundP P k ⇒ boundP (lamT Q P) k) ∧
  (∀k P. boundP P k ⇒ boundP (appT P) k)
End

Definition closedP:
  closedP P = boundP P 0
End

Theorem bound_compile:
  ∀s k P. boundL s k ⇒ boundP P k ⇒ boundP (gamma s P) k
Proof
  Induct_on `boundL` >> rw[] >> rw[Once gamma] >> metis_tac[boundP_rules]
QED

val _ = export_theory ()