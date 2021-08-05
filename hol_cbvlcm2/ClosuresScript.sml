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
  ∀P Q k W.
    Forall (λx. boundP x 1) W ⇒
    substPl P k (Q::W) = substP (substPl P (SUC k) W) k Q
Proof
  cheat
QED

(*


Lemma substPl_cons P Q k W:
  Forall (<P 1) W -> substPl P k (Q::W) = substP (substPl P (S k) W) k Q.
Proof.
  intros cl. induction P in k|-*;cbn.
  -reflexivity.
  -decide (k>n);[|decide (k=n)].
   all:decide (S k > n);try omega;cbn.
   1,2:decide (n=k);try omega.
   +now rewrite IHP.
   +subst k. rewrite minus_diag. cbn. now rewrite IHP.
   +destruct n. 1:omega. rewrite <- minus_Sn_m with (m:=k). 2:omega. cbn.
    destruct nth_error eqn:eq.
    *cbn. erewrite boundP_substP. now rewrite IHP. eapply boundP_mono. eapply Forall_forall with (1:=cl).
     now eauto using nth_error_In. omega.
    *unfold substP;fold substP. decide _. omega. now rewrite IHP.
  -now rewrite IHP.
  -now rewrite IHP1,IHP2.
Qed.
Lemma substP_boundP P k W:
  Forall (<P 1) W -> P <P k + length W -> substPl P k W <P k.
Proof.
  induction P in k |-*. all:cbn;intros cl bnd;inv bnd.
  -constructor.
  -decide _.
   +constructor. all:eauto.
   +edestruct nth_error_lt_Some as (?&eq);[|rewrite eq]. omega. constructor. 2:eauto. eapply boundP_mono. eapply Forall_forall with (1:=cl). now eauto using nth_error_In. omega.
  -constructor. eauto.
  -constructor. all:eauto.
Qed.
Notation "P / E" := (closC P E).

Fixpoint δC k (e:Clo) :=
  let (C,E):=e in
  substPl C k (map (δC 1) E).

Reserved Notation "P <C k" (at level 70).

Inductive boundC : Clo -> nat -> Prop :=
  boundC_C k P E : P <P k+length E -> (forall e, e ∈ E -> e <C 1) -> P/E <C k
where "e <C k" := (boundC e k).
Notation "'(<C' k ')'" := (fun P => P <C k) (at level 0, format "'(<C' k ')'").

Hint Constructors boundC.

Lemma translateC_boundP e k:
  e <C k -> δC k e <P k.
Proof.
  induction 1. cbn.
  apply substP_boundP. 2: now rewrite map_length. eapply Forall_forall.
  setoid_rewrite in_map_iff. intros ? (?&<-&?). eauto.
Qed.
*)

val _ = export_theory ()