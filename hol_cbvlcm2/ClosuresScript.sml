open HolKernel Parse boolLib bossLib;
open arithmeticTheory;
open listTheory;
open PrelimsTheory;
open ProgramsTheory;

val _ = new_theory "Closures";

(*
Inductive Clo := closC (P:Pro) (E : list Clo).

Subtitution Lemmas
Fixpoint substPl P (k:nat) W: Pro:=
  match P with
    retT => retT
  | varT n P =>
    let P' := substPl P k W in
    if Dec (k>n) then varT n P' else
      match W.[n-k] with
        Some Q => lamT Q P'
      | _ => varT n P'
      end
  | lamT Q P => lamT (substPl Q (S k) W) (substPl P k W)
  | appT P => appT (substPl P k W)
  end.

Lemma substPl_nil P k:
  substPl P k [] = P.
Proof.
  induction P in k |-*. all:cbn.
  1,3,4:congruence.
  decide (k>n). congruence.
  rewrite (proj2 (nth_error_None _ _)). 2:cbn;omega.
  congruence.
Qed.
Lemma boundP_mono P k k':
  P <P k-> k <= k' -> P <P k'.
Proof.
  intros bnd. induction bnd in k'|-*;intros gt. all:cbn.
  -constructor.
  -constructor. omega. eauto.
  -constructor. now apply IHbnd1;omega. now eapply IHbnd2.
  -constructor. eauto.
Qed.
Lemma boundP_substP P Q k:
  P <P k -> substP P k Q = P.
Proof.
  intros bnd. induction bnd. all:cbn.
  -reflexivity.
  -decide _. omega. now rewrite IHbnd.
  -rewrite IHbnd1,IHbnd2. reflexivity.
  -now rewrite IHbnd.
Qed.
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