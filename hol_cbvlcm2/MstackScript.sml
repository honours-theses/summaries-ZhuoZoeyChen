open HolKernel Parse boolLib bossLib;
open arithmeticTheory;
open listTheory;
open PrelimsTheory;
open LTheory;
open RefinementsTheory;
open ProgramsTheory;

val _ = new_theory "Mstack";


Definition stateS : Type := list Pro*list Pro.
Hint Transparent stateS.

(* Reserved Notation "σ ≻S_ l σ'" (at level 70, l at level 0,format "σ '≻S_' l σ'"). *)

Inductive stepS:

End

Inductive stepS : label -> stateS -> stateS -> Prop:=
| stepS_betaC P Q R T V:
    ((appT P) :: T,R :: Q ::V) ≻S_β (substP Q 0 R :: P :: T,V)
| stepS_pushVal P Q T V:
    (lamT Q P::T,V) ≻S_τ (P::T,Q::V)
| stepS_nil T V:
    (retT::T,V) ≻S_τ (T,V)
where "σ ≻S_ l σ'" := (stepS l σ σ').

Notation "(≻S_ l )" := (stepS l) (at level 0, format "'(≻S_' l ')'").
(* workaround to prefere "x ≻ y" over "(≻) x y"*) Notation "σ ≻S_ l σ'" := 0.
Notation "σ ≻S_ l σ'" := (stepS l σ σ').
Notation "(≻S)" := (any stepS) (at level 0).
Notation "σ ≻S σ'" := (any stepS σ σ') (at level 70).

Canonical Structure stack_machine := {| M_rel := stepS |}.

Hint Constructors stepS.

Lemma tau_functional :
  functional (≻S_β).
Proof.
  inversion 1. inversion 1. congruence.
Qed.
Lemma beta_functional :
  functional (≻S_β).
Proof.
  inversion 1. inversion 1. congruence.
Qed.
Lemma stepS_functional :
  functional (≻S).
Proof.
  intros ? ? ? [? R1] [? R2]. inv R1;inv R2;congruence.
Qed.
Lemma tau_terminating σ:
  terminatesOn (≻S_τ) σ.
Proof.
  destruct σ as (T,V). induction T as [|P T] in V|-*.
  -constructor;intros ? R. inv R.
  -induction P in V|-*.
   all:constructor;intros ? R;inv R.
   all:easy.
Qed.
Lemma beta_terminating σ:
  terminatesOn (≻S_β) σ.
Proof.
  destruct σ as (T,V). revert T. induction V using (size_induction (f:=@length _));intros T.
  constructor. intros ? R. inv R. eapply H. cbn;omega.
Qed.
Function δT T A : option (list term) :=
  match T with
    [] => Some A
  | P::T' => match δ P A with
            | Some A' => δT T' A'
            | _ => None
            end
  end.

Function δV V : option (list term) :=
  match V with
  | [] => Some []
  | P::V' => match δ P [],δV V' with
              Some [s],Some A => Some (lam s::A)
            | _,_ => None
            end
  end.

Definition repsSL : stateS -> term -> Prop :=
  fun '(T,V) s => exists A, δV V = Some A /\ δT T A = Some [s].
Notation "(≫SL)" := (repsSL) (at level 0).
Notation "σ ≫SL s" := (repsSL σ s) (at level 70).

Lemma repsSL_functional :
  functional (≫SL).
Proof.
  hnf. unfold repsSL. intros (T,V) ? ?. firstorder subst. congruence.
Qed.
Lemma repsSL_computable :
  computable (≫SL).
Proof.
  exists (fun '(T,V) => try A := δV V in match δT T A with Some [s] => Some s | _ => None end). intros [T V];hnf.
  unfold repsSL. destruct δV. 2:firstorder congruence.
  destruct δT as [[|? []]|] eqn:eq. 2:eauto. all:intros ? (A&[= ->]&?). all:congruence.
Qed.
Only in COq, to prettify reasoning
Lemma decompileTask_inv P T A B:
  δT (P:: T) A = Some B -> exists A', δ P A = Some A' /\ δT T A' = Some B.
  functional inversion 1;subst. eauto.
Qed.

Only in Coq, to prettify reasoning
Lemma decompileTask_step P T A A':
  δ P A = Some A' -> δT (P:: T) A = δT T A'.
Proof.
  cbn. now intros ->.
Qed.
Only in Coq, to prettify reasoning
Lemma decompileArg_inv P V A:
  δV (P::V) = Some A -> exists s A', A=(lam s)::A' /\ δ P [] = Some [s] /\ δV V = Some A'.
Proof.
  functional inversion 1;subst. eauto.
Qed.
Only in Coq, to prettify reasoning
Lemma decompileArg_step P V s A :
  δ P [] = Some [s] -> δV V = Some A -> δV (P::V) = Some (lam s::A).
Proof.
  cbn. intros -> ->. tauto.
Qed.
Lemma tau_simulation T V T' V' s :
  (T,V) ≫SL s -> (T,V) ≻S_τ (T',V') -> (T',V') ≫SL s.
Proof.
  intros (A&repV&repT) R. inv R.
  -eapply decompileTask_inv in repT as (A'&rep'&eq1).
   eapply decompile_lamT_inv in rep' as (t&eq2&eq3).
   exists (lam t :: A).
   erewrite decompileArg_step. 2-3:eassumption.
   erewrite decompileTask_step. all:eauto.
  -cbn in *. eauto.
Qed.
Lemma decompileArg_abstractions V A:
  δV V = Some A -> Forall abstraction A.
Proof.
  revert A. functional induction (δV V);intros ? H;inv H. all:eauto.
Qed.
Here should be two lemmas only shown in the paper
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
Qed.

val _ = export_theory ()
