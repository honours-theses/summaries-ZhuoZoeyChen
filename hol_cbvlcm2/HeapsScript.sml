open PrelimsTheory;
open ClosuresTheory;
open CodesTheory;

val _ = new_theory "Heaps";

(* ---------------------
           Heaps
   --------------------- *)



(*
Class heap PA :=
  {
    Heap : Type;
    HA : Set;
    HC := (PA * HA) % type;
    HE := option (HC * HA);
    get : Heap -> HA -> option HE;
    put : Heap -> HC -> HA -> Heap*HA;
    extended H H' := forall a, get H a <> None -> get H a = get H' a;
    HR1: forall H g a H' b, put H g a = (H', b) -> get H' b = Some (Some (g,a));
    HR2: forall H g a H' b, put H g a = (H', b) -> extended H H';
  }.

Coercion get : Heap >-> Funclass.

Section heap.
  Variable codeImpl : code.
  Variable C : Code.
  Variable heapImpl : heap PA.
  Implicit Type H : Heap.

  Reserved Notation "a ≫E_ H E" (at level 70, H at level 0, format "a '≫E_' H E").

  Inductive representsEnv H : HA -> list Clo -> Prop :=
  | representsEnvNil a:
      H a = Some None ->
      a ≫E_H []
  | representsEnvCons a b c p P F E:
      H a = Some(Some ((p,b),c)) ->
      p ≫p_C P ->
      b ≫E_H F ->
      c ≫E_H E ->
      a ≫E_H (P/F)::E
  where "a ≫E_ H E" := (representsEnv H a E).

  Hint Constructors representsEnv.

  Lemma representsEnv_functional H:
  functional (representsEnv H).
  Proof.
    intros a E E' H1. induction H1 in E'|-*; inversion 1;try congruence;repeat f_equal. all:rewrite H0 in H3;inv H3. all:now try eapply representsPro_functional;eauto.
  Qed.
  Lemma representsEnv_extend H H' a E :
    extended H H' -> a ≫E_H E -> a ≫E_H' E.
  Proof.
    intros ext. induction 1 as [? eq|? ? ? ? ? ? ? eq].
    -econstructor. erewrite ext in eq. eauto. congruence.
    -econstructor. 2-4:now eauto.
     erewrite ext in eq. eauto. congruence.
  Qed.
  Reserved Notation "g ≫C_ H e" (at level 70,H at level 0, format "g '≫C_' H e").

  Inductive representsClos H : HC -> Clo -> Prop :=
    representsClos_C p a P E : p ≫p_C P -> a ≫E_H E -> (p,a) ≫C_H P/E
  where "g ≫C_ H e" := (representsClos H g e).
  Hint Constructors representsClos.

  Notation "(≫C( H ) )" := (representsClos H) (at level 0, format "'(≫C(' H ')' ')'").
  (* workaround to prefere "x ≻ y" over "(≻) x y"*) Notation "g ≫C_ H e" := 0.
  Notation "g ≫C_ H e" := (representsClos H g e).

  Lemma representsClos_extend H H' g e :
    extended H H' -> g ≫C_H e -> g ≫C_H' e.
  Proof.
    intros ext. inversion 1. all:eauto using representsEnv_extend.
  Qed.

  Fixpoint lookup H a n : option HC:=
    match H a with
      Some (Some (g,a')) =>
      match n with
        0 => Some g
      | S n=> lookup H a' n
      end
    | _ => None
    end.
  Notation "H .[ a , n ]" := (lookup H a n) (at level 1, format "H '.[' a ',' n ]").

  Lemma nth_error_unlinedEnv H a E n e :
    a ≫E_H E -> E.[n] = Some e -> exists g, H.[a,n] = Some g /\ g ≫C_H e.
  Proof.
    induction n in e,a,E|-*;cbn;intros uE eq.
    -inv uE. congruence. inv eq. rewrite H0. eauto.
    -inv uE. congruence. rewrite H0. eapply IHn. all:eauto.
  Qed.
  Lemma lookup_unlinedEnv H a E n g :
    a ≫E_H E -> H.[a,n] = Some g -> exists e, E.[n] = Some e /\ g ≫C_H e.
  Proof.
    induction n in g,a,E|-*;cbn;intros uE eq.
    -inv uE;rewrite H0 in *. all:inv eq. eauto.
    -inv uE;rewrite H0 in *. congruence. now eauto.
  Qed.
End heap.

  Notation "H .[ a , n ]" := (lookup H a n) (at level 1, format "H '.[' a ',' n ]").

Hint Constructors representsClos representsEnv.

Instance heapImpl PA: heap PA :=
  {|
    Heap:=list ((PA*nat)*nat);
    HA := nat;
    put H g a:=(H++[(g,a)],S (length H));
    get H a := match a with
                   | 0 => Some None
                   | S a =>
                     match H.[a] with
                     | Some (g,b) => Some (Some (g,b))
                     | None => None
                     end
                   end
  |}.
Proof.
  -intros ? ? ? ? ? [= <- <-]. rewrite nth_error_app2. now rewrite <- minus_n_n. reflexivity.
  -intros ? ? ? ? ? [= <- <-] [|] neq. easy. destruct nth_error as [[? ?]|] eqn:eq. 2:easy.
   rewrite nth_error_app1;eauto using nth_error_Some_lt. now rewrite eq.
Defined
*)

val _ = export_theory ()