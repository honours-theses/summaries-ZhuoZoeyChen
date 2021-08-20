open PrelimsTheory;
open ClosuresTheory;
open CodesTheory;

val _ = new_theory "Heaps";

(* ---------------------
           Heaps
   --------------------- *)

Type Heap = ``:(('a # num) # num) list``;
Type HA = ``:num``;
Type HC = ``:'a # HA``;
Type HE = ``:(('a HC) # HA) option``;

Datatype:
  heap =
    <|
      get : 'a Heap -> HA -> ('a HE) option;
      put : 'a Heap -> 'a HC -> HA -> ('a Heap) # HA;
    |>
End

Definition extended:
  extended H H' hImpl =
    ∀a. hImpl.get H a ≠ NONE ⇒ hImpl.get H a = hImpl.get H' a
End

Definition HR1:
  HR1 hImpl =
    ∀H g a H' b.
      hImpl.put H g a = (H', b) ⇒ hImpl.get H' b = SOME (SOME (g,a))
End

Definition HR2:
  HR2 hImpl =
    ∀H g a H' b.
      hImpl.put H g a = (H', b) ⇒ extended H H' hImpl
End

Definition HR:
  HR hImpl = (HR1 hImpl ∧ HR2 hImpl)
End

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
*)

(*
Section heap.
  Variable codeImpl : code.
  Variable C : Code.
  Variable heapImpl : heap PA.
  Implicit Type H : Heap.
*)

(* Reserved Notation "a ≫E_ H E" (at level 70, H at level 0, format "a '≫E_' H E"). *)
(* "a ≫E_ H E" := (representsEnv H a E). *)
(* HA -> list Clo -> Prop *)
Inductive representsEnv:
[~Nil:]
  (∀hImpl C H a. hImpl.get H a = SOME NONE ⇒ representsEnv hImpl C H a []) ∧
[~Cons:]
  (∀hImpl C H a b c p P F E.
         hImpl.get H a = SOME (SOME ((p, b), c)) ∧
         representsPro C p P ∧
         representsEnv hImpl C H b F ∧
         representsEnv hImpl C H c E ⇒
         representsEnv hImpl C H a ((closC P F)::E)
  )
End

Theorem representsEnv_functional:
  ∀hImpl C H. functional (representsEnv hImpl C H)
Proof
  simp[functional] >>
  Induct_on `representsEnv` >> rw[] (* 2 *)
  >- (fs[Once representsEnv_cases] >> fs[])
  >> pop_assum mp_tac >> rw[Once representsEnv_cases] >>
  metis_tac[representsPro_functional, functional]
QED

Theorem representsEnv_extend:
  ∀C hImpl H H' a E.
    extended H H' hImpl ⇒
    representsEnv hImpl C H a E ⇒
    representsEnv hImpl C H' a E
Proof
  Induct_on `representsEnv` >> rw[]
  >- (fs[extended] >>
      `hImpl.get H a ≠ NONE` by fs[] >>
      first_x_assum drule >> rw[] >>
      rw[Once representsEnv_cases])
  >> rw[Once representsEnv_cases] >>
  qexistsl_tac [`a'`, `a''`, `p`] >> rw[] >>
  fs[extended] >>
  `hImpl.get H a ≠ NONE` by fs[] >>
  first_x_assum drule >> rw[]
QED

(*  Reserved Notation "g ≫C_ H e" (at level 70,H at level 0, format "g '≫C_' H e"). *)
Inductive representsClos:
[~C:]
  (∀hImpl p a P E.
    representsPro C p P ∧
    representsEnv hImpl C H a E ⇒
    representsClos hImpl C H (p,a) (closC P E))
End

(*
  Inductive representsClos H : HC -> Clo -> Prop :=
    representsClos_C p a P E : p ≫p_C P -> a ≫E_H E -> (p,a) ≫C_H P/E
  where "g ≫C_ H e" := (representsClos H g e).
  Hint Constructors representsClos.

  Notation "(≫C( H ) )" := (representsClos H) (at level 0, format "'(≫C(' H ')' ')'").
  Notation "g ≫C_ H e" := 0.
  Notation "g ≫C_ H e" := (representsClos H g e).
*)

Theorem representsClos_extend:
  ∀H H' g e hImpl C.
    extended H H' hImpl ⇒
    representsClos hImpl C H g e ⇒
    representsClos hImpl C H' g e
Proof
  rw[] >> fs[Once representsClos_cases] >>
  metis_tac[representsEnv_extend]
QED

(* Notation "H .[ a , n ]" := (lookup H a n) (at level 1, format "H '.[' a ',' n ]"). *)
Definition lookup:
  lookup hImpl H a n =
    case (hImpl.get H a) of
      SOME (SOME (g, a')) =>
        (case n of
          0 => SOME g
        | SUC n => lookup hImpl H a' n)
      | _ => NONE
End

Theorem nth_error_unlinedEnv:
  ∀hImpl C H a E n e.
    representsEnv hImpl C H a E ⇒
    nth_error n E = SOME e ⇒
    (∃g. lookup hImpl H a n = SOME g ∧
         representsClos hImpl C H g e)
Proof
  Induct_on `n` >> rw[]
  >- cheat
  >> cheat
QED


(*
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

Definition heapImpl:
  heapImpl =
    <|
      put := (λH g a. (H++[(g,a)], SUC (LENGTH H)));
      get := (λH a. case a of
                     | 0 => SOME NONE
                     | SUC a =>
                       (case nth_error a H of
                        | SOME (g,b) => SOME (SOME (g,b))
                        | NONE => NONE)
             )
    |>
End

val _ = export_theory ()