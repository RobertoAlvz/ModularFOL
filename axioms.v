(** * General Header Autosubst - Assumptions and Definitions *)

(** ** Axiomatic Assumptions
    For our development, during rewriting of the reduction rules,  we have to extend Coq with two well known axiomatic assumptions, namely _functional extensionality_ and _propositional extensionality_. The latter entails _proof irrelevance_.
*)

(** *** Functional Extensionality
    We import the axiom from the Coq Standard Library and derive a utility tactic to make the assumption practically usable.
*)
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Program.Tactics.

Tactic Notation "nointr" tactic(t) :=
  let m := fresh "marker" in
  pose (m := tt);
  t; revert_until m; clear m.

Ltac fext := nointr repeat (
  match goal with
    [ |- ?x = ?y ] =>
    (refine (@functional_extensionality_dep _ _ _ _ _) ||
     refine (@forall_extensionality _ _ _ _) ||
     refine (@forall_extensionalityP _ _ _ _) ||
     refine (@forall_extensionalityS _ _ _ _)); intro
  end).


(** ** Functor Instances
Exemplary functor instances needed to make Autosubst's generation possible for functors.
Two things are important:
1. The names are fixed.
2. For Coq to check termination, also the proofs have to be closed with Defined.
 *)

(** *** List Instance *)
Require Export List.

Definition funcomp {X Y Z} (g : Y -> Z) (f : X -> Y)  :=
  fun x => g (f x).

Notation "'list_map'" := map.

Definition list_ext {A B} {f g : A -> B} :
  (forall x, f x = g x) -> forall xs,  list_map f xs = map g xs.
  intros H. induction xs. reflexivity.
  cbn. f_equal. apply H. apply IHxs.
Defined.

Definition list_id {A}  { f : A -> A} :
  (forall x, f x = x) -> forall xs, List.map f xs = xs.
Proof.
  intros H. induction xs. reflexivity.
  cbn. rewrite H. rewrite IHxs; eauto.
Defined.

Definition list_comp {A B C} {f: A -> B} {g: B -> C} {h} :
  (forall x, (funcomp  g f) x = h x) -> forall xs, map g (map f xs) = map h xs.
Proof.
  induction xs. reflexivity.
  cbn. rewrite <- H. f_equal. apply IHxs.
Defined.

(** *** Prod Instance *)

Definition prod_map {A B C D} (f : A -> C) (g : B -> D) (p : A * B) :
  C * D.
Proof.
  destruct p. split. auto. auto.
Defined.

Definition prod_id {A B} {f : A -> A} {g : B -> B} :
  (forall x, f x = x) -> (forall x, g x = x) -> forall p, prod_map f g p = p.
Proof.
  intros. destruct p. cbn. f_equal; auto.
Defined.

Definition prod_ext {A B C D} {f f' : A -> C} {g g': B -> D} :
  (forall x, f x = f' x) -> (forall x, g x = g' x) -> forall p, prod_map f g p = prod_map f' g' p.
Proof.
  intros. destruct p. cbn. f_equal; auto.
Defined.

Definition prod_comp {A B C D E F} {f1 : A -> C} {g1 : C -> E} { h1} {f2: B -> D} {g2: D -> F} {h2}:
  (forall x, (funcomp  g1 f1) x = h1 x) -> (forall x, (funcomp g2 f2) x = h2 x) -> forall p, prod_map g1 g2 (prod_map f1 f2 p) = prod_map h1 h2 p.
Proof.
  intros. destruct p. cbn. f_equal; auto.
  now rewrite <- H. now rewrite <- H0.
Defined.


(** *** Function Instance *)

Definition cod X A:  Type :=  X -> A.

Definition cod_map {X} {A B} (f : A -> B) (p : X -> A) :
  X -> B.
Proof. eauto. Defined.

(** Note that this requires functional extensionality. *)
Definition cod_id {X} {A} {f : A -> A} :
  (forall x, f x = x) -> forall (p: X -> A), cod_map f p = p.
Proof. intros H p. unfold cod_map. fext. congruence. Defined.

Definition cod_ext {X} {A B} {f f' : A -> B} :
  (forall x, f x = f' x) -> forall (p: X -> A), cod_map f p = cod_map f' p.
Proof. intros H p. unfold cod_map. fext. congruence. Defined.

Definition cod_comp {X} {A B C} {f : A -> B} {g : B -> C} {h} :
  (forall x, (funcomp g f) x =  h x) -> forall (p: X -> _), cod_map g (cod_map f p) = cod_map h p.
Proof. intros H p. unfold cod_map. fext. intros x. now rewrite <- H. Defined.

Hint Rewrite in_map_iff : FunctorInstances.


Require Import Coq.Vectors.Vector.

Definition vect := Vector.t.
Definition vect_map {A B} (f:A->B) {n} (v : vect A n) : vect B n := Vector.map f v.

Lemma vect_map_id A: forall n (v : vect A n), vect_map (fun x => x) v = v.
Proof. induction v. now reflexivity. unfold vect_map in *. cbn. rewrite <- IHv. congruence. Defined.

Lemma vect_map_ext A B: forall (f g:A->B), (forall a, f a = g a) -> forall n (v : vect A n), vect_map f v = vect_map g v.
Proof. induction v. now reflexivity. unfold vect_map in *. cbn. rewrite IHv. congruence. Defined.

Lemma vect_map_map A B C: forall (f:A->B) (g:B->C) n (v : vect A n), vect_map g (vect_map f v) = vect_map (fun x => g (f x)) v.
Proof. induction v. now reflexivity. unfold vect_map in *. cbn. rewrite IHv. congruence. Defined.

Definition vect_id {A} {f : A -> A} {n} :
  (forall x, f x = x) -> forall (v : vect A n), vect_map f v = v.
Proof. intros H v. unfold vect_map. rewrite <- vect_map_id. now apply vect_map_ext. Defined.

Definition vect_ext {A B} {f f' : A -> B} {n} :
  (forall x, f x = f' x) -> forall (v: vect A n), vect_map f v = vect_map f' v.
Proof. intros H v. unfold vect_map. now apply vect_map_ext. Defined.

Definition vect_comp {A B C} {f : A -> B} {g : B -> C} {n} {h} :
  (forall x, (funcomp g f) x =  h x) -> forall (v: vect _ n), vect_map g (vect_map f v) = vect_map h v.
Proof. intros H v. rewrite vect_map_map. now apply vect_ext. Defined.