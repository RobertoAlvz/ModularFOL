Require Import Coq.Vectors.Vector.
From Coq Require Import List.
Import ListNotations.

Class Signature := Sig { Funcs : Type; f_ar : Funcs -> nat ; Preds : Type; p_ar : Preds -> nat }.

Context {Sigma : Signature}.

Inductive term : Type :=
  | Var (x : nat)
  | Func : forall f:Funcs, Vector.t term (f_ar f) -> term.

Fixpoint subst_term (sigma : nat -> term) (s : term) : term :=
match s with 
  | Var n => sigma n
  | Func f args => Func f (Vector.map (subst_term sigma) args)
end.

Variable formula : Type.
Variable subst : (nat -> term) -> formula -> formula.
Notation "[ A ] p" := (subst A p) (at level 31).

Inductive f_atomic : Type -> Type :=
  | Pred : forall (P : Preds), Vector.t term (p_ar P) -> f_atomic formula
  | Bot : f_atomic formula.
Notation "⊥" := (Bot).

Definition subst_atomic (sigma : nat -> term) (s : f_atomic formula) : f_atomic formula :=
match s with
  | ⊥ => ⊥
  | Pred P args => Pred P (Vector.map (subst_term sigma) args)
end.

Inductive f_implicative : Type -> Type :=
  | Imp : formula -> formula -> f_implicative formula.
Notation "p ~> q" := (Imp p q) (at level 51, right associativity).
(* Notation "! p" := (p ~> Bot) (at level 35, right associativity). *)

Definition subst_implicative (sigma : nat -> term) (s : f_implicative formula) : f_implicative formula :=
match s with
  | p ~> q => [sigma]p ~> [sigma]q
end.

Inductive f_universal : Type -> Type :=
  | Univ : formula -> f_universal formula.
Notation "∀ p" := (Univ p) (at level 52).

Definition subst_universal (sigma : nat -> term) (s : f_universal formula) : f_universal formula :=
match s with
  | ∀ p => ∀ [fun n => sigma (S n)]p
end.

Reserved Notation "A |- p" (at level 70).
Inductive deduction (A : list formula) : formula -> Prop :=
  | ndHyp p : In p A -> A |- p
where "A |- p" := (deduction A p).


Reserved Notation "A |-_atm p" (at level 70).
Inductive deduction_atomic (A : list formula) : f_atomic formula -> Prop :=
  | ndExp p  : A |-_atm ⊥  ->  A |-_atm p
where "H |-_atm p" := (deduction_atomic H p).

Reserved Notation "A |-_imp p" (at level 70).
Inductive deduction_implicative (A : list formula) : formula + f_implicative formula -> Prop :=
  | ndII p q : p::A |- q  -> A |-_imp inr (p ~> q)
  | ndIE p q : A |-_imp inr (p ~> q)  ->  A |- p  -> A |-_imp inl q
where "A |-_imp p" := (deduction_implicative A p).


Definition instantiate t := subst (fun n => match n with 0 => t | n => Var n end).
Definition shifted := map (subst (fun n => Var (S n))).

Reserved Notation "A |-_unv p" (at level 70).
Inductive deduction_universal (A : list formula) : formula + f_universal formula -> Prop :=
  | ndUI p : shifted A |-_unv inl p -> A |-_unv inr (∀ p)
  | ndUE t p : A |-_unv inr (∀ p) -> A |-_unv inl (instantiate t p)
where "A |-_unv p" := (deduction_universal A p).

Lemma weakening A B p : A |- p -> incl A B -> B |- p.
Proof. induction 1; intro Hinc.
  -apply ndHyp. now apply (Hinc p).
Qed.

Lemma weakening_atm A B p : A |-_atm p -> incl A B -> B |-_atm p.
Proof. induction 1 as [ p nd ]; intro Hinc.
  -now apply ndExp, IHnd.
Qed.

Lemma weakening_imp A B p : A |-_imp p -> incl A B -> B |-_imp p.
Proof. induction 1 as [ p q nd | p q nd ]; intro Hinc.
  -apply ndII, (weakening (p::A)). assumption.
   intros a [Hh | Ht]. now left. right. now apply (Hinc a).
  -apply (ndIE _ p q). now apply IHnd. now apply (weakening A).
Qed.

Lemma weakening_unv A B p : A |-_unv p -> incl A B -> B |-_unv p.
Proof. revert A B. induction 1 as [ Hs p nd | Hs t p nd ]; intro Hinc.
  -apply ndUI. admit.
  -now apply ndUE, IHnd.
Admitted.


(* TODO  define implicative+falsity variant to proove A|-p -> A|-(p~>⊥)~>⊥ *)

Inductive f_1 : Type :=
  | inj_atm (a : f_atomic f_1)
  | inj_imp (i : f_implicative f_1).
